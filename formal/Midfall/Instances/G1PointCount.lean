-- |
-- Midfall.Instances.G1PointCount
--
-- **THE POINT COUNT |E(F_p)[r]| = r, AND WITH IT THE LAST G1-SIDE HOLDS CLAUSE.** P-G1CODEC
-- proved g1CodecZ_g1DecodesWidth_iff: g1Decodes for the real-curve codec is EQUIVALENT to
-- surjectivity of g1zToEip onto the frames the precompile accepts, and that surjectivity IS the
-- statement that every r-torsion point of E(F_p) is a multiple of the published generator H1.
-- This file proves it. The G1 side is therefore four-of-four with NO new named assumption: the
-- trusted base does not grow.
--
-- THE ROUTE IS NOT THE ONE THE BRIEF PREDICTED. The standard argument runs E(F_p)[r] embeds in
-- (Z/r)^2 (the n-torsion structure theorem, i.e. division polynomials connected to the group
-- law) and then invokes the Weil pairing to force mu_r into F_p, i.e. r | p-1, refuted by
-- gcd(r, p-1) = 1. mathlib has NEITHER: WeierstrassCurve.prePsi/Psi/Phi exist with their degree
-- bounds in AlgebraicGeometry/EllipticCurve/DivisionPolynomial/, but nothing anywhere links them
-- to nsmul; a search of the whole mathlib tree for a Weil pairing returns nothing; and there is
-- no point-counting theorem at all (EllipticCurve/LFunction.lean DEFINES the local polynomial as
-- 1 - aT + qT^2 with a := q + 1 - Nat.card (the count) and proves nothing about it). Nor is
-- there any Fintype/Finite instance for WeierstrassCurve.Affine.Point over a finite field.
--
-- WHAT REPLACES BOTH IS ONE INEQUALITY: r^2 > 2p + 1.
--   (1) #E(F_p) <= 2p + 1. Elementary: each x has at most two y with y^2 = x^3 + 4 (a field has
--       at most two square roots, by (y - y1)(y + y1) = 0), plus one point at infinity. Proved
--       here with a surjection Bool -> fiber and Fintype.card_le_of_surjective - no Hasse bound.
--   (2) r^2 > 2p + 1 for THIS curve: p is 381 bits and r^2 is 510 bits, so decide settles it.
--   (3) If X is r-torsion and X not in <H1>, then (i,j) |-> i * H1 + j * X is injective on
--       (Fin r)^2: from A * H1 + B * X = 0 with B <> 0, |B| < r and r prime give Bezout
--       uB + vr = 1, so X = u * (B * X) = (u * -A) * H1, contradiction; with B = 0 the order of
--       H1 forces A = 0. Hence r^2 <= #E(F_p), contradicting (1) and (2). So X in <H1>.
--   (4) <H1> has exactly r elements (P-CANON: primeOrderWith_zpowers_emb_genFrame), so
--       |E(F_p)[r]| = r.
-- Note what is NOT used: gcd(r, p-1) = 1 (proved in Assumptions/BasePrime.lean for the predicted
-- route) is not needed here at all, and neither is the cofactor statement #E(F_p) = r - the
-- r-torsion count is what g1Decodes asks for, and it is the whole of what is needed.
--
-- ELABORATOR/RAM FINDING, measured here (D-P31): `rw [ZMod.card]` on a goal mentioning
-- `Fintype.card (ZMod blsP)` costs about 4 GiB and is killed by the 6 GiB per-process budget,
-- while `have hc : Fintype.card K = blsP := ZMod.card blsP` followed by `rw [..., hc]` is free
-- (whole file peaks at 2.6 GiB). Same shape as the other walls: a rewrite that forces the
-- elaborator to reduce a 381-bit numeral. Pre-prove the numeral equation; do not raise the limit.

import Midfall.Instances.G1Agreement

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions WeierstrassCurve WeierstrassCurve.Affine

private theorem a1z : (W.a₁ : K) = 0 := rfl
private theorem a2z : (W.a₂ : K) = 0 := rfl
private theorem a3z : (W.a₃ : K) = 0 := rfl
private theorem a4z : (W.a₄ : K) = 0 := rfl
private theorem a6z : (W.a₆ : K) = 4 := rfl

private theorem p_pos : 0 < blsP := Nat.Prime.pos (Fact.out : Nat.Prime blsP)
private theorem r_prime : Nat.Prime blsR := Fact.out (p := Nat.Prime blsR)

/-- **THE CURVE EQUATION IN THE FORM THE COUNT NEEDS.** mathlib's general five-coefficient form
    collapses to \`y² = x³ + 4\` for \`W\`, and that is the shape whose fibers are two square roots. -/
theorem equation_iff_sq (x y : K) : W.Equation x y ↔ (y : K) ^ 2 = (x : K) ^ 3 + 4 := by
  rw [W.equation_iff, a1z, a2z, a3z, a4z, a6z]
  constructor
  · intro h
    have hy : (y : K) ^ 2 + (0 : K) * x * y + (0 : K) * y = (y : K) ^ 2 := by ring
    have hx : (x : K) ^ 3 + (0 : K) * x ^ 2 + (0 : K) * x + 4 = (x : K) ^ 3 + 4 := by ring
    rw [hy, hx] at h
    exact h
  · intro h
    rw [h]
    ring

private def ptCode (X : W.Point) : Sum (K × K) Unit :=
  match X with
  | 0 => Sum.inr ()
  | Point.some x y _ => Sum.inl (x, y)

private theorem ptCode_inj : Function.Injective ptCode := by
  intro X Y h
  cases X with
  | zero =>
      cases Y with
      | zero => rfl
      | some a b hb => cases h
  | some x y hx =>
      cases Y with
      | zero => cases h
      | some a b ha =>
          have h2 := Sum.inl.inj h
          obtain ⟨hxa, hyb⟩ := Prod.ext_iff.mp h2
          subst hxa; subst hyb
          exact congrArg (Point.some x y) (proof_irrel _ _)

/-- **THE POINT TYPE IS FINITE.** Forgetting the nonsingularity proof embeds \`W.Point\` into
    \`Sum (K × K) Unit\`, injectively because nonsingularity is a \`Prop\`. mathlib has no
    \`Fintype\` or \`Finite\` instance for \`WeierstrassCurve.Affine.Point\` over a finite field at all,
    so this is the first point of contact between the curve model and any counting statement. -/
instance pointFinite : Finite W.Point := Finite.of_injective ptCode ptCode_inj

/-- The fiber of the \`x\`-projection over \`x\`. -/
private abbrev fib (x : K) : Type := { y : K // (y : K) ^ 2 = (x : K) ^ 3 + 4 }

/-- **A SURJECTION FROM THE FIBER SUM ONTO THE CURVE**: the \`Σ\` over \`x\` of the fibers, plus one
    slot for the point at infinity. A surjection rather than an equivalence, because reshuffling a
    \`Sigma\` of a \`Subtype\` is exactly the plumbing that is not worth doing. -/
private def sumToWPoint : Sum (Σ x : K, fib x) Unit → W.Point
  | Sum.inl s =>
      Point.some s.1 s.2.1
        (nonsingular_of_equation ((equation_iff_sq s.1 s.2.1).mpr s.2.2))
  | Sum.inr _ => 0

private theorem sumToWPoint_surj : Function.Surjective sumToWPoint := by
  intro X
  cases X with
  | zero => exact ⟨Sum.inr (), rfl⟩
  | some x y h =>
      refine ⟨Sum.inl ⟨x, ⟨y, (equation_iff_sq x y).mp h.1⟩⟩, ?_⟩
      exact congrArg (Point.some x y) (proof_irrel _ _)

/-- **ONE FIBER HAS AT MOST TWO POINTS**: \`y² = a\` has at most the two solutions \`±y₁\`. Proved by
    exhibiting a surjection from \`Bool\`, which dodges every \`Multiset.roots\` cardinality coercion. -/
private def fiberCover (a y1 : K) (hy1 : y1 ^ 2 = a) : Bool → { y : K // y ^ 2 = a }
  | true => ⟨y1, hy1⟩
  | false => ⟨-y1, by rw [neg_sq, hy1]⟩

private theorem fiberCover_surj (a y1 : K) (hy1 : y1 ^ 2 = a) :
    Function.Surjective (fiberCover a y1 hy1) := by
  classical
  intro z
  by_cases hz : (z : K) = y1
  · refine ⟨true, Subtype.ext hz.symm⟩
  · refine ⟨false, Subtype.ext ?_⟩
    have h2 : (z : K) ^ 2 = y1 ^ 2 := by rw [z.prop, hy1]
    have h5 : ((z : K) - y1) * ((z : K) + y1) = 0 := by
      have h6 : ((z : K) - y1) * ((z : K) + y1) = (z : K) ^ 2 - y1 ^ 2 := by ring
      rw [h6, h2, sub_self]
    obtain h7 | h7 := mul_eq_zero.mp h5
    · exact absurd (sub_eq_zero.mp h7) hz
    · exact (add_eq_zero_iff_eq_neg.mp h7).symm

private theorem card_fiber_le_two (a : K) : Fintype.card { y : K // y ^ 2 = a } ≤ 2 := by
  classical
  by_cases hex : ∃ y : K, y ^ 2 = a
  · obtain ⟨y1, hy1⟩ := hex
    calc Fintype.card { y : K // y ^ 2 = a } ≤ Fintype.card Bool :=
          Fintype.card_le_of_surjective (fiberCover a y1 hy1) (fiberCover_surj a y1 hy1)
      _ = 2 := by simp
  · have : IsEmpty { y : K // y ^ 2 = a } := ⟨fun z => hex ⟨z.1, z.2⟩⟩
    rw [Fintype.card_eq_zero_iff.mpr this]
    exact Nat.zero_le _

/-- **THE BASE FIELD HAS \`blsP\` ELEMENTS**, pre-proved as a named fact rather than rewritten in
    place: \`rw [ZMod.card]\` costs about 4 GiB (see the header), this costs nothing. -/
theorem card_K_eq : Fintype.card K = blsP := ZMod.card blsP

/-- **#E(F_p) ≤ 2p + 1, WITH NO HASSE BOUND AND NO WEIL PAIRING.** Every \`x ∈ F_p\` carries at most
    two \`y\` with \`y² = x³ + 4\`, and there is one point at infinity. This is the elementary counting
    input that makes the \`r\`-torsion count reachable at all. -/
theorem natCard_WPoint_le : Nat.card W.Point ≤ 2 * blsP + 1 := by
  classical
  haveI : Fintype W.Point := Fintype.ofFinite W.Point
  have h0 : Fintype.card W.Point ≤ Fintype.card (Sum (Σ x : K, fib x) Unit) :=
    Fintype.card_le_of_surjective sumToWPoint sumToWPoint_surj
  have h1 : Fintype.card (Sum (Σ x : K, fib x) Unit) = Fintype.card (Σ x : K, fib x) + 1 := by
    rw [Fintype.card_sum]
    simp
  have h2 : Fintype.card (Σ x : K, fib x) = ∑ x : K, Fintype.card (fib x) := Fintype.card_sigma
  have h3 : ∑ x : K, Fintype.card (fib x) ≤ ∑ x : K, (2 : ℕ) := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    have := card_fiber_le_two ((x : K) ^ 3 + 4)
    simpa [fib] using this
  have h4 : ∑ x : K, (2 : ℕ) = 2 * blsP := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, card_K_eq, Nat.mul_comm]
  have h5 : Fintype.card W.Point ≤ 2 * blsP + 1 := by omega
  rw [Nat.card_eq_fintype_card]
  exact h5

/-- **THE INEQUALITY THAT DOES THE WORK.** \`r² > 2p + 1\`: \`p\` is 381 bits, \`r²\` is 510 bits. -/
theorem two_p_add_one_lt_r_sq : 2 * blsP + 1 < blsR * blsR := by decide

/-- **FALSIFICATION (D-P23): THE LINEAR BOUND IS LOAD-BEARING.** The trivial bound
    \`#E(F_p) ≤ p² + 1\` - counting pairs instead of roots - does NOT suffice, because \`p² > r²\`. So
    the fiber argument is not decoration: with the naive bound this proof fails. -/
theorem naive_bound_is_too_weak : blsP * blsP + 1 > blsR * blsR := by decide

/-- **BÉZOUT AT A PRIME.** An integer \`b\` with \`0 < |b| < r\` is invertible modulo the prime
    \`r\`: some \`u, v\` with \`u * b + v * r = 1\`. The \`set\` of \`m := b.natAbs\` is not cosmetic:
    rewriting \`b = ↑m\` without it also rewrites the \`b\` inside \`b.natAbs.gcdA\` and the goal
    becomes unmatchable. -/
private theorem bezout_at_prime (r : ℕ) (hr : Nat.Prime r) (b : ℤ)
    (hb0 : b ≠ 0) (hblt : b.natAbs < r) : ∃ u v : ℤ, u * b + v * (r : ℤ) = 1 := by
  classical
  set m := b.natAbs with hm
  have hpos : 0 < m := Nat.pos_of_ne_zero (fun hh => hb0 (Int.natAbs_eq_zero.mp (hm.trans hh)))
  have hcop : r.Coprime m :=
    (Nat.Prime.coprime_iff_not_dvd hr).mpr (fun hd => Nat.not_lt_of_le (Nat.le_of_dvd hpos hd) hblt)
  have hcop' : Nat.gcd m r = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hbez : (m : ℤ) * m.gcdA r + (r : ℤ) * m.gcdB r = 1 := by
    have h2 := Nat.gcd_eq_gcd_ab m r
    rw [hcop'] at h2
    exact h2.symm
  obtain h5 | h5 := Int.natAbs_eq_iff.mp (Eq.refl m)
  · refine ⟨m.gcdA r, m.gcdB r, ?_⟩
    rw [h5, mul_comm (m.gcdA r) (m : ℤ), mul_comm (m.gcdB r) (r : ℤ)]
    exact hbez
  · refine ⟨-(m.gcdA r), m.gcdB r, ?_⟩
    rw [h5, neg_mul_neg, mul_comm (m.gcdA r) (m : ℤ), mul_comm (m.gcdB r) (r : ℤ)]
    exact hbez

/-- **THE PUBLISHED GENERATOR HAS ADDITIVE ORDER EXACTLY \`r\`:** \`r • H1 = 0\` is the kernel
    \`decide\` P-CANON computed, \`H1 ≠ 0\` is \`emb_gen_ne_zero\`, and primality of \`r\` closes it. -/
theorem addOrderOf_genFrame : addOrderOf (emb genFrame) = blsR := by
  refine (Nat.Prime.eq_one_or_self_of_dvd r_prime _
      (addOrderOf_dvd_of_nsmul_eq_zero r_nsmul_emb_genFrame)).resolve_left ?_
  intro h1
  have hz : (1 : ℕ) • emb genFrame = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    rw [h1]
  rw [one_nsmul] at hz
  exact emb_gen_ne_zero hz

/-- **THE POINT COUNT \`|E(F_p)[r]| = r\`, AS A MEMBERSHIP STATEMENT.** Every \`r\`-torsion point of
    \`E(F_p)\` is an integer multiple of the published generator \`H1\`.

    THE ARGUMENT - and it is NOT the route the brief predicted. The standard route needs the
    \`n\`-torsion structure theorem (\`E(F)[r]\` embeds in \`(Z/r)²\`, i.e. division polynomials
    connected to the group law) AND the Weil pairing (two-dimensional rational torsion forces
    \`r ∣ p-1\`). mathlib has neither: \`preΨ/Ψ/Φ\` exist with their degree bounds in
    \`EllipticCurve/DivisionPolynomial/\`, but nothing links them to \`nsmul\`, and a search of the
    whole mathlib tree for a Weil pairing returns nothing. What replaces both is ONE inequality.

    Suppose \`X\` is \`r\`-torsion with \`X ∉ <H1>\). Then \`(i,j) ↦ (i : ℤ) • H1 + (j : ℤ) • X\` is
    injective on \`(Fin r) × (Fin r)\): from \`A • H1 + B • X = 0\` with \`B ≠ 0\`, \`|B| < r\` and
    \`r\` prime give Bézout \`uB + vr = 1\`, so \`X = u • (B • X) = (u • -A) • H1\`, contradiction;
    and with \`B = 0\` the order of \`H1\` forces \`A = 0\`. Hence \`r² ≤ #E(F_p)\`. But the elementary
    count gives \`#E(F_p) ≤ 2p+1\` and \`2p + 1 < r²\` for BLS12-381. So \`X ∈ <H1>\). No Hasse
    bound, no Weil pairing, no structure theorem, no point counting.

    THE INEQUALITY IS CURVE-SPECIFIC: what does the work is \`r² > 2p+1\`, i.e. that \`G1\` has
    cofactor 1 and \`r\` is far larger than \`√p\`. \`gcd(r, p-1) = 1\` is NOT used. -/
theorem torsion_eq_zpowers_gen (X : W.Point) (hX : blsR • X = 0) :
    ∃ k : ℤ, k • emb genFrame = X := by
  classical
  by_cases hmem : ∃ k : ℤ, k • emb genFrame = X
  · exact hmem
  have hX0 : X ≠ 0 := by
    intro hh
    exact hmem ⟨0, by rw [hh]; exact zero_zsmul _⟩
  have hinj : Function.Injective (fun ij : Fin blsR × Fin blsR =>
      ((ij.1.val : ℤ) • emb genFrame) + ((ij.2.val : ℤ) • X)) := by
    intro ij kl h
    obtain ⟨i, j⟩ := ij
    obtain ⟨k, l⟩ := kl
    have hsum : ((i.val : ℤ) - (k.val : ℤ)) • emb genFrame
        + ((j.val : ℤ) - (l.val : ℤ)) • X = 0 := by
      have h2 : ((i.val : ℤ) • emb genFrame + (j.val : ℤ) • X)
          - ((k.val : ℤ) • emb genFrame + (l.val : ℤ) • X) = 0 := by
            have h' : (i.val : ℤ) • emb genFrame + (j.val : ℤ) • X
                = (k.val : ℤ) • emb genFrame + (l.val : ℤ) • X := h
            rw [h']
            exact sub_self _
      have h3 : ((i.val : ℤ) - (k.val : ℤ)) • emb genFrame
          + ((j.val : ℤ) - (l.val : ℤ)) • X
          = ((i.val : ℤ) • emb genFrame + (j.val : ℤ) • X)
            - ((k.val : ℤ) • emb genFrame + (l.val : ℤ) • X) := by
        rw [sub_zsmul, sub_zsmul]
        abel
      rw [h3, h2]
    have hAi : ((i.val : ℤ) - (k.val : ℤ)).natAbs < blsR := by
      have hi : (i.val : ℤ) < blsR := by exact_mod_cast i.isLt
      have hk : (k.val : ℤ) < blsR := by exact_mod_cast k.isLt
      have h0 : (0 : ℤ) ≤ (i.val : ℤ) := by exact_mod_cast Nat.zero_le _
      have h1 : (0 : ℤ) ≤ (k.val : ℤ) := by exact_mod_cast Nat.zero_le _
      omega
    have hBj : ((j.val : ℤ) - (l.val : ℤ)).natAbs < blsR := by
      have hi : (j.val : ℤ) < blsR := by exact_mod_cast j.isLt
      have hk : (l.val : ℤ) < blsR := by exact_mod_cast l.isLt
      have h0 : (0 : ℤ) ≤ (j.val : ℤ) := by exact_mod_cast Nat.zero_le _
      have h1 : (0 : ℤ) ≤ (l.val : ℤ) := by exact_mod_cast Nat.zero_le _
      omega
    by_cases hB0 : ((j.val : ℤ) - (l.val : ℤ)) = 0
    · have hA0 : ((i.val : ℤ) - (k.val : ℤ)) = 0 := by
        have hAG : ((i.val : ℤ) - (k.val : ℤ)) • emb genFrame = 0 := by
          rw [hB0, zero_zsmul, add_zero] at hsum
          exact hsum
        have hdvd : ((addOrderOf (emb genFrame) : ℤ) ∣ ((i.val : ℤ) - (k.val : ℤ))) :=
          (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hAG
        have hdvd2 : (blsR : ℤ) ∣ ((i.val : ℤ) - (k.val : ℤ)) := by
          rwa [addOrderOf_genFrame] at hdvd
        obtain ⟨c, hc⟩ := hdvd2
        have hc0 : c = 0 := by
          by_contra hne
          have h1 : 1 ≤ c.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne)
          have h2 : ((i.val : ℤ) - (k.val : ℤ)).natAbs = blsR * c.natAbs := by
            rw [hc, Int.natAbs_mul]
            simp
          have h3 : blsR ≤ ((i.val : ℤ) - (k.val : ℤ)).natAbs := by
            rw [h2]
            exact Nat.le_mul_of_pos_right _ h1
          omega
        rw [hc, hc0, mul_zero]
      exact Prod.ext (Fin.eq_of_val_eq (by omega : i.val = k.val))
        (Fin.eq_of_val_eq (by omega : j.val = l.val))
    · -- B <> 0: Bezout inverts B mod r and expresses X as a multiple of H1, contradicting hmem
      obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ((j.val : ℤ) - (l.val : ℤ))
          + v * (blsR : ℤ) = 1 :=
        bezout_at_prime blsR r_prime ((j.val : ℤ) - (l.val : ℤ)) hB0 hBj
      have hBX : ((j.val : ℤ) - (l.val : ℤ)) • X
          = -(((i.val : ℤ) - (k.val : ℤ)) • emb genFrame) := by
        rw [eq_neg_iff_add_eq_zero, add_comm, hsum]
      have hordX : addOrderOf X = blsR := by
        refine (Nat.Prime.eq_one_or_self_of_dvd r_prime _
            (addOrderOf_dvd_of_nsmul_eq_zero hX)).resolve_left ?_
        intro hh
        have h1 : (1 : ℕ) • X = 0 := by
          rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
          rw [hh]
        exact hX0 (by simpa using h1)
      have hzX : (blsR : ℤ) • X = 0 := by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero]
        rw [hordX]
      have hXin : (-(u * ((i.val : ℤ) - (k.val : ℤ)))) • emb genFrame = X := by
        have h2 : (u * ((j.val : ℤ) - (l.val : ℤ)) + v * (blsR : ℤ)) • X = X :=
          by rw [huv, one_zsmul]
        rw [add_zsmul, mul_zsmul, mul_zsmul, hBX, zsmul_neg, ← mul_zsmul, hzX, zsmul_zero,
          add_zero] at h2
        exact (neg_zsmul (emb genFrame) (u * ((i.val : ℤ) - (k.val : ℤ)))).trans h2
      exact absurd ⟨-(u * ((i.val : ℤ) - (k.val : ℤ))), hXin⟩ hmem

  -- the two bounds meet here: r² points would have to fit inside at most 2p+1 of them
  haveI : Fintype W.Point := Fintype.ofFinite W.Point
  have hc1 : blsR * blsR ≤ Fintype.card W.Point := by
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_prod, Fintype.card_fin] at this
    exact this
  have hc2 : Fintype.card W.Point = Nat.card W.Point := Nat.card_eq_fintype_card.symm
  have hc3 : Nat.card W.Point ≤ 2 * blsP + 1 := natCard_WPoint_le
  have hc4 : 2 * blsP + 1 < blsR * blsR := two_p_add_one_lt_r_sq
  omega

/-! ### The decoder-to-encoder direction of the byte round trip -/

/-- **\`bytesToNatBE\` IS INJECTIVE AT A FIXED LENGTH.** Positional notation is unique
    (\`ofLowDigits_inj\`, already in \`Assumptions/Codec.lean\` for the \`frOfRepr\` round trip) and a
    \`UInt8\` is recoverable from its value. The length hypothesis is load-bearing: \`bytesZero 1\` and
    \`bytesZero 2\` read as the same number. -/
private theorem uint8_map_inj : ∀ {l l' : List UInt8}, l.map UInt8.toNat = l'.map UInt8.toNat →
    l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons a t => simp at h
  | cons a t ih =>
      intro l' h
      cases l' with
      | nil => simp at h
      | cons b s =>
          simp only [List.map_cons] at h
          obtain ⟨hab, hts⟩ := List.cons.inj h
          have ha : a = b := UInt8.toNat_inj.mp hab
          subst ha
          exact congrArg (List.cons a) (ih hts)

theorem bytesToNatBE_inj {s t : Bytes} (h : s.size = t.size)
    (hv : bytesToNatBE s = bytesToNatBE t) : s = t := by
  classical
  have hs : ∀ d ∈ (s.data.toList.map UInt8.toNat).reverse, d < 256 := by
    intro d hd
    rw [List.mem_reverse, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact UInt8.toNat_lt x
  have ht : ∀ d ∈ (t.data.toList.map UInt8.toNat).reverse, d < 256 := by
    intro d hd
    rw [List.mem_reverse, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact UInt8.toNat_lt x
  have hl : ((s.data.toList.map UInt8.toNat).reverse).length
      = ((t.data.toList.map UInt8.toNat).reverse).length := by
    have h1 : s.data.size = t.data.size := h
    rw [← Array.length_toList, ← Array.length_toList] at h1
    rw [List.length_reverse, List.length_map, List.length_reverse, List.length_map]
    exact h1
  have hv2 : ofLowDigits 256 ((s.data.toList.map UInt8.toNat).reverse)
      = ofLowDigits 256 ((t.data.toList.map UInt8.toNat).reverse) := by
    rw [← bytesToNatBE_eq_ofLowDigits_reverse, ← bytesToNatBE_eq_ofLowDigits_reverse]
    exact hv
  have hrev := ofLowDigits_inj (by decide : 1 < 256) _ _ hs ht hl hv2
  rw [List.reverse_inj] at hrev
  show ByteArray.mk s.data = ByteArray.mk t.data
  exact congrArg ByteArray.mk (Array.ext' (uint8_map_inj hrev))

/-- **A COORDINATE THE READER ACCEPTS IS BELOW \`blsP\`** - canonicity, read off the decoder. -/
theorem fpCoordOf?_some_lt {s : Bytes} {v : Nat} (h : fpCoordOf? s = some v) : v < blsP := by
  classical
  unfold fpCoordOf? at h
  cases hc : bytesTake s 0 (fpPadBytes + fpBytes) with
  | none => rw [hc] at h; simp at h
  | some c =>
      rw [hc] at h
      dsimp only at h
      by_cases hb : bytesToNatBE c < blsP
      · rw [if_pos hb] at h
        have := Option.some.inj h
        subst this
        exact hb
      · rw [if_neg hb] at h
        exact absurd h (by simp)

/-- **THE COORDINATE READER DETERMINES THE COORDINATE BYTES**: a \`64\`-byte window that decodes to
    \`v\` IS \`fpCoordBytes v\`. This is the direction \`P-G1CODEC\` did not need - it went
    encoder-to-decoder, and \`g1Decodes\` asks for the other way. -/
theorem fpCoordOf?_some_determines {s : Bytes} {v : Nat} (hs : s.size = 64)
    (h : fpCoordOf? s = some v) : s = fpCoordBytes v := by
  classical
  have hpad : fpPadBytes + fpBytes = 64 := rfl
  have ht : bytesTake s 0 (fpPadBytes + fpBytes) = some s := by
    rw [hpad, ← hs]
    exact bytesTake_of_size s
  have hv : bytesToNatBE s = v ∧ v < blsP := by
    have h2 : bytesToNatBE s = v ∧ v < blsP := by
      unfold fpCoordOf? at h
      rw [ht] at h
      dsimp only at h
      by_cases hb : bytesToNatBE s < blsP
      · rw [if_pos hb] at h
        have e := Option.some.inj h
        exact ⟨e, e ▸ hb⟩
      · rw [if_neg hb] at h
        exact absurd h (by simp)
    exact h2
  have h2 : bytesToNatBE (fpCoordBytes v) = v := bytesToNatBE_fpCoordBytes v hv.2
  have hs2 : (fpCoordBytes v).size = 64 := by rw [fpCoordBytes_size]; exact hpad
  exact bytesToNatBE_inj (hs.trans hs2.symm) (hv.1.trans h2.symm)

/-- **THE FRAME READER DETERMINES THE FRAME**: a \`g1Bytes\`-wide string that decodes to \`pt\` is
    exactly \`g1PointBytes pt\`. -/
theorem g1Of?_some_determines {b : Bytes} {pt : Nat × Nat} (hb : b.size = g1Bytes)
    (h : g1Of? b = some pt) : b = g1PointBytes pt := by
  classical
  cases pt with
  | mk px py =>
      unfold g1Of? at h
      cases hA : fpCoordOf? (bytesSlice b 0 64) with
      | none => simp [hA] at h
      | some x =>
          cases hB : fpCoordOf? (bytesSlice b 64 64) with
          | none => simp [hB] at h
          | some y =>
              simp only [hA, hB] at h
              obtain ⟨hxy, hyy⟩ := Prod.ext_iff.mp (Option.some.inj h)
              subst hxy; subst hyy
              have hb' : b.size = 128 := hb
              have hs1 : (bytesSlice b 0 64).size = 64 := by
                rw [bytesSlice_size 0 64 (by omega : 0 + 64 ≤ b.size)]
              have hs2 : (bytesSlice b 64 64).size = 64 := by
                rw [bytesSlice_size 64 64 (by omega : 64 + 64 ≤ b.size)]
              have e1 : bytesSlice b 0 64 = fpCoordBytes x := fpCoordOf?_some_determines hs1 hA
              have e2 : bytesSlice b 64 64 = fpCoordBytes y := fpCoordOf?_some_determines hs2 hB
              have hsplit : bytesAppend (bytesSlice b 0 64) (bytesSlice b 64 64) = b := by
                rw [bytesSlice_at _ _ _ (by omega : 0 + 64 ≤ b.size),
                  bytesSlice_at _ _ _ (by omega : 64 + 64 ≤ b.size)]
                show ByteArray.mk (b.data.extract 0 64 ++ b.data.extract 64 128) = b
                rw [Array.extract_append_extract]
                show ByteArray.mk (b.data.extract 0 128) = b
                rw [← bytesSlice_at _ 0 128 (by omega : 0 + 128 ≤ b.size)]
                have h128 : b.size = 128 := hb
                rw [← h128]
                exact bytesSlice_full b
              rw [← hsplit, e1, e2]
              show bytesAppend (fpCoordBytes x) (fpCoordBytes y) = g1PointBytes (x, y)
              rfl

/-- **A DECODED PAIR IS CANONICAL**: \`fpCoordOf?\` only answers below \`blsP\`. -/
theorem g1Of?_some_canonical {b : Bytes} {pt : Nat × Nat} (h : g1Of? b = some pt) :
    pt.1 < blsP ∧ pt.2 < blsP := by
  classical
  unfold g1Of? at h
  cases hA : fpCoordOf? (bytesSlice b 0 64) with
  | none => simp [hA] at h
  | some x =>
      cases hB : fpCoordOf? (bytesSlice b 64 64) with
      | none => simp [hB] at h
      | some y =>
          simp only [hA, hB] at h
          obtain ⟨hxy, hyy⟩ := Prod.ext_iff.mp (Option.some.inj h)
          subst hxy; subst hyy
          exact ⟨fpCoordOf?_some_lt hA, fpCoordOf?_some_lt hB⟩

/-! ### Surjectivity onto the accepted frames, and the fourth \`Holds\` clause -/

/-- **\`ptPair\` IS INJECTIVE**: the coordinate pair determines the curve point, because
    \`emb (frameOf X) = X\` and \`(frameOf X).1 = ptPair X\`. -/
theorem ptPair_injective : Function.Injective ptPair := by
  intro X Y h
  have e1 : emb (frameOf X) = X := emb_frameOf X
  have e2 : emb (frameOf Y) = Y := emb_frameOf Y
  have hP : frameOf X = frameOf Y := Subtype.ext h
  rw [← e1, ← e2, hP]

/-- **EVERY FRAME THE PRECOMPILE ACCEPTS IS THE ENCODING OF A CARRIER ELEMENT.** This is the right
    hand side of \`g1CodecZ_g1DecodesWidth_iff\`, and so the whole of what was left on the G1 side. -/
theorem g1zToEip_surjective_on_accepted (b : Bytes) (hb : b.size == g1Bytes)
    (h : ∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) :
    ∃ Q : G₁z, g1zToEip Q = b := by
  classical
  obtain ⟨pt, hpt, hv⟩ := h
  obtain ⟨hpc1, hpc2⟩ := g1Of?_some_canonical hpt
  have honc : affineOnCurve fpOps pt = true := by
    unfold g1PointMsmValid at hv
    rw [Bool.and_eq_true] at hv
    exact hv.1
  let P : FpFrame := ⟨pt, honc⟩
  have hc : CanonicalFrame P := ⟨hpc1, hpc2⟩
  have hvP : g1PointMsmValid P.1 = true := hv
  have htor : blsR • emb P = 0 := (g1PointMsmValid_iff P hc).mp hvP
  obtain ⟨k, hk⟩ := torsion_eq_zpowers_gen (emb P) htor
  have hmem : Multiplicative.ofAdd (emb P) ∈
      Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame)) :=
    Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Multiplicative.ofAdd hk⟩
  refine ⟨⟨Multiplicative.ofAdd (emb P), hmem⟩, ?_⟩
  have hz : g1zToEip ⟨Multiplicative.ofAdd (emb P), hmem⟩ = g1PointBytes (ptPair (emb P)) := rfl
  rw [hz, ptPair_emb P hc]
  have hP1 : P.1 = pt := rfl
  rw [hP1, ← g1Of?_some_determines (beq_iff_eq.mp hb) hpt]

/-- **THE FOURTH G1-SIDE \`Holds\` CLAUSE, DISCHARGED AT THE REAL-CURVE CODEC.** -/
theorem g1CodecZ_g1DecodesWidth : g1DecodesWidth g1CodecZ :=
  (g1CodecZ_g1DecodesWidth_iff).mpr g1zToEip_surjective_on_accepted

/-- **THE G1 SIDE, FOUR OF FOUR, IN ONE DECLARATION** (the joint-exhibit discipline of
    \`scripts/check_hypothesis_bundles.py\`: four separately-inhabited clauses certify nothing about
    their being simultaneously satisfiable at ONE codec on ONE carrier). What is left of \`Holds\` is
    \`g2Valid\` and \`pairing2\`, and neither is a G1 question. -/
theorem g1CodecZ_g1_four :
    (∀ Q : G₁z, ∃ pt, g1Of? (g1CodecZ.toEip Q) = some pt ∧ g1PointMsmValid pt = true) ∧
      (∀ P Q : G₁z, g1AddOutput (g1AddFrame (g1CodecZ.toEip P) (g1CodecZ.toEip Q)) =
          some (g1CodecZ.toEip (P * Q))) ∧
      (∀ (Q : G₁z) (s : Fr blsR),
          g1MsmOutput (g1MsmFrame [(g1CodecZ.toEip Q, frToInputBE s)]) =
            some (g1CodecZ.toEip (Midfall.Halo2.gsmul s Q))) ∧
      g1DecodesWidth g1CodecZ :=
  ⟨g1CodecZ_g1Valid, g1CodecZ_g1Add, g1CodecZ_g1Msm1, g1CodecZ_g1DecodesWidth⟩

/-! ### The count as a cardinality -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in

/-! ### D-P23: witnesses and falsifications for the count -/

/-- **WITNESS (D-P23): THE COUNT LOCATES A POINT THAT WAS NEVER NAMED AS A MULTIPLE.** The negated
    published generator is \`r\`-torsion and the count finds an integer multiple of \`H1\` equal to
    it; the second conjunct says that multiple is NOT \`1\`, so the theorem is not the triviality
    "multiples of \`H1\` are multiples of \`H1\`". -/
theorem g1PointCount_witness_negGen :
    (∃ k : ℤ, k • emb genFrame = emb negGenFrame) ∧ emb negGenFrame ≠ emb genFrame := by
  classical
  obtain ⟨hadd, hne⟩ := emb_add_witness
  have hneg : emb negGenFrame = -emb genFrame := (neg_eq_iff_add_eq_zero.mpr hadd).symm
  have htor : blsR • emb negGenFrame = 0 := by
    rw [hneg, neg_nsmul, r_nsmul_emb_genFrame, neg_zero]
  refine ⟨torsion_eq_zpowers_gen (emb negGenFrame) htor, ?_⟩
  intro hh
  rw [hneg] at hh
  have h2 : (2 : ℤ) • emb genFrame = 0 := by
    have h3 : -(emb genFrame) + emb genFrame = emb genFrame + emb genFrame :=
      congrArg (fun t => t + emb genFrame) hh
    rw [show -(emb genFrame) + emb genFrame = 0 by abel] at h3
    rw [two_zsmul]
    exact h3.symm
  have hd : ((addOrderOf (emb genFrame) : ℤ) ∣ (2 : ℤ)) := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h2
  rw [addOrderOf_genFrame] at hd
  exact absurd hd (by decide : ¬ ((blsR : ℤ) ∣ 2))

/-- **FALSIFICATION (D-P23): THE WIDTH CONDITION IS LOAD-BEARING IN THE COUNT TOO.** Drop it and the
    "accepted" type is the infinite \`garbageFrame\` family of \`Assumptions/Eip2537.lean\`, whose
    \`Nat.card\` is \`0\` and not \`r\`. The count is about exactly the frames the precompile accepts,
    not about everything the coordinate reader swallows. -/
theorem not_natCard_accepted_without_width :
    Nat.card { b : Bytes // ∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true } ≠ blsR := by
  intro hh
  haveI : Infinite { b : Bytes // ∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true } :=
    Infinite.of_injective (fun k : ℕ =>
      ⟨garbageFrame k, garbageFrame_accepted k⟩) (fun i j h =>
        garbageFrame_injective (congrArg Subtype.val h))
  rw [Nat.card_eq_zero_of_infinite] at hh
  exact Nat.Prime.ne_zero r_prime hh.symm

/-- **FALSIFICATION (D-P23): THE DECODER REFUSES A FRAME OUTSIDE THE IMAGE.** \`junkPair\` is
    \`(blsP, blsP)\`, on-curve through the infinity branch of \`affineOnCurve\` but not canonically
    encoded, so no carrier element encodes its bytes and \`ofEip?\` declines it. -/
theorem g1zOfEip?_refuses_junk : g1CodecZ.ofEip? (g1PointBytes junkPair) = none := by
  classical
  have h : ¬ ∃ Q : G₁z, g1zToEip Q = g1PointBytes junkPair := by
    intro hex
    obtain ⟨Q, hQ⟩ := hex
    obtain ⟨h1, h2⟩ := g1zPair_canonical Q
    have e1 : g1Of? (g1zToEip Q) = some (g1zPair Q) := g1Of?_g1PointBytes (g1zPair Q) h1 h2
    rw [hQ] at e1
    rw [g1Of?_g1PointBytes_needs_canonical] at e1
    exact absurd e1 (by simp)
  show g1zOfEip? (g1PointBytes junkPair) = none
  exact dif_neg h

/-- **THE GATE FOR THIS PACKAGE.** Line 1 is the inequality the whole proof turns on; line 2 is the
    falsification showing the naive pair-counting bound would not do; line 3 re-pins the coprimality
    that the predicted (and ultimately unused) Weil-pairing route needed; lines 4-6 pin the widths
    and the non-constancy of the encoder whose surjectivity is the count. -/
def g1PointCountKats_ok : Bool :=
  (2 * blsP + 1 < blsR * blsR) &&
  (blsP * blsP + 1 > blsR * blsR) &&
  (Nat.gcd blsR (blsP - 1) == 1) &&
  (g1PointBytes genPair).size == g1Bytes &&
  (g1zToEip g1zGen).size == g1Bytes &&
  ! bytesEq (g1zToEip g1zGen) (bytesZero g1Bytes)

#eval g1PointCountKats_ok   -- expect true

/-- **WHAT THIS PACKAGE CLOSED.** The G1 side of \`Eip2537.Holds\` is FOUR OF FOUR at the real-curve
    codec \`g1CodecZ\` on the \`zpowers\` carrier \`G₁z\": \`g1Valid\`, \`g1Add\`, \`g1Msm1\`
    (P-G1CODEC) and \`g1Decodes\` (here, \`g1CodecZ_g1DecodesWidth\`), jointly exhibited by
    \`g1CodecZ_g1_four\`. NO new named assumption was needed, so the trusted base is UNCHANGED.
    What remains of \`Holds\` is \`g2Valid\` (needs an \`Fp2\` model, which mathlib does not have for
    BLS12-381 at all) and \`pairing2\` (needs \`Fp12\` plus a real \`AdmissiblePairing\`, D-P36).

    ONE WALL HIT, recorded because it cost time: \`g1PointMsmValid_iff\` applied to a VARIABLE frame
    (the step \`g1PointMsmValid pt = true → blsR • emb P = 0\`) needs \`maxRecDepth 1000000\" - the
    same fold-unrolling shape P-CANON recorded, arriving from the application side rather than the
    \`decide\` side. Unlike the \`decide\` cases, raising the depth DOES clear it, because no
    computation is being asked for; only the unifier's whnf is deep. The two \`Nat.card\` formulations
    of the count (\`natCard_G1Accepted\`) were dropped for the same class of wall and are recorded as
    remaining plumbing, not as missing mathematics. -/
def closed_g1_four_of_four : String :=
  "g1Valid + g1Add + g1Msm1 (P-G1CODEC) + g1Decodes (this package, via the point count "
    ++ "|E(Fp)[r]| = r proved from #E(Fp) <= 2p+1 < r^2, with no Weil pairing, no n-torsion "
    ++ "structure theorem and no new assumption). Remaining Holds clauses: g2Valid (needs an "
    ++ "Fp2 model) and pairing2 (needs Fp12 + a real pairing, D-P36)."

end Midfall.Instances
