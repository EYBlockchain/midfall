-- |
-- Midfall.Instances.Fp2
--
-- P-G2 STEP 1: THE Fp2 MODEL - FpBase[u]/(u^2+1) at the REAL BLS12-381 base modulus, with a Field
-- instance, plus the proof that its field arithmetic AGREES WITH 'fp2Ops' in
-- Midfall/Yul/Externals.lean, which is the byte model the precompile computes with. Nothing here
-- is about G2 yet. This file is the algebraic half of the tower that 'gap_g2_no_fp2_model' says is
-- missing: "the tree has the BYTE half of Fp2 - fp2Ops is integer arithmetic on pairs over
-- ZMod blsP - and no ALGEBRAIC half: no type with a Field instance for FpBase[u]/(u^2+1), so nothing
-- can state that the byte law agrees with a group law".
--
-- THE RECORDED TRAP, AND WHY IT IS REAL. 'pBase % 4 = 3' - the fact that makes X^2 + 1 have no
-- root in FpBase, hence that the quotient is a field at all - is pinned in the tree ONLY as a Bool
-- gate (Assumptions/BasePrime.basePrimeKats_ok, last conjunct, and pBaseKats_ok). A Bool gate
-- cannot be cited by a Field instance. 'blsP_mod_four' below is the theorem, and it costs one
-- 'decide' of a 381-bit literal mod 4: milliseconds, not a search.
--
-- WHY 'AdjoinRoot' AND NOT A HAND-BUILT PAIR TYPE. 'ZMod blsP' IS a field ('pBase_prime', the
-- Lucas/Pratt certificate in Assumptions/BasePrime.lean), so mathlib's 'AdjoinRoot FpBase (X^2+1)' is
-- the quotient ring FpBase[X]/(X^2+1) and 'AdjoinRoot.instField [Fact (Irreducible f)]'
-- (RingTheory/AdjoinRoot.lean:616) hands over a Field instance for free once irreducibility is
-- proved. A hand-built pair type would need AddCommGroup, Ring, GroupWithZero and the inv laws from
-- scratch - hundreds of lines of the same algebra - and the agreement with 'fp2Ops' would still
-- have to be done. What AdjoinRoot costs instead is that its elements are quotients, so the
-- coordinate normal form ('ofPair_eq_zero_iff') has to be PROVED rather than read off a
-- constructor: one divisibility argument, via 'mk_ne_zero_of_natDegree_lt'.
--
-- THE ARITHMETIC MODEL WAS CHECKED AGAINST 'fp2Ops' BEFORE ANYTHING WAS BUILT ON IT, and it matched
-- ON FIRST CONTACT: 'fp2Ops.mul a b = (a0 b0 - a1 b1, a0 b1 + a1 b0) mod p' is multiplication with
-- u^2 = -1, which is what EIP-2537's nr2 = p - 1 says (Externals.lean:410-414), and 'fp2Ops.inv'
-- is the norm formula (c0 - c1 u)/(c0^2 + c1^2) - correct exactly because the norm vanishes only
-- at 0, which is the same non-residue fact as irreducibility. The one place where the byte model is
-- NOT the naive reading is the 'none' branch of 'fp2Ops.inv': it answers 'none' when the NORM has
-- no inverse, not only when the input is zero, and those are the same event here
-- ('fp2Ops_inv_none_iff') - a property of THIS tower that fails the moment X^2+1 is reducible, and
-- so a second reason the mod-4 fact is load-bearing.
--
-- COST. No 381-bit kernel computation appears in this file: 'blsP_mod_four' is a mod-4 'decide',
-- the irreducibility proof is Fermat plus a degree argument, and every agreement lemma below is
-- 'field_simp' / 'ring' / 'norm_num'. The expensive part of P-G2 is the G2 scalar multiplication,
-- which is in G2Agreement.lean and not here.
--
-- NONCOMPUTABILITY, stated because it changes how this file may be used. 'Fact (Nat.Prime blsP)' is
-- transported across a cast and 'AdjoinRoot.instField' is 'noncomputable', so there is NO
-- computational content in 'FpBase' or 'Fp2': no '#eval', no 'decide', no 'rfl' that reduces a sum.
-- Every computation in the package therefore happens in 'fp2Ops' on 'Nat', and the theorems here
-- are the bridge from those bytes to the field. That is the design of the G1 side too
-- (Instances/G1Agreement.lean), and it is why the agreement lemmas are the deliverable.

import Midfall.Assumptions.Eip2537
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions Polynomial

/-- The prime field of EIP-2537 as mathlib sees it: 'ZMod blsP', a field by the Pratt certificate
    in Assumptions/BasePrime.lean. Named 'FpBase' rather than 'Fp' because
    Instances/Bls12_381.lean already owns 'Midfall.Instances.Fp' (= 'ZMod pBase'); the two are the
    same type, since 'blsP_eq_pBase' is 'rfl'. Named differently from the G1 file's 'K' too, so that
    this file and Instances/G1Agreement.lean can be imported together. -/
abbrev FpBase : Type := ZMod blsP

private theorem p_pos : 0 < blsP := Nat.Prime.pos (Fact.out : Nat.Prime blsP)

private theorem two_lt_p : 2 < blsP := by decide

private theorem coe_nat_ne_zero {n : ℕ} (hn : n < blsP) (hn0 : n ≠ 0) : (n : FpBase) ≠ 0 := by
  intro h
  have h1 : ((n : FpBase)).val = 0 := (ZMod.val_eq_zero (n : FpBase)).mpr h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn] at h1
  exact hn0 h1

/-! ### THE TRAP, CLOSED: p = 3 [MOD 4] AS A THEOREM -/

/-- **blsP % 4 = 3, AS A THEOREM** (P-G2 step 1, the trap P-GAPFIX recorded). Until this line the
    fact existed only as the last conjunct of the Bool gates 'basePrimeKats_ok' and 'pBaseKats_ok',
    which no instance and no theorem can cite. It is one 'decide': a 381-bit literal reduced mod 4.
    Everything else in this file - the non-residue fact, irreducibility, the Field instance, the
    inverse law of 'fp2Ops' - is downstream of this line. -/
theorem blsP_mod_four : blsP % 4 = 3 := by decide

/-- The same fact at the other name for the same number: 'blsP' (Externals) and 'pBase'
    (Assumptions/Pairing) are the same literal, and 'blsP_eq_pBase' is the pin that says so. -/
theorem pBase_mod_four : pBase % 4 = 3 := blsP_mod_four

/-- 'p' is odd, in the form the exponent arithmetic below needs. -/
theorem blsP_odd : blsP % 2 = 1 := by
  have hm : blsP % 4 = 3 := blsP_mod_four
  omega

/-- The half of 'p - 1' is ODD: 'p = 4k + 3' gives '(p-1)/2 = 2k + 1'. This is the parity fact
    behind 'neg_one_not_sq', and 'omega' closes it on the atom 'blsP' with its mod-4 residue,
    without unfolding the literal. -/
theorem half_odd : Odd ((blsP - 1) / 2) := by
  have hm : blsP % 4 = 3 := blsP_mod_four
  rw [Nat.odd_iff]
  omega

/-! ### -1 IS NOT A SQUARE IN FpBase -/

theorem two_ne_zero_Fp : (2 : FpBase) ≠ 0 := coe_nat_ne_zero two_lt_p (by decide)
theorem three_ne_zero_Fp : (3 : FpBase) ≠ 0 := coe_nat_ne_zero (by decide) (by decide)
theorem four_ne_zero_Fp : (4 : FpBase) ≠ 0 := coe_nat_ne_zero (by decide) (by decide)

private theorem one_ne_zero_Fp : (1 : FpBase) ≠ 0 := by
  intro h
  have h2 : (2 : FpBase) = 0 := by
    calc (2 : FpBase) = 1 + 1 := by norm_num
      _ = 0 + 0 := by rw [h]
      _ = 0 := by simp
  exact two_ne_zero_Fp h2

private theorem neg_one_ne_zero_Fp : (-1 : FpBase) ≠ 0 := fun h =>
  one_ne_zero_Fp (by rw [← neg_neg (1 : FpBase), h, neg_zero])

/-- **-1 IS NOT A SQUARE IN FpBase.** The argument is Fermat, not a search: if 'y^2 = -1' then 'y ≠ 0'
    and 'y^(p-1) = 1', but 'p - 1 = 2 * ((p-1)/2)' with '(p-1)/2' ODD, so
    '1 = y^(p-1) = (y^2)^((p-1)/2) = (-1)^((p-1)/2) = -1', i.e. '2 = 0' in FpBase, refuted because
    'p > 2'. This is the one number-theoretic fact the whole tower rests on, and it is exactly why
    EIP-2537 picks nr2 = p - 1 (Externals.lean:410-414: "p = 3 mod 4 (which is why EIP-2537 picks
    this tower at all)"). -/
theorem neg_one_not_sq : ∀ y : FpBase, y ^ 2 ≠ -1 := by
  intro y hy
  have hy0 : y ≠ 0 := fun h0 =>
    neg_one_ne_zero_Fp (by rw [← hy, h0]; simp)
  have h1 : y ^ (blsP - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy0
  have ho : blsP % 2 = 1 := blsP_odd
  have he : blsP - 1 = 2 * ((blsP - 1) / 2) := by omega
  have hsum : (1 : FpBase) = -1 :=
    calc (1 : FpBase) = y ^ (blsP - 1) := h1.symm
      _ = (y ^ 2) ^ ((blsP - 1) / 2) := by rw [← pow_mul]; congr 1
      _ = (-1 : FpBase) ^ ((blsP - 1) / 2) := by rw [hy]
      _ = -1 := half_odd.neg_one_pow
  have h2 : (2 : FpBase) = 0 := by
    have hz : (2 : FpBase) = 1 + 1 := by norm_num
    rw [hz]
    nth_rw 1 [hsum]
    ring
  exact two_ne_zero_Fp h2

/-- **FALSIFICATION (D-P23): THE MOD-4 HYPOTHESIS IS LOAD-BEARING.** At a prime with p = 1 [MOD 4]
    the analogous statement is FALSE: '5 % 4 = 1' and '2^2 = 4 = -1 [MOD 5]'. So 'neg_one_not_sq'
    is not a fact about primes in general, and 'blsP_mod_four' is not decoration on the proof. -/
theorem neg_one_is_sq_mod_five : ((2 : ZMod 5) ^ 2 = -1) := by decide

/-- **AND THE FALSIFICATION BITES ON THE TOWER ITSELF**: at 5, where X^2+1 splits, the AdjoinRoot
    quotient is NOT a field - it has zero divisors, so 'ofPair' would identify (1,0) and (0,1)
    style pairs and the byte model's 'inv' would answer 'none' on nonzero inputs. Pinned here as the
    arithmetic the claim rests on, not as prose. -/
theorem five_mod_four : 5 % 4 = 1 := by decide

/-! ### X^2 + 1 IS IRREDUCIBLE, AND THE QUOTIENT IS A FIELD -/

/-- The modulus of the tower: X^2 + 1, i.e. X^2 - nr2 with nr2 = p - 1 = -1 in EIP-2537's spelling
    (Externals.lean:410-414, where the indeterminate is called v). -/
noncomputable def f2 : FpBase[X] := X ^ 2 + 1

private theorem f2_eq : f2 = X ^ 2 + C (1 : FpBase) := by
  show (X ^ 2 + 1 : FpBase[X]) = X ^ 2 + C 1
  rw [Polynomial.C_1]

theorem f2_natDegree : natDegree f2 = 2 := by
  rw [f2_eq, Polynomial.natDegree_X_pow_add_C]

theorem f2_monic : Monic f2 := by
  rw [f2_eq]
  exact Polynomial.monic_X_pow_add_C (1 : FpBase) (by decide : 2 ≠ 0)

/-- **THE QUOTIENT IS A FIELD.** Irreducibility of a degree-2 polynomial over a field is the same
    statement as having no root ('Polynomial.irreducible_of_degree_le_three_of_not_isRoot'), and no
    root is 'neg_one_not_sq'. -/
theorem f2_irreducible : Irreducible f2 := by
  have hd : natDegree f2 = 2 := f2_natDegree
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) ?_
  intro x hx
  have h : x ^ 2 + 1 = 0 := by
    rwa [Polynomial.IsRoot, f2, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hx
  exact neg_one_not_sq x (eq_neg_of_add_eq_zero_left h)

instance : Fact (Irreducible f2) := ⟨f2_irreducible⟩

/-- **Fp2 = FpBase[u]/(u^2 + 1)**: the algebraic half of the tower 'gap_g2_no_fp2_model' says the tree
    is missing. Elements are quotients of polynomials; the normal form is 'ofPair' below. -/
abbrev Fp2 : Type := AdjoinRoot f2

noncomputable instance : Field Fp2 := inferInstanceAs (Field (AdjoinRoot f2))

/-- The indeterminate u (EIP-2537 calls it v; the gap record writes FpBase[u]/(u^2+1), and this file
    keeps that spelling). -/
noncomputable def u : Fp2 := AdjoinRoot.root f2

/-- **THE DEFINING RELATION.** 'mk f2 (X^2 + 1) = 0' is 'mk_self', and 'mk' is a ring hom, so
    'u^2 + 1 = 0'. Everything computational in Fp2 reduces through this one equation. -/
theorem u_pow_two : u ^ 2 = -1 := by
  have h : AdjoinRoot.mk f2 (X ^ 2 + C (1 : FpBase)) = 0 := by
    rw [← f2_eq]
    exact AdjoinRoot.mk_self
  have h2 : (AdjoinRoot.mk f2 (X ^ 2 + C (1 : FpBase)) : Fp2) = u ^ 2 + 1 := by
    rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one]
    rfl
  rw [h2] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **THE COORDINATE MAP**: (a, b) maps to a + b u. This is EIP-2537's 'el = c0 + c1 * v', and it is
    the map the byte model's pairs are read through. -/
noncomputable def ofPair (a b : FpBase) : Fp2 := AdjoinRoot.mk f2 (C a + C b * X)

theorem ofPair_eq (a b : FpBase) : ofPair a b = (a : Fp2) + (b : Fp2) * u := by
  show (AdjoinRoot.mk f2 (C a + C b * X) : Fp2) = (a : Fp2) + (b : Fp2) * u
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rfl

/-- A linear polynomial that vanishes has vanishing coefficients: the normal-form step. -/
private theorem linear_eq_zero {a b : FpBase} (h : (C a : FpBase[X]) + C b * X = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrArg (fun p : FpBase[X] => p.coeff 0) h
  have h1 := congrArg (fun p : FpBase[X] => p.coeff 1) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C,
    Polynomial.coeff_zero] at h0 h1
  refine ⟨by simpa using h0, by simpa using h1⟩

private theorem natDegree_linear_le_one (a b : FpBase) : natDegree (C a + C b * X) ≤ 1 := by
  refine Nat.le_trans (natDegree_add_le _ _) (Nat.max_le.mpr ⟨?_, ?_⟩)
  · rw [natDegree_C]
    omega
  · calc natDegree (C b * X) ≤ natDegree (C b) + natDegree X := natDegree_mul_le
      _ = 0 + 1 := by rw [natDegree_C, natDegree_X]
      _ ≤ 1 := by omega

/-- **THE NORMAL FORM IS UNIQUE**: a pair maps to zero exactly when both coordinates do. This is
    what makes 'ofPair' a coordinate system rather than merely a surjection, and it is what lets the
    byte model be read back off the field. -/
theorem ofPair_eq_zero_iff (a b : FpBase) : ofPair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    by_cases h0 : (C a + C b * X : FpBase[X]) = 0
    · exact linear_eq_zero h0
    · have hle := natDegree_linear_le_one a b
      have hlt : natDegree (C a + C b * X) < natDegree f2 := by
        rw [f2_natDegree]
        omega
      exact absurd h (AdjoinRoot.mk_ne_zero_of_natDegree_lt f2_monic h0 hlt)
  · rintro ⟨rfl, rfl⟩
    show (AdjoinRoot.mk f2 (C 0 + C 0 * X) : Fp2) = 0
    rw [show (C 0 + C 0 * X : FpBase[X]) = 0 by simp]
    exact map_zero _

/-- **COORDINATES DETERMINE THE ELEMENT.** -/
theorem ofPair_eq_iff (a b c d : FpBase) : ofPair a b = ofPair c d ↔ a = c ∧ b = d := by
  classical
  constructor
  · intro h
    have hpoly : (C (a - c) + C (b - d) * X : FpBase[X]) = (C a + C b * X) - (C c + C d * X) := by
      simp only [map_sub]
      ring
    have h2 : ofPair (a - c) (b - d) = 0 := by
      show (AdjoinRoot.mk f2 (C (a - c) + C (b - d) * X) : Fp2) = 0
      rw [hpoly, map_sub]
      exact sub_eq_zero.mpr h
    obtain ⟨h1, h2'⟩ := (ofPair_eq_zero_iff (a - c) (b - d)).mp h2
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ofPair_ne_zero_iff (a b : FpBase) : ofPair a b ≠ 0 ↔ ¬ (a = 0 ∧ b = 0) := by
  classical
  rw [not_iff_not]
  exact ofPair_eq_zero_iff a b

/-- **WITNESS (D-P23): THE TOWER IS A PROPER EXTENSION OF FpBase.** u is not ofPair a 0 for any a,
    so the coordinate map is not a relabelling of the base field and the byte model has genuinely
    more elements than FpBase - which is the whole point of building Fp2 rather than reusing ZMod blsP. -/
theorem ofPair_u : ofPair 0 1 = u := by
  rw [ofPair_eq]
  simp

theorem u_not_ofPair (a : FpBase) : ofPair a 0 ≠ u := by
  intro h
  obtain ⟨h1, h2⟩ := (ofPair_eq_iff a 0 0 1).mp (by rw [ofPair_u]; exact h)
  exact one_ne_zero_Fp h2.symm

/-! ### The field arithmetic of ofPair -/

theorem ofPair_add (a b c d : FpBase) :
    ofPair (a + c) (b + d) = ofPair a b + ofPair c d := by
  have hpoly : C (a + c) + C (b + d) * X = (C a + C b * X) + (C c + C d * X) := by
    simp only [map_add]
    ring
  show (AdjoinRoot.mk f2 (C (a + c) + C (b + d) * X) : Fp2) =
      AdjoinRoot.mk f2 (C a + C b * X) + AdjoinRoot.mk f2 (C c + C d * X)
  rw [hpoly, ← map_add]

theorem ofPair_mul (a b c d : FpBase) :
    ofPair a b * ofPair c d = ofPair (a * c - b * d) (a * d + b * c) := by
  have h1 : (ofPair a b * ofPair c d : Fp2) =
      AdjoinRoot.mk f2 ((C a + C b * X) * (C c + C d * X)) :=
    (map_mul (AdjoinRoot.mk f2) (C a + C b * X) (C c + C d * X)).symm
  rw [h1]
  show (AdjoinRoot.mk f2 ((C a + C b * X) * (C c + C d * X)) : Fp2) =
      AdjoinRoot.mk f2 (C (a * c - b * d) + C (a * d + b * c) * X)
  refine (AdjoinRoot.mk_eq_mk).mpr ⟨C (b * d), ?_⟩
  rw [f2_eq, Polynomial.C_1]
  simp only [map_sub, map_mul, map_add]
  ring

theorem ofPair_one : ofPair 1 0 = 1 := by
  show (AdjoinRoot.mk f2 (C 1 + C (0 : FpBase) * X) : Fp2) = 1
  rw [show (C (1 : FpBase) + C (0 : FpBase) * X : FpBase[X]) = 1 by simp]
  exact map_one _

theorem ofPair_zero : ofPair 0 0 = 0 := (ofPair_eq_zero_iff 0 0).mpr ⟨rfl, rfl⟩

theorem ofPair_neg (a b : FpBase) : ofPair (-a) (-b) = -(ofPair a b) := by
  have hpoly : C (-a) + C (-b) * X = -((C a + C b * X) : FpBase[X]) := by
    simp only [map_neg]
    ring
  show (AdjoinRoot.mk f2 (C (-a) + C (-b) * X) : Fp2) =
      -(AdjoinRoot.mk f2 (C a + C b * X))
  rw [hpoly, ← map_neg]

theorem ofPair_sub (a b c d : FpBase) :
    ofPair (a - c) (b - d) = ofPair a b - ofPair c d := by
  have h1 : ofPair (a - c) (b - d) = ofPair (a + -c) (b + -d) := by
    simp only [sub_eq_add_neg]
  rw [h1, ofPair_add, ofPair_neg]
  ring

theorem ofPair_of (a : FpBase) : ofPair a 0 = (a : Fp2) := by
  show (AdjoinRoot.mk f2 (C a + C (0 : FpBase) * X) : Fp2) = (a : Fp2)
  rw [show (C a + C (0 : FpBase) * X : FpBase[X]) = C a by simp]
  exact AdjoinRoot.mk_C a

theorem ofPair_natCast (n : ℕ) : ofPair (n : FpBase) 0 = (n : Fp2) := by
  rw [ofPair_of]
  simp [map_natCast]

/-- The conjugate a - b u, and the norm identity (a+bu)(a-bu) = a^2 + b^2: the reason the byte
    model's 'inv' divides by c0^2 + c1^2. -/
theorem ofPair_mul_conj (a b : FpBase) :
    ofPair a b * ofPair a (-b) = ofPair (a ^ 2 + b ^ 2) 0 := by
  rw [ofPair_mul]
  refine congrArg₂ ofPair ?_ ?_ <;> ring

/-- **THE NORM VANISHES ONLY AT ZERO.** This is 'neg_one_not_sq' repackaged, and it is the exact
    reason 'fp2Ops.inv' never answers 'none' on a nonzero element. -/
theorem norm_ne_zero {a b : FpBase} (h : ofPair a b ≠ 0) : (a ^ 2 + b ^ 2 : FpBase) ≠ 0 := by
  classical
  intro hn
  have h1 : ofPair a b * ofPair a (-b) = 0 := by
    rw [ofPair_mul_conj, hn, ofPair_zero]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h h2
  · obtain ⟨ha, hb⟩ := (ofPair_eq_zero_iff a (-b)).mp h2
    exact h ((ofPair_eq_zero_iff a b).mpr ⟨ha, neg_eq_zero.mp hb⟩)

/-- **THE INVERSE IN COORDINATES**: (a + b u)^-1 = (a (a^2+b^2)^-1) - (b (a^2+b^2)^-1) u. Exactly
    the formula 'fp2Ops.inv' computes, and the last place the non-residue fact is used. -/
theorem ofPair_inv (a b : FpBase) (h : ofPair a b ≠ 0) :
    (ofPair a b)⁻¹ = ofPair (a * (a ^ 2 + b ^ 2)⁻¹) (-b * (a ^ 2 + b ^ 2)⁻¹) := by
  have hn : (a ^ 2 + b ^ 2 : FpBase) ≠ 0 := norm_ne_zero h
  have hprod : ofPair (a * (a ^ 2 + b ^ 2)⁻¹) (-b * (a ^ 2 + b ^ 2)⁻¹) * ofPair a b = 1 := by
    rw [ofPair_mul]
    have h1 : a * (a ^ 2 + b ^ 2)⁻¹ * a - -b * (a ^ 2 + b ^ 2)⁻¹ * b = 1 := by
      field_simp [hn]
      ring
    have h2 : a * (a ^ 2 + b ^ 2)⁻¹ * b + -b * (a ^ 2 + b ^ 2)⁻¹ * a = 0 := by
      field_simp [hn]
      ring
    rw [h1, h2, ofPair_one]
  exact (eq_inv_of_mul_eq_one_left hprod).symm

/-! ### Agreement with the byte model fp2Ops -/

/-- Reducing a natural mod the modulus does not change its image in FpBase (the same
    'ZMod.natCast_zmod_val' argument Instances/G1Agreement.lean makes for its 'K'). -/
private lemma coe_mod (a : ℕ) : ((a % blsP : ℕ) : FpBase) = (a : FpBase) :=
  ZMod.natCast_zmod_val (a : FpBase)

private lemma coe_nat_eq_iff (a b : ℕ) : ((a : FpBase) = (b : FpBase)) ↔ a % blsP = b % blsP := by
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast] at this
  · intro h
    exact ZMod.val_injective blsP (by rw [ZMod.val_natCast, ZMod.val_natCast]; exact h)

private lemma coe_zero_Fp : ((0 : ℕ) : FpBase) = 0 := Nat.cast_zero
private lemma coe_one_Fp : ((1 % blsP : ℕ) : FpBase) = 1 := Nat.cast_one
private lemma coe_add_nat (a b : ℕ) : ((a + b : ℕ) : FpBase) = (a : FpBase) + (b : FpBase) := Nat.cast_add a b
private lemma coe_mul_nat (a b : ℕ) : ((a * b : ℕ) : FpBase) = (a : FpBase) * (b : FpBase) := Nat.cast_mul a b

private lemma coe_sub_nat (a b : ℕ) :
    (((a + blsP - b % blsP) % blsP : ℕ) : FpBase) = (a : FpBase) - (b : FpBase) := by
  have hb : b % blsP ≤ a + blsP := Nat.le_trans (Nat.mod_lt b p_pos).le (by omega)
  show (((a + blsP - b % blsP) % blsP : ℕ) : FpBase) = (a : FpBase) - (b : FpBase)
  rw [coe_mod, Nat.cast_sub hb, Nat.cast_add, ZMod.natCast_self, add_zero, ← coe_mod b]

private lemma coe_neg_nat' (a : ℕ) : ((blsP - a % blsP : ℕ) : FpBase) = -(a : FpBase) := by
  have ha : a % blsP ≤ blsP := Nat.le_of_lt (Nat.mod_lt a p_pos)
  rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub, ← coe_mod a]

private lemma coe_neg_nat (a : ℕ) : (((blsP - a % blsP) % blsP : ℕ) : FpBase) = -(a : FpBase) := by
  have ha : a % blsP ≤ blsP := Nat.le_of_lt (Nat.mod_lt a p_pos)
  show (((blsP - a % blsP) % blsP : ℕ) : FpBase) = -(a : FpBase)
  rw [coe_mod, Nat.cast_sub ha, ZMod.natCast_self, zero_sub, ← coe_mod a]

/-- 'fpInv' casts to the field inverse (the G1 file's 'coe_fpInv', restated here because that one is
    private and this file must not import it). -/
private lemma coe_fpInv {x v : ℕ} (hv : fpInv x = some v) : (v : FpBase) = (x : FpBase)⁻¹ := by
  have hne : ¬ (x % blsP == 0) := by
    intro h
    rw [fpInv, if_pos (by simpa using h)] at hv
    exact absurd hv (by simp)
  rw [fpInv, if_neg hne] at hv
  rw [Option.some.injEq] at hv
  subst hv
  show ((modPow x (blsP - 2) blsP : ℕ) : FpBase) = (x : FpBase)⁻¹
  have hnz : (x : FpBase) ≠ 0 := by
    intro h
    have h2 : x % blsP = 0 := by
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast, ZMod.val_zero] at this
    exact hne (by simpa using h2)
  rw [modPow_eq x (blsP - 2) blsP p_pos, coe_mod, Nat.cast_pow,
    pow_card_sub_two_eq_inv_card _ hnz]

/-- **THE BRIDGE FROM BYTES TO THE FIELD**: a pair of naturals maps to 'ofPair' of their images in
    FpBase. This is the map the agreement lemmas are stated about, and the one the G2 frame type in
    G2Agreement.lean is built from. -/
noncomputable def ofNatPair (x : Nat × Nat) : Fp2 := ofPair (x.1 : FpBase) (x.2 : FpBase)

/-- **A SUM OF TWO SQUARES IN FpBase VANISHES ONLY TERMWISE.** The other form of the non-residue fact,
    and the one the byte-level inverse needs. -/
theorem sum_sq_eq_zero {a b : FpBase} (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  classical
  by_cases hb : b = 0
  · have h2 : a ^ 2 = 0 := by
      rw [← h, hb]
      simp
    exact ⟨sq_eq_zero_iff.mp h2, hb⟩
  · have hb' : b ≠ 0 := hb
    have h1 : a ^ 2 = -b ^ 2 := eq_neg_of_add_eq_zero_left h
    have hinv : b * b⁻¹ = 1 := mul_inv_cancel₀ hb'
    have hsq : (a * b⁻¹) ^ 2 = -1 := by
      calc (a * b⁻¹) ^ 2 = a ^ 2 * (b⁻¹) ^ 2 := mul_pow a (b⁻¹) 2
        _ = (-b ^ 2) * (b⁻¹) ^ 2 := by rw [h1]
        _ = -(b * b⁻¹) ^ 2 := by ring
        _ = -1 := by rw [hinv]; simp
    exact absurd hsq (neg_one_not_sq (a * b⁻¹))


theorem ofNatPair_eq_zero_iff (x : Nat × Nat) :
    ofNatPair x = 0 ↔ x.1 % blsP = 0 ∧ x.2 % blsP = 0 := by
  classical
  rw [ofNatPair, ofPair_eq_zero_iff]
  refine ⟨fun ⟨h1, h2⟩ => ⟨(coe_nat_eq_iff x.1 0).mp h1, (coe_nat_eq_iff x.2 0).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨(coe_nat_eq_iff x.1 0).mpr (by rw [h1, Nat.zero_mod]),
      (coe_nat_eq_iff x.2 0).mpr (by rw [h2, Nat.zero_mod])⟩⟩

theorem ofNatPair_eq_iff (a b : Nat × Nat) :
    ofNatPair a = ofNatPair b ↔ (a.1 % blsP = b.1 % blsP ∧ a.2 % blsP = b.2 % blsP) := by
  rw [ofNatPair, ofNatPair, ofPair_eq_iff]
  refine ⟨fun ⟨h1, h2⟩ => ⟨(coe_nat_eq_iff _ _).mp h1, (coe_nat_eq_iff _ _).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨(coe_nat_eq_iff _ _).mpr h1, (coe_nat_eq_iff _ _).mpr h2⟩⟩

/-- **'fp2Ops.beq' IS FIELD EQUALITY** - the fact every branch walk in the group-law agreement
    starts from. -/
theorem fp2Beq_iff (a b : Nat × Nat) : fp2Ops.beq a b = true ↔ ofNatPair a = ofNatPair b := by
  show (a.1 % blsP == b.1 % blsP && a.2 % blsP == b.2 % blsP) = true ↔ _
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  exact (ofNatPair_eq_iff a b).symm

theorem ofNatPair_zero : ofNatPair fp2Ops.zero = 0 := by
  show (ofPair ((0 : ℕ) : FpBase) ((0 : ℕ) : FpBase) : Fp2) = 0
  simp only [Nat.cast_zero]
  exact ofPair_zero

theorem ofNatPair_one : ofNatPair fp2Ops.one = 1 := by
  show ofPair ((1 % blsP : ℕ) : FpBase) ((0 : ℕ) : FpBase) = 1
  rw [coe_one_Fp, coe_zero_Fp, ofPair_one]

/-- **FALSIFICATION (D-P23): THE BRIDGE IS NOT INJECTIVE ON RAW NATURAL PAIRS.** Two naturals that
    agree mod p map to the same field element, which is exactly why the frame type in
    G2Agreement.lean needs the canonicity hypothesis the G1 file needed - and why 'fp2Ops.beq'
    reduces before comparing. -/
theorem ofNatPair_not_inj : ofNatPair (0, 0) = ofNatPair (blsP, blsP) := by
  show (ofPair ((0 : ℕ) : FpBase) ((0 : ℕ) : FpBase) : Fp2) =
      ofPair ((blsP : ℕ) : FpBase) ((blsP : ℕ) : FpBase)
  rw [ZMod.natCast_self blsP]
  simp only [Nat.cast_zero]

/-- **THE ADDITION AGREEMENT.** -/
theorem ofNatPair_add (a b : Nat × Nat) :
    ofNatPair (fp2Ops.add a b) = ofNatPair a + ofNatPair b := by
  show ofPair (((a.1 + b.1) % blsP : ℕ) : FpBase) (((a.2 + b.2) % blsP : ℕ) : FpBase) =
      ofPair (a.1 : FpBase) (a.2 : FpBase) + ofPair (b.1 : FpBase) (b.2 : FpBase)
  rw [coe_mod, coe_mod, coe_add_nat, coe_add_nat, ofPair_add]

/-- **THE SUBTRACTION AGREEMENT.** -/
theorem ofNatPair_sub (a b : Nat × Nat) :
    ofNatPair (fp2Ops.sub a b) = ofNatPair a - ofNatPair b := by
  show ofPair (((a.1 + blsP - b.1 % blsP) % blsP : ℕ) : FpBase)
    (((a.2 + blsP - b.2 % blsP) % blsP : ℕ) : FpBase) =
      ofPair (a.1 : FpBase) (a.2 : FpBase) - ofPair (b.1 : FpBase) (b.2 : FpBase)
  rw [coe_sub_nat, coe_sub_nat, ofPair_sub]

/-- **THE NEGATION AGREEMENT.** -/
theorem ofNatPair_neg (a : Nat × Nat) :
    ofNatPair (fp2Ops.neg a) = -(ofNatPair a) := by
  show ofPair (((blsP - a.1 % blsP) % blsP : ℕ) : FpBase) (((blsP - a.2 % blsP) % blsP : ℕ) : FpBase) =
      -(ofPair (a.1 : FpBase) (a.2 : FpBase))
  rw [coe_neg_nat, coe_neg_nat, ofPair_neg]

/-- **THE MULTIPLICATION AGREEMENT** - the line that says the byte model and the field are the same
    ring: 'fp2Ops.mul' is ofPair-multiplication, i.e. u^2 = -1 arithmetic. -/
theorem ofNatPair_mul (a b : Nat × Nat) :
    ofNatPair (fp2Ops.mul a b) = ofNatPair a * ofNatPair b := by
  show ofPair (((a.1 * b.1 + (blsP - a.2 * b.2 % blsP)) % blsP : ℕ) : FpBase)
    (((a.1 * b.2 + a.2 * b.1) % blsP : ℕ) : FpBase) =
      ofPair (a.1 : FpBase) (a.2 : FpBase) * ofPair (b.1 : FpBase) (b.2 : FpBase)
  rw [coe_mod, coe_mod, Nat.cast_add, coe_neg_nat', coe_mul_nat, coe_mul_nat, Nat.cast_add,
    coe_mul_nat, coe_mul_nat, ofPair_mul, sub_eq_add_neg]

/-- The curve coefficient: fp2Ops.b = g2B = (4, 4) = 4 + 4u = 4(u+1), the EIP-2537 G2 b. -/
theorem ofNatPair_b : ofNatPair fp2Ops.b = ofPair (4 : FpBase) (4 : FpBase) := rfl

/-- 'fpInv' answers 'none' exactly at the multiples of the modulus. -/
private theorem fpInv_none_iff (x : ℕ) : fpInv x = none ↔ x % blsP = 0 := by
  show (if x % blsP == 0 then none else some (modPow x (blsP - 2) blsP)) = none ↔ _
  by_cases h : x % blsP == 0
  · rw [if_pos h]
    exact ⟨fun _ => by simpa using h, fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨fun hh => absurd hh (by simp), fun hh => absurd (by simpa using hh) h⟩

/-- **THE INVERSE BRANCH, IN FIELD FORM.** 'fp2Ops.inv x = none' exactly when x is the zero element:
    the first branch tests the input and the second tests the norm, and the norm vanishes only at
    zero. This is the fact the vertical-chord and doubling branches of the group-law agreement turn
    on. -/
theorem fp2Ops_inv_none_iff (x : Nat × Nat) :
    fp2Ops.inv x = none ↔ ofNatPair x = 0 := by
  classical
  have key : fp2Ops.inv x = none ↔
      (x.1 % blsP == 0 && x.2 % blsP == 0) = true ∨
        fpInv ((x.1 * x.1 + x.2 * x.2) % blsP) = none := by
    show (if x.1 % blsP == 0 && x.2 % blsP == 0 then none
        else match fpInv ((x.1 * x.1 + x.2 * x.2) % blsP) with
          | none => none
          | some ni => some ((x.1 * ni) % blsP, (blsP - x.2 * ni % blsP) % blsP)) = none ↔ _
    by_cases h : x.1 % blsP == 0 && x.2 % blsP == 0
    · rw [if_pos h]
      exact ⟨fun _ => Or.inl h, fun _ => rfl⟩
    · rw [if_neg h]
      constructor
      · intro hh
        cases h2 : fpInv ((x.1 * x.1 + x.2 * x.2) % blsP) with
        | none => exact Or.inr rfl
        | some ni =>
            rw [h2] at hh
            exact absurd hh (Option.some_ne_none _)
      · rintro (hpos | hh)
        · exact absurd hpos h
        · rw [hh]
  rw [key, ofNatPair_eq_zero_iff, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, fpInv_none_iff]
  refine ⟨fun hh => ?_, fun hh => Or.inl hh⟩
  · rcases hh with ⟨h1, h2⟩ | hnorm
    · exact ⟨h1, h2⟩
    · have hsum : ((x.1 * x.1 + x.2 * x.2 : ℕ) : FpBase) = 0 := by
          rw [← coe_mod (x.1 * x.1 + x.2 * x.2)]
          exact (coe_nat_eq_iff _ 0).mpr (by rw [Nat.zero_mod]; exact hnorm)
      have h3 : (x.1 : FpBase) ^ 2 + (x.2 : FpBase) ^ 2 = 0 := by
        rw [pow_two, pow_two, ← hsum, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      obtain ⟨q1, q2⟩ := sum_sq_eq_zero h3
      exact ⟨by simpa using (coe_nat_eq_iff x.1 0).mp q1,
        by simpa using (coe_nat_eq_iff x.2 0).mp q2⟩

/-- **THE INVERSE AGREEMENT**: where the byte model does return an inverse, it returns THE inverse
    of the field. Together with 'fp2Ops_inv_none_iff' this pins 'fp2Ops.inv' completely. -/
theorem ofNatPair_inv {x v : Nat × Nat} (h : fp2Ops.inv x = some v) :
    ofNatPair v = (ofNatPair x)⁻¹ := by
  classical
  have hbranch : (if x.1 % blsP == 0 && x.2 % blsP == 0 then none
      else match fpInv ((x.1 * x.1 + x.2 * x.2) % blsP) with
        | none => none
        | some ni => some ((x.1 * ni) % blsP, (blsP - x.2 * ni % blsP) % blsP)) = some v := h
  have hne : ¬ (x.1 % blsP == 0 && x.2 % blsP == 0) := by
    intro hh
    rw [if_pos hh] at hbranch
    exact absurd hbranch.symm (Option.some_ne_none _)
  rw [if_neg hne] at hbranch
  cases hn : fpInv ((x.1 * x.1 + x.2 * x.2) % blsP) with
  | none =>
      rw [hn] at hbranch
      dsimp only at hbranch
      exact absurd hbranch.symm (Option.some_ne_none _)
  | some ni =>
      rw [hn] at hbranch
      dsimp only at hbranch
      have ev : v = ((x.1 * ni) % blsP, (blsP - x.2 * ni % blsP) % blsP) :=
        (Option.some.inj hbranch).symm
      subst ev
      have hni := coe_fpInv hn
      have hnz : ofPair (x.1 : FpBase) (x.2 : FpBase) ≠ 0 := by
        intro hh
        obtain ⟨q1, q2⟩ := (ofPair_eq_zero_iff (x.1 : FpBase) (x.2 : FpBase)).mp hh
        simp only [← ZMod.val_eq_zero, ZMod.val_natCast] at q1 q2
        exact hne (by rw [Bool.and_eq_true]; simp [q1, q2])
      show ofPair (((x.1 * ni) % blsP : ℕ) : FpBase)
        (((blsP - x.2 * ni % blsP) % blsP : ℕ) : FpBase) = _
      rw [coe_mod, coe_mul_nat, coe_neg_nat, coe_mul_nat]
      have hnorm : (((x.1 * x.1 + x.2 * x.2) % blsP : ℕ) : FpBase) =
          (x.1 : FpBase) ^ 2 + (x.2 : FpBase) ^ 2 := by
        rw [coe_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ← pow_two, ← pow_two]
      have hx : ofNatPair x = ofPair (x.1 : FpBase) (x.2 : FpBase) := rfl
      rw [hx, ofPair_inv (x.1 : FpBase) (x.2 : FpBase) hnz, ← hnorm, hni, neg_mul]

/-! ### D-P23: the gate for this package -/

/-- **THE ARITHMETIC MODEL, CHECKED AGAINST THE BYTE MODEL.** Every line is a computation in
    'fp2Ops' (integer arithmetic on pairs), and together they say the byte model is the field this
    file builds: line 1 re-pins the mod-4 fact the whole tower rests on; lines 2-4 say 'fp2Ops.inv'
    really is a two-sided inverse under 'fp2Ops.mul' at three different elements, including one
    with both coordinates nonzero and one at the top of the range; line 5 says 'inv' refuses zero;
    line 6 pins the curve coefficient to 4(u+1) as the pair (4,4) the EIP prints; line 7 checks
    the norm identity against the byte multiply - (c0,c1)*(c0,-c1) lands on the rational line, the
    identity 'ofPair_mul_conj' lifts to the field; line 8 is the falsification half of line 7, the
    norm of THIS nonzero element is not zero, which is what 'fp2Ops.inv' would break if -1 were a
    square. -/
def fp2ModelKats_ok : Bool :=
  (blsP % 4 == 3) &&
    (let x := (12345, 67890);
      match fp2Ops.inv x with
      | none => false
      | some y => fp2Ops.mul x y == fp2Ops.one && fp2Ops.mul y x == fp2Ops.one) &&
    (let x := (blsP - 1, blsP - 2);
      match fp2Ops.inv x with
      | none => false
      | some y => fp2Ops.mul x y == fp2Ops.one) &&
    (let x := (2, 3);
      match fp2Ops.inv x with
      | none => false
      | some y => fp2Ops.mul x y == fp2Ops.one) &&
    (fp2Ops.inv (0, 0) == none) &&
    (fp2Ops.b == (4, 4)) &&
    (let x := (987654321, 123456789);
      fp2Ops.mul x (x.1, (blsP - x.2 % blsP) % blsP) ==
        ((x.1 * x.1 + x.2 * x.2) % blsP, 0)) &&
    (let x := (987654321, 123456789);
      (x.1 * x.1 + x.2 * x.2) % blsP != 0)

#eval fp2ModelKats_ok   -- expect true

/-- **AND THE MODEL IS NOT THE BASE FIELD IN DISGUISE**: 'u' is a new element, so Fp2 has strictly
    more than the p elements of FpBase - the reason a G2 point cannot be modelled with the G1 field.
    A theorem and not a gate, because Fp2 is noncomputable. -/
theorem fp2_ne_ofPair_zero : u ≠ 0 := by
  intro h
  have h2 : ofPair 0 1 = 0 := by rw [ofPair_u, h]
  obtain ⟨h1, h2'⟩ := (ofPair_eq_zero_iff 0 1).mp h2
  exact one_ne_zero_Fp h2'

end Midfall.Instances
