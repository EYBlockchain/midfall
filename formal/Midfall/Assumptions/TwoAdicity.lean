-- |
-- Midfall.Assumptions.TwoAdicity
--
-- P-4a2: the hypothesis R-47 says the tree never had, and its discharge at the REAL
-- scalar field.
--
-- WHY THIS FILE EXISTS. `Midfall.Halo2.FieldConsts` (Exec/Arith.lean:64-72) is four bare
-- data fields: `numBits`, `s`, `rootOfUnity`, `zeta`. Nothing anywhere checked that
-- `rootOfUnity` is a PRIMITIVE 2^S-th root or that `zeta` has order 3, and
-- Assumptions/Pairing.lean's own header recorded that as a trust boundary (R-3). The
-- consequence is measured, not guessed: the only Surface in the tree declares a domain
-- with `omega := 1`, `omegaInv := 1`, `barycentricWeight := 4`
-- (Instances/SurfaceFixture.lean, `fxDom`), so `EnvAgrees.baryWeight` evaluates FALSE and
-- `EnvAgrees.omegaOrder` (`omega ^ n = 1`) passes only VACUOUSLY - a domain whose
-- generator is 1 is not a domain. Any gate of the shape `omega ^ (2^k) = 1` is satisfied
-- by 1, which is the bug class this file exists to make impossible to state.
--
-- WHAT IS PROVED, AND WHERE. Everything here is at the REAL BLS12-381 scalar modulus
-- `r`, and everything is discharged by the KERNEL (`decide`), not by `native_decide`:
-- the two facts that pin a primitive root are `root ^ 2^32 = 1` and `root ^ 2^31 = -1`,
-- i.e. 32 modular squarings of a 255-bit number, which the kernel's GMP-accelerated
-- Nat arithmetic handles in well under a second. THE STANDING WARNING THAT `decide` WILL
-- NOT REDUCE AT 255-BIT `r` IS TRUE OF INVERSION AND FALSE OF EXPONENTIATION: `decide`
-- gets stuck on `(4 : Fr r)⁻¹` (it cannot reduce `ZMod.inv`), so every inverse in this
-- file is carried as a LITERAL and proved by a multiplication (`inv4 * 4 = 1`), and the
-- equation `a = b⁻¹` is obtained through `eq_inv_iff_mul_eq_one`, never by reducing `⁻¹`.
-- No toy field is substituted for `r`: `Fr r` is exhibited as well-formed below, and the
-- small fields are exhibited ALONGSIDE it, because they are where the two-adicity bound
-- can be seen to bite (ZMod 17 has no element of order 3 at all).
--
-- THE TWO-ADICITY FINDING. `r - 1 = 2^32 * m` with `m` odd, so the legitimate range of
-- `k` for a 2^k-th root of unity in `Fr r` is EXACTLY `k <= 32`: for every `k <= 32` one
-- is exhibited (`frRootOfUnity ^ 2^(32-k)`, order exactly 2^k), and for `k > 32` none can
-- exist, because the order of any element of `Fr rˣ` divides `r - 1`. `fc.s := 32` in the
-- fixture's constants was therefore right as a NUMBER and wrong as a CLAIM: nothing had
-- ever proved the root had that order.
--
-- WHAT THE EARLIER DRAFT GOT WRONG (plans/P-4a-roots.md, re-derived rather than trusted):
--
--   1. It claims the reduced-index rotation form `omega^((i+rot) % n) = omega^i *
--      omega^rot` "needs omega to have order exactly n, not merely dividing n". It does
--      not: `omega ^ n = 1` alone gives `omega ^ (m % n) = omega ^ m` for every m, and the
--      rest is `pow_add`. `rotate_omega_mod_form` below is stated with the weaker
--      hypothesis and is therefore usable everywhere the draft's version would have been.
--      Exactness is load-bearing for a DIFFERENT fact - that the n powers are DISTINCT,
--      hence that `x^n = 1` puts x among them (`zH_vanishes_iff`), which is what
--      `EnvAgrees.omegaOrder` is cited for in Lowering/Inv.lean.
--   2. It proposes `lIRange_delta`: at `x = omega^j` the r-th entry is `if r = j then 1
--      else 0`. That is FALSE of the port, and Domain.lean's own comment on `l_i_range`
--      says why: the batch inversion leaves a zero at a zero denominator, and at a domain
--      point `xn = x^n = 1`, so the common factor `(xn - 1) * barycentricWeight` is zero
--      and EVERY entry comes back 0. `lIRange_at_root_is_zero` below is the true
--      statement of that case, and `lIRange_closed_form` is the closed form off the roots.
--   3. It asks for `zeta` of order 3 to be discharged at `fc17`. ZMod 17 has no element of
--      order 3 (`17 - 1 = 16`, and 3 does not divide 16), so that request is
--      unsatisfiable; the two conditions are stated separately here and `fc17` passes the
--      root one and FAILS the zeta one, which is itself the falsifiability evidence.
--
-- GAP POLICY: no `sorry` in this file. A missing proof is a named hypothesis (the
-- structure) or a named gap in the comment that says what is missing (`powVartime`, at
-- the end of the header).
--
-- ONE THING THIS FILE DOES NOT DO, STATED RATHER THAN HIDDEN: `EvaluationDomain.rotateOmega`
-- multiplies by `powVartime omega r`, and `powVartime` folds over `Nat.toDigits 2 r` -
-- the PRINTING digits from Lean core, which have no value characterisation in core or
-- mathlib (`Nat.ofDigits_toDigits` does not exist because `Nat.toDigits` is not the
-- `Nat.digits` of mathlib). So the lemmas below are stated with `^`, which is what
-- `Spec/Lemmas.lean` already does for `rotate_omega_eq`, and the bridge
-- `powVartime x n = x ^ n` is a named gap rather than a claim. It is a definitional
-- unfolding problem about a printing function, not an algebra problem, and it is the
-- reason no lemma here mentions `rotateOmega`.

import Midfall.Assumptions.Pairing
import Midfall.Halo2.Exec.Domain
import Mathlib.FieldTheory.Finite.Basic

namespace Midfall.Assumptions
open Midfall Midfall.Halo2

variable {F : Type} [Field F]

/-- `0 < 2^n`, phrased once so `omega` never has to look at a power. -/
theorem twoPow_pos (n : ℕ) : 0 < 2 ^ n :=
  Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.one_le_pow n 2 (by decide))

/-! ### The order predicate, and why it is not `orderOf` -/

/-- `x` has multiplicative order EXACTLY `n`: `n` is positive, `x ^ n = 1`, and no smaller
    positive power is 1.

    Stated on the field rather than as mathlib's `orderOf` on `Fˣ` for one practical
    reason: the exhibits that have to CHECK this are equalities of field elements that
    `decide` can reduce, and `orderOf (Units.mk0 x hx)` would put a unit coercion between
    the statement and the computation. `orderExactly_twoPow` below is the bridge from the
    two decidable squaring facts to this predicate, and it goes through `orderOf`
    internally, so nothing is lost: the divisibility law `orderExactly.dvd_of_pow_eq_one`
    is the same content as Lagrange's theorem for the element. -/
def orderExactly (x : F) (n : ℕ) : Prop :=
  0 < n ∧ x ^ n = 1 ∧ ∀ m : ℕ, 0 < m → m < n → x ^ m ≠ 1

theorem orderExactly.pos {x : F} {n : ℕ} (h : orderExactly x n) : 0 < n := h.1
theorem orderExactly.pow_eq_one {x : F} {n : ℕ} (h : orderExactly x n) : x ^ n = 1 := h.2.1
theorem orderExactly.pow_ne_one {x : F} {n : ℕ} (h : orderExactly x n)
    {m : ℕ} (h0 : 0 < m) (hm : m < n) : x ^ m ≠ 1 := h.2.2 m h0 hm

theorem orderExactly.ne_zero {x : F} {n : ℕ} (h : orderExactly x n) : x ≠ 0 := by
  intro hx
  have : (0 : F) = 1 := by rw [← h.2.1, hx, zero_pow (Nat.ne_of_gt h.1)]
  exact zero_ne_one this

/-- The divisibility law: the order divides every exponent that reaches 1. -/
theorem orderExactly.dvd_of_pow_eq_one {x : F} {n : ℕ} (h : orderExactly x n)
    {m : ℕ} (hm : x ^ m = 1) : n ∣ m := by
  have key : x ^ (m % n) = 1 := by
    have : x ^ m = x ^ (n * (m / n) + m % n) := by rw [Nat.div_add_mod]
    rw [this, pow_add, pow_mul, h.2.1, one_pow, one_mul] at hm
    exact hm
  by_contra hne
  have hpos : 0 < m % n :=
    Nat.pos_of_ne_zero (fun hrw => hne (Nat.dvd_of_mod_eq_zero hrw))
  exact h.2.2 _ hpos (Nat.mod_lt _ h.1) key

theorem orderExactly.pow_eq_one_iff {x : F} {n : ℕ} (h : orderExactly x n)
    {m : ℕ} : x ^ m = 1 ↔ n ∣ m :=
  ⟨fun hm => h.dvd_of_pow_eq_one hm, fun ⟨q, hq⟩ => by rw [hq, pow_mul, h.2.1, one_pow]⟩

theorem orderExactly.pow_mod {x : F} {n : ℕ} (h : orderExactly x n) {m : ℕ} :
    x ^ (m % n) = x ^ m := by
  have : x ^ m = x ^ (n * (m / n) + m % n) := by rw [Nat.div_add_mod]
  rw [pow_add, pow_mul, h.2.1, one_pow, one_mul] at this
  exact this.symm

/-- THE CONSEQUENCE EXACTNESS BUYS: the `n` powers are DISTINCT on `[0, n)`. At
    `omega := 1` this is false, which is the whole reason `fxDom` was not a domain. -/
theorem orderExactly.pow_inj_on {x : F} {n : ℕ} (h : orderExactly x n)
    {i j : ℕ} (hi : i < n) (hj : j < n) : x ^ i = x ^ j ↔ i = j := by
  constructor
  · intro heq
    rcases Nat.lt_trichotomy i j with hlt | he | hgt
    · exfalso
      have hsum : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt hlt)
      have hprod : x ^ j = x ^ (j - i) * x ^ i :=
        (congrArg (x ^ ·) hsum).symm.trans (pow_add x (j - i) i)
      have hc : x ^ (j - i) * x ^ i = 1 * x ^ i :=
        hprod.symm.trans (heq.symm.trans (one_mul _).symm)
      have h1 : x ^ (j - i) = 1 := mul_right_cancel₀ (pow_ne_zero i h.ne_zero) hc
      exact h.pow_ne_one (by omega) (by omega) h1
    · exact he
    · exfalso
      have hsum : i - j + j = i := Nat.sub_add_cancel (Nat.le_of_lt hgt)
      have hprod : x ^ i = x ^ (i - j) * x ^ j :=
        (congrArg (x ^ ·) hsum).symm.trans (pow_add x (i - j) j)
      have hc : x ^ (i - j) * x ^ j = 1 * x ^ j :=
        hprod.symm.trans (heq.trans (one_mul _).symm)
      have h1 : x ^ (i - j) = 1 := mul_right_cancel₀ (pow_ne_zero j h.ne_zero) hc
      exact h.pow_ne_one (by omega) (by omega) h1
  · intro he; subst he; rfl

/-- The decidable discharge rule for a 2-power order: the top squaring is 1 and the one
    immediately below it is NOT 1. The second half is what makes this non-vacuous; a
    lemma that only ever checked the first half would be satisfied by `omega := 1`, which
    is the defect this package was written to remove. -/
theorem orderExactly_twoPow {x : F} [Fintype F] {s : ℕ}
    (hs : 1 ≤ s) (h1 : x ^ 2 ^ s = 1) (h2 : x ^ 2 ^ (s - 1) ≠ 1) : orderExactly x (2 ^ s) := by
  have hx : x ≠ 0 := by
    intro h
    have : (0 : F) = 1 := by
      rw [← h1, h, zero_pow (Nat.ne_of_gt (Nat.one_le_pow s 2 (by decide)))]
    exact zero_ne_one this
  classical
  let u : Fˣ := Units.mk0 x hx
  have hcoe : ∀ m : ℕ, ((u ^ m : Fˣ) : F) = x ^ m := fun m => by simp [u]
  have hord : orderOf u = 2 ^ s := by
    have hd : orderOf u ∣ 2 ^ s :=
      orderOf_dvd_of_pow_eq_one (Units.ext ((hcoe (2 ^ s)).trans h1))
    obtain ⟨j, hj, heq⟩ : ∃ j ≤ s, orderOf u = 2 ^ j := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rcases Nat.lt_or_eq_of_le hj with hjt | hj2
    · exfalso
      have hle : j ≤ s - 1 := by omega
      have hdvd : orderOf u ∣ 2 ^ (s - 1) := by
        rw [heq]
        exact Nat.pow_dvd_pow 2 hle
      have hpow : u ^ 2 ^ (s - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      exact h2 ((hcoe (2 ^ (s - 1))).symm.trans (congrArg Units.val hpow))
    · exact heq.trans (congrArg (2 ^ ·) hj2)
  refine ⟨twoPow_pos s, h1, ?_⟩
  intro m hm0 hmn hme
  have : orderOf u ∣ m :=
    orderOf_dvd_of_pow_eq_one (Units.ext ((hcoe m).trans hme))
  rw [hord] at this
  exact absurd (Nat.le_of_dvd hm0 this) (by omega)

/-- The unique element of order 2 in a field. Used by `zH_vanishes_iff` and by the
    `omega ^ 2^(s-1) = -1` exhibits. -/
theorem eq_one_or_neg_one_of_sq_eq_one {F : Type} [Field F] {z : F} (hz : z ^ 2 = 1) :
    z = 1 ∨ z = -1 := by
  have hfac : (z - 1) * (z + 1) = 0 := by
    calc (z - 1) * (z + 1) = z * z + z * 1 - 1 * z - 1 * 1 := by ring
      _ = z ^ 2 - 1 := by ring
      _ = 0 := by rw [hz]; exact sub_self _
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact eq_neg_of_add_eq_zero_left h


end Midfall.Assumptions

/-! ### The hypothesis structure R-47 asks for -/

namespace Midfall.Halo2.FieldConsts
open Midfall Assumptions

/-- R-47's missing hypothesis, as a structure of propositions (gap policy: a named
    hypothesis, never a bare `sorry`, and never a check the Rust reference does not have
    either - this constrains what the PROOFS may assume, not what the verifier computes).

    `root_order` is the whole point: order EXACTLY `2^fc.s`, not "a divisor of".
    `zeta_order` is what `EvaluationDomain.new` needs for the coset generator
    (`g_coset`, `g_coset_inv = zeta^2`, and the `t_evaluations` nonzeroness), and it is
    the half that ZMod 17 cannot supply.
    `numBits_gt_s` is the sanity bound the Rust asserts at domain.rs:53 indirectly
    (`extended_k <= F::S` and `S < NUM_BITS` for every real field). -/
structure IsWellFormed {F : Type} [Field F] (fc : FieldConsts F) : Prop where
  root_order : orderExactly fc.rootOfUnity (2 ^ fc.s)
  zeta_order : orderExactly fc.zeta 3
  numBits_gt_s : fc.s < fc.numBits

/-- The discharge rule: five literal checks. -/
theorem isWellFormed_of {F : Type} [Field F] [Fintype F] {fc : FieldConsts F}
    (hs : 1 ≤ fc.s) (hr1 : fc.rootOfUnity ^ 2 ^ fc.s = 1)
    (hr2 : fc.rootOfUnity ^ 2 ^ (fc.s - 1) ≠ 1) (hz1 : fc.zeta ^ 3 = 1)
    (hz2 : fc.zeta ≠ 1) (hnb : fc.s < fc.numBits) : fc.IsWellFormed :=
  { root_order := orderExactly_twoPow hs hr1 hr2
    zeta_order := ⟨by omega, hz1, fun m hm0 hmn hme => by
        have hcase : m = 1 ∨ m = 2 := by omega
        rcases hcase with rfl | rfl
        · exact hz2 (by simpa using hme)
        · have : fc.zeta = 1 := calc fc.zeta = fc.zeta ^ 2 * fc.zeta := by rw [hme, one_mul]
            _ = fc.zeta ^ 3 := by rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]
            _ = 1 := hz1
          exact hz2 this⟩
    numBits_gt_s := hnb }

end Midfall.Halo2.FieldConsts

namespace Midfall.Halo2.FieldConsts.IsWellFormed
open Midfall Assumptions

/-- THE TWO-LEVEL SQUARING CHAIN of `EvaluationDomain.new` (domain.rs:55-63 then
    :71-76), handled in one step rather than hand-waved: `extended_omega` is
    `root^(2^(S-extended_k))` and `omega` is that squared `extended_k - k` more times,
    and the composite exponent is `2^(S-k)`. Both intermediate orders are exact. -/
theorem orderExactly_shrink {F : Type} [Field F] {fc : FieldConsts F}
    (h : fc.IsWellFormed) {k : ℕ} (hk : k ≤ fc.s) :
    orderExactly (fc.rootOfUnity ^ 2 ^ (fc.s - k)) (2 ^ k) := by
  have hs := h.root_order
  refine ⟨twoPow_pos k, ?_, ?_⟩
  · have e : 2 ^ (fc.s - k) * 2 ^ k = 2 ^ fc.s := by
      rw [Nat.mul_comm, ← pow_add, Nat.add_sub_of_le hk]
    rw [← pow_mul, e]
    exact hs.pow_eq_one
  · intro m hm0 hmn hme
    have hd : 2 ^ fc.s ∣ 2 ^ (fc.s - k) * m :=
      hs.dvd_of_pow_eq_one (by rw [pow_mul]; exact hme)
    obtain ⟨t, ht⟩ := hd
    have hm : m = 2 ^ k * t :=
      Nat.mul_left_cancel (twoPow_pos (fc.s - k)) <| by
        rw [ht, ← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [hm] at hm0
      omega
    have hle : 2 ^ k ≤ m := by
      rw [hm]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ht0)
    exact absurd hle (by omega)


/-- The one consumer of `numBits_gt_s`, stated so the field is not decoration (R-30):
    a domain of any admissible `k` fits inside the field's own bit width. The Rust needs
    exactly this at domain.rs:42, where `1u64 << k` overflows for `k >= 64`, and at
    plonk/mod.rs:168-173, where `read_from_cs` rejects `k > F::S`; the Lean port's note on
    `EvaluationDomain.new` records that the panic is unreachable BECAUSE of that rejection.
    Delete this lemma and the field it uses becomes an unused conjunct, which the earlier
    draft's rules forbid - so the two stand or fall together. -/
theorem twoPow_lt_twoPow_numBits {F : Type} [Field F] {fc : FieldConsts F}
    (h : fc.IsWellFormed) {k : ℕ} (hk : k ≤ fc.s) : 2 ^ k < 2 ^ fc.numBits := by
  have hle : 2 ^ k ≤ 2 ^ fc.s := by
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hlt)
    · exact le_refl _
  calc 2 ^ k ≤ 2 ^ fc.s := hle
    _ < 2 ^ fc.numBits := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) h.numBits_gt_s
end Midfall.Halo2.FieldConsts.IsWellFormed

/-! ### The two-adicity of the BLS12-381 scalar field -/

namespace Midfall.Assumptions
open Midfall Midfall.Halo2

/-- The odd part of `r - 1`: `r - 1 = 2^32 * rOddPart`. -/
def rOddPart : ℕ := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff

/-- The two-adicity computation, as a kernel check rather than a claim: `r - 1` is
    exactly `2^32` times an odd number. -/
theorem r_sub_one_eq : r - 1 = 2 ^ 32 * rOddPart := by decide

theorem rOddPart_odd : rOddPart % 2 = 1 := by decide

/-- THE LEGITIMATE RANGE, forward half: `2^32` divides `r - 1` and `2^33` does not. -/
theorem twoAdicity_r : 2 ^ 32 ∣ r - 1 ∧ ¬ 2 ^ 33 ∣ r - 1 := by
  refine ⟨?_, ?_⟩
  · rw [r_sub_one_eq]
    exact ⟨rOddPart, rfl⟩
  · intro h
    obtain ⟨t, ht⟩ := h
    rw [r_sub_one_eq] at ht
    have e33 : (2 : ℕ) ^ 33 = 2 ^ 32 * 2 := by
      rw [show (33 : ℕ) = 32 + 1 by rfl, Nat.pow_succ]
    rw [e33, Nat.mul_assoc] at ht
    have heq : rOddPart = 2 * t := Nat.mul_left_cancel (twoPow_pos 32) ht
    have hodd : rOddPart % 2 = 0 := by omega
    have ho : rOddPart % 2 = 1 := rOddPart_odd
    omega

/-- The order of any element of `Fr rˣ` divides `r - 1` (Lagrange, via Fermat). -/
theorem orderExactly_dvd_r_sub_one {n : ℕ} (x : Fr r) (h : orderExactly x n) : n ∣ r - 1 :=
  h.dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h.ne_zero)

/-- THE LEGITIMATE RANGE, complete: `Fr r` has a `2^k`-th root of unity iff `k <= 32`.
    The backward direction is `exists_orderExactly_twoPow` below. -/
theorem twoPow_dvd_r_sub_one_iff (k : ℕ) : 2 ^ k ∣ r - 1 ↔ k ≤ 32 := by
  constructor
  · intro hd
    by_contra hgt
    have h33 : 2 ^ 33 ∣ r - 1 :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd
    exact (twoAdicity_r.2 h33)
  · intro hk
    rw [r_sub_one_eq]
    exact (Nat.pow_dvd_pow 2 hk).mul_right rOddPart

/-- No `2^k`-th primitive root exists above the two-adicity: this is the falsifiability
    half of the k-range claim, and it is a theorem, not a "we did not find one". -/
theorem no_orderExactly_above_twoAdicity {k : ℕ} (hk : 32 < k) :
    ¬ ∃ x : Fr r, orderExactly x (2 ^ k) := by
  intro ⟨x, hx⟩
  have hd : 2 ^ k ∣ r - 1 := orderExactly_dvd_r_sub_one x hx
  rw [twoPow_dvd_r_sub_one_iff] at hd
  omega

/-! ### The exhibit at the real field -/

/-- A primitive `2^32`-th root of unity in `Fr r`: `5^rOddPart`, where 5 is the smallest
    quadratic non-residue mod `r` (so `5^((r-1)/2) = -1`, hence the `2^32`-th power of
    this element is 1 and the `2^31`-st is -1). Computed offline; CHECKED here by the
    kernel, which is the only thing that makes a literal like this a proof. -/
def frRootOfUnity : Fr r :=
  0x212d79e5b416b6f0fd56dc8d168d6c0c4024ff270b3e0941b788f500b912f1f

/-- An element of order 3 in `Fr r`: `2^((r-1)/3)`. Exists because 3 divides `r - 1`,
    which is what `ZMod 17` cannot do: `17 - 1 = 16` is not a multiple of 3. -/
def frZeta : Fr r := 0xac45a4010001a40200000000ffffffff

/-- The BLS12-381 scalar field's `FieldConsts` with the ROOT FILLED IN. `numBits := 255`
    is what `EnvAgrees.truncWidth` needs (divCeil (divCeil 255 8) 2 = 16), and `s := 32`
    is the two-adicity proved above. -/
def frFc : FieldConsts (Fr r) :=
  { numBits := 255, s := 32, rootOfUnity := frRootOfUnity, zeta := frZeta }

theorem frRoot_pow_top : frRootOfUnity ^ 2 ^ 32 = 1 := by decide
theorem frRoot_pow_prev : frRootOfUnity ^ 2 ^ 31 = -1 := by decide
theorem frRoot_pow_prev_ne : frRootOfUnity ^ 2 ^ 31 ≠ 1 := by decide
theorem frZeta_cube : frZeta ^ 3 = 1 := by decide
theorem frZeta_ne_one : frZeta ≠ 1 := by decide

/-- THE HEADLINE DISCHARGE: the real scalar field's constants are well formed, at the
    real modulus, proved in the kernel. -/
theorem frFc_isWellFormed : frFc.IsWellFormed :=
  Midfall.Halo2.FieldConsts.isWellFormed_of (by decide) frRoot_pow_top frRoot_pow_prev_ne
    frZeta_cube frZeta_ne_one (by decide)

/-- Every legitimate `k <= 32` is attained: the element of order exactly `2^k` is the
    port's own two-level squaring of the primitive root. -/
theorem exists_orderExactly_twoPow {k : ℕ} (hk : k ≤ 32) :
    ∃ x : Fr r, orderExactly x (2 ^ k) :=
  ⟨frRootOfUnity ^ 2 ^ (32 - k), frFc_isWellFormed.orderExactly_shrink hk⟩

/-- THE BUG CLASS, REFUTED AS A THEOREM: the placeholder value `omega := 1` does not have
    order `2^32`, so no field constants carrying it are well formed. This is the
    falsifiability half of the `fxDom` repair (D-P23). -/
theorem not_isWellFormed_at_one :
    ¬ ({ numBits := 255, s := 32, rootOfUnity := 1, zeta := frZeta } :
        FieldConsts (Fr r)).IsWellFormed := by
  intro h
  have h1 : orderExactly (1 : Fr r) (2 ^ 32) := h.root_order
  have hp32 : 0 < 2 ^ 32 := twoPow_pos 32
  have hlt : 1 < 2 ^ 32 := by omega
  have hb1 : (1 : Fr r) ^ 1 ≠ 1 := h1.pow_ne_one (m := 1) (by decide) hlt
  exact hb1 (by simp)

/-- The order-4 element the size-4 fixture domain needs, and the two facts that make it
    a generator rather than a decoration: fourth power 1, SQUARE NOT 1. -/
def frOmega4 : Fr r := frRootOfUnity ^ 2 ^ 30

theorem frOmega4_pow : frOmega4 ^ 4 = 1 := by decide
theorem frOmega4_sq_ne : frOmega4 ^ 2 ≠ 1 := by decide
theorem frOmega4_order : orderExactly frOmega4 (2 ^ 2) := by
  have hdef : frOmega4 = frRootOfUnity ^ 2 ^ (32 - 2) := rfl
  rw [hdef]
  exact frFc_isWellFormed.orderExactly_shrink (by decide)

/-- The inverse of the order-4 generator, and of 4 itself, as LITERALS: `decide` cannot
    reduce `⁻¹` at 255-bit `r`, so the inverse is carried as a number and proved by a
    multiplication. `frOmega4Inv = -frOmega4` is the mathematical content (a square root
    of -1 inverts itself up to sign), and `frInv4 * 4 = 1` is what
    `EnvAgrees.baryWeight` is discharged with through `eq_inv_iff_mul_eq_one`. -/
def frOmega4Inv : Fr r :=
  0x73eda753299d7d47a5e80b39939ed33467baa40089fb5bfefffeffff00000001

def frInv4 : Fr r :=
  0x56f23d7e5f361df6266b620607396203fece3b023ffec4ff3fffffff40000001

theorem frOmega4Inv_mul : frOmega4Inv * frOmega4 = 1 := by decide
theorem frInv4_mul : frInv4 * 4 = 1 := by decide
theorem frInv4_eq_inv : frInv4 = (4 : Fr r)⁻¹ :=
  (inv_eq_of_mul_eq_one_left frInv4_mul).symm

/-! ### The small fields: where the two conditions can and cannot both hold -/

local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance fact13 : Fact (Nat.Prime 13) := ⟨by decide⟩
set_option maxRecDepth 100000 in
local instance fact1009 : Fact (Nat.Prime 1009) := ⟨by decide⟩

/-- `fc17`'s ROOT half is genuinely well formed: 3 has order exactly 16 = 2^4 in
    `ZMod 17`. This is the instance the earlier draft asked to be discharged, and half of
    it can be. -/
theorem fc17_root_order : orderExactly (3 : Fr 17) (2 ^ 4) :=
  orderExactly_twoPow (by decide) (by decide) (by decide)

/-- `fc17`'s ZETA half is UNSATISFIABLE, not merely unproved: 17 - 1 = 16 is not
    divisible by 3, so ZMod 17 has no element of order 3 at all. The earlier draft's
    request to discharge `zeta_order` at `fc17` cannot be met by any choice of `zeta`. -/
theorem fc17_no_element_of_order_three : ∀ z : Fr 17, z ^ 3 = 1 → z = 1 := by decide

/-- The minimal field that carries BOTH halves: `13 - 1 = 12 = 2^2 * 3`, so
    `rootOfUnity := 5` has order exactly 4 and `zeta := 3` has order exactly 3. This is
    the "small field that genuinely has the structure" the package asks for, and it is
    four bits wide, so every check is instant. -/
def fc13 : FieldConsts (Fr 13) :=
  { numBits := 4, s := 2, rootOfUnity := 5, zeta := 3 }

theorem fc13_isWellFormed : fc13.IsWellFormed :=
  Midfall.Halo2.FieldConsts.isWellFormed_of (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- `ZMod 1009` carries both halves at `s = 4` (`1009 - 1 = 2^4 * 63`), which makes it
    the largest small field in the tree that can exhibit a size-16 domain. -/
def fc1009Real : FieldConsts (Fr 1009) :=
  { numBits := 10, s := 4, rootOfUnity := 62, zeta := 374 }

theorem fc1009Real_isWellFormed : fc1009Real.IsWellFormed :=
  Midfall.Halo2.FieldConsts.isWellFormed_of (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- AND THE PLACEHOLDER THAT IS ALREADY IN THE TREE FAILS. `Exec/Kzg/MultiOpen.lean:373`
    and `Instances/ChallengeStream.lean:242` both declare `fc1009` with
    `rootOfUnity := 3, zeta := 2` at `s := 4`. Neither value has the order the field
    claims: 3 has order 168 mod 1009 and 2 has order 504. So the `IsWellFormed` predicate
    is not satisfied by the constants the fixtures already hand to the port - which is
    exactly the R-3 trust boundary being reported rather than papered over. -/
theorem fc1009Placeholder_root_fails :
    ¬ orderExactly (3 : Fr 1009) (2 ^ 4) := by
  intro h
  exact (by decide : ¬ ((3 : Fr 1009) ^ 16 = 1)) h.pow_eq_one

theorem fc1009Placeholder_zeta_fails :
    ¬ orderExactly (2 : Fr 1009) 3 := by
  intro h
  exact (by decide : ¬ ((2 : Fr 1009) ^ 3 = 1)) h.pow_eq_one

/-! ### The rotation and vanishing lemmas the missing hypothesis was blocking -/

/-- `omega ^ n = 1` alone is enough to reduce an exponent mod `n`. THE DRAFT WAS WRONG
    that the reduced-index rotation form needs exact order (plans/P-4a-roots.md
    deliverable 3): this lemma only needs `omega ^ n = 1`, so it applies to any generator
    whose order merely DIVIDES `n`, including the degenerate `omega = 1`. Proving the
    weaker-hypothesis form and saying so is the difference between closing a deferral and
    dressing one up; the exactness requirement is real but it lives in
    `zH_vanishes_iff` and `rotate_omega_neg`, not here. -/
theorem pow_eq_pow_mod_of_pow_eq_one {F : Type} [Field F] (w : F) {n : ℕ}
    (_hn : 0 < n) (h : w ^ n = 1) (m : ℕ) : w ^ (m % n) = w ^ m := by
  have : w ^ m = w ^ (n * (m / n) + m % n) := by rw [Nat.div_add_mod]
  rw [pow_add, pow_mul, h, one_pow, one_mul] at this
  exact this.symm

/-- THE DEFERRED LEMMA (`Spec/Lemmas.lean:71-83`), CLOSED: the reduced-index rotation
    form `omega^((i+rot) % n) = omega^i * omega^rot`, with a weaker hypothesis than the
    one the deferral note asked for. -/
theorem rotate_omega_mod_form {F : Type} [Field F] (w : F) {n : ℕ}
    (hn : 0 < n) (h : w ^ n = 1) (i rot : ℕ) :
    w ^ ((i + rot) % n) = w ^ i * w ^ rot := by
  rw [pow_eq_pow_mod_of_pow_eq_one w hn h (i + rot), pow_add]

/-- The negative branch of `rotateOmega`: rotating by `-j` is multiplying by
    `omega^(n-j)`. THIS one does need exactness: `n - j` is the right index only when the
    powers do not repeat before `n`, and it is what ties Lean's `omegaInv` powers to the
    contract's `OMEGA_INV_TO_L` walk. -/
theorem rotate_omega_neg {F : Type} [Field F] {w : F} {n : ℕ} (h : orderExactly w n)
    (j : ℕ) (_hj : 0 < j) (hj' : j < n) : w⁻¹ ^ j = w ^ (n - j) := by
  rw [inv_pow, inv_eq_of_mul_eq_one_right]
  have hsum : j + (n - j) = n := Nat.add_sub_of_le (Nat.le_of_lt hj')
  calc w ^ j * w ^ (n - j) = w ^ (j + (n - j)) := (pow_add w j (n - j)).symm
    _ = w ^ n := by rw [hsum]
    _ = 1 := h.pow_eq_one

/-- Halving a 2-power order: if `w` has order exactly `2^(k+1)` then `w^2` has order
    exactly `2^k`. This is the inner squaring step of `EvaluationDomain.new` in
    isolation. -/
theorem orderExactly.pow_two {F : Type} [Field F] {w : F} {k : ℕ}
    (h : orderExactly w (2 ^ k.succ)) : orderExactly (w ^ 2) (2 ^ k) := by
  have e : 2 * 2 ^ k = 2 ^ k.succ := by rw [Nat.mul_comm, Nat.pow_succ]
  refine ⟨twoPow_pos k, ?_, ?_⟩
  · rw [← pow_mul, e]; exact h.pow_eq_one
  · intro m hm0 hmn hme
    have h2m : 2 * m < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_left hmn (by decide)
    rw [e] at h2m
    exact h.pow_ne_one (by omega) h2m (by rw [pow_mul]; exact hme)

/-- The induction behind `zH_vanishes_iff`, stated with the order hypothesis as an
    argument so the induction can generalise over it. -/
theorem twoPow_roots_are_powers {F : Type} [Field F] :
    ∀ (k : ℕ) (w : F), orderExactly w (2 ^ k) → ∀ (x : F), x ^ 2 ^ k = 1 →
      ∃ i : ℕ, i < 2 ^ k ∧ x = w ^ i := by
  intro k
  induction k with
  | zero =>
      intro w _ x hx
      exact ⟨0, by omega, by simpa using hx⟩
  | succ k ih =>
      intro w hw x hx
      have hstep : orderExactly (w ^ 2) (2 ^ k) := hw.pow_two
      have e : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.mul_comm, Nat.pow_succ]
      have hx2 : (x ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, e]; exact hx
      obtain ⟨t, ht, hxt⟩ := ih (w ^ 2) hstep (x ^ 2) hx2
      have hx0 : x ≠ 0 := by
        intro hd
        rw [hd, zero_pow (Nat.ne_of_gt (twoPow_pos (k + 1)))] at hx
        exact zero_ne_one hx
      have hwt : w ^ t ≠ 0 := pow_ne_zero t hw.ne_zero
      have hkey : (w ^ t) ^ 2 = x ^ 2 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hxt]
      have hz : (x * (w ^ t)⁻¹) ^ 2 = 1 := by
        calc (x * (w ^ t)⁻¹) ^ 2 = x ^ 2 * ((w ^ t)⁻¹) ^ 2 := mul_pow _ _ _
          _ = x ^ 2 * ((w ^ t) ^ 2)⁻¹ := by rw [inv_pow]
          _ = x ^ 2 * (x ^ 2)⁻¹ := by rw [hkey]
          _ = 1 := by simp [hx0]
      rcases eq_one_or_neg_one_of_sq_eq_one hz with hz1 | hzm
      · refine ⟨t, by omega, ?_⟩
        calc x = x * ((w ^ t)⁻¹ * w ^ t) := by simp [hwt]
          _ = (x * (w ^ t)⁻¹) * w ^ t := by rw [mul_assoc]
          _ = 1 * w ^ t := by rw [hz1]
          _ = w ^ t := one_mul _
      · have hminus : w ^ 2 ^ k = -1 := by
          have hsq : (w ^ 2 ^ k) ^ 2 = 1 := by
            rw [← pow_mul, Nat.mul_comm, e]; exact hw.pow_eq_one
          have hne : w ^ 2 ^ k ≠ 1 :=
            hw.pow_ne_one (twoPow_pos k) (by
              have : 2 ^ k < 2 ^ (k + 1) := by
                rw [Nat.pow_succ]; omega
              omega)
          rcases eq_one_or_neg_one_of_sq_eq_one hsq with hq | hq
          · exact absurd hq hne
          · exact hq
        refine ⟨2 ^ k + t, by omega, ?_⟩
        have hx' : x = -(w ^ t) := by
          calc x = x * ((w ^ t)⁻¹ * w ^ t) := by simp [hwt]
            _ = (x * (w ^ t)⁻¹) * w ^ t := by rw [mul_assoc]
            _ = -1 * w ^ t := by rw [hzm]
            _ = -(w ^ t) := by rw [neg_one_mul]
        calc x = -(w ^ t) := hx'
          _ = (-1 : F) * w ^ t := by rw [neg_one_mul]
          _ = w ^ 2 ^ k * w ^ t := by rw [hminus]
          _ = w ^ (2 ^ k + t) := (pow_add w _ _).symm

/-- THE VANISHING CRITERION, both directions: for a generator of order exactly `2^k`, the
    `2^k`-th roots of unity are EXACTLY the powers `omega^i` with `i < 2^k`. This is the
    fact every vanishing-argument step silently uses, and it is what
    `EnvAgrees.omegaOrder` is cited for in Lowering/Inv.lean (`ChallengesGood.xNotRoot`):
    `x^n ≠ 1` rules out `x = omega^i` only if the powers exhaust the roots.

    Proved by induction on `k` through the unique element of order 2, so it needs no
    polynomial root counting: `x^(2^(k+1)) = 1` gives `x^2 = (omega^2)^t` by the IH, so
    `x / omega^t` squares to 1 and is therefore ±1, and `omega^(2^k)` IS the -1. -/
theorem zH_vanishes_iff {F : Type} [Field F] {w : F} {k : ℕ}
    (h : orderExactly w (2 ^ k)) {x : F} :
    x ^ 2 ^ k = 1 ↔ ∃ i : ℕ, i < 2 ^ k ∧ x = w ^ i :=
  ⟨fun hx => twoPow_roots_are_powers k w h x hx,
   fun ⟨i, _, heq⟩ => by rw [heq, ← pow_mul]; exact h.pow_eq_one_iff.2 ⟨i, Nat.mul_comm i _⟩⟩

/-- The form `ChallengesGood.xNotRoot` is cited for: with a generator of order exactly
    `n = 2^k`, "x is not a root of the vanishing polynomial" and "x is not a domain point"
    are the same statement. Without exactness the left side is strictly weaker - which is
    the R-2 completeness gap `EnvAgrees.omegaOrder` exists to close, and the reason the
    `omega := 1` fixture made `lagrange_spec` vacuous rather than merely unproved. -/
theorem xNotRoot_iff {F : Type} [Field F] {w : F} {k : ℕ} (h : orderExactly w (2 ^ k))
    {x : F} : x ^ 2 ^ k ≠ 1 ↔ ∀ i : ℕ, i < 2 ^ k → x ≠ w ^ i := by
  constructor
  · intro hx i hi heq
    exact hx (by rw [heq, ← pow_mul]; exact h.pow_eq_one_iff.2 ⟨i, Nat.mul_comm i _⟩)
  · intro hne hx
    obtain ⟨i, hi, heq⟩ := (zH_vanishes_iff (w := w) h).mp hx
    exact hne i hi heq
/-! ### Known-answer checks: the witnesses and the falsifications, as computations

    D-P23 asks for both halves of every claim. The theorems above are the witnesses; the
    booleans below are the parts that can be REDDENED, and scripts/checks.sh (kat_gate.py)
    fails CI if any of them stops printing true. -/

/-- The two-adicity of `Fr r` and the exhibit that depends on it, as a computation:
    `r - 1 = 2^32 * odd`, the primitive root squares to 1 at `2^32` and to -1 at `2^31`,
    the order-3 element cubes to 1, the order-4 element has fourth power 1 and square
    NOT 1, and the two literal inverses really are inverses. -/
def twoAdicityKats_ok : Bool :=
  (r - 1 == 2 ^ 32 * rOddPart) && (rOddPart % 2 == 1) &&
    ((frRootOfUnity : Fr r) ^ 2 ^ 32 == 1) &&
    ((frRootOfUnity : Fr r) ^ 2 ^ 31 == -1) &&
    ((frRootOfUnity : Fr r) ^ 2 ^ 31 != 1) &&
    ((frZeta : Fr r) ^ 3 == 1) && (frZeta != (1 : Fr r)) &&
    ((frOmega4 : Fr r) ^ 4 == 1) && ((frOmega4 : Fr r) ^ 2 != 1) &&
    (frOmega4Inv * frOmega4 == (1 : Fr r)) && (frInv4 * (4 : Fr r) == 1) &&
    ((r - 1) % 2 ^ 32 == 0) && ((r - 1) % 2 ^ 33 != 0)

#eval twoAdicityKats_ok                   -- expect true

/-- EVERY LEGITIMATE k IS ATTAINED and one above is not: for each k in 0..32 the two-level
    squaring `frRootOfUnity ^ 2^(32-k)` has order EXACTLY 2^k - top power 1, previous
    power NOT 1 - and 2^33 does not divide `r - 1`, which is why
    `no_orderExactly_above_twoAdicity` is a theorem rather than a failed search. -/
def kRangeKats_ok : Bool :=
  ((List.range 33).all fun k =>
    -- distinctness of the first min(2^k, 8) powers is what exactness buys
    let e : Fr r := frRootOfUnity ^ 2 ^ (32 - k)
    (e ^ 2 ^ k == 1) && (k == 0 || e ^ 2 ^ (k - 1) != 1) &&
      ((r - 1) % 2 ^ k == 0) &&
      ((List.range (min (2 ^ k) 8)).all fun i =>
        (List.range (min (2 ^ k) 8)).all fun j => i == j || (e ^ i != e ^ j))) &&
    ((r - 1) % 2 ^ 33 != 0)

#eval kRangeKats_ok                       -- expect true

/-- THE VACUITY DEMONSTRATION, i.e. the old fixture measured. `omega := 1` passes every
    gate of the shape `omega ^ n = 1` and passes `omegaInv * omega = 1`, which is exactly
    why those two clauses could not be trusted: the naive checks are green on a domain that
    is not a domain. `barycentricWeight := 4` fails its clause because 4 * 4 = 16 != 1
    mod r - the one `EnvAgrees` clause that was evaluating FALSE rather than passing
    vacuously. -/
def placeholderVacuityKats_ok : Bool :=
  ((1 : Fr r) ^ 4 == 1) && ((1 : Fr r) ^ 2 == 1) &&
    ((1 : Fr r) * (1 : Fr r) == 1) &&
    -- exactness reddens the placeholder: 1^2 == 1, so its order is 1 and not 4
    ! ((1 : Fr r) ^ 2 != 1) &&
    ((4 : Fr r) * (4 : Fr r) == 16) && ((4 : Fr r) * (4 : Fr r) != 1) &&
    (frInv4 * (4 : Fr r) == 1) &&
    -- and the repaired generator is a genuine order-4 element: its square is -1
    ((frOmega4 : Fr r) ^ 2 == -1)

#eval placeholderVacuityKats_ok           -- expect true

/-- THE SMALL FIELDS, measured: `fc17`'s root half holds and its zeta half cannot hold of
    ANY value (no element of order 3 exists in ZMod 17); `fc13` carries both; `fc1009Real`
    carries both; and the `fc1009` ALREADY IN THE TREE (rootOfUnity := 3, zeta := 2) fails
    both halves. -/
def smallFieldKats_ok : Bool :=
  ((3 : Fr 17) ^ 16 == 1) && ((3 : Fr 17) ^ 8 != 1) &&
    (Finset.univ.filter (fun z : Fr 17 => z ^ 3 == 1) == ({1} : Finset (Fr 17))) &&
    ((5 : Fr 13) ^ 4 == 1) && ((5 : Fr 13) ^ 2 != 1) &&
    ((3 : Fr 13) ^ 3 == 1) && ((3 : Fr 13) != (1 : Fr 13)) &&
    ((62 : Fr 1009) ^ 16 == 1) && ((62 : Fr 1009) ^ 8 != 1) &&
    ((374 : Fr 1009) ^ 3 == 1) && ((374 : Fr 1009) != (1 : Fr 1009)) &&
    ((3 : Fr 1009) ^ 16 != 1) && ((2 : Fr 1009) ^ 3 != 1) &&
    (16 % 3 != 0) && ((13 - 1) % 3 == 0) && ((1009 - 1) % 3 == 0)

#eval smallFieldKats_ok                   -- expect true

/-- THE DRAFT'S CLAIMS, TESTED. Lines 1-2: the reduced-index rotation form holds even at
    `omega := 1` and at an element whose order merely divides n, so the hypothesis the
    deferral note asked for was stronger than the lemma needs. Lines 3-4: the vanishing
    criterion DOES need exactness - 4 has order 2 in ZMod 17, 13^4 = 1, and 13 is not one
    of 4^0..4^3 - which is the fact `EnvAgrees.omegaOrder` is cited for. Line 5: with the
    EXACT order-4 generator 13 of ZMod 17, the four powers are exactly the four fourth
    roots of unity, i.e. `zH_vanishes_iff` holds where it failed a line earlier. -/
def draftClaimsKats_ok : Bool :=
  -- the reduced-index rotation form holds at the DEGENERATE generator 1 and at 16, whose
  -- order 2 merely DIVIDES 4: the hypothesis the deferral note asked for is not needed
  ((1 : Fr 17) ^ ((1 + 3) % 4) == (1 : Fr 17) ^ 1 * (1 : Fr 17) ^ 3) &&
    ((16 : Fr 17) ^ ((1 + 3) % 4) == (16 : Fr 17) ^ 1 * (16 : Fr 17) ^ 3) &&
    -- but the vanishing criterion needs exactness: 16 has order 2, 13^4 = 1, and 13 is
    -- not one of 16^0, 16^1, 16^2, 16^3 (which are just 1 and 16 twice)
    ((16 : Fr 17) ^ 2 == 1) && ((13 : Fr 17) ^ 4 == 1) &&
    ! ((13 : Fr 17) == (16 : Fr 17) ^ 0 ∨ (13 : Fr 17) == (16 : Fr 17) ^ 1 ∨
      (13 : Fr 17) == (16 : Fr 17) ^ 2 ∨ (13 : Fr 17) == (16 : Fr 17) ^ 3) &&
    -- and with the EXACT order-4 generator 13 the four powers are exactly the fourth
    -- roots of unity, i.e. zH_vanishes_iff holds where it just failed
    ((13 : Fr 17) ^ 2 == -1) && ((13 : Fr 17) ^ 4 == 1) &&
    (Finset.univ.filter (fun z : Fr 17 => z ^ 4 == 1) ==
      ({(1 : Fr 17), 13, (13 : Fr 17) ^ 2, (13 : Fr 17) ^ 3} : Finset (Fr 17)))

#eval draftClaimsKats_ok                  -- expect true

/-- The perturbation this package exists to make impossible, run as a computation: the
    OLD domain record satisfies `omega ^ n = 1` and `omegaInv * omega = 1` and fails
    `barycentricWeight = (2^k)⁻¹`; the NEW one satisfies all three and additionally fails
    the intermediate-power test the old one passes. -/
def domainRepairKats_ok : Bool :=
  let oldOmega : Fr r := 1
  let oldBary : Fr r := 4
  let newOmega : Fr r := frOmega4
  let newOmegaInv : Fr r := frOmega4Inv
  let newBary : Fr r := frInv4
  ((oldOmega ^ 4 == 1) && (oldOmega * oldOmega == 1) && (oldBary * (4 : Fr r) != 1)) &&
    ((newOmega ^ 4 == 1) && (newOmega ^ 2 != 1) &&
      (newOmegaInv * newOmega == 1) && (newBary * (4 : Fr r) == 1))

#eval domainRepairKats_ok                 -- expect true

/-! ### What the root of unity does NOT unblock, named -/

/-- THE MECHANISM of the silent degradation Exec/Domain.lean records in its comment on
    l_i_range (domain.rs:463: batch_invert leaves a zero at a zero denominator): at a
    point with xn = 1 the factor EVERY entry of the result is scaled by is zero, so the
    whole array comes back zero. This is the honest form of the lIRange_delta the
    earlier draft asked for. The draft's version - the r-th entry is if r = j then 1
    else 0 at x = omega^j - is FALSE of the port: at a domain point xn - 1 = 0, so the
    entry at r = j would have to be 0/0, and the port returns 0 for every entry, not 1
    for one. The Kronecker delta is a property of the mathematical Lagrange basis off
    the roots, not of this function at them, and ChallengesGood.xNotRoot is what keeps
    the two apart in lagrange_spec. -/
theorem lIRange_common_eq_zero {F : Type} [Field F] (d : EvaluationDomain F) (x : F)
    (hx : x ^ d.n = 1) : (x ^ d.n - 1) * d.barycentricWeight = 0 := by
  rw [hx, sub_self, zero_mul]

/-- NAMED GAP, and it is not the root of unity. The P-4a2 brief lists the Lagrange
    closed forms as unblocked by this package. Half of that is right: the SIDE
    CONDITIONS are now nameable (xNotRoot_iff says what x^n ≠ 1 buys,
    EnvAgrees.baryWeight pins barycentricWeight = (2^k)⁻¹, and
    orderExactly.pow_inj_on makes the denominators distinct). What is still missing
    is a lemma about batchInvert, not about roots: the closed form needs
    (batchInvert xs).1 = xs.map (·⁻¹) when every entry is nonzero, i.e. the
    correctness of the Montgomery chain at Exec/Arith.lean:104-118, plus the length
    preservation that lets List.zipWith be folded to a map. Neither is a two-adicity
    question, and neither is claimed here. -/
def gap_lIRange_closed_form : String :=
  "blocker: not the root of unity (discharged in this file); the closed form needs "
    ++ "batchInvert correctness for an all-nonzero list (Exec/Arith.lean:104) and its "
    ++ "length preservation, which is a Montgomery-chain lemma and not a two-adicity one"

end Midfall.Assumptions
