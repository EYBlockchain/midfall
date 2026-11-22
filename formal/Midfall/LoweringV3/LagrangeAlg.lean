-- |
-- Midfall.LoweringV3.LagrangeAlg
--
-- RENDER-FREE ALGEBRA HELPERS FOR T3.9.g ('lag_agrees'): the binary exponentiation
-- `powVartime x e = x ^ e`, and the entrywise specification of the Lean `batchInvert`
-- used by `EvaluationDomain.lIRange`.  No Yul, no render, no fixture.
--
-- AXIOMS. Standard three or fewer; no 'sorryAx', no 'native_decide'.
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Verifier
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

set_option autoImplicit false

namespace Midfall.LoweringV3.LagrangeAlg

open Midfall.Halo2

lemma toDigitsCore_zero_fuel (f : Nat) (hf : 0 < f) (acc : List Char) :
    Nat.toDigitsCore 2 f 0 acc = ['0'] ++ acc := by
  rcases f with _ | f
  · omega
  · rfl

lemma toDigitsCore_fuel_aux (n : Nat) : ∀ (f f' : Nat) (acc : List Char),
    n < f → n < f' →
    Nat.toDigitsCore 2 f n acc = Nat.toDigitsCore 2 f' n acc := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f f' acc hf hf'
    rcases n with _ | n
    · exact (toDigitsCore_zero_fuel f (by omega) acc).trans
        (toDigitsCore_zero_fuel f' (by omega) acc).symm
    · rcases f with _ | f
      · omega
      · rcases f' with _ | f'
        · omega
        · simp only [Nat.toDigitsCore]
          split
          · rfl
          · rw [ih ((n+1)/2) (by omega) f f' (((n+1)%2).digitChar :: acc) (by omega) (by omega)]

lemma toDigitsCore_append : ∀ (f n : Nat) (acc : List Char),
    Nat.toDigitsCore 2 f n acc = Nat.toDigitsCore 2 f n [] ++ acc := by
  intro f
  induction f with
  | zero => intro n acc; rfl
  | succ f ih =>
      intro n acc
      simp only [Nat.toDigitsCore]
      split
      · rfl
      · rw [ih (n/2) ((n%2).digitChar :: acc), ih (n/2) [(n%2).digitChar]]
        simp [List.append_assoc]

lemma toDigitsCore_step {n : Nat} (h : 2 ≤ n) :
    Nat.toDigitsCore 2 (n+1) n [] = Nat.toDigitsCore 2 n (n/2) [(n%2).digitChar] := by
  simp only [Nat.toDigitsCore]
  rw [ite_eq_right]
  omega

lemma toDigitsCore_digits (n : Nat) (h : 0 < n) :
    Nat.toDigitsCore 2 (n+1) n [] = (Nat.digits 2 n).reverse.map Nat.digitChar := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [show Nat.toDigitsCore 2 2 1 [] = [Nat.digitChar 1] from rfl]
      rw [Nat.digits_of_lt 2 1 (by norm_num) (by norm_num)]
      rfl
    · rw [toDigitsCore_step hge]
      have hhalf : 0 < n/2 := by omega
      have hhalf_lt : n/2 < n := by omega
      rw [toDigitsCore_append]
      rw [toDigitsCore_fuel_aux (n/2) n (n/2+1) [] (by omega) (by omega)]
      rw [ih (n/2) hhalf_lt hhalf]
      rw [Nat.digits_eq_cons_digits_div (by norm_num : 1 < 2) (by omega : n ≠ 0)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

lemma toDigits_eq_digits_of_pos (n : Nat) (h : 0 < n) :
    Nat.toDigits 2 n = (Nat.digits 2 n).reverse.map Nat.digitChar := by
  rw [show Nat.toDigits 2 n = Nat.toDigitsCore 2 (n+1) n [] from rfl]
  exact toDigitsCore_digits n h

lemma toDigits_zero : Nat.toDigits 2 0 = ['0'] := rfl

/-- The binary-digit fold (LSB first) is the power. -/
lemma foldr_digits_step {F : Type} [Field F] (x : F) :
    ∀ (L : List Nat), (∀ d ∈ L, d < 2) →
      (L.map Nat.digitChar).foldr
        (fun c acc => acc * acc * if (c == '1') = true then x else 1) 1
        = x ^ Nat.ofDigits 2 L
  | [], _ => by simp
  | d :: L, h => by
      rw [List.map_cons, List.foldr_cons]
      have hL : ∀ e ∈ L, e < 2 := by intro e he; exact h e (by simp [he])
      rw [foldr_digits_step x L hL]
      have hd : d = 0 ∨ d = 1 := by
        have := h d (by simp); omega
      rcases hd with rfl | rfl
      · have h0 : Nat.digitChar 0 = '0' := rfl
        rw [h0, Nat.ofDigits_cons]
        norm_num
        rw [← pow_two, ← pow_mul]
        congr 1
        ring
      · have h1 : Nat.digitChar 1 = '1' := rfl
        rw [h1, Nat.ofDigits_cons]
        norm_num
        rw [← pow_two, ← pow_mul, ← pow_succ]
        congr 1
        ring

lemma foldl_digits_step {F : Type} [Field F] (x : F) (L : List Nat)
    (h : ∀ d ∈ L, d < 2) :
    (L.reverse.map Nat.digitChar).foldl
      (fun res c => res * res * if (c == '1') = true then x else 1) 1
      = x ^ Nat.ofDigits 2 L := by
  rw [List.map_reverse, List.foldl_reverse]
  exact foldr_digits_step x L h

theorem powVartime_eq_pow {p : ℕ} [Fact (Nat.Prime p)] (x : ZMod p) (e : Nat) :
    powVartime x e = x ^ e := by
  rw [powVartime]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [show Nat.toDigits 2 0 = ['0'] from rfl]
    simp only [pow_zero, List.foldl_cons, List.foldl_nil]
    norm_num
  · rw [toDigits_eq_digits_of_pos e he]
    have h : ∀ d ∈ Nat.digits 2 e, d < 2 := by
      intro d hd
      have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
      simpa using this
    rw [foldl_digits_step x (Nat.digits 2 e) h]
    rw [Nat.ofDigits_digits]

end Midfall.LoweringV3.LagrangeAlg

namespace Midfall.Halo2

variable {F : Type} [Field F] [DecidableEq F]

/-- Product of the non-zero entries, in order. -/
def biProd : List F → F
  | [] => 1
  | x :: xs => if x = 0 then biProd xs else x * biProd xs

/-- The forward prefix product before each entry. -/
def biPref (p : F) : List F → List F
  | [] => []
  | x :: xs => p :: biPref (if x = 0 then p else p * x) xs

/-- Entrywise inverse, zero at zero. -/
def biInv : List F → List F
  | [] => []
  | x :: xs => (if x = 0 then 0 else x⁻¹) :: biInv xs

def biFwdStep (st : F × List (F × F)) (p : F) : F × List (F × F) :=
  ((if p = 0 then st.1 else st.1 * p), st.2 ++ [(st.1, p)])

def biFwdAux : F × List (F × F) → List F → F × List (F × F)
  | init, [] => init
  | init, x :: xs => biFwdAux (biFwdStep init x) xs

lemma bi_foldl_fwdAux (init : F × List (F × F)) (xs : List F) :
    xs.foldl biFwdStep init = biFwdAux init xs := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, biFwdAux, ih]

lemma biFwdAux_spec (p : F) (tmp : List (F × F)) (xs : List F) :
    biFwdAux (p, tmp) xs = (p * biProd xs, tmp ++ (biPref p xs).zip xs) := by
  induction xs generalizing p tmp with
  | nil => simp [biFwdAux, biProd, biPref]
  | cons x xs ih =>
      have hstep : biFwdAux (p, tmp) (x :: xs) =
          biFwdAux (if x = 0 then p else p * x, tmp ++ [(p, x)]) xs := rfl
      rw [hstep, ih]
      rw [Prod.mk.injEq]
      constructor
      · by_cases hx : x = 0
        · subst hx; simp [biProd]
        · simp only [hx, if_false, biProd]
          ring
      · rw [List.append_assoc]
        by_cases hx : x = 0
        · subst hx; simp [biPref]
        simp only [hx, ite_false, biPref, List.zip_cons_cons, List.singleton_append]

def biBwdStep (q : F × F) (st : F × List F) : F × List F :=
  let pre := st.1
  let v := q.2
  let skip := v = 0
  ((if skip then pre else pre * v), (if skip then v else q.1 * pre) :: st.2)

def biBwdAux : F × List F → List (F × F) → F × List F
  | init, [] => init
  | init, q :: qs => biBwdStep q (biBwdAux init qs)

lemma bi_foldr_bwdAux (init : F × List F) (tmp : List (F × F)) :
    tmp.foldr biBwdStep init = biBwdAux init tmp := by
  induction tmp with
  | nil => rfl
  | cons q qs ih => simp only [List.foldr_cons, biBwdAux, ih]

lemma biBwdAux_spec (p pre : F) (hp : p ≠ 0) (xs out : List F)
    (hpre : pre = (p * biProd xs)⁻¹) :
    biBwdAux (pre, out) ((biPref p xs).zip xs) = (p⁻¹, biInv xs ++ out) := by
  induction xs generalizing p pre out with
  | nil =>
      simp only [biPref, List.zip_nil_left, biBwdAux, biInv, List.nil_append]
      rw [hpre]
      simp [biProd]
  | cons x xs ih =>
      by_cases hx : x = 0
      · subst hx
        have hp' : p ≠ 0 := hp
        have hpre' : pre = (p * biProd xs)⁻¹ := by
          rw [hpre]; simp [biProd]
        have h := ih p pre hp' out hpre'
        simp [biPref, biProd] at h ⊢
        simp only [biBwdAux]
        rw [h]
        simp only [biBwdStep, if_pos rfl, biInv, ite_true]
        rw [List.cons_append]
      · have hp' : p * x ≠ 0 := mul_ne_zero hp hx
        have hpre' : pre = ((p * x) * biProd xs)⁻¹ := by
          rw [hpre]; simp [biProd, hx]; ring
        have h := ih (p * x) pre hp' out hpre'
        simp only [biPref, biProd, hx, ite_false] at h ⊢
        rw [List.zip_cons_cons]
        simp only [biBwdAux]
        rw [h]
        simp only [biBwdStep, if_neg hx, biInv]
        rw [List.cons_append]
        rw [Prod.mk.injEq]
        constructor
        · field_simp
        · field_simp

/-- The Lean `batchInvert` is entrywise inversion, zero at zero. -/
theorem batchInvert_eq (xs : List F) :
    batchInvert xs.toArray = ((biInv xs).toArray, (biProd xs)⁻¹) := by
  have hfwd : xs.foldl biFwdStep (1, []) = (biProd xs, (biPref 1 xs).zip xs) := by
    rw [bi_foldl_fwdAux, biFwdAux_spec]
    simp
  have hbwd : ((biPref 1 xs).zip xs).foldr biBwdStep ((biProd xs)⁻¹, []) =
      (1, biInv xs) := by
    rw [bi_foldr_bwdAux, biBwdAux_spec 1 ((biProd xs)⁻¹) one_ne_zero xs []]
    · simp
    · simp [biProd]
  unfold batchInvert
  dsimp only
  change ((List.foldr biBwdStep
      ((List.foldl biFwdStep (1, []) xs).1⁻¹, [])
      (List.foldl biFwdStep (1, []) xs).2).2.toArray,
    (List.foldl biFwdStep (1, []) xs).1⁻¹) =
    ((biInv xs).toArray, (biProd xs)⁻¹)
  rw [hfwd]
  dsimp only
  rw [show ((biPref 1 xs).zip xs).foldr biBwdStep ((biProd xs)⁻¹, []) =
      (1, biInv xs) from hbwd]

lemma biInv_length (xs : List F) : (biInv xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [biInv, ih]

lemma biPref_length (p : F) (xs : List F) : (biPref p xs).length = xs.length := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [biPref, ih]

theorem batchInvert_fst (xs : List F) :
    (batchInvert xs.toArray).1 = (biInv xs).toArray := by
  rw [batchInvert_eq]

theorem batchInvert_snd (xs : List F) :
    (batchInvert xs.toArray).2 = (biProd xs)⁻¹ := by
  rw [batchInvert_eq]

theorem batchInvert_size (xs : List F) :
    (batchInvert xs.toArray).1.size = xs.length := by
  rw [batchInvert_fst]
  simp [biInv_length]

theorem batchInvert_toList (xs : List F) :
    (batchInvert xs.toArray).1.toList = biInv xs := by
  rw [batchInvert_fst]

lemma biInv_map {α : Type} (f : α → F) (xs : List α) :
    biInv (xs.map f) = xs.map (fun x => if f x = 0 then 0 else (f x)⁻¹) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [biInv, ih]

/-- `lIRange` entrywise, when no denominator vanishes: the batch inverse is the inverse
of each `x - ω^r`, and the rotation is applied last. -/
theorem lIRange_toList_of_ne_zero (d : EvaluationDomain F) (x xn : F) (rots : List Int)
    (h : ∀ r ∈ rots, x - d.rotateOmega 1 (Rotation.value r) ≠ 0) :
    (d.lIRange x xn rots).toList =
      rots.map (fun r => d.rotateOmega
        ((x - d.rotateOmega 1 (Rotation.value r))⁻¹ * ((xn - 1) * d.barycentricWeight))
        (Rotation.value r)) := by
  unfold EvaluationDomain.lIRange
  dsimp only
  rw [batchInvert_toList]
  have hbi : biInv (rots.map (fun r => x - d.rotateOmega 1 (Rotation.value r))) =
      rots.map (fun r => (x - d.rotateOmega 1 (Rotation.value r))⁻¹) := by
    rw [biInv_map]
    apply List.map_congr_left
    intro r hr
    rw [if_neg (h r hr)]
  rw [hbi]
  rw [List.zipWith_map_left]
  rw [List.zipWith_self]

theorem biInv_get? (xs : List F) (i : Nat) :
    (biInv xs)[i]? = (xs[i]?).map (fun x => if x = 0 then 0 else x⁻¹) := by
  induction xs generalizing i with
  | nil => simp [biInv]
  | cons x xs ih =>
      cases i with
      | zero => simp [biInv]
      | succ i => simp [biInv, ih]


lemma flatMap_pure {α β : Type} (l : List α) (f : α → β) :
    List.flatMap (fun a => pure (f a)) l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap, List.flatten_cons, List.map_cons]
      change [f a] ++ (List.map (fun a => [f a]) l).flatten = f a :: List.map f l
      rw [show (List.map (fun a => [f a]) l).flatten = List.flatMap (fun a => [f a]) l from rfl]
      have ih' : List.flatMap (fun a => [f a]) l = l.map f := ih
      rw [ih']
      rfl

/-- The three projections `lagrangeTriple` writes, over the concrete rotation list. -/
theorem lagrangeTriple_ok {p : ℕ} [Fact (Nat.Prime p)] {G : Type}
    (vk : VerifyingKey (Fr p) G) (x xn : Fr p)
    {bf : Nat} (hbf : vk.cs.blindingFactors = .ok bf) {tri : LagrangeTriple (Fr p)}
    (h : lagrangeTriple vk x xn = .ok tri) :
    let rots : List Int := List.map (fun i => -((bf + 1 : Nat) : Int) + (i : Int))
      (List.flatMap (fun a => pure ((a : Nat) : Int)) (List.range (bf + 2)))
    let E := vk.domain.lIRange x xn rots
    E.size = bf + 2 ∧ tri.lLast = E[0]! ∧
      tri.lBlind = ((E.toList.drop 1).take bf).foldl (init := 0) (· + ·) ∧
      tri.l0 = E[bf + 1]! := by
  unfold lagrangeTriple at h
  rw [hbf] at h
  dsimp only [Bind.bind, Except.bind] at h
  split at h
  · rename_i hsize
    injection h with htri
    subst htri
    dsimp only
    exact ⟨beq_iff_eq.mp hsize, rfl, rfl, rfl⟩
  · simp at h

end Midfall.Halo2
