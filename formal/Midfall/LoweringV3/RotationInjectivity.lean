-- |
-- Midfall.LoweringV3.RotationInjectivity
--
-- The field-algebra core of the D-GATE5/D-GATE6 KZG query-map datum: on the
-- rotation image `x * omega^r`, equality of points forces equality of the
-- integer rotations. `x != 0` is D-GATE5 `ChallengesGood.xNonzero`; exact order
-- of `omega` and `omegaInv * omega = 1` are `EnvAgrees.omegaOrder` /
-- `EnvAgrees.omegaInvMul`; the final `hdistinct` premise is D-GATE6
-- rotation-distinctness (equal rotations modulo `n` are equal). This file is
-- deliberately independent of the datum construction: it is the injectivity
-- fact that datum consumes.
import Midfall.LoweringV3.LagrangeAlg
import Midfall.Assumptions.TwoAdicity

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Assumptions

variable {F : Type} [Field F] [DecidableEq F]

theorem rotateOmega_eq_mul_zpow (d : EvaluationDomain F) (x : F) (z : Int)
    (hwi : d.omegaInv * d.omega = 1) (hω : d.omega ≠ 0) :
    d.rotateOmega x (Rotation.value z) = x * (d.omega ^ z) := by
  rw [rotateOmega_value]
  by_cases hz : 0 ≤ z
  · rw [if_pos hz, LagrangeAlg.powVartime_eq_pow]
    simp only [EvaluationDomain.getOmega]
    have hz' : z = (z.toNat : Int) := (Int.toNat_of_nonneg hz).symm
    conv_rhs => rw [hz']
    rw [zpow_natCast]
  · have hzneg : z < 0 := by omega
    rw [if_neg hz, LagrangeAlg.powVartime_eq_pow]
    simp only [EvaluationDomain.getOmegaInv]
    have hwinv : d.omegaInv = d.omega⁻¹ :=
      eq_inv_of_mul_eq_one_left hwi
    rw [hwinv]
    have hz' : z = -((z.natAbs : Nat) : Int) := by omega
    conv_rhs => rw [hz']
    rw [zpow_neg, zpow_natCast, inv_pow]

theorem rotateOmega_injective_on_rotations (d : EvaluationDomain F) (x : F)
    (hx : x ≠ 0) (hwi : d.omegaInv * d.omega = 1)
    (hord : Midfall.Assumptions.orderExactly d.omega d.n)
    (hdistinct : ∀ r s : Int, r ≡ s [ZMOD (d.n : Int)] → r = s)
    {r s : Int}
    (h : d.rotateOmega x (Rotation.value r) = d.rotateOmega x (Rotation.value s)) :
    r = s := by
  have hω : d.omega ≠ 0 := hord.ne_zero
  rw [rotateOmega_eq_mul_zpow d x r hwi hω,
    rotateOmega_eq_mul_zpow d x s hwi hω] at h
  have hpow : d.omega ^ r = d.omega ^ s := mul_left_cancel₀ hx h
  let u : Fˣ := Units.mk0 d.omega hω
  have hu : u ^ r = u ^ s := by
    apply Units.ext
    simpa [u] using hpow
  have hmod := (zpow_eq_zpow_iff_modEq.mp hu)
  have horder : orderOf u = d.n := by
    refine (orderOf_eq_iff hord.pos).mpr ⟨?_, ?_⟩
    · apply Units.ext
      simpa [u] using hord.pow_eq_one
    · intro m hmlt hmpos hmu
      apply hord.pow_ne_one hmpos hmlt
      have := congrArg (fun z : Fˣ => (z : F)) hmu
      simpa [u] using this
  rw [horder] at hmod
  exact hdistinct r s hmod

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem le_foldl_max_init {α : Type} [LinearOrder α] (l : List α) (init : α) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons a as ih =>
      rw [List.foldl_cons]
      exact le_trans (le_max_left init a) (ih (max init a))

theorem le_foldl_max_of_mem {α : Type} [LinearOrder α] {a : α} :
    ∀ {l : List α}, a ∈ l → ∀ init : α, a ≤ l.foldl max init := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b bs ih =>
      intro h init
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with hab | hmem
      · subst b
        exact le_trans (le_max_right init a) (le_foldl_max_init bs (max init a))
      · exact ih hmem (max init b)

/-- A rotation-image key for `Fr p`: on `x * omega^r` (with `r` in `rots`) it
    returns `r`; off the image it returns `N + val p`, with `N` above every
    `|r|`. -/
noncomputable def rotationKey (d : EvaluationDomain (Fr p)) (x : Fr p)
    (rots : List Int) (N : Int) (q : Fr p) : Int :=
  if h : ∃ r, r ∈ rots ∧ q = d.rotateOmega x (Rotation.value r) then
    Classical.choose h
  else
    N + (ZMod.val q : Int)

theorem rotationKey_image (d : EvaluationDomain (Fr p)) (x : Fr p)
    (rots : List Int) (N : Int)
    (hx : x ≠ 0) (hwi : d.omegaInv * d.omega = 1)
    (hord : Midfall.Assumptions.orderExactly d.omega d.n)
    (hdistinct : ∀ r s : Int, r ≡ s [ZMOD (d.n : Int)] → r = s)
    {r : Int} (hr : r ∈ rots) :
    rotationKey d x rots N (d.rotateOmega x (Rotation.value r)) = r := by
  unfold rotationKey
  rw [dif_pos ⟨r, hr, rfl⟩]
  have hch := Classical.choose_spec (show ∃ r', r' ∈ rots ∧
    d.rotateOmega x (Rotation.value r) = d.rotateOmega x (Rotation.value r') from ⟨r, hr, rfl⟩)
  have hcr : Classical.choose (show ∃ r', r' ∈ rots ∧
      d.rotateOmega x (Rotation.value r) = d.rotateOmega x (Rotation.value r') from
      ⟨r, hr, rfl⟩) = r := by
    exact (rotateOmega_injective_on_rotations d x hx hwi hord hdistinct hch.2).symm
  exact hcr

theorem rotationKey_not_image (d : EvaluationDomain (Fr p)) (x : Fr p)
    (rots : List Int) (N : Int) {q : Fr p}
    (hq : ¬ ∃ r, r ∈ rots ∧ q = d.rotateOmega x (Rotation.value r)) :
    rotationKey d x rots N q = N + (ZMod.val q : Int) := by
  unfold rotationKey
  rw [dif_neg hq]

theorem rotationKey_image_lt (d : EvaluationDomain (Fr p)) (x : Fr p)
    (rots : List Int) {r : Int} (hr : r ∈ rots) :
    r < ((rots.map (fun r => (r.natAbs : Int))).foldl max 0 + 1) := by
  have hle : (r.natAbs : Int) ≤
      (rots.map (fun r => (r.natAbs : Int))).foldl max 0 :=
    le_foldl_max_of_mem (a := (r.natAbs : Int))
      (l := rots.map (fun r => (r.natAbs : Int)))
      (List.mem_map.mpr ⟨r, hr, rfl⟩) 0
  have habs : r ≤ (r.natAbs : Int) := by omega
  omega

theorem rotationKey_injective [NeZero p]
    (d : EvaluationDomain (Fr p)) (x : Fr p) (rots : List Int) (N : Int)
    (hx : x ≠ 0) (hwi : d.omegaInv * d.omega = 1)
    (hord : Midfall.Assumptions.orderExactly d.omega d.n)
    (hdistinct : ∀ r s : Int, r ≡ s [ZMOD (d.n : Int)] → r = s)
    (hN : ∀ r ∈ rots, r < N) :
    Function.Injective (rotationKey d x rots N) := by
  intro a b hab
  by_cases ha : ∃ r, r ∈ rots ∧ a = d.rotateOmega x (Rotation.value r)
  · obtain ⟨ra, hra, rfl⟩ := ha
    by_cases hb : ∃ r, r ∈ rots ∧ b = d.rotateOmega x (Rotation.value r)
    · obtain ⟨rb, hrb, rfl⟩ := hb
      have hka := rotationKey_image d x rots N hx hwi hord hdistinct hra
      have hkb := rotationKey_image d x rots N hx hwi hord hdistinct hrb
      rw [hka, hkb] at hab
      rw [hab]
    · have hkb := rotationKey_not_image d x rots N hb
      have hka := rotationKey_image d x rots N hx hwi hord hdistinct hra
      rw [hka, hkb] at hab
      have hlt := hN ra hra
      have hval : 0 ≤ (ZMod.val b : Int) := by exact_mod_cast Nat.zero_le _
      omega
  · have hka := rotationKey_not_image d x rots N ha
    by_cases hb : ∃ r, r ∈ rots ∧ b = d.rotateOmega x (Rotation.value r)
    · obtain ⟨rb, hrb, rfl⟩ := hb
      have hkb := rotationKey_image d x rots N hx hwi hord hdistinct hrb
      rw [hka, hkb] at hab
      have hlt := hN rb hrb
      have hval : 0 ≤ (ZMod.val a : Int) := by exact_mod_cast Nat.zero_le _
      omega
    · have hkb := rotationKey_not_image d x rots N hb
      rw [hka, hkb] at hab
      have hv : ZMod.val a = ZMod.val b := by omega
      exact ZMod.val_injective p hv

theorem exists_pointKey [NeZero p]
    (d : EvaluationDomain (Fr p)) (x : Fr p) (rots : List Int)
    (hx : x ≠ 0) (hwi : d.omegaInv * d.omega = 1)
    (hord : Midfall.Assumptions.orderExactly d.omega d.n)
    (hdistinct : ∀ r s : Int, r ≡ s [ZMOD (d.n : Int)] → r = s) :
    ∃ fk : Fr p → Int,
      (∀ a b, (a == b) = (fk a == fk b)) ∧
      (∀ r ∈ rots, fk (d.rotateOmega x (Rotation.value r)) = r) := by
  let N : Int := ((rots.map (fun r => (r.natAbs : Int))).foldl max 0 + 1)
  have hN : ∀ r ∈ rots, r < N := by
    intro r hr
    exact rotationKey_image_lt d x rots hr
  refine ⟨rotationKey d x rots N, ?_, ?_⟩
  · intro a b
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : rotationKey d x rots N a ≠ rotationKey d x rots N b := fun h =>
        hab (rotationKey_injective d x rots N hx hwi hord hdistinct hN h)
      have ha : (a == b) = false := by simpa [beq_iff_eq] using hab
      have hb : (rotationKey d x rots N a == rotationKey d x rots N b) = false := by
        simpa [beq_iff_eq] using hne
      rw [ha, hb]
  · intro r hr
    exact rotationKey_image d x rots N hx hwi hord hdistinct hr


end Midfall.LoweringV3
