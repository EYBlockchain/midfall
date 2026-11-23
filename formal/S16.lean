import Midfall.LoweringV3.EndToEndAlgebra
open Midfall Midfall.Halo2
namespace Midfall.LoweringV3

theorem le_foldl_max_val_init (acc : Nat) (ps : List Phase) :
    acc ≤ ps.foldl (fun acc p => max acc p.val) acc := by
  induction ps generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons p rest ih =>
      exact Nat.le_trans (Nat.le_trans (le_max_left acc p.val)
        (ih (max acc p.val))) (Nat.le_refl _)

theorem le_foldl_max_val (b : Nat) (ps : List Phase) :
    ∀ x ∈ ps, x.val ≤ ps.foldl (fun acc p => max acc p.val) b := by
  induction ps generalizing b with
  | nil => intro x hx; simp at hx
  | cons p rest ih =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · show p.val ≤ (p :: rest).foldl (fun acc p => max acc p.val) b
        simp only [List.foldl_cons]
        exact Nat.le_trans (le_max_right b p.val) (le_foldl_max_val_init (max b p.val) rest)
      · exact ih (max b p.val) x hx

theorem advicePhaseCols_length_eq_count {p : ℕ} [Fact (Nat.Prime p)]
    (cs : ConstraintSystem (Fr p)) (ph : Nat) :
    (advicePhaseCols cs ph).length = (cs.adviceColumnPhaseNats.toList).count ph := by
  have hlen : (cs.adviceColumnPhaseNats.toList).length = cs.numAdviceColumns := by
    unfold ConstraintSystem.adviceColumnPhaseNats
    rw [Array.length_toList, Array.size_map]
  rw [advicePhaseCols, ← hlen, length_filterMap_ite]
  have hp : (fun i => ((cs.adviceColumnPhase[i]?.map (fun q => q.val)) == some ph))
      = (fun i => (cs.adviceColumnPhaseNats.toList)[i]? == some ph) := by
    funext i
    unfold ConstraintSystem.adviceColumnPhaseNats
    rw [Array.toList_map, List.getElem?_map, ← Array.getElem?_toList]
  rw [hp]
  exact countP_getElem? _ _

theorem adviceReadCount_eq_phaseSize {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁)
    (h : vk.cs.adviceColumnPhase.size = vk.cs.numAdviceColumns) :
    adviceReadCount vk.cs 1 = vk.cs.adviceColumnPhase.size := by
  have hbound : ∀ x ∈ vk.cs.adviceColumnPhaseNats.toList,
      x < vk.cs.adviceColumnPhase.foldl (fun acc p => max acc p.val) 0 + 1 := by
    intro x hx
    unfold ConstraintSystem.adviceColumnPhaseNats at hx
    rw [Array.toList_map] at hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rw [Array.foldl_toList]
    have := le_foldl_max_val 0 vk.cs.adviceColumnPhase.toList q hq
    omega
  unfold adviceReadCount ConstraintSystem.phases
  simp only [Nat.one_mul]
  rw [List.map_map]
  have hfun : (fun i => (advicePhaseCols vk.cs ({ val := i } : Phase).val).length)
      = (fun i => (vk.cs.adviceColumnPhaseNats.toList).count i) := by
    funext i
    exact advicePhaseCols_length_eq_count vk.cs i
  rw [hfun, sum_range_count_eq_length _ _ hbound]
  have hlen : (vk.cs.adviceColumnPhaseNats.toList).length = vk.cs.numAdviceColumns := by
    unfold ConstraintSystem.adviceColumnPhaseNats
    rw [Array.length_toList, Array.size_map]
  rw [hlen, h]

end Midfall.LoweringV3
