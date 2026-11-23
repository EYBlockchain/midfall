import Midfall.LoweringV3.EndToEndAlgebra
open Midfall Midfall.Halo2
namespace Midfall.LoweringV3

theorem countP_getElem? (l : List Nat) (a : Nat) :
    (List.range l.length).countP (fun i => l[i]? == some a) = l.count a := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
        Function.comp_def]
      simp only [Nat.succ_eq_add_one, List.getElem?_cons_zero, List.getElem?_cons_succ]
      rw [ih, List.count_cons]
      simp only [Option.some.injEq, beq_iff_eq]

theorem sum_map_ite_one {α : Type} (l : List α) (p : α → Bool) :
    (l.map (fun x => if p x then 1 else 0)).sum = l.countP p := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, List.sum_cons, List.countP_cons, ih]; omega

theorem sum_range_count_eq_length (l : List Nat) (m : Nat) (h : ∀ x ∈ l, x < m) :
    ((List.range m).map (fun ph => l.count ph)).sum = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : a < m := h a (by simp)
      have has : ∀ x ∈ as, x < m := fun x hx => h x (by simp [hx])
      have hstep : (List.map (fun ph => (a :: as).count ph) (List.range m)).sum
          = (List.map (fun ph => as.count ph) (List.range m)).sum
            + (List.map (fun ph => if (a == ph) then 1 else 0) (List.range m)).sum := by
        rw [← List.sum_map_add]
        apply congrArg List.sum
        apply List.map_congr_left
        intro ph _
        rw [List.count_cons]
      rw [hstep, ih has]
      have hind : (List.map (fun ph => if (a == ph) then 1 else 0)
          (List.range m)).sum = 1 := by
        rw [sum_map_ite_one]
        have hc : (List.range m).count a = 1 := by
          rw [List.count_range]; simp [ha]
        rw [← hc, List.count_eq_countP]
        apply List.countP_congr
        intro x _
        rw [beq_iff_eq, beq_iff_eq, eq_comm]
      rw [hind]
      simp
end Midfall.LoweringV3
