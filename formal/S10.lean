import Midfall.LoweringV3.EndToEnd
#check @List.countP_comm
#check @List.countP_comm'
#check @List.sum_map_add
#check @List.sum_map_ite
#check @List.sum_map_sub
#check @List.sum_cons
#check @List.sum_map_mul_left
#check @List.count_cons
#check @List.countP_eq_length_filter
#check @List.countP_true
#check @List.sum_pos
#check @List.sum_eq_zero_iff
open Midfall Midfall.Halo2
example (l : List Nat) (m : Nat) (h : ∀ x ∈ l, x < m) :
    ((List.range m).map (fun ph => l.count ph)).sum = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
        have ha : a < m := h a (by simp)
        have has : ∀ x ∈ as, x < m := fun x hx => h x (by simp [hx])
        rw [ih has]
        -- goal: sum of map (count over cons) = as.length + 1
        have hc : ∀ ph, (a :: as).count ph = as.count ph + (if ph = a then 1 else 0) := by
          intro ph
          rw [List.count_eq_countP, List.count_eq_countP, List.countP_cons]
          simp only [beq_iff_eq]
          congr 1
          by_cases hp : ph = a <;> simp [hp]
        sorry
