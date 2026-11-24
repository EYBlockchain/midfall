import Batteries.Data.String.Lemmas
import Mathlib.Tactic
set_option autoImplicit false
open String

namespace Midfall.Generator.SplitOnLines

/-! ## `String.splitOn` at the newline separator

  Lean's legacy `String.splitOn` is an opaque byte-level scanner with no inverse
  lemma in the toolchain.  The statements below are the exact facts the constant
  template needs: the inverse on a single newline separator, and the round trip
  of `String.intercalate "\n"` with `String.splitOn "\n"`.  They are proved by
  comparing the legacy scanner with `String.splitToList` (which does have a
  `Batteries` characterization) and then using the verified `List.splitOn`
  library. -/

theorem newline_utf8Size : Char.utf8Size '\n' = 1 := by
  decide

theorem get_newline_zero : String.Pos.Raw.get "\n" 0 = '\n' := by
  decide

theorem next_newline_zero : String.Pos.Raw.next "\n" 0 = (⟨1⟩ : String.Pos.Raw) := by
  decide

theorem atEnd_newline_one : String.Pos.Raw.atEnd "\n" (⟨1⟩ : String.Pos.Raw) = true := by
  decide

theorem unoffset_next_eq (l m : List Char) :
    (⟨String.utf8Len (l ++ m) + Char.utf8Size '\n'⟩ : String.Pos.Raw).unoffsetBy
      (⟨1⟩ : String.Pos.Raw) = ⟨String.utf8Len l + String.utf8Len m⟩ := by
  apply String.Pos.Raw.ext
  rw [newline_utf8Size]
  simp [String.utf8Len_append]

/-- The state-general simulation lemma: `splitOnAux` with separator `"\n"` starting at a
    character boundary with an empty pattern prefix agrees with `splitAux` and the
    list-level `splitOnP` specification. -/
theorem splitOnAux_newline_ofList (l m r : List Char) (acc : List String) :
    String.splitOnAux (String.ofList (l ++ m ++ r)) "\n"
      ⟨String.utf8Len l⟩ ⟨String.utf8Len l + String.utf8Len m⟩ 0 acc =
    acc.reverse ++ (List.splitOnPPrepend (· == '\n') r m.reverse).map String.ofList := by
  cases r with
  | nil =>
      rw [String.splitOnAux.eq_1]
      simp only [List.append_nil, String.atEnd_iff, String.rawEndPos_ofList,
        String.utf8Len_append, String.Pos.Raw.le_iff, Nat.le_refl, ite_true,
        List.splitOnPPrepend_nil, List.map_cons, List.map_nil]
      rw [show String.Pos.Raw.extract (String.ofList (l ++ m)) ⟨String.utf8Len l⟩
          ⟨String.utf8Len l + String.utf8Len m⟩ = String.ofList m by
        simpa using extract_of_valid l m []]
      simp [List.reverse_reverse]
  | cons c r =>
      rw [String.splitOnAux.eq_1]
      have hatEnd : String.Pos.Raw.atEnd (String.ofList (l ++ m ++ (c :: r)))
          ⟨String.utf8Len l + String.utf8Len m⟩ = false := by
        have h : ¬ (String.rawEndPos (String.ofList (l ++ m ++ (c :: r))) ≤
            (⟨String.utf8Len l + String.utf8Len m⟩ : String.Pos.Raw)) := by
          simp only [String.rawEndPos_ofList, String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_mk,
            String.utf8Len_append]
          have hpos : 0 < String.utf8Len (c :: r) := by
            rw [String.utf8Len_cons]
            exact Nat.lt_of_lt_of_le (Char.utf8Size_pos c) (Nat.le_add_left _ _)
          omega
        cases hb : String.Pos.Raw.atEnd (String.ofList (l ++ m ++ (c :: r)))
            ⟨String.utf8Len l + String.utf8Len m⟩ with
        | false => rfl
        | true => exact absurd ((String.atEnd_iff _ _).mp hb) h
      rw [hatEnd]
      simp only [Bool.false_eq_true, ite_false]
      have hget : String.Pos.Raw.get (String.ofList (l ++ m ++ (c :: r)))
          ⟨String.utf8Len l + String.utf8Len m⟩ = c := by
        rw [show String.utf8Len l + String.utf8Len m = String.utf8Len (l ++ m) by
          rw [String.utf8Len_append]]
        rw [get_of_valid]
        rfl
      have hnext : String.Pos.Raw.next (String.ofList (l ++ m ++ (c :: r)))
          ⟨String.utf8Len l + String.utf8Len m⟩ =
          ⟨String.utf8Len (l ++ m) + c.utf8Size⟩ := by
        rw [show String.utf8Len l + String.utf8Len m = String.utf8Len (l ++ m) by
          rw [String.utf8Len_append]]
        rw [next_of_valid]
      rw [hget, get_newline_zero]
      by_cases hc : (c == '\n') = true
      · rw [ite_eq_left hc]
        have hc' : c = '\n' := by simpa using hc
        subst c
        rw [hnext, next_newline_zero, atEnd_newline_one]
        simp only [ite_true]
        rw [unoffset_next_eq]
        rw [extract_of_valid]
        have hsplit : (fun x : Char => x == '\n') '\n' = true := by rfl
        rw [show List.splitOnPPrepend (fun x : Char => x == '\n') ('\n' :: r) m.reverse =
            (m.reverse).reverse :: List.splitOnP (fun x : Char => x == '\n') r from
          List.splitOnPPrepend_cons_pos hsplit]
        simp only [List.reverse_reverse]
        simpa [List.append_assoc, List.reverse_cons,
          String.utf8Len_append, newline_utf8Size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using splitOnAux_newline_ofList (l ++ m ++ ['\n']) [] r ((String.ofList m) :: acc)
      · rw [ite_eq_right hc]
        rw [String.Pos.Raw.unoffsetBy_zero]
        rw [hnext]
        rw [show String.utf8Len (l ++ m) + c.utf8Size =
            String.utf8Len l + String.utf8Len (m ++ [c]) by
          simp [String.utf8Len_append, Nat.add_assoc]]
        have hcf : (fun x : Char => x == '\n') c = false := by
          simpa using hc
        rw [show List.splitOnPPrepend (fun x : Char => x == '\n') (c :: r) m.reverse =
            List.splitOnPPrepend (fun x : Char => x == '\n') r (c :: m.reverse) from
          List.splitOnPPrepend_cons_neg hcf]
        simpa [List.append_assoc, List.reverse_append, List.reverse_singleton,
          String.utf8Len_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using splitOnAux_newline_ofList l (m ++ [c]) r acc

/-- Legacy `String.splitOn "\n"` is `String.splitToList (· == '\n')`. -/
theorem splitOn_newline_eq_splitToList (s : String) :
    s.splitOn "\n" = s.splitToList (· == '\n') := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.splitToList_of_valid]
  unfold String.splitOn
  rw [if_neg (by decide : ¬ (("\n" : String) == "") = true)]
  simpa using splitOnAux_newline_ofList ([] : List Char) ([] : List Char) s.toList
    ([] : List String)

theorem splitOn_newline_ne_nil (s : String) : s.splitOn "\n" ≠ [] := by
  intro h
  have hp := List.splitOnP_ne_nil (fun c : Char => c == '\n') s.toList
  rw [splitOn_newline_eq_splitToList, String.splitToList_of_valid] at h
  exact hp (by simpa using h)

/-- Mapping a split-on-newline result back to characters is the list-level split. -/
theorem map_toList_splitOn_newline (s : String) :
    (s.splitOn "\n").map String.toList = s.toList.splitOn '\n' := by
  rw [splitOn_newline_eq_splitToList, String.splitToList_of_valid]
  rw [List.map_map]
  rw [show List.splitOnP (fun c : Char => c == '\n') s.toList =
      List.splitOn '\n' s.toList from (List.splitOn_eq_splitOnP).symm]
  simp [Function.comp_def]

/-- `String.intercalate "\n"` is the left inverse of `String.splitOn "\n"`. -/
theorem intercalate_splitOn_newline (s : String) :
    String.intercalate "\n" (s.splitOn "\n") = s := by
  apply String.toList_inj.mp
  rw [String.toList_intercalate, map_toList_splitOn_newline]
  rw [show ("\n".toList : List Char) = ['\n'] by decide]
  rw [List.intercalate_splitOn]

/-- The inverse for a list of lines with no embedded newline. -/
theorem splitOn_intercalate_newline (l : List String) (hl : l ≠ [])
    (h : ∀ s ∈ l, '\n' ∉ s.toList) :
    (String.intercalate "\n" l).splitOn "\n" = l := by
  apply (List.map_inj_right (f := String.toList)
    (fun x y hxy => String.toList_inj.mp hxy)).mp
  rw [map_toList_splitOn_newline, String.toList_intercalate]
  rw [show List.splitOn '\n' ("\n".toList.intercalate (l.map String.toList)) =
      l.map String.toList by
    rw [show ("\n".toList : List Char) = ['\n'] by decide]
    rw [List.splitOn_intercalate]
    · simpa using h
    · simpa using hl]

theorem splitOnPPrepend_no_mem {p : Char → Bool} :
    ∀ (xs acc : List Char), (∀ x ∈ acc, p x = false) →
      ∀ l ∈ List.splitOnPPrepend p xs acc, ∀ x ∈ l, p x = false := by
  intro xs
  induction xs with
  | nil =>
      intro acc hacc l hl x hx
      simp only [List.splitOnPPrepend_nil, List.mem_singleton] at hl
      subst hl
      exact hacc x (List.mem_reverse.mp hx)
  | cons a as ih =>
      intro acc hacc l hl x hx
      rw [List.splitOnPPrepend_cons_eq_ite] at hl
      split at hl
      · rename_i ha
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact hacc x (List.mem_reverse.mp hx)
        · exact ih [] (by simp) l hl x hx
      · rename_i ha
        exact ih (a :: acc) (fun y hy => by
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · simpa using ha
          · exact hacc y hy) l hl x hx

theorem splitOnP_no_mem {p : Char → Bool} (xs : List Char) :
    ∀ l ∈ xs.splitOnP p, ∀ x ∈ l, p x = false := by
  rw [List.splitOnP_eq_splitOnPPrepend]
  exact splitOnPPrepend_no_mem xs [] (by simp)

/-- Every element of `s.splitOn "\n"` is newline-free. -/
theorem splitOn_newline_no_nl (s : String) :
    ∀ l ∈ s.splitOn "\n", '\n' ∉ l.toList := by
  rw [splitOn_newline_eq_splitToList, String.splitToList_of_valid]
  intro l hl hx
  rw [List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have hx' : '\n' ∈ l' := by simpa using hx
  have hp := splitOnP_no_mem (p := fun c => c == '\n') s.toList l' hl' '\n' hx'
  simpa using hp

end Midfall.Generator.SplitOnLines
