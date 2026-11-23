import Midfall.LoweringV3.ModexpGeneral
open Midfall.LoweringV3
namespace ScratchA5
example (b : List Nat) :
    (b.drop 10).take 19 = (b.drop 10).take 1 ++ ((b.drop 11).take 10 ++ (b.drop 21).take 8) := by
  rw [show (19 : Nat) = 1 + 18 by norm_num, List.take_add]
  rw [show (b.drop 10).drop 1 = b.drop 11 by rw [List.drop_drop]]
  rw [show (18 : Nat) = 10 + 8 by norm_num, List.take_add]
  rw [show (b.drop 11).drop 10 = b.drop 21 by rw [List.drop_drop]]
example (b : List Nat) :
    (b.drop 0).take 2 ++ ((b.drop 2).take 8 ++ ((b.drop 10).take 19 ++ ((b.drop 29).take 1 ++ (b.drop 30).take 4)))
      = (b.drop 0).take 34 := by
  simp only [List.drop_zero]
  rw [show (34 : Nat) = 2 + 32 by norm_num, List.take_add]
  rw [show (32 : Nat) = 8 + 24 by norm_num, List.take_add]
  rw [show (b.drop 2).drop 8 = b.drop 10 by rw [List.drop_drop]]
  rw [show (24 : Nat) = 19 + 5 by norm_num, List.take_add]
  rw [show (b.drop 10).drop 19 = b.drop 29 by rw [List.drop_drop]]
  rw [show (5 : Nat) = 1 + 4 by norm_num, List.take_add]
  rw [show (b.drop 29).drop 1 = b.drop 30 by rw [List.drop_drop]]
end ScratchA5
