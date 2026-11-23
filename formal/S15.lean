import Midfall.LoweringV3.EndToEndAlgebra
open Midfall Midfall.Halo2
#check @Array.foldl_toList
#check @Array.foldl
#check @List.foldl
example {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p)) :
    cs.adviceColumnPhase.foldl (fun acc p => max acc p.val) 0
      = cs.adviceColumnPhase.toList.foldl (fun acc p => max acc p.val) 0 := rfl
#check @List.foldl_max
#check @le_max_left
#check @le_max_right
