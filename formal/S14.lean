import Midfall.LoweringV3.EndToEndAlgebra
open Midfall Midfall.Halo2
example {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p)) (i : ℕ) :
    cs.adviceColumnPhaseNats.toList[i]? = (cs.adviceColumnPhase[i]?).map (fun q => q.val) := by
  unfold ConstraintSystem.adviceColumnPhaseNats
  rw [Array.toList_map, List.getElem?_map, ← Array.getElem?_toList]
