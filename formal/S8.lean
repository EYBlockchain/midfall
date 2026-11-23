import Midfall.LoweringV3.TranscriptRows
open Midfall Midfall.Halo2
example (l : List Nat) : Midfall.Lowering.sumNat l = l.sum := rfl
example (l : List Nat) : l.sum = Midfall.Lowering.sumNat l := rfl
