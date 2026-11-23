import Midfall.LoweringV3.EndToEndAlgebra
open Midfall Midfall.Halo2 Midfall.Lowering
example : (match Inline.shadowed ["buf_len", "cptr", "ret"] "cptr" with
    | true => (1:Nat) | false => 2) = 1 := by
  simp [Inline.shadowed]
example : (match Inline.shadowed ["buf_len", "cptr", "ret"] "x_hi_word" with
    | true => (1:Nat) | false => 2) = 2 := by
  simp [Inline.shadowed]
available_section_variables
