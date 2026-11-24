-- |
-- Midfall.Instances.ConstsCert6
--
-- CERT.6's concrete constant-text gate at the tracked poseidon fixture.
--
-- The generic `prog_constLinesLiteral`/`prog_constTable` targets in
-- `Generator/Certified.lean` require a generic line-splitting lemma for the
-- 90-line `renderConstants` template; the character-level interpolation
-- lemmas are in `Generator/ConstText.lean`. This file records the concrete
-- poseidon instance, closed by `native_decide` (D-P20's instance confinement).
import Midfall.Instances.ConstsKats
import Midfall.LoweringV3.Statements
import Midfall.Generator.ConstTextResidual
set_option autoImplicit false
namespace Midfall.Instances.ConstsCert6

open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonValid Midfall.Instances.PoseidonV2

/-- The tracked poseidon fixture's constant lines are all literal. -/
theorem poseidon_constLinesLiteral :
    Midfall.LoweringV3.constLinesLiteral poseidonM = true := by
  native_decide

/-- The table read back from the poseidon render's text is the data table. -/
theorem poseidon_constTable :
    (Midfall.LoweringV2.constTableOf poseidonM ==
      Midfall.LoweringV3.expectedConsts poseidonPv poseidonM) = true := by
  native_decide


open Midfall.Generator.ConstTextResidual

/-- The poseidon render split into its exact current lines. -/
def poseidonConstTextLines : List String :=
  (renderConstants (partialCtxOfVerifier poseidonM)).splitOn "\n"

theorem poseidon_render_eq :
    renderConstants (partialCtxOfVerifier poseidonM) =
      String.intercalate "\n" poseidonConstTextLines := by
  native_decide

theorem poseidon_lines_literal :
    poseidonConstTextLines.all LineLiteral = true := by
  native_decide

/-- A concrete inhabitant of the exact generic residual interface at poseidon:
    the line list, its recomposition, its literal proof, and the table
    round-trip are all closed at the fixture. -/
def poseidonConstTextWitness : ConstTextWitness poseidonPv poseidonM :=
  { lines := poseidonConstTextLines
    render_eq := poseidon_render_eq
    split_eq := rfl
    lines_literal := poseidon_lines_literal
    table_eq := poseidon_constTable }

end Midfall.Instances.ConstsCert6
