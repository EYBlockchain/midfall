-- |
-- Midfall.Instances.ConstsCert6
--
-- CERT.6's concrete constant-text gate at the tracked poseidon fixture.
--
-- The generic `prog_constLinesLiteral`/`prog_constTable` targets in
-- `Generator/Certified.lean` now reduce to the generic template reassociation
-- plus the per-line literal/table round-trips (`Generator/ConstTextResidual.lean`).
-- This file closes the same witness at the poseidon fixture by `native_decide`
-- (D-P20's instance confinement).
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

/-- The generic transcribed line list at the poseidon fixture. -/
def poseidonConstTextLines : List String :=
  renderConstantsLines (partialCtxOfVerifier poseidonM)

/-- The transcribed line list recomposes the poseidon render. -/
theorem poseidon_render_eq :
    renderConstants (partialCtxOfVerifier poseidonM) =
      String.intercalate "\n" poseidonConstTextLines := by
  native_decide

/-- Every transcribed line at poseidon has a literal constant RHS. -/
theorem poseidon_lines_literal :
    poseidonConstTextLines.all LineLiteral = true := by
  native_decide

/-- A concrete inhabitant of the generic residual interface at poseidon:
    the template reassociation, the per-line literal proof, and the table
    round-trip are all closed at the fixture. -/
theorem poseidonConstTextWitness : ConstTextWitness poseidonPv poseidonM :=
  { render_eq := poseidon_render_eq
    lines_literal := poseidon_lines_literal
    table_eq := poseidon_constTable }

end Midfall.Instances.ConstsCert6
