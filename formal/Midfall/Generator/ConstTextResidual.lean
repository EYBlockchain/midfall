-- |
-- Midfall.Generator.ConstTextResidual
--
-- The exact remaining interface for CERT.6's generic constant-text targets.
--
-- `ConstText.lean` proves the character-level interpolation facts. What is
-- still missing is the proof-only line list for `renderConstants`: a list
-- `lines` with `renderConstants = String.intercalate "\n" lines`, the split
-- equality, and the per-line literal proof. `ConstTextWitness` packages
-- exactly those obligations; the two theorems below are the reductions from
-- a witness to `prog_constLinesLiteral` / `prog_constTable`. They are NOT used
-- to replace the target statements, which remain unchanged.
import Midfall.LoweringV3.Statements
import Midfall.Generator.Artifacts
set_option autoImplicit false
open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.LoweringV3
namespace Midfall.Generator.ConstTextResidual

/-- The per-line body of `constLinesLiteral`, named so a line list can be
    checked without re-typing the parser. -/
def LineLiteral (l : String) : Bool :=
  match l.splitOn "uint256 internal constant " with
  | [_, rest] =>
      (match rest.splitOn "=" with
       | [_, rhs] =>
           let v := ((rhs.splitOn ";").headD "").trimAscii.toString
           let digits := if v.startsWith "0x" then (v.drop 2).toString else v
           !digits.isEmpty && digits.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
       | _ => false)
  | _ => true

theorem constLinesLiteral_eq_all_lineLiteral (m : Model) :
    Midfall.LoweringV3.constLinesLiteral m =
      ((renderConstants (partialCtxOfVerifier m)).splitOn "\n").all LineLiteral := rfl

/-- The exact missing generic data: a line list preserving the current text,
    its split equality, and the per-line literal proof. `table_eq` is the
    remaining `solConstantLine?`/value round-trip for the table target. -/
structure ConstTextWitness (pv : PlanView) (m : Model) where
  lines : List String
  render_eq : renderConstants (partialCtxOfVerifier m) = String.intercalate "\n" lines
  split_eq : (renderConstants (partialCtxOfVerifier m)).splitOn "\n" = lines
  lines_literal : lines.all LineLiteral = true
  table_eq : (Midfall.LoweringV2.constTableOf m ==
    Midfall.LoweringV3.expectedConsts pv m) = true

/-- A witness discharges the generic line-literal target. -/
theorem constLinesLiteral_of_witness {pv : PlanView} {m : Model}
    (h : ConstTextWitness pv m) :
    Midfall.LoweringV3.constLinesLiteral m = true := by
  rw [constLinesLiteral_eq_all_lineLiteral, h.split_eq]
  exact h.lines_literal

/-- A witness also carries the table round-trip conclusion. -/
theorem constTable_of_witness {pv : PlanView} {m : Model}
    (h : ConstTextWitness pv m) :
    (Midfall.LoweringV2.constTableOf m ==
      Midfall.LoweringV3.expectedConsts pv m) = true :=
  h.table_eq

end Midfall.Generator.ConstTextResidual
