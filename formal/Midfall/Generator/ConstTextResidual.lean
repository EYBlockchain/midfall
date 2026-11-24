-- |
-- Midfall.Generator.ConstTextResidual
--
-- The exact remaining interface for CERT.6's generic constant-text targets.
--
-- `SplitOnLines.lean` proves the toolchain-missing inverse of `String.splitOn`
-- at a newline separator. `ConstLines.lean` transcribes the `renderConstants`
-- template into a list of literal chunks, proves the per-arm chunk equalities,
-- and proves that splitting the concatenation of those chunks recovers the line
-- list. The remaining `render_eq` is the definitional reassociation of the
-- `renderConstants` template into the transcribed chunk list; `lines_literal`
-- and `table_eq` are then the per-line `LineLiteral` and `solConstantLine?`
-- round-trips. The two target statements are unchanged.
import Midfall.LoweringV3.Statements
import Midfall.Generator.Artifacts
import Midfall.Generator.ConstLines
set_option autoImplicit false
open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.LoweringV3
namespace Midfall.Generator.ConstTextResidual

open Midfall.Generator.ConstLines
open Midfall.Generator.SplitOnLines

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

/-- The generic line list of the constant template. This is the transcription
    produced by `ConstLines.renderConstantsChunks`; it covers the VK, quotient,
    accumulator, and direct arms. -/
def renderConstantsLines (ctx : PartialCtx) : List String :=
  ConstLines.renderConstantsLines ctx

/-- `splitOn "\n"` of the generic line list's concatenation is the list itself.
    This is the toolchain fact the previous residual lacked. -/
theorem splitOn_renderConstantsLines_chunks (ctx : PartialCtx) :
    (String.join ((ConstLines.renderConstantsChunks ctx).map Chunk.text)).splitOn "\n" =
      renderConstantsLines ctx :=
  ConstLines.splitOn_renderConstantsChunks ctx

/-- If the template reassociation `render_eq` holds, the split equality follows
    with no further string reasoning. -/
theorem split_eq_of_render_eq {ctx : PartialCtx}
    (h : renderConstants ctx =
      String.intercalate "\n" (renderConstantsLines ctx)) :
    (renderConstants ctx).splitOn "\n" = renderConstantsLines ctx := by
  rw [h, splitOn_intercalate_newline]
  · exact ConstLines.renderConstantsLines_ne_nil ctx
  · exact ConstLines.renderConstantsLines_no_nl ctx

/-- The exact missing generic data: the template reassociation, the per-line
    literal proof, and the `solConstantLine?`/value round-trip for the table
    target. `render_eq` is the only remaining string-level obligation; the split
    equality follows from it by `split_eq_of_render_eq`. -/
structure ConstTextWitness (pv : PlanView) (m : Model) where
  render_eq : renderConstants (partialCtxOfVerifier m) =
    String.intercalate "\n" (renderConstantsLines (partialCtxOfVerifier m))
  lines_literal : (renderConstantsLines (partialCtxOfVerifier m)).all LineLiteral = true
  table_eq : (Midfall.LoweringV2.constTableOf m ==
    Midfall.LoweringV3.expectedConsts pv m) = true

/-- A witness discharges the generic line-literal target. -/
theorem constLinesLiteral_of_witness {pv : PlanView} {m : Model}
    (h : ConstTextWitness pv m) :
    Midfall.LoweringV3.constLinesLiteral m = true := by
  rw [constLinesLiteral_eq_all_lineLiteral]
  rw [split_eq_of_render_eq h.render_eq]
  exact h.lines_literal

/-- A witness also carries the table round-trip conclusion. -/
theorem constTable_of_witness {pv : PlanView} {m : Model}
    (h : ConstTextWitness pv m) :
    (Midfall.LoweringV2.constTableOf m ==
      Midfall.LoweringV3.expectedConsts pv m) = true :=
  h.table_eq

end Midfall.Generator.ConstTextResidual
