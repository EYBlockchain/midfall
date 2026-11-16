/-
  Midfall.LoweringV2.ProgramLemmas

  GENERATOR-SIDE OBLIGATIONS ABOUT THE PROGRAM OF `Program.lean` - the lemmas that compose the
  slices into the main block, and the inlining lemma that licenses proving contracts per slice.

  REFINABLE (Q0.3): this file is NOT in `Frozen.sha256`. It holds exactly §5 of the original
  `Program.lean`, moved verbatim; the section number is kept so PLAN-V2's references resolve.
  Nothing here may be imported BY the frozen surface (that would make a refinable fact a premise
  of a frozen statement).
-/
import Midfall.LoweringV2.Program
import Midfall.LoweringV2.Shared

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

/-! ## 5. Generator-side obligations (theorems; owned by WP-A) -/

/-- The names a block binds at its top level (`let`, function names). -/
def topBinders (b : YulBlock) : List String := b.flatMap Inline.boundOf

/-- Inlining distributes over concatenation when the left block binds no constant name at top
    level. This is what licenses proving contracts per slice and composing them. OBLIGATION. -/
theorem inline_append (consts : List (String × Nat)) (a b : YulBlock)
    (h : ∀ x ∈ topBinders a, x ∉ consts.map Prod.fst) :
    Inline.inlineContractConstants consts (a ++ b) =
      Inline.inlineContractConstants consts a ++ Inline.inlineContractConstants consts b := by
  sorry

/-- The main block is the helpers followed by the slices in include order. Replaces the v1
    `main_concat` PIN (a hypothesis on a free field) by a THEOREM about the emitter. -/
theorem emitSlices_eq (pv : PlanView) :
    GenAst.emitSlices pv =
      GenAst.emitPartial pv .vkLoading ++ GenAst.emitPartial pv .transcriptParser ++
      GenAst.emitPartial pv .lagrange ++ GenAst.emitPartial pv .quotientLin ++
      GenAst.emitPartial pv .pcs ++ GenAst.emitPartial pv .finalPairing ++
      GenAst.emitPartial pv .traceReturn := by
  simp [GenAst.emitSlices, Midfall.Lowering.partials, List.append_assoc]

end Midfall.LoweringV2