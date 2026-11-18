/-
  Midfall.LoweringV2.ProgramLemmas

  GENERATOR-SIDE OBLIGATIONS ABOUT THE PROGRAM OF `Program.lean` - the lemmas that compose the
  slices into the main block, and the inlining lemma that licenses proving contracts per slice.

  REFINABLE (Q0.3): this file is NOT in `Frozen.sha256`. It holds exactly §5 of the original
  `Program.lean`, moved verbatim; the section number is kept so PLAN-V2's references resolve.
  Nothing here may be imported BY the frozen surface (that would make a refinable fact a premise
  of a frozen statement) - and since ST.6 the direction is visible in the import list: this file
  imports `Statements.lean`, not the other way round, because `topBinders` moved into the frozen
  surface with the clause that reads it.
-/
import Midfall.LoweringV2.Program
import Midfall.LoweringV2.Shared
import Midfall.LoweringV2.Statements

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

/-! ## 5. Generator-side obligations (theorems; owned by WP-A) -/

/- `topBinders` MOVED OUT by ST.6 (D-P67): it is the head of the frozen `noShadowCore` clause
    text, and a frozen statement may not rest on this refinable file (D-P65). It now lives in
    `Midfall/LoweringV2/Statements.lean`, which this file now imports, and which `inline_append` below states its hypothesis on. Same text, same `Inline.boundOf`. -/

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

/-- The model-aware analogue of `emitSlices_eq` above, and the equation `mainAsmRaw` now rests on:
    the seven slices in include order, with the `.quotientLin` arm carrying the two
    `quotient_numerator` includes in front of the linearization scope (OBJ.2). Same one-`simp`
    discharge: the cost of this lemma is the emitter's, not the proof's. -/
theorem emitSlicesM_eq (pv : PlanView) (c : Midfall.Generator.PartialCtx) :
    GenAst.emitSlicesM pv c =
      GenAst.emitPartialM pv c .vkLoading ++ GenAst.emitPartialM pv c .transcriptParser ++
      GenAst.emitPartialM pv c .lagrange ++ GenAst.emitPartialM pv c .quotientLin ++
      GenAst.emitPartialM pv c .pcs ++ GenAst.emitPartialM pv c .finalPairing ++
      GenAst.emitPartialM pv c .traceReturn := by
  simp [GenAst.emitSlicesM, Midfall.Lowering.partials, List.append_assoc]

end Midfall.LoweringV2