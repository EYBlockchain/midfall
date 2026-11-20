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
    level. This is what licenses proving contracts per slice and composing them. PROVED (GEN.4).

    THE SHAPE OF THE PROOF. `inlineContractConstants` is one `inlineScan` at `inlineFuel`, and a
    scan is a `List.foldl` over the block (`Inline.inlineStep_eq_foldl`), so the distribution is
    `List.foldl_append` plus the two accumulator facts `Inline.foldl_stepAcc_sh` and
    `Inline.foldl_stepAcc_blks_split`: the fold's statements are the accumulator's own followed by
    what a FRESH accumulator at the same shadow list produces, and its shadow list is the
    followed by every binder of the list. That gives the scan at the threaded shadow list
    `topBinders a`; the hypothesis says none of those names is a constant name, and a shadow list
    that names no constant is inert (`Inline.inlineScan_irrel`), which collapses it to the scan at
    `[]`. Nothing is assumed about the render: the statement is about the transform.

    WHY THE HYPOTHESIS CANNOT BE DROPPED. `Inline.inlineScan_append_is_threaded` is a proved
    falsifier of the unthreaded equation, and `Inline.inline_append_is_guarded` below is a proved
    falsifier of this one with `h` dropped - a model that binds a constant's name at top level makes
    the equation FALSE, not merely unproved (findings B-5/D-13, the `r` hazard). -/
theorem inline_append (consts : List (String × Nat)) (a b : YulBlock)
    (h : ∀ x ∈ topBinders a, x ∉ consts.map Prod.fst) :
    Inline.inlineContractConstants consts (a ++ b) =
      Inline.inlineContractConstants consts a ++ Inline.inlineContractConstants consts b := by
  have hsb : ∀ x ∈ a.flatMap Inline.boundOf, x ∉ consts.map Prod.fst := h
  have h2 : Inline.inlineScan Inline.inlineFuel consts (a.flatMap Inline.boundOf) b =
      Inline.inlineScan Inline.inlineFuel consts [] b := by
    simpa [List.append_nil] using
      Inline.inlineScan_irrel consts Inline.inlineFuel (a.flatMap Inline.boundOf) [] b hsb
  show (Inline.inlineScan Inline.inlineFuel consts [] (a ++ b)).blks =
       (Inline.inlineScan Inline.inlineFuel consts [] a).blks ++
         (Inline.inlineScan Inline.inlineFuel consts [] b).blks
  have key := Inline.inlineScan_append 63 consts [] a b
  rw [show ((63 : Nat) + 1) = Inline.inlineFuel from rfl] at key
  rw [key]
  simp only [List.nil_append]
  rw [← h2]

/-- **THE `topBinders` SIDE CONDITION IS LOAD-BEARING**: the falsifier of `inline_append` with `h`
    dropped (GEN.4 step 4; `Inline.inlineScan_append_is_threaded` is the same measurement one level
    down, on the scan rather than on the transform). `a` DECLARES `X` at top level and `X` is a
    constant name, so in `a ++ b` the read of `X` is shadowed and survives as a variable, while in
    the standalone `b` it is substituted to 7. This is the B-5/D-13 hazard - a model constant
    named `r` - and it is why `prog_slices_decomp` cannot be stated for a generic render without the
    shadow fact, and why the V2 leaf must not be re-pointed at a statement that lacks it. -/
theorem inline_append_needs_h :
    ¬ (Inline.inlineContractConstants [("X", 7)]
        (Inline.inlineAppendFalsA ++ Inline.inlineAppendFalsB) =
        Inline.inlineContractConstants [("X", 7)] Inline.inlineAppendFalsA ++
          Inline.inlineContractConstants [("X", 7)] Inline.inlineAppendFalsB) := by
  intro h
  have h1 : Inline.readsX
      (Inline.inlineContractConstants [("X", 7)]
        (Inline.inlineAppendFalsA ++ Inline.inlineAppendFalsB)) = true := rfl
  have h2 : Inline.readsX
      (Inline.inlineContractConstants [("X", 7)] Inline.inlineAppendFalsA ++
        Inline.inlineContractConstants [("X", 7)] Inline.inlineAppendFalsB) = false := rfl
  rw [h] at h1
  rw [h2] at h1
  exact absurd h1 Bool.false_ne_true

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

-- GEN.4: `inline_append` is PROVED - sorry-free, standard axioms only, no `native_decide`.
#print axioms Midfall.LoweringV2.inline_append
#print axioms Midfall.LoweringV2.inline_append_needs_h
