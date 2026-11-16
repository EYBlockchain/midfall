/-
  Midfall.Tools.ConeReport

  THE CONE REPORT - the progress measure of EXECUTION-V2 section 6. This file imports nothing but the
  V2 statement surface and the cone tool, so it is where the two claims that the whole V2 package rests
  on are checked, and where the baseline numbers live:

    * imports_avoid: the V2 cone does not transitively import ANY of the 14 retired v1 modules;
    * cone_avoids:   the dependency cone of each headline theorem touches none of them either, so a
                     later proof cannot smuggle one back in through a lemma;
    * cone_sorries:  how many declarations inside each cone still use sorryAx - the distance left.

  The two roots are the generic composition theorem and the end-to-end corollary. Since the Q0.3
  split they live in `Midfall/LoweringV2/Blocks.lean` (the REFINABLE half), not in `Statements.lean`
  (the FROZEN half); their NAMES are unchanged, so the cone queries below did not have to move.
  Both are `sorry` today (WP-M5, WP-E1); the counts printed here are the baseline Q0.3 compares against.
-/
import Midfall.LoweringV2.Shared
import Midfall.LoweringV2.Program
import Midfall.LoweringV2.Statements
import Midfall.LoweringV2.Blocks
import Midfall.Tools.ConeSorries

#imports_avoid [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_avoids Midfall.LoweringV2.lowering_equivalence_of_blocks [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_avoids Midfall.LoweringV2.end_to_end [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_sorries Midfall.LoweringV2.lowering_equivalence_of_blocks

#cone_sorries Midfall.LoweringV2.end_to_end
