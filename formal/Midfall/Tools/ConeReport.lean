/-
  Midfall.Tools.ConeReport

  THE CONE REPORT - the progress measure of EXECUTION-V2 section 6. This file imports nothing but the
  V2 statement surface and the cone tool, so it is where the two claims that the whole V2 package rests
  on are checked, and where the baseline numbers live:

    * imports_avoid: the V2 cone does not transitively import ANY of the 14 retired v1 modules;
    * cone_avoids:   the dependency cone of each headline theorem touches none of them either, so a
                     later proof cannot smuggle one back in through a lemma;
    * cone_sorries:  how many declarations inside each cone still use sorryAx - the distance left.

  THE ROOTS. Three of them, and the first is the one every later card is measured against:
  `lowering_equivalence_poseidon` (C.1, `Midfall/Instances/PoseidonV2.lean`) is the headline stated
  AT A DEPLOYMENT - `poseidonRender`, formed from D.1's five generator terms and D.2's five
  verifier terms - and its cone is the three named sorried lemmas of that file plus the sorried
  obligations of `Blocks.lean` that composition already leaned on. The other two are the generic
  composition theorem and the end-to-end corollary; since the Q0.3 split they live in
  `Midfall/LoweringV2/Blocks.lean` (the REFINABLE half), not in `Statements.lean` (the FROZEN half),
  and their NAMES are unchanged, so the cone queries below did not have to move. All three are
  `sorry` today (WP-M5, WP-E1, and C.1's three); the counts printed here are what later cards move.

  One import note, because it is load-bearing and it is C.1's finding: `Midfall.Instances.PoseidonEnv`
  reached ten of the AVOID 14 through a single edge to `Midfall.Instances.CurveSurface`, and that
  edge existed only to state one `rfl` pin. `#imports_avoid` below is a FILE-level check, so the pin
  moved to CurveSurface.lean (same content, new home) rather than the render being left out of this
  file. If `imports_avoid` ever reddens again from an `Instances/` import, look for an edge like that.
-/
import Midfall.LoweringV2.Shared
import Midfall.LoweringV2.Program
import Midfall.LoweringV2.Statements
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Blocks.FinalPairing
import Midfall.Instances.PoseidonV2
import Midfall.Tools.ConeSorries

#imports_avoid [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_avoids Midfall.LoweringV2.lowering_equivalence_of_blocks [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_avoids Midfall.LoweringV2.end_to_end [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_sorries Midfall.LoweringV2.lowering_equivalence_of_blocks

#cone_sorries Midfall.LoweringV2.end_to_end

#cone_avoids Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_sorries Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon

-- FP.0's own root: the FinalPairing block contract, whose cone is exactly the three named lemma
--    groups (P.1 / T.4 / T.5). Nothing in the headline's cone cites it yet - the headline reaches the
--    per-block contracts only through the generic sorried `blockContracts_of_valid` - so this is the
--    number P.1, T.4 and T.5 watch, and it is the number that says the three groups are in the cone. 
#cone_sorries Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts
#cone_avoids Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]
