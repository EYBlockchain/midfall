/-
  Midfall.Tools.ConeReport

  THE CONE REPORT - the progress measure of EXECUTION-V2 section 6. This file imports nothing but the
  V2 statement surface and the cone tool, so it is where the two claims that the whole V2 package rests
  on are checked, and where the baseline numbers live:

    * imports_avoid: the V2 cone does not transitively import ANY of the 14 retired v1 modules;
    * cone_avoids:   the dependency cone of each headline theorem touches none of them either, so a
                     later proof cannot smuggle one back in through a lemma;
    * cone_sorries:  how many declarations inside each cone still use sorryAx - the distance left.

  THE ROOTS. Two of them, the surviving V2 roots: the generic composition theorem
  `lowering_equivalence_of_blocks` and the end-to-end corollary `end_to_end`. Since the Q0.3 split
  they live in `Midfall/LoweringV2/Blocks.lean` (the REFINABLE half), not in `Statements.lean` (the
  FROZEN half), and their NAMES are unchanged, so the cone queries below did not have to move.

  W13/PL.1 RETIRED THE DEPLOYMENT ROOT. `Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon`
  (C.1's headline at `poseidonRender`) was DELETED together with its refuted `poseidon_valid` input:
  `poseidonRender_notValid` proves the `Valid` hypothesis false, so keeping the theorem in the tree
  would keep a cone that proves `False`. The surviving V2 root is the generic composition above; the
  deployment render itself and the conditional `poseidon_block_contracts` remain in
  `Midfall/Instances/PoseidonV2.lean`. Both surviving roots are `sorry` today (WP-M5 and WP-E1); the
  counts printed here are what later cards move.

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
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.Instances.PoseidonV2
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

#imports_avoid [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_avoids Midfall.LoweringV2.lowering_equivalence_of_blocks [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_avoids Midfall.LoweringV2.end_to_end [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_sorries Midfall.LoweringV2.lowering_equivalence_of_blocks

#cone_sorries Midfall.LoweringV2.end_to_end

-- FP.0's own root: the FinalPairing block contract, whose cone is exactly the three named lemma
--    groups (P.1 / T.4 / T.5). Nothing in the surviving V2 roots' cones cites it yet - they reach the
--    per-block contracts only through the generic sorried `blockContracts_of_valid` - so this is the
--    number P.1, T.4 and T.5 watch, and it is the number that says the three groups are in the cone. 
#cone_sorries Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts
-- T.1's own root: TraceReturn's PROGRESS contract, hand-proved with no sorry. The cone count printed
--    here is 0 by construction - the acceptance check is that it STAYS 0 as the interface is reused,
--    and that the V2 roots above do not move (nothing in either cone cites this file yet).
#cone_sorries Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress
#cone_avoids Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]
#cone_avoids Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

#cone_sorries Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound
-- T.2's own root: TraceReturn's SOUNDNESS contract, both conjuncts, hand-proved with no sorry.
--    Conjunct 2 is the poisoned walk, whose whole content is tr_fail_reverts (the lemma T.5 cites).
--    The count is 0 by construction; the acceptance finding is that the V2 roots above do NOT move,
--    because no per-block proof reaches them until the generic hinge blockContracts_of_valid
--    (Blocks.lean:152, still sorry) is proved.
#cone_avoids Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

-- S.4's own roots: the vkLoading row and the sorry-free part of its interface. The row's cone count
--    is 3 by construction (the clean walk, the poisoned walk, the exhibited run - named in
--    Blocks/VkLoading.lean section 6); vk_slice is 0. The acceptance finding is that the V2 roots
--    above do NOT move, because no per-block row reaches them until the generic hinge
--    blockContracts_of_valid (Blocks.lean:152, still sorry) is proved.
#cone_sorries Midfall.LoweringV2.Blocks.VkLoading.vk_blockRow
#cone_sorries Midfall.LoweringV2.Blocks.VkLoading.vk_slice
#cone_avoids Midfall.LoweringV2.Blocks.VkLoading.vk_blockRow [Midfall.Lowering.Surface, Midfall.Lowering.Partials, Midfall.Lowering.Obligations, Midfall.Lowering.Accumulator, Midfall.Lowering.AccEncoding, Midfall.Lowering.RunEmitted, Midfall.Lowering.FrameWalk, Midfall.Yul.ShellModel, Midfall.Yul.ImportSolcIR, Midfall.Yul.IRCheck, Midfall.Instances.ImportedIR, Midfall.Instances.IrCheckBlindness, Midfall.Instances.RunShellInversion, Midfall.Instances.RunShellInhabited]

/- ## THE AXIOM GATE (PLAN-V3 section 6)

The axiom half of DONE as a build error. While the surviving V2 root is open, `sorryAx` is allowed
BY NAME and everything else is already pinned: a user axiom, or a `native_decide` outside the
listed declarations, reddens the build today. DONE is the commit that deletes the token `sorryAx`
here. W13/PL.1 re-pointed this gate from the deleted deployment headline to the generic composition:
the fixture computation (`poseidonModel_isOk`) is no longer in a V2 root's cone, so the native list
is EMPTY. -/
open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV2.lowering_equivalence_of_blocks
  [propext, Classical.choice, Quot.sound, sorryAx] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound [propext, Classical.choice, Quot.sound]
open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress [propext, Classical.choice, Quot.sound]
