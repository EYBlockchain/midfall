/-
Midfall.Instances.FrameWalkWitness

P-FRAME (docs/plans/P-FRAME.md) STEP 1, THE VERDICT ON THE ACTUAL EMITTED PROGRAM.

THE QUESTION. R-66 proved that the dispatcher prologue 'mstore(0x40, memoryguard(128))' leaves the
arm running in a frame with 'activeWords' 3 and word 0x40 equal to 128, while 'RunVerifier's
'initState' always has 'activeWords' 0, and it exhibited a program whose two runs from the two frames
halt with different payloads ('ShellModel.prologue_write_is_observable'). From that it concluded
'LoweringCorrect.ir_refines' is false FOR A GENERAL PROGRAM. The question this file answers is the one
R-66 left open: is it false of the program this generator actually emits?

THE ANSWER, AND IT IS A MEASUREMENT. No. The emitted program is frame-insensitive:

  * 'msize' does not occur anywhere in 'GenAst.emitMain' at the curve Surface's plan - not in the
    top-level statement list, not in any of the eight emitted helper bodies, called or not
    ('mainHasNoMsize').
  * Of the 75 memory reads the walk finds in 'emitMain', NONE touches the byte range [64, 96) the two
    frames disagree about, and every one of the 75 has an address the walk could resolve
    ('mainFrameClean', 'mainSiteCount'). An unresolved address counts dirty, so this is not the walk
    shrugging.
  * The whole verifyProof ARM - 'headGuard ++ bindLocals ++ main', the program 'RunShell' actually
    runs - has exactly ONE frame-visible read, and it is 'mload(0x40)' inside 'headGuard's bound test
    'gt(mload(0x40), 0x1000)' ('armDirtyIsTheHeadGuardOnly'). And that test answers the same way from
    both frames, because 0 and 128 both fail 'gt · 0x1000'
    ('FrameWalk.headGuard_indifferent_at_the_model_threshold').

So the frame difference R-66 named is NOT the obstruction at 'ShellModel.modelIr S'. That is the
required finding, and it moves the crux from 'the statement is false' to 'the statement needs the run
leg', which is a different and much smaller wall. 'what_step1_does_not_settle' names what this does
NOT buy.

WHY 'fxPlan' AND NOT 'curveSurface.plan' IN THE COMPUTED TERMS. 'curveSurface' is a 'noncomputable
def' - 'g1CodecZ.ofEip?' is a 'Classical.choose' - and the code generator refuses to compile ANY
projection of it, so 'decide' over 'curveSurface.plan' is not writable. The blocks below are built
from 'fxPlan', which is what 'curveSurface.plan' IS, and each is linked back to the Surface by an 'rfl'
theorem ('mainBlk_is_the_curve_main', 'armBlk_is_the_shell_codeBlock'). That is the same shape
'CurveSurface' already uses for exactly this reason, and it is a pin rather than a substitution: the
kernel checks the identification.

WHY THE VERDICTS ARE 'decide' AND NOT KATs. Every verdict below is kernel-checked: 'decide' runs the
whole interprocedural walk over the real emitted AST and finds the answer, so the compiler is not
trusted for the headline. The constant table the walk resolves names through is PINNED in
'FrameWalk' and gated against the rendered contract by 'shellConsts_matches_artifact_ok', because the
kernel cannot run 'String.splitOn' and an unpinned literal table would be a second source of truth
(R-58).

THE NEGATIVE CONTROLS. 'FrameWalk' lands ten plants on hand-written blocks. This file lands the ones
that matter most on a CLONE OF THE REAL PROGRAM: append 'mload(64)' and the walk rejects; append
'msize()' and it rejects; put the read inside a helper the program calls and it rejects. A walk that
had been silently constant would not notice, and this project has measured 28 gate blind spots, so the
plants go into the real emitted program rather than only into a toy.

D-P23, BOTH HALVES, AS THEOREMS. Satisfiability: 'mainFrameClean', 'armDirtyIsTheHeadGuardOnly',
'perPartialClean' - the property exhibited of the actual program, seven partials and all.
Falsification: the planted clones, 'walkIsNotConstantTrue' (the walk answers false on a plant and
true on a clean block, so neither verdict is the walk answering one thing always), and
'fuelBoundIsLoadBearing' (starve the fuel and the same clean program turns dirty, so 'clean' means the
walk FINISHED). THE LIMIT, STATED NOT HIDDEN: no gate in this repository deletes a falsification
theorem and reddens the build - measured twenty-eight times, and no coverage is claimed for it here.
-/
import Midfall.Lowering.FrameWalk
import Midfall.Instances.CurveSurface
import Midfall.Yul.ShellModel
open Midfall Midfall.Lowering Midfall.Lowering.FrameWalk Midfall.Instances
open Midfall.Instances.SurfaceFixture Midfall.Instances.CurveSurface
open YulSemantics
open YulSemantics.EVM (Op)

abbrev FOp := YulSemantics.EVM.Op

namespace Midfall.Instances.FrameWalkWitness

/-- The emitted main block at the fixture plan, which IS the curve Surface's plan. -/
def mainBlk : List (Stmt FOp) := Midfall.Lowering.GenAst.emitMain fxPlan

/-- The arm the shell runs: 'headGuard ++ bindLocals ++ main', spelled from the fixture's own three
    pieces, which is what the curve Surface's fields reduce to. -/
def armBlk : List (Stmt FOp) := fxHeadGuard ++ ([] : List (Stmt FOp))
  ++ Midfall.Lowering.GenAst.emitMain fxPlan

/-- **THE WALKED MAIN IS THE CURVE SURFACE'S MAIN.** 'curveSurface.L.main' is
    'GenAst.emitMain curveSurface.plan' by 'curveBlk', and 'curveSurface.plan' is 'fxPlan', so the
    block the walk measured is the block the headline's Surface emits. By 'rfl', i.e. by the kernel. -/
theorem mainBlk_is_the_curve_main :
    mainBlk = Midfall.Instances.CurveSurface.curveSurface.L.main :=
  Midfall.Instances.CurveSurface.curveBlk.2

/-- **THE WALKED ARM IS THE RUN ARM.** Not a claim about a model of it: the same statement list, by
    definition unfolding. Without this the walk could be about a block that merely resembles the
    program rather than the program itself. -/
theorem armBlk_is_the_shell_codeBlock :
    armBlk = Midfall.Instances.CurveSurface.curveSurface.shell.codeBlock := rfl

/-- And it is the dispatcher's arm body, the block 'ShellModel.wrap' runs after the prologue. -/
theorem armBlk_is_the_arm_body :
    armBlk = Midfall.Yul.ShellModel.armBody Midfall.Instances.CurveSurface.curveSurface := rfl

/-- **THE EMITTED MAIN IS FRAME-INSENSITIVE.** Kernel-checked: 'decide' runs the whole interprocedural
    walk over the real emitted program and finds no frame-visible read. THE HEADLINE MEASUREMENT OF
    P-FRAME. -/
theorem mainFrameClean : frameClean mainBlk = true := by decide

/-- **AND 'msize' IS NOWHERE IN IT**, every helper body entered whether called or not. -/
theorem mainHasNoMsize : mentionsMsize mainBlk = false := by decide

/-- The walk actually looked at 75 reads. Stated as a number because 'clean' with zero sites would be a
    vacuous pass; this says it is not: 75 reads resolved, none dirty. -/
theorem mainSiteCount : (frameSites mainBlk).length = 75 := by decide

/-- **THE ARM HAS EXACTLY ONE FRAME-VISIBLE READ, AND IT IS THE HEAD GUARD'S.** The whole arm - guard,
    locals, main - reduces to one dirty site, 'mload' at base 64 with the word size 32, which is
    'headGuard's bound test and nothing else. Stated as an equality against a one-element list, so a
    second window read anywhere would redden it. -/
theorem armDirtyIsTheHeadGuardOnly :
    frameDirty armBlk = [{ op := "mload", base := some 64, size := some 32 }] := by decide

/-- The arm is NOT 'frameClean' - it does read the window once - and the reason that is harmless is
    'headGuard_indifferent_at_the_model_threshold', not an exemption baked into the walk. Stated so
    nobody reads this as a cleanliness claim about the arm. -/
theorem armIsNotCleanButHasNoMsize :
    (frameClean armBlk || mentionsMsize armBlk) = false := by decide

/-- **EVERY EMITTED PARTIAL, SEVEN OF SEVEN.** The walk runs on each slice the dispatcher can return,
    not only on the concatenation, so a dirty read the concatenation might hide is still caught. -/
theorem perPartialClean :
    (Midfall.Lowering.partials.map fun q => frameClean (GenAst.emitPartial fxPlan q)) =
      [true, true, true, true, true, true, true] := by decide

/- The call-name walk. A '/- -/' comment and not a doc string because a doc string cannot precede the
   'mutual' command - the same measurement Partials.lean:1469 records. -/
mutual
partial def callNamesE : Expr FOp -> List String
  | Expr.call f args => f :: (args.flatMap callNamesE)
  | Expr.builtin _ args => args.flatMap callNamesE
  | _ => []
partial def callNamesS : Stmt FOp -> List String
  | Stmt.block b => b.flatMap callNamesS
  | Stmt.funDef _ _ _ b => b.flatMap callNamesS
  | Stmt.letDecl _ (some e) => callNamesE e
  | Stmt.letDecl _ none => []
  | Stmt.assign _ e => callNamesE e
  | Stmt.cond c b => callNamesE c ++ b.flatMap callNamesS
  | Stmt.switch c cs d =>
      callNamesE c ++ (cs.flatMap fun x => x.2.flatMap callNamesS) ++
        (match d with | some dd => dd.flatMap callNamesS | none => [])
  | Stmt.forLoop i c p b =>
      i.flatMap callNamesS ++ callNamesE c ++ p.flatMap callNamesS ++ b.flatMap callNamesS
  | Stmt.exprStmt e => callNamesE e
  | _ => []
end

/-- **THE REACHABILITY SCOPE, AS DATA.** 'frameSites' walks a function body at its CALL SITES and not
    at its definition site, so a helper no call site reaches is not walked. Exactly one emitted helper
    is in that position at this plan, and it is named rather than hidden. Its own reads are at a local
    it re-binds to a literal, and 'mentionsMsize' enters it anyway, so neither claim depends on the
    omission. -/
def uncalledHelpers : List String :=
  (mainBlk.filterMap fun | Stmt.funDef n _ _ _ => some n | _ => none).filter fun n =>
    !((mainBlk.flatMap callNamesS).contains n)

/-- The uncalled set, as a gate rather than a paragraph. Stated as a KAT and not an 'rfl' theorem
    because 'callNamesS' is a 'partial' def, and the kernel will not reduce a 'partial' definition -
    so this is compiler-trusted, which is the weaker of the two discharges and is labelled as such.
    The 'decide'-checked verdicts above are the ones the headline rests on. -/
def uncalledHelpers_is_one_helper_ok : Bool := uncalledHelpers == ["scalar_inv"]

#eval uncalledHelpers_is_one_helper_ok -- expect true

/-- **PLANT 1 ON THE REAL PROGRAM: a clone of 'emitMain' with a read of word 0x40 appended.** The walk
    rejects it. Without this, 'mainFrameClean' could be the walk answering 'true' to everything. -/
theorem plantedCloneRejectsRead :
    frameClean (mainBlk ++ [Stmt.exprStmt (Expr.builtin YulSemantics.EVM.Op.sstore
      [Expr.lit (Literal.number 0), Expr.builtin YulSemantics.EVM.Op.mload [Expr.lit (Literal.number 64)]])]) = false :=
  by decide

/-- **PLANT 2 ON THE REAL PROGRAM: the same clone with 'msize()' instead.** Rejected by the read walk,
    and separately caught by the whole-block walk, so both channels are covered on the real AST. -/
theorem plantedCloneRejectsMsize :
    frameClean (mainBlk ++ [Stmt.exprStmt (Expr.builtin YulSemantics.EVM.Op.sstore
        [Expr.lit (Literal.number 0), Expr.builtin YulSemantics.EVM.Op.msize []])]) = false ∧
      mentionsMsize (mainBlk ++ [Stmt.exprStmt (Expr.builtin YulSemantics.EVM.Op.sstore
        [Expr.lit (Literal.number 0), Expr.builtin YulSemantics.EVM.Op.msize []])]) = true := by
  refine ⟨by decide, by decide⟩

/-- **PLANT 3: the read reached through a HELPER the program calls.** A walk that stopped at the
    statement list would miss it; this one inlines the call and rejects. The second conjunct says a
    clean extra statement at the same position stays clean, so the rejection is about the read and not
    about the extra code. -/
theorem plantedInsideHelperRejects :
    frameClean (mainBlk ++ (yul% { function leaky () { sstore(0, mload(64)) } leaky() })) = false ∧
      frameClean (mainBlk ++ (yul% { sstore(0, mload(0x3000)) })) = true := by
  refine ⟨by decide, by decide⟩

/-- **THE WALK IS NOT CONSTANTLY FALSE, AND NOT CONSTANTLY TRUE.** The plants reject and the clean
    controls accept, so the verdicts discriminate. -/
theorem walkIsNotConstantTrue :
    (frameClean plantLiteral, frameClean controlCleanAbove,
      frameClean plantMsize, frameClean controlCleanEdgeBelow) =
      (false, true, false, true) := by decide

/-- **THE FUEL BOUND IS LOAD-BEARING.** Starved to a single layer the walk reports exhaustion on the
    SAME program it calls clean at a bound of 160, so 'frameClean = true' carries the information that
    the walk finished, not that it gave up. -/
theorem fuelBoundIsLoadBearing :
    (frameCleanAt shellConsts 1 mainBlk, frameCleanAt shellConsts 160 mainBlk) = (false, true) := by
  decide

/-- **THE PIN THAT MAKES THE TABLE HONEST.** The walk resolves 'mload(VK_DIGEST_MPTR)' to a number
    through 'FrameWalk.pinnedConstants', and that literal table is the rendered contract's own constant
    section. Computed here as a gate so a drift in either direction reddens 'checks.sh'. -/
def pinnedTableMatchesArtifact_ok : Bool := shellConsts_matches_artifact_ok

#eval pinnedTableMatchesArtifact_ok -- expect true

/-- The site count as a KAT beside the theorem, so a change in the emitter shows up in the gate output
    and not only as a proof that no longer builds. -/
def mainSiteCount_ok : Bool := (frameSites mainBlk).length == 75

#eval mainSiteCount_ok -- expect true

/-- The one window read of the whole arm, as a KAT. -/
def armDirtySingleton_ok : Bool :=
  frameDirty armBlk == [{ op := "mload", base := some 64, size := some 32 }]

#eval armDirtySingleton_ok -- expect true

/-- The uncalled-helper set as a KAT beside its theorem. -/
def uncalledHelpers_ok : Bool := uncalledHelpers == ["scalar_inv"]

#eval uncalledHelpers_ok -- expect true

/-- **WHAT STEP 1 DOES NOT SETTLE, stated so the next package does not over-read this one.** The walk
    is about ADDRESSES. It says the emitted program reads neither channel of the frame difference. It
    does NOT say the two runs agree, for three reasons named rather than absorbed:

      1. THE RUN LEG. 'ObsEquiv' is a biconditional over view-existence, and no calldata is known at
         which either side has a run at all - 'gap_runLeg_unexhibited'. A per-read lemma
         ('readBytes_avoids_window') is not an induction over 'Step'; that induction is the same cost
         class as the registered hole 'Bridge.Run_worldEq_of_noWriters', still an open hole in this tree.
      2. THE ENTRY PATH. 'wrap' runs the dispatcher - callvalue guard, thirteen ABI bounds tests,
         'bindLocalsFromImmutables' - and 'RunShell' runs the arm alone. Even with a frame-blind body
         the two programs differ wherever a guard fires or a bound local is read. That is a different
         gap from the frame, and Step 1 says nothing about it.
      3. THE WRITES. The walk treats a write into the window as harmless, which is right for the frame
         difference ('mstore' is blind) but is NOT a claim that the two runs write the same bytes.
         Memory is not in 'ObsView', so this is a limit on what the walk checked, not a hole in the
         observation argument. -/
def what_step1_does_not_settle : String :=
  "Step 1 says the emitted program reads neither channel of the frame difference: no msize anywhere "
    ++ "in GenAst.emitMain, and no memory read overlapping [64,96) except headGuard's bound test, "
    ++ "which 0 and 128 both pass. It does NOT discharge ir_refines at ShellModel.modelIr S. The "
    ++ "remaining blockers are the run leg (gap_runLeg_unexhibited: no calldata at which either side "
    ++ "is known to have a run), the dispatcher entry path (the guards and bindLocalsFromImmutables "
    ++ "that RunShell does not run), and the Step-relation induction that turns a per-read lemma into "
    ++ "a per-run lemma (same cost class as the registered hole Bridge.Run_worldEq_of_noWriters)."

/-! ### The finding Step 1 turned up that is NOT about the frame -/

/-- **THE ARM BLOCK LEAVES 61 IDENTIFIERS UNBOUND.** 'RunEmitted.lean:67-76' already records that the
    emitted program is a FRAGMENT - the identifiers it references include the contract-level
    'uint256 internal constant' declarations of 'Halo2Verifier.sol' and the two shell locals, and
    D-P30 puts the Solidity wrapper out of scope - and 'RunEmitted' binds them with 'shellLets' in
    order to run the fragment through the interpreter. What had not been written down anywhere is that
    the block 'RunShell' actually runs does NOT bind them: 'curveSurface.bindLocals = []' and
    'shell_unfolds' pins the code block to 'headGuard ++ bindLocals ++ main', so the program 'RunShell'
    is stated over has 61 free identifiers, 'vk' among them, and the first non-definition statement of
    'main' evaluates 'extcodesize(vk)' unconditionally. -/
theorem armHasFreeIdentifiers : (freeNames armBlk).length = 61 := by native_decide

/-- 'vk' specifically, the one the first executed statement needs.

    THE DISCHARGE HERE IS THE WEAKER ONE, AND IT IS LABELLED AS SUCH. 'freeNames' is a 'mutual'
    structural recursion, which Lean compiles through 'WellFounded.fix' - the same reason
    'Bridge.noWritersScan' exists and the same reason every verdict ABOVE is a 'decide'. So these two
    facts are compiler-trusted ('native_decide', hence 'Lean.ofReduceBool' in their axiom set) while
    the frame-insensitivity verdicts are kernel-trusted. That asymmetry is deliberate: the headline
    claims get the kernel, and this supporting measurement gets the compiler. 'native_decide' is
    confined to 'Midfall/Instances/' by D-P20, and this file is in Instances. -/
theorem vk_is_free : "vk" ∈ freeNames armBlk := by native_decide

/-- Nothing in the Surface binds it: the arm's local-binding field is empty at this Surface, by 'rfl'. -/
theorem bindLocals_binds_nothing :
    Midfall.Instances.CurveSurface.curveSurface.bindLocals = [] := rfl

/-- **AND THE DISPATCHER SIDE IS INHABITED WHERE THE SHELL SIDE IS EMPTY.**
    'unroutable_calldata_reverts' (ShellModel.lean:1360) gives, for ANY arm body and any frame whose
    calldata is shorter than four bytes, a run of 'dispatcher body' ending 'some (.revert, [])', and
    'size_test_skips_the_switch_on_empty_calldata' pins the hypothesis at the empty calldata by 'rfl'.
    So the dispatcher reaches a revert observation without ever entering the arm. The inversion this
    record used to name as the missing half is now proved, one file over, and it went the refutation
    way - so the two facts above are no longer the shape of an obstruction but the two halves of a
    REFUTATION. -/
def gap_runShell_uninhabited_candidate : String :=
  "CLOSED BY P-RUNSHELL, AS A REFUTATION AND NOT A GAP. The inversion landed: RunShell curveSurface "
    ++ "W H cd c g is EMPTY for every world, hash, calldata, call relation and gas oracle "
    ++ "(RunShellInversion.no_arm_run, runShell_curveSurface_empty). The arm's first executed "
    ++ "statement reads vk, EXPECTED_VK_LENGTH and EXPECTED_VK_CODEHASH_WORD, nothing binds them "
    ++ "(armHasFreeIdentifiers, vk_is_free, bindLocals_binds_nothing), YulSemantics.Run starts the "
    ++ "variable environment at [] (BigStep.lean:366) and Step.var needs VEnv.get V x = some v. The "
    ++ "head guard is NOT the obstruction: guard_forced proves it passes and binds nothing, and "
    ++ "guard_is_not_the_obstruction exhibits a run of [head guard; revert(0,0)] from the same frame, "
    ++ "while bound_read_has_a_run proves the read has a derivation once vk IS bound. So the emptiness "
    ++ "is the binding, not the frame, the builtin, or every program. CONSEQUENCE: ObsEquiv fails "
    ++ "(obsEquiv_wrap_runShell_fails), so LoweringCorrect.ir_refines at ShellModel.modelIr "
    ++ "curveSurface is REFUTED (ir_refines_refuted_at_curveSurface) and LoweringCorrect curveSurface "
    ++ "product has NO instance for ANY product (curveSurface_not_LoweringCorrect) - the fourth "
    ++ "refuted headline hypothesis in this project, and lowering_equivalence is vacuous at the curve "
    ++ "Surface. STILL OPEN, and it is a spec question rather than this one: Surface.bindLocals cannot "
    ++ "close the program. A Yul function is not a closure - Step.callOk binds the parameters and the "
    ++ "zeroed return slots and nothing else (BigStep.lean:189) - and six of the eight emitted helpers "
    ++ "read names their own signature does not provide (RunShellInversion.helperOwnFree_count_ok), so "
    ++ "no legal value of bindLocals makes the arm a closed program. The fix belongs in the emitter "
    ++ "(inline the contract-level constants, as solc does) or in the spec (a bindInside-style "
    ++ "transform), not in this fixture. The Surface was NOT edited and RunShell was NOT changed."


#print axioms Midfall.Instances.FrameWalkWitness.mainFrameClean
#print axioms Midfall.Instances.FrameWalkWitness.mainHasNoMsize
#print axioms Midfall.Instances.FrameWalkWitness.armDirtyIsTheHeadGuardOnly
#print axioms Midfall.Instances.FrameWalkWitness.perPartialClean
#print axioms Midfall.Instances.FrameWalkWitness.plantedCloneRejectsRead
#print axioms Midfall.Instances.FrameWalkWitness.fuelBoundIsLoadBearing
#print axioms Midfall.Lowering.FrameWalk.headGuard_indifferent_at_the_model_threshold
#print axioms Midfall.Lowering.FrameWalk.readBytes_avoids_window
#print axioms Midfall.Lowering.FrameWalk.plantViaParameterRejects

end Midfall.Instances.FrameWalkWitness

