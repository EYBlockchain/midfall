/-
  GeneratorRowsWitness.lean (SCRATCH - W12 evidence for GeneratorRows.lean; TESTS, not proofs)

  Fixtures are tests under D-P71, so `native_decide` and `#eval` are allowed HERE and nowhere in
  `GeneratorRows.lean`. Each block says which statement it is evidence for.
-/
import GeneratorRows
import Midfall.Instances.PoseidonPins

set_option autoImplicit false

namespace Midfall.LoweringV2.V3.Gen.Witness

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV2.V3 Midfall.LoweringV2.V3.Gen
open Midfall.Instances Midfall.Instances.PoseidonValid

def cs : Inline.Consts := constTableOf poseidonM

/-! ### W12(a) for the lagrange children: their hypotheses hold together at F1 -/

/-- `lag_sq_loop`, `lag_denoms_loop`, `lag_second_pass_loop`, `lag_lblind_loop`,
    `lag_instance_loop`: every hypothesis, at the fixture's table and plan view. -/
def lagChildrenHyps : Bool :=
  let n := poseidonPv.numInstances
  let m := poseidonPv.numNegLagranges
  cs.lookup "r" == none && decide (poseidonPv.k < 2 ^ 256) && decide (2 ≤ m) &&
  (match cs.lookup "OMEGA_INV_TO_L_MPTR", cs.lookup "LAGRANGE_DENOMS_MPTR",
      cs.lookup "INSTANCE_CPTR" with
   | some aL, some D, some aI =>
       decide (aL < 2 ^ 256) && decide (D + 32 * (n + m) < 2 ^ 256) &&
       decide (aL + 32 ≤ D ∨ D + 32 * (n + m) ≤ aL) && decide (D + 32 * m < 2 ^ 256) &&
       decide (aI + 32 * n < 2 ^ 256)
   | _, _, _ => false)

#eval lagChildrenHyps   -- expect true
theorem lagChildrenHyps_ok : lagChildrenHyps = true := by native_decide

-- The numbers behind it.
#eval (poseidonPv.k, poseidonPv.numInstances, poseidonPv.numNegLagranges,
  cs.lookup "OMEGA_INV_TO_L_MPTR", cs.lookup "LAGRANGE_DENOMS_MPTR", cs.lookup "INSTANCE_CPTR")

/-! ### The premise gaps, evaluated at F1 (each is satisfiable, so each is a real clause) -/

/-- PG-CONSTS-LAG at F1, name by name. -/
def pgLagRows : List (String × Bool) :=
  [("X_MPTR", cs.lookup "X_MPTR" == some (ptrAddr poseidonPv.memory.xMptr)),
   ("X_N_MPTR", cs.lookup "X_N_MPTR" == some (ptrAddr poseidonPv.memory.xNMptr)),
   ("L_LAST_MPTR", cs.lookup "L_LAST_MPTR" == some (ptrAddr poseidonPv.memory.lLastMptr)),
   ("L_BLIND_MPTR", cs.lookup "L_BLIND_MPTR" == some (ptrAddr poseidonPv.memory.lBlindMptr)),
   ("L_0_MPTR", cs.lookup "L_0_MPTR" == some (ptrAddr poseidonPv.memory.l0Mptr)),
   ("INSTANCE_EVAL_MPTR",
     cs.lookup "INSTANCE_EVAL_MPTR" == some (ptrAddr poseidonPv.memory.instanceEvalMptr))]

#eval pgLagRows.filter (fun r => !r.2)   -- expect []

/-- PG-CONSTS-TP at F1, name by name. -/
def pgTpRows : List (String × Bool) :=
  let M := poseidonPv.memory
  [("THETA_MPTR", cs.lookup "THETA_MPTR" == some (ptrAddr M.thetaMptr)),
   ("BETA_MPTR", cs.lookup "BETA_MPTR" == some (ptrAddr M.betaMptr)),
   ("GAMMA_MPTR", cs.lookup "GAMMA_MPTR" == some (ptrAddr M.gammaMptr)),
   ("TRASH_CHALLENGE_MPTR", cs.lookup "TRASH_CHALLENGE_MPTR" == some (ptrAddr M.trashChallengeMptr)),
   ("Y_MPTR", cs.lookup "Y_MPTR" == some (ptrAddr M.yMptr)),
   ("X_MPTR", cs.lookup "X_MPTR" == some (ptrAddr M.xMptr)),
   ("X1_MPTR", cs.lookup "X1_MPTR" == some (ptrAddr M.x1Mptr)),
   ("X2_MPTR", cs.lookup "X2_MPTR" == some (ptrAddr M.x2Mptr)),
   ("X3_MPTR", cs.lookup "X3_MPTR" == some (ptrAddr M.x3Mptr)),
   ("X4_MPTR", cs.lookup "X4_MPTR" == some (ptrAddr M.x4Mptr)),
   ("ADVICE_COMMS_MPTR_BASE",
     cs.lookup "ADVICE_COMMS_MPTR_BASE" == some (ptrAddr M.adviceCommsMptrBase)),
   ("LOOKUP_M_COMMS_MPTR_BASE",
     cs.lookup "LOOKUP_M_COMMS_MPTR_BASE" == some (ptrAddr M.lookupMCommsMptrBase)),
   ("PERM_Z_COMMS_MPTR_BASE",
     cs.lookup "PERM_Z_COMMS_MPTR_BASE" == some (ptrAddr M.permZCommsMptrBase)),
   ("LOOKUP_HELPER_COMMS_MPTR_BASE",
     cs.lookup "LOOKUP_HELPER_COMMS_MPTR_BASE" == some (ptrAddr M.lookupHelperCommsMptrBase)),
   ("LOOKUP_Z_COMMS_MPTR_BASE",
     cs.lookup "LOOKUP_Z_COMMS_MPTR_BASE" == some (ptrAddr M.lookupZCommsMptrBase)),
   ("TRASHCAN_COMMS_MPTR_BASE",
     cs.lookup "TRASHCAN_COMMS_MPTR_BASE" == some (ptrAddr M.trashcanCommsMptrBase)),
   ("QUOTIENT_LIMB_COMMS_MPTR_BASE",
     cs.lookup "QUOTIENT_LIMB_COMMS_MPTR_BASE" == some (ptrAddr M.quotientLimbCommsMptrBase)),
   ("REVERSED_EVALS_MPTR", cs.lookup "REVERSED_EVALS_MPTR" == some (ptrAddr M.reversedEvalsMptr)),
   ("F_COM_MPTR", cs.lookup "F_COM_MPTR" == some (ptrAddr M.fComMptr)),
   ("PI_MPTR", cs.lookup "PI_MPTR" == some (ptrAddr M.piMptr)),
   ("Q_EVAL_CPTR_MPTR", cs.lookup "Q_EVAL_CPTR_MPTR" == some (ptrAddr M.qEvalCptrMptr)),
   ("PROOF_CPTR", cs.lookup "PROOF_CPTR" == some poseidonPv.proofLayout.proofCptr),
   ("NUM_INSTANCE_CPTR", cs.lookup "NUM_INSTANCE_CPTR" == some poseidonPv.proofLayout.proofEnd)]

#eval pgTpRows.filter (fun r => !r.2)   -- expect []

-- PG-NOSHADOW, PG-NEGLAG, PG-G1ID at F1, and PG-FRMOD against the tree's modulus constant.
#eval (cs.lookup "r" == none, decide (2 ≤ poseidonPv.numNegLagranges),
  decide (0x80 ≤ ptrAddr poseidonPv.memory.g1IdentityMptr),
  cs.lookup "FR_MODULUS" == some frModulusConstant)   -- expect (true, true, true, true)

-- PG-PCS-EMIT at F1 TODAY: does the PCS emitter produce a slice at the fixture's plan view?
#eval (GenAst.emitPcsFromPlan poseidonPv).length
#eval match Midfall.Lowering.GenAstPcs.computationsAst poseidonPv.meta_ poseidonPv.dat
    poseidonPv.memory poseidonPv.truncatedChallenges false with
  | .ok bs => s!"ok, {bs.length} blocks"
  | .error _ => "FAULT"

/-! ### W12 for `tp_events_slots` (the transcript-parser child ROW.TP.6) -/

def slotBit : WireSlot → Bool
  | .g1 => true
  | .fr => false

/-- The parser's read schedule at a plan view, as bits. -/
def scheduleBits (pv : PlanView) : List Bool :=
  ((tpEvents pv.numInstances pv.userPhases pv.numLookups pv.numPermutationZs pv.lookupHPlusAcc
    pv.numTrashcans pv.truncatedChallenges pv.proofLayout).filterMap TEv.slot?).map slotBit

/-- The layout's slot list, as bits. -/
def layoutBits (L : ProofCalldataLayout) : List Bool :=
  (RepackedProofLayoutPlan.fromProofLayout L).slots.map slotBit

-- WITNESS: at F1 the two lists are equal (and not empty).
#eval (scheduleBits poseidonPv == layoutBits poseidonPv.proofLayout,
  (scheduleBits poseidonPv).length, (layoutBits poseidonPv.proofLayout).length)
theorem tp_events_slots_F1 :
    scheduleBits poseidonPv = layoutBits poseidonPv.proofLayout := by native_decide

-- FALSIFIER 1: a plan view whose lookup count is zero skips the lookup-m section.
#eval scheduleBits (GenAst.withNumLookups 0 poseidonPv) == layoutBits poseidonPv.proofLayout
theorem tp_events_slots_falsifier :
    scheduleBits (GenAst.withNumLookups 0 poseidonPv) ≠ layoutBits poseidonPv.proofLayout := by
  native_decide

-- FALSIFIER 2: the emitter itself moves with the same mutation (the mutated plan view prints a different slice), so the falsifier is about the emitter's output and not about `tpEvents`.
#eval ((GenAst.emitTranscriptParser poseidonPv).length,
  (GenAst.emitTranscriptParser (GenAst.withNumLookups 0 poseidonPv)).length)

/-! ### The schedule and the emitter agree on what a walk is (sanity of `tpEvents`) -/

-- Number of `g1WalkLoop`/absorb sites the emitter prints against the walks of the schedule: printed top-level statements, and frames scheduled.
#eval ((GenAst.emitTranscriptParser poseidonPv).length,
  (scheduleBits poseidonPv).filter id |>.length, (scheduleBits poseidonPv).filter (!·) |>.length)

end Midfall.LoweringV2.V3.Gen.Witness
