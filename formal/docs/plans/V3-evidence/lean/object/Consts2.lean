import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Program
set_option autoImplicit false

/-!
  PROPOSED: `formal/Midfall/LoweringV2/Consts.lean` (new, refinable until the next re-pin).
  ONE decidable clause replacing vkPins.vkMptr, vkPins.payloadLen, vkProgressPins.vkLen,
  vkProgressPins.vkHash, Valid.transcriptMptr's lookup half, D-P46's table half and D-P48.
-/

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

/-- Byte address of a layout pointer (same adapter as `Inv.ptrAddr`). -/
def cAddr (q : Ptr) : Nat := Value.asUsizeNat q.value

/-- THE CONTRACT CONSTANT TABLE AS DATA, in the order of `templates/partials/verifier/Constants.sol`.
    Every address is read from the PLAN VIEW (the record `Inv` reads), every length from the plan
    view's payload, every calldata pointer from the plan view's proof layout. Only the build-time
    numbers that the plan view does not carry come from the model: the three optional-arm selectors
    (`expectedVkCodehash`, `quotientExternal`/`expectedQuotient*`, `expectedHasAccumulator`), the
    gas schedule and the two derived gas numbers. The 14 trailing entries are template literals. -/
def expectedConsts (pv : PlanView) (m : Model) : List (String × Nat) :=
  let M := pv.memory
  let H := m.vkHeader
  let hdr (w : Nat) : Nat := cAddr (Ptr.add M.vkMptr w)
  (match m.expectedVkCodehash with
    | some _ =>
        [ ("EXPECTED_VK_PAYLOAD_LENGTH", pv.vk.len)
        , ("EXPECTED_VK_LENGTH", pv.vk.len + 1)
        , ("EXPECTED_VK_CODEHASH_WORD", (keccak256 pv.vk.runtimeBytes).toNat) ]
    | none => []) ++
  (match m.quotientExternal, m.expectedQuotientCodehash with
    | some _, some h =>
        [ ("EXPECTED_QUOTIENT_LENGTH", m.expectedQuotientLen.getD 0)
        , ("EXPECTED_QUOTIENT_CODEHASH_WORD", h.toNat) ]
    | _, _ => []) ++
  [ ("PROOF_LEN_CPTR", pv.proofLayout.proofCptr - 32)
  , ("PROOF_CPTR", pv.proofLayout.proofCptr)
  , ("NUM_INSTANCE_CPTR", pv.proofLayout.proofEnd)
  , ("INSTANCE_CPTR", pv.proofLayout.proofEnd + 32)
  , ("TRANSCRIPT_MPTR", M.transcriptMptr)
  , ("RETURN_MPTR", M.verifierReturnMptr)
  , ("VK_MPTR", cAddr M.vkMptr)
  , ("VK_DIGEST_MPTR", hdr H.vkDigest)
  , ("NUM_INSTANCES_MPTR", hdr H.numInstances)
  , ("K_MPTR", hdr H.k)
  , ("N_INV_MPTR", hdr H.nInv)
  , ("OMEGA_MPTR", hdr H.omega)
  , ("OMEGA_INV_MPTR", hdr H.omegaInv)
  , ("OMEGA_INV_TO_L_MPTR", hdr H.omegaInvToL)
  , ("HAS_ACCUMULATOR_MPTR", hdr H.hasAccumulator)
  , ("ACC_OFFSET_MPTR", hdr H.accOffset)
  , ("NUM_ACC_LIMBS_MPTR", hdr H.numAccLimbs)
  , ("NUM_ACC_LIMB_BITS_MPTR", hdr H.numAccLimbBits)
  , ("G1_BASE_MPTR", hdr H.g1Base)
  , ("G2_BASE_MPTR", hdr H.g2Base)
  , ("NEG_S_G2_BASE_MPTR", hdr H.negSG2Base)
  , ("CHALLENGE_MPTR", cAddr M.challengeMptr)
  , ("THETA_MPTR", cAddr M.thetaMptr)
  , ("BETA_MPTR", cAddr M.betaMptr)
  , ("GAMMA_MPTR", cAddr M.gammaMptr)
  , ("TRASH_CHALLENGE_MPTR", cAddr M.trashChallengeMptr)
  , ("Y_MPTR", cAddr M.yMptr)
  , ("X_MPTR", cAddr M.xMptr)
  , ("X1_MPTR", cAddr M.x1Mptr)
  , ("X2_MPTR", cAddr M.x2Mptr)
  , ("X3_MPTR", cAddr M.x3Mptr)
  , ("X4_MPTR", cAddr M.x4Mptr)
  , ("F_COM_MPTR", cAddr M.fComMptr)
  , ("PI_MPTR", cAddr M.piMptr)
  , ("ACC_LHS_MPTR", cAddr M.accLhsMptr)
  , ("ACC_RHS_MPTR", cAddr M.accRhsMptr)
  , ("X_N_MPTR", cAddr M.xNMptr)
  , ("X_N_MINUS_1_INV_MPTR", cAddr M.xNMinus1InvMptr)
  , ("L_LAST_MPTR", cAddr M.lLastMptr)
  , ("L_BLIND_MPTR", cAddr M.lBlindMptr)
  , ("L_0_MPTR", cAddr M.l0Mptr)
  , ("INSTANCE_EVAL_MPTR", cAddr M.instanceEvalMptr)
  , ("QUOTIENT_EVAL_MPTR", cAddr M.quotientEvalMptr)
  , ("QUOTIENT_MPTR", cAddr M.quotientMptr)
  , ("F_EVAL_MPTR", cAddr M.fEvalMptr)
  , ("V_MPTR", cAddr M.vMptr)
  , ("FINAL_COM_MPTR", cAddr M.finalComMptr)
  , ("PAIRING_LHS_MPTR", cAddr M.pairingLhsMptr)
  , ("PAIRING_RHS_MPTR", cAddr M.pairingRhsMptr)
  , ("ROT_POINTS_MPTR", cAddr M.rotPointsMptr)
  , ("X1_POWERS_MPTR", cAddr M.x1PowersMptr)
  , ("Q_COM_MPTR", cAddr M.qComMptr)
  , ("Q_EVAL_SET_MPTR", cAddr M.qEvalSetMptr)
  , ("Q_EVAL_CPTR_MPTR", cAddr M.qEvalCptrMptr)
  , ("G1_IDENTITY_MPTR", cAddr M.g1IdentityMptr)
  , ("REVERSED_EVALS_MPTR", cAddr M.reversedEvalsMptr)
  , ("SELECTOR_ACC_MPTR", M.selectorAccMptr)
  , ("QUOTIENT_RETURN_MPTR", M.quotientReturnMptr)
  , ("BATCH_INV_SCRATCH_MPTR", M.batchInvertScratchMptr)
  , ("LAGRANGE_DENOMS_MPTR", M.lagrangeDenomsMptr)
  , ("TRACE_U256_MPTR", M.traceU256Mptr)
  , ("ADVICE_COMMS_MPTR_BASE", cAddr M.adviceCommsMptrBase)
  , ("LOOKUP_M_COMMS_MPTR_BASE", cAddr M.lookupMCommsMptrBase)
  , ("PERM_Z_COMMS_MPTR_BASE", cAddr M.permZCommsMptrBase)
  , ("LOOKUP_HELPER_COMMS_MPTR_BASE", cAddr M.lookupHelperCommsMptrBase)
  , ("LOOKUP_Z_COMMS_MPTR_BASE", cAddr M.lookupZCommsMptrBase)
  , ("TRASHCAN_COMMS_MPTR_BASE", cAddr M.trashcanCommsMptrBase)
  , ("QUOTIENT_LIMB_COMMS_MPTR_BASE", cAddr M.quotientLimbCommsMptrBase)
  , ("G1ADD_GAS", m.templateConstants.gas.g1add)
  , ("G1MSM_GAS_1PAIR", m.templateConstants.gas.g1msmOnePair)
  , ("PAIRING_GAS_2PAIR", m.templateConstants.gas.pairingTwoPair)
  , ("MODEXP_GAS", m.templateConstants.gas.modexp)
  , ("G1MSM_GAS_SMOKE", m.constructorG1msmSmokeGas) ] ++
  (if m.expectedHasAccumulator then [("ACC_RHS_MSM_GAS", m.accRhsMsmGas)] else []) ++
  [ ("ERR_BAD_CALLDATA_SHAPE", 0x1b99e37c)
  , ("ERR_VK_MISMATCH", 0xa447d73e)
  , ("ERR_NON_CANONICAL_SCALAR", 0x77530042)
  , ("ERR_BAD_POINT_ENCODING", 0xf27905ec)
  , ("ERR_PRECOMPILE_FAILED", 0x84e81692)
  , ("ERR_PROOF_REJECTED", 0xc3b0d8cd)
  , ("ERR_QUOTIENT_PROGRAM_INVALID", 0x3cc81b89)
  , ("ERR_MEMORY_LAYOUT_VIOLATED", 0xc9888d23)
  , ("FR_MODULUS", 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
  , ("BLS_P_HI", 0x1a0111ea397fe69a4b1ba7b6434bacd7)
  , ("BLS_P_MINUS_ONE_LO", 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_1", 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84) ]

/-- The names the un-inlined program reads that it does not bind: exactly the contract constants
    plus the two wrapper locals. Includes the ABI guard block, which `mainClosed` omits. -/
def progConstNames (pv : PlanView) (m : Model) : List String :=
  (freeNames (abiGuardBlock m ++ mainAsmRaw pv)).filter
    fun x => x != "vk" && x != "quotientEvaluator"

/-- Every constant line of the rendered `Constants.sol` that declares a `uint256 internal constant`
    has a LITERAL right-hand side (decimal or 0x-hex digits only) - the KAT `Program.lean:55-57`
    asks for and never got. Without it `solConstantLine?` silently mis-parses `sub(0, 0x20)`. -/
def constLinesLiteral (m : Model) : Bool :=
  ((renderConstants (partialCtxOfVerifier m)).splitOn "\n").all fun l =>
    match l.splitOn "uint256 internal constant " with
    | [_, rest] =>
        (match rest.splitOn "=" with
         | [_, rhs] =>
             let v := ((rhs.splitOn ";").headD "").trimAscii.toString
             let digits := if v.startsWith "0x" then (v.drop 2).toString else v
             !digits.isEmpty && digits.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
         | _ => false)
    | _ => true

/-- **THE ONE CONSTANTS-COHERENCE CLAUSE.** Four conjuncts, all computations on the render:
    1. first-headline scope: no Direct lowering (its constant lines are free strings);
    2. every constant line parses as a literal;
    3. the table read back from the rendered text IS the data-level table of the plan view;
    4. no name is declared twice, and every name the program reads is declared. -/
def constsCoherent (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone &&
  constLinesLiteral m &&
  constTableOf m == expectedConsts pv m &&
  ((expectedConsts pv m).map Prod.fst).Nodup &&
  (progConstNames pv m).all fun x => ((expectedConsts pv m).map Prod.fst).contains x

def ConstsCoherent (pv : PlanView) (m : Model) : Prop := constsCoherent pv m = true

/-- What a block proof uses: a table lookup is a lookup in the DATA table. Generic in the render. -/
theorem consts_lookup_of_coherent {pv : PlanView} {m : Model} (h : ConstsCoherent pv m)
    (name : String) :
    (constTableOf m).lookup name = (expectedConsts pv m).lookup name := by
  have h3 : (constTableOf m == expectedConsts pv m) = true := by
    unfold ConstsCoherent constsCoherent at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.2
  rw [eq_of_beq h3]

end Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.LoweringV2 Midfall.Lowering

-- 1. the clause at the fixture
#eval constsCoherent poseidonPv poseidonM
-- 2. its conjuncts, separately
#eval (poseidonM.quotientDirect.isNone, constLinesLiteral poseidonM,
       constTableOf poseidonM == expectedConsts poseidonPv poseidonM,
       decide (((expectedConsts poseidonPv poseidonM).map Prod.fst).Nodup),
       (progConstNames poseidonPv poseidonM).all fun x =>
         ((expectedConsts poseidonPv poseidonM).map Prod.fst).contains x)
#eval ((expectedConsts poseidonPv poseidonM).length, (constTableOf poseidonM).length)
-- 3. which constants the program actually reads (today's AST: 6761 tokens), and how many are unused
#eval (progConstNames poseidonPv poseidonM).length
#eval progConstNames poseidonPv poseidonM
#eval ((expectedConsts poseidonPv poseidonM).map Prod.fst).filter
        (fun n => !(progConstNames poseidonPv poseidonM).contains n)
-- 4. FALSIFIERS: one-literal mutations of the plan view / model redden the clause
def pvShifted : PlanView := { poseidonPv with memory := { poseidonPv.memory with transcriptMptr := poseidonPv.memory.transcriptMptr + 32 } }
#eval constsCoherent pvShifted poseidonM                                   -- expect false
def pvLayout : PlanView := { poseidonPv with proofLayout := { poseidonPv.proofLayout with proofEnd := poseidonPv.proofLayout.proofEnd + 32 } }
#eval constsCoherent pvLayout poseidonM                                    -- expect false
def mGas : Model := { poseidonM with constructorG1msmSmokeGas := poseidonM.constructorG1msmSmokeGas + 1 }
#eval constsCoherent poseidonPv mGas                                       -- TRUE: a model-only number is rendered and expected from the same field
def mRet : Model := { poseidonM with memory := { poseidonM.memory with verifierReturnMptr := 0x80 } }
#eval constsCoherent poseidonPv mRet                                       -- expect false (model memory moved, plan view did not)
-- 5. the pins this clause subsumes, as lookups in the DATA table
#eval ((expectedConsts poseidonPv poseidonM).lookup "VK_MPTR", ptrAddr poseidonPv.memory.vkMptr,
       (expectedConsts poseidonPv poseidonM).lookup "EXPECTED_VK_PAYLOAD_LENGTH", poseidonPv.vk.len,
       (expectedConsts poseidonPv poseidonM).lookup "EXPECTED_VK_LENGTH", poseidonPv.vk.runtimeBytes.size,
       (expectedConsts poseidonPv poseidonM).lookup "RETURN_MPTR",
       (expectedConsts poseidonPv poseidonM).lookup "TRANSCRIPT_MPTR",
       (expectedConsts poseidonPv poseidonM).lookup "NUM_INSTANCE_CPTR", poseidonPv.proofLayout.proofEnd)

-- 6. the generic lookups are provable for EVERY render with no string parsing: by rfl on the data table
example (pv : PlanView) (m : Model) (h : m.expectedVkCodehash = none) (hq : m.quotientExternal = none) :
    (expectedConsts pv m).lookup "TRANSCRIPT_MPTR" = some pv.memory.transcriptMptr := by
  simp [expectedConsts, h, hq, List.lookup]

#print axioms Midfall.LoweringV2.consts_lookup_of_coherent
