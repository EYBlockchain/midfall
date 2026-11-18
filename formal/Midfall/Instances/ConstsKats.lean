/-
  Midfall.Instances.ConstsKats — OBJ.4's Accept line, as gates (D-P17: instance facts live here).

  `Midfall/LoweringV2/Consts.lean` proves the lookup lemmas for EVERY render and cannot print anything
  at the fixture without importing `Midfall/Instances/` — which would make a theorem-bearing file
  depend on a concrete model, and the Instances-confinement gate in checks.sh forbids exactly that. So
  the measurements live here and the proofs live there.

  THE CARD'S ACCEPT LINE, ITEM BY ITEM:
  * `constsCoherent poseidonPv poseidonM` prints true, with both tables 90 long;
  * FALSIFIERS print false: `transcriptMptr + 32` in the plan view, `proofEnd + 32` in the plan
    view, `verifierReturnMptr := 0x80` in the model;
  * and the one perturbation that CANNOT be caught, printed as data rather than hidden in a
    docstring: `constructorG1msmSmokeGas + 1` leaves the clause TRUE, because the renderer and
    `expectedConsts` read the same `Model` field, so both sides of conjunct 3 move together. The same
    holds for `templateConstants.gas` and `accRhsMsmGas`. What conjunct 3 CAN catch is a disagreement
    between the table and the PLAN VIEW, and the three falsifiers above are one of each kind: a
    transcript address, a calldata pointer, a return address.

  EVERY GATE IS A ONE-LINE `#eval <name>_ok -- expect <v>` because kat_gate.py's regex is line-based:
  a multi-line `#eval` prints but is NOT a gate, and an ungated print is a report wearing a gate's
  clothes (the reason P-GATEINTEG exists). Fifteen gates, each a named `Bool`.

  NO `sorry` and NO `native_decide` in this file: every gate is a plain `Bool` computation and the
  lemmas it exercises are in `Consts.lean`.
-/
import Midfall.LoweringV2.Consts
import Midfall.Instances.PoseidonValid
import Midfall.Instances.PoseidonV2

namespace Midfall.Instances.ConstsKats

open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonValid Midfall.Instances.PoseidonV2

/-- The plan view with its transcript base moved 32 bytes up: a table/plan-view disagreement. -/
def pvShifted : PlanView :=
  { poseidonPv with memory := { poseidonPv.memory with
      transcriptMptr := poseidonPv.memory.transcriptMptr + 32 } }

/-- The plan view with the calldata tail moved 32 bytes up: same kind, different window. -/
def pvLayout : PlanView :=
  { poseidonPv with proofLayout := { poseidonPv.proofLayout with
      proofEnd := poseidonPv.proofLayout.proofEnd + 32 } }

/-- The MODEL's own memory moved under the plan view: the return window. -/
def mRet : Model := { poseidonM with memory := { poseidonM.memory with
    verifierReturnMptr := 0x80 } }

/-- A number ONLY the model carries. Not falsifiable by this clause, and the gate says so. -/
def mGas : Model := { poseidonM with
    constructorG1msmSmokeGas := poseidonM.constructorG1msmSmokeGas + 1 }

-- 1. THE CLAUSE HOLDS AT THE FIXTURE, and the two tables are the same length (90, 90).
def coherent_ok : Bool := constsCoherent poseidonPv poseidonM
#eval coherent_ok                                                           -- expect true
def tableLengths_ok : Bool :=
  (expectedConsts poseidonPv poseidonM).length == (constTableOf poseidonM).length
  && (constTableOf poseidonM).length == 90
#eval tableLengths_ok                                                       -- expect true

-- 2. the five conjuncts separately, so a regression names itself
def conj12_ok : Bool := poseidonM.quotientDirect.isNone && constLinesLiteral poseidonM
#eval conj12_ok                                                             -- expect true
def conj4_nodup_ok : Bool := decide (((expectedConsts poseidonPv poseidonM).map Prod.fst).Nodup)
#eval conj4_nodup_ok                                                        -- expect true
def conj5_reads_ok : Bool := (progConstNames poseidonPv poseidonM).all fun x =>
  ((expectedConsts poseidonPv poseidonM).map Prod.fst).contains x
#eval conj5_reads_ok                                                        -- expect true

-- 3. FALSIFIERS: a plan-view perturbation reddens the clause
def fals_transcript_ok : Bool := constsCoherent pvShifted poseidonM
#eval fals_transcript_ok                                                    -- expect false
def fals_proofEnd_ok : Bool := constsCoherent pvLayout poseidonM
#eval fals_proofEnd_ok                                                      -- expect false
def fals_returnMptr_ok : Bool := constsCoherent poseidonPv mRet
#eval fals_returnMptr_ok                                                    -- expect false

-- 4. THE MODEL-ONLY NUMBER IS NOT FALSIFIABLE HERE (the header's claim, as data)
def modelOnly_notFalsifiable_ok : Bool := constsCoherent poseidonPv mGas
#eval modelOnly_notFalsifiable_ok                                           -- expect true

-- 5. THE FIVE UNCONDITIONAL LOOKUPS at the fixture — the conclusions of Consts.lean section 3,
--    evaluated: no `native_decide`, no string parsing, each value read off the plan view it must
--    agree with.
def lookup_uncond5_ok : Bool :=
  (expectedConsts poseidonPv poseidonM).lookup "VK_MPTR" == some (ptrAddr poseidonPv.memory.vkMptr)
  && (expectedConsts poseidonPv poseidonM).lookup "RETURN_MPTR"
      == some poseidonPv.memory.verifierReturnMptr
  && (expectedConsts poseidonPv poseidonM).lookup "TRANSCRIPT_MPTR"
      == some poseidonPv.memory.transcriptMptr
  && (expectedConsts poseidonPv poseidonM).lookup "NUM_INSTANCE_CPTR"
      == some poseidonPv.proofLayout.proofEnd
  && (expectedConsts poseidonPv poseidonM).lookup "FR_MODULUS" == some frModulusConstant
#eval lookup_uncond5_ok                                                     -- expect true

-- 6. THE THREE GUARDED LOOKUPS, under the arm the render actually has
def vkArm_present_ok : Bool := poseidonM.expectedVkCodehash.isSome
#eval vkArm_present_ok                                                      -- expect true
def lookup_vkArm3_ok : Bool :=
  (expectedConsts poseidonPv poseidonM).lookup "EXPECTED_VK_PAYLOAD_LENGTH"
      == some poseidonPv.vk.len
  && (expectedConsts poseidonPv poseidonM).lookup "EXPECTED_VK_LENGTH"
      == some poseidonPv.vk.runtimeBytes.size
  && (expectedConsts poseidonPv poseidonM).lookup "EXPECTED_VK_CODEHASH_WORD"
      == some (keccak256 poseidonPv.vk.runtimeBytes).toNat
#eval lookup_vkArm3_ok                                                      -- expect true

-- 7. THE DATA FACT the guarded lookups rest on, at the fixture
def runtimeBytes_size_ok : Bool := poseidonPv.vk.runtimeBytes.size == poseidonPv.vk.len + 1
#eval runtimeBytes_size_ok                                                  -- expect true

-- 8. THE RESIDUAL, printed so it cannot be forgotten: the two pins that are NOT table facts hold at
--    the fixture, but for a reason this clause has nothing to do with. `numInst` is a
--    model/configuration agreement; `disjoint` is a layout inequality.
def residual_numInst_ok : Bool := poseidonPv.numInstances == poseidonConfig.numInstances
#eval residual_numInst_ok                                                   -- expect true
def residual_disjoint_ok : Bool :=
  ptrAddr poseidonPv.memory.g1IdentityMptr + 128 <= ptrAddr poseidonPv.memory.vkMptr
  || ptrAddr poseidonPv.memory.vkMptr + poseidonPv.vk.len
      <= ptrAddr poseidonPv.memory.g1IdentityMptr
#eval residual_disjoint_ok                                                  -- expect true

end Midfall.Instances.ConstsKats
