import Midfall.Instances.PoseidonValid
import Midfall.Generator.Vk
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldCompute
set_option autoImplicit false

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.LoweringV2 Midfall.Lowering
open Midfall.Generator.ContractKats Midfall.Generator.VerifierPartialKats

namespace PlanProbe

def pn (p : Ptr) : Nat := Value.asUsizeNat p.value

/-! ## A. The text gate: what does the Lean port print with NOTHING from the artifact
       except (i) the VK payload parse and (ii) the quotient blocks/program? -/

-- A1. PCS lines: ported `computations` at the plan's (meta, data, memory) vs artifact-sliced.
#eval poseidonM.pcsComputations == pcsDeployedComputations poseidonVerifierDump
#eval (poseidonM.pcsComputations.map List.length,
       (pcsDeployedComputations poseidonVerifierDump).map List.length)

-- A2. whole file from the model alone (partsOf = Program.lean's own, no artifact part)
def selfRender : String := renderHalo2Verifier (rootCtxOfVerifier poseidonM) (partsOf poseidonM)
def diffLines (a b : String) : List (Nat × String × String) :=
  ((a.splitOn "\n").zip (b.splitOn "\n")).zipIdx.filterMap fun ((x, y), i) =>
    if x == y then none else some (i + 1, x, y)
#eval (selfRender == poseidonVerifierDump, selfRender.length, poseidonVerifierDump.length,
       (selfRender.splitOn "\n").length, (poseidonVerifierDump.splitOn "\n").length)
#eval (diffLines selfRender poseidonVerifierDump).length
#eval (diffLines selfRender poseidonVerifierDump).take 3

-- A3. same with the one build-fact line (BUILD_ID) overridden, PCS from the MODEL (not the artifact)
def selfRenderBuildId : String :=
  let c : PartialCtx := { partialCtxOfVerifier poseidonM with
    buildId := Midfall.Generator.poseidonCtx.buildId }
  let rc : RootCtx := { base := c, abiSelectorBytes := poseidonM.abiSelectorBytes,
                        abiProofHeadOffset := poseidonM.abiProofHeadOffset,
                        abiInstancesHeadCptr := poseidonM.abiInstancesHeadCptr }
  renderHalo2Verifier rc
    { (partsOf poseidonM) with constants := renderConstants c }
#eval (selfRenderBuildId == poseidonVerifierDump, (diffLines selfRenderBuildId poseidonVerifierDump).length)
#eval (diffLines selfRenderBuildId poseidonVerifierDump).take 3

/-! ## B. meta_data_for_stable_static_layout on the exported constraint system -/

def envB : VkBuildEnv Unit :=
  { newVerifierMemoryLayout := VerifierMemoryLayout.new
    compactQuotientProgramFor := fun _ _ => .error (Fault.panic "scratch: unported")
    quotientProgramPlan := fun _ _ => .error (Fault.panic "scratch: unported")
    buildQuotientProgramItems := fun _ => .error (Fault.panic "scratch: unported") }

/-- the RAW meta, i.e. `ConstraintSystemMeta.new` (numPointSets = 0) -/
def rawMeta : ConstraintSystemMeta := poseidonMeta

def inputsB : VerifierBuildInputs Yul.blsR G₁z Unit :=
  { params := { gLagrange := [], g2 := (), sG2 := () }
    vk := poseidonVkExec
    numInstances := 1
    numCommittedInstances := 1
    accEncoding := none
    meta_ := rawMeta }

def stable : Except Fault (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) :=
  metaDataForStableStaticLayout Features.solidity envB inputsB poseidonVkGen

#eval (rawMeta.numPointSets, rawMeta.numDummyEvals, rawMeta.numEvals)
#eval match stable with
  | .ok (vkMptr, m, _, mem) =>
      s!"ok vkMptr={pn vkMptr} (0x2900={0x2900}) numPointSets={m.numPointSets} numDummyEvals={m.numDummyEvals} numEvals={m.numEvals} mem.vkMptr={pn mem.vkMptr}"
  | .error (Fault.panic s) => "PANIC " ++ s
  | .error _ => "ERR"

/-- the proof layout the generator derives from the POST-PROCESSED meta -/
def stableLayout : Except Fault ProofCalldataLayout := do
  let (_, m, _, _) ← stable
  ProofCalldataLayout.fromProtocol m.protocol abiVerifyProofProofCptr m.numEvals m.numPointSets

#eval match stableLayout with
  | .ok l => s!"proofLen={l.proofLen} proofEnd={l.proofEnd} planProofLen={poseidonPlanV2.proofLayout.proofLen} planProofEnd={poseidonPlanV2.proofLayout.proofEnd}"
  | .error _ => "ERR"

-- frozen clause 1 at the faithful meta: false; frozen clause 2 at the faithful meta: true
#eval match stable with
  | .ok (_, m, _, _) => (m == rawMeta, m == rawMeta.setNumPointSets 3)
  | .error _ => (false, false)

def pcsReq : Except Fault PcsMemoryRequirements := do
  let (_, m, d, _) ← stable
  memoryRequirements m d

#eval match pcsReq with
  | .ok r => pcsMemoryRequirementsDebug r
  | .error _ => "ERR"
#eval pcsMemoryRequirementsDebug poseidonPlanV2.pcsMemoryRequirements

end PlanProbe
