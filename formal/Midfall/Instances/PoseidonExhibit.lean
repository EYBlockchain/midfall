-- |
-- Midfall.Instances.PoseidonExhibit
--
-- T3.11 (PLAN-V3, D-P71): **THE W14 EXECUTABLE EXHIBIT - RUN THE THEOREM'S PROGRAM BEFORE PROVING
-- ABOUT IT.** A TEST, NEVER A PREMISE OF A PROOF. Nothing in this file may enter the cone of
-- 'lowering_equivalence_poseidon': there is no theorem here, no 'native_decide', no 'sorry', and the
-- only declarations are 'Bool' / 'IO Bool' gates that 'scripts/kat_gate.py' runs.
--
-- WHAT IT ESTABLISHES, IN ONE LINE. The closed emitted program 'asmOf poseidonPv poseidonM 0 0' -
-- the object OBJ.5 pins at 14,109 tokens and keccak '3149ae4f...bef176' - RUNS on the F1 bundle's
-- real calldata at the OPEN HONEST DIALECT ('Midfall.LoweringV2.honestExec', T3.1) from an
-- entry-like frame, and it returns 'abiTrue'; and a byte-flip mutant of the same calldata does NOT.
-- Both halves are required by W14: an exhibit where every input succeeds says the interpreter is
-- not discriminating.
--
-- THE TWO OUTCOMES, AS MEASURED HERE (fuel 10,000,000; wall time is the 'lake env lean' VM, this
-- host, 2026-11-18):
--
--   REAL calldata (4,484 bytes, the exact bytes of the accepted revm call in evm.json):
--     outcome = Outcome.halt   halted = some (HaltKind.ret,
--       [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1])   = abiTrue   [22.4 s]
--   MUTANT calldata (one bit flipped), the eight gated ones, every one a REVERT and none abiTrue:
--     proof-offset word          bit0 -> revert [27,153,227,124]  ERR_BAD_CALLDATA_SHAPE  [  0 ms]
--     instances-offset word      bit0 -> revert [27,153,227,124]  ERR_BAD_CALLDATA_SHAPE  [  0 ms]
--     proof-length word          bit0 -> revert [27,153,227,124]  ERR_BAD_CALLDATA_SHAPE  [ 53 ms]
--     instance-count word        bit0 -> revert [27,153,227,124]  ERR_BAD_CALLDATA_SHAPE  [ 53 ms]
--     calldata truncated by 1           -> revert [27,153,227,124]  ERR_BAD_CALLDATA_SHAPE [ 53 ms]
--     calldata with a trailing byte     -> revert [27,153,227,124]  ERR_BAD_CALLDATA_SHAPE [ 54 ms]
--     point 0 x pad byte         bit0 -> revert [242,121,5,236]   ERR_BAD_POINT_ENCODING  [ 55 ms]
--     point 10 x pad byte        bit0 -> revert [242,121,5,236]   ERR_BAD_POINT_ENCODING  [ 86 ms]
--
-- THE REVERT PAYLOADS ARE NOT PASTED LITERALS. Each mutant's expected four bytes are computed by
-- 'errPayload' from the render's OWN constant table ('constTableOf poseidonM', the ERR_* codes the
-- emitter splices into every fail), and the gate compares the interpreter's halt against THAT. R-38
-- finding 1 is the failure class this avoids: a gate that compares a constant against a copy of
-- itself cannot see the constant move.
--
-- WHERE THE CALLDATA COMES FROM, AND THE ONE THING THAT IS NOT REPRODUCIBLE. 'fixtureCdM' is
-- 'Midfall.Lowering.repackThenEncode' (Lowering/Calldata.lean:257) applied to the bundle's own
-- 'proof.bin' and the single public instance from 'instances.json', at 'g1AffineCodec' - the card's
-- Needs, spelled as a term. Gate 1 then checks the result BYTE FOR BYTE against the bundle's
-- 'calldata.bin' (and pins its keccak). That answers the question REF.14 was written to ask - the
-- Lean repack-then-encode reproduces the Rust/EVM calldata exactly at this codec - and it is what
-- makes the run 'real calldata' and not a reconstruction. REFUTED-AT-CODEC NOTE: the render's own
-- codec 'poseidonRender.E.g1' is a NONCOMPUTABLE def (PoseidonCoherence's check 3), so the repack
-- cannot be run at it at all; 'g1AffineCodec' is the VM-decodable codec and the gate says so.
--
-- The bundle is ONE PINNED RUN: 'proof.bin' is not reproducible across exporter runs
-- ('blind_quotient_limbs' uses 'OsRng', REF.11), so the calldata inherits that. What is reproducible
-- is the file in the tree, and every hash pinned here (calldata keccak '434221dc...505da3', the
-- 4,484 length) is recomputed from the tracked bytes by this gate, so nothing is pinned that a
-- later run cannot regenerate. 'manifest.sha256' pins the files upstream; 'vk/cs/params/instances'
-- are reproducible, 'proof.bin'/'calldata.bin'/'mutations.json'/'evm.json'/'trace.json' are the
-- run-dependent half.
--
-- WHAT THE EXHIBIT DOES NOT SHOW, STATED RATHER THAN HIDDEN. 'PairingProduct' is 'Bytes -> Bool' and
-- the exhibit runs it at 'fun _ => true': the pairing is a PARAMETER of the statement (T3.1's
-- 'honestExec'), the numerator is not computed in this tree, and the card's Does-not-need names it.
-- So what the gated corpus actually discriminates on is: the program's OWN shape and decode guards
-- (the ABI head words, the length bound, the EIP-2537 canonicality test the transcript parser runs on
-- every point), which the interpreter evaluates on the real bytes - plus the honest precompile
-- VALIDITY rules (EIP-2537 on-curve and r-torsion), which are computed here and not mocked but whose
-- rejection class lands too late to gate (next paragraph). Measured consequence of the mock, and it
-- is the card's guidance verbatim: flipping a bit of the PUBLIC INSTANCE WORD (byte 4452) still returns
-- abiTrue, because the instance reaches the verifier only through the pairing argument the mock
-- answers for (measured: ret abiTrue, 21.8 s). That mutant is therefore NOT in the gated corpus - it
-- is not a rejection - and recording it is the honest bound on what 'a mutant does not reach the
-- intended outcome' means at this commit.
--
-- THE EIGHTH-PLUS-ONE, MEASURED AND DELIBERATELY UNGATED: flipping the LOW BIT of point 0's x (byte
-- 163) leaves a canonical encoding the parser accepts and is refused later, by the EIP-2537 MSM
-- precompile's own on-curve / r-torsion check: revert [132,232,22,146] = ERR_PRECOMPILE_FAILED,
-- measured 6.99 s (a flip of point 0's y behaves the same way, measured 6.94 s). It is not in the
-- gated corpus because the card's acceptance is a KAT that evaluates in at most 30 s and a 7 s mutant
-- next to the 22 s run does not fit inside it. The class is recorded here, with its number, not
-- dropped.
--
-- THE exitScan FORK IS NOT REACHED. This exhibit is a direct 'Interp.run'; it never calls
-- 'Midfall.LoweringV2.exitScan' or the §4 'ExitMeasure.lean' copy, so the 'break'/'continue'-in-a-
-- for-post disagreement between them cannot decide any outcome here.
--
-- THE TWO NAMES Report.lean's '#exhibits' also asks for - 'fixture_leanAccepts_ok' and
-- 'mutants_leanRejects_ok' - are the LEAN verifier's side of the exhibit ('LeanAccepts', i.e.
-- 'verifyMsgs' at the real pairing). They belong to REF.12 (needs the exported trapdoor and
-- 'SrsEncodes'), not to T3.11, and this card does not fake them: after this commit the report reads
-- 2 PRESENT, 2 MISSING.
--
-- WHY THE FIXTURE ARRIVES BY IO. 'proof.bin' and 'calldata.bin' are BINARY, so 'include_str' refuses
-- them; this is the same channel PoseidonCoherence (F.1) uses, with the same two-candidate path list
-- so the gate runs from 'formal/' (kat_gate) and from the repo root alike. A failed read yields the
-- EMPTY bundle and every gate below goes FALSE on empty rather than passing on a default.

import Midfall.Instances.PoseidonValid
import Midfall.Instances.Bls12_381
import Midfall.Instances.ObjectFingerprint
import Midfall.Lowering.Calldata
import Midfall.LoweringV2.HonestExec

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option linter.unusedVariables false

namespace Midfall.Instances.PoseidonExhibit

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonV2 Midfall.Lowering
open Midfall.LoweringV2 Midfall.Yul Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

/-! ## 1. The dialect, the program, the frame -/

/-- **THE PAIRING PRODUCT, MOCKED.** 'honestExec' takes it as a parameter; the numerator is not in
    this tree (the card's Does-not-need). Everything the exhibit discriminates on is computed. -/
def exhibitProduct : PairingProduct := fun _ => true

/-- THE OPEN HONEST DIALECT (T3.1): the executable 'ExecDialect' whose relation is the honest one. -/
abbrev E : ExecDialect := honestExec exhibitProduct

/-- An explicit fuel bound, not a claim of termination. 'outOfFuel' and 'stuck' both read as no-halt
    below, so neither can pass a gate. -/
def fuel : Nat := 10000000

/-- **THE OBJECT THE HEADLINE IS ABOUT**: the closed program at the deployment addresses 0 0, the
    same term OBJ.5 fingerprints. -/
def exhibitProg : YulBlock := asmOf poseidonPv poseidonM 0 0

/-- The VK address the frame deploys the render's runtime at. 0 keeps the exhibit on the pinned
    object; 'DeploymentV2.disjoint' only asks that it not be a precompile address. -/
def vkAddr : U256 := 0

def vkRuntimeBytes : List UInt8 := poseidonPlanV2.vk.runtimeBytes.data.toList

/-- The deployment world, in the shape 'DeploymentV2' asks for: the VK runtime at 'vkAddr', its
    codehash under the frame's own hash, zero call value. Same construction as
    'Instances/R72GateProbe.lean's 'probeW'. -/
def exhibitW : ExecEnv :=
  { callvalue := 0,
    keccakOf := hashOfBytes keccak256,
    extCodeOf := fun a => if a = vkAddr then vkRuntimeBytes else [],
    extCodeHashOf := fun a =>
      if (if a = vkAddr then vkRuntimeBytes else []).length = 0 then 0
      else hashOfBytes keccak256 (if a = vkAddr then vkRuntimeBytes else []) }

/-- An arbitrary shell layout: the exhibit never reads it (same as 'R72GateProbe.probeLyt'). -/
def exhibitLyt : EVM.Layout := { code := [], dataOffset := fun _ => 0, dataSize := fun _ => 0 }

/-- **THE ENTRY-LIKE FRAME**, built by the theorem's own 'initState' with 'mem₀ := fun _ => 0' -
    exactly the state 'entryFrame_inhabited' (Blocks.lean:865) produces for a selector-carrying
    calldata in a zero-value world. -/
def entryState (cd : Bytes) : EvmState := initState exhibitW exhibitLyt keccak256 cd (fun _ => 0)

/-- The halt the run left behind, or 'none' if it did not halt (stuck, out of fuel, or no result). -/
def haltOf (cd : Bytes) : Option (HaltKind × List UInt8) :=
  match Interp.run E fuel exhibitProg (entryState cd) with
  | .ok (_, st, _) => st.halted
  | _ => none

/-- THE INTENDED OUTCOME: 'return(abiTrue)', the payload 'Bridge.abiTrue' the trace-return block
    stores - not a copy of it. -/
def returnsAbiTrue (cd : Bytes) : Bool := haltOf cd == some (HaltKind.ret, abiTrue)

/-- A revert carrying exactly the four bytes the named ERR_* constant produces. -/
def revertsToSelector (cd : Bytes) (sel : List UInt8) : Bool :=
  sel != [] && haltOf cd == some (HaltKind.revert, sel)

/-! ## 2. The fixture calldata, as a Lean term -/

/-- The F1 bundle (REF.11, schema 2). Two candidates so the gate runs from 'formal/' and from the
    repo root, exactly as PoseidonCoherence does. -/
def bundleDirs : List String :=
  ["fixtures/conformance/poseidon-testsrs", "formal/fixtures/conformance/poseidon-testsrs"]

def readBinOrEmpty (p : String) : IO Bytes := do
  try IO.FS.readBinFile p catch _ => pure Bytes.empty

def readBinFirst (cs : List String) : IO Bytes :=
  cs.foldl (fun acc p => acc >>= fun got => if got.size > 0 then pure got else readBinOrEmpty p)
    (pure Bytes.empty)

/-- proof.bin: the 2,640 compressed proof bytes of the pinned run. -/
def proofBin : IO Bytes := readBinFirst (bundleDirs.map (· ++ "/proof.bin"))

/-- calldata.bin: the exact bytes of the accepted revm call (evm.json: calldata_sha256). -/
def calldataBin : IO Bytes := readBinFirst (bundleDirs.map (· ++ "/calldata.bin"))

abbrev Rmod : ℕ := Midfall.Assumptions.r
local instance factR : Fact (Nat.Prime Rmod) := inferInstance

/-- The repack slot schedule the deployed plan implies (same term as PoseidonCoherence's). -/
def repackedPlan : RepackedProofLayoutPlan :=
  RepackedProofLayoutPlan.fromProofLayout poseidonPlanV2.proofLayout

/-- instances.json 'public[0]' - the one public instance the fixture proves about. -/
def fixtureInstanceWord : Nat :=
  0x5bc80c2903b88ec11dbfd6aea02fa8405d5e5a12dda02dd18e7d1a0e7ac8e43c

def fixtureInstances : Array (Fr Rmod) := #[Nat.cast fixtureInstanceWord]

/-- **THE FIXTURE CALLDATA AS A LEAN TERM**: 'Lowering.repackThenEncode' (Calldata.lean:257) on the
    bundle's own proof and instance. '.error' yields the empty bytes, which gate 1 then refuses. -/
def fixtureCdM : IO Bytes := do
  let π ← proofBin
  match repackThenEncode (p := Rmod) poseidonConfig.numInstances repackedPlan g1AffineCodec π
      fixtureInstances with
  | .ok cd => pure cd
  | .error _ => pure Bytes.empty

/-! ## 3. The mutants -/

/-- Flip one bit of one byte of the calldata. -/
def xorByte (cd : Bytes) (i : Nat) (m : UInt8) : Bytes :=
  ByteArray.mk (List.toArray
    (cd.data.toList.take i ++ [UInt8.xor cd.data.toList[i]! m] ++ cd.data.toList.drop (i + 1)))

/-- The calldata with its last 'n' bytes removed. -/
def dropLast (cd : Bytes) (n : Nat) : Bytes :=
  ByteArray.mk (List.toArray (cd.data.toList.take (cd.size - n)))

/-- The calldata with one zero byte appended. -/
def withTrailingByte (cd : Bytes) : Bytes :=
  ByteArray.mk (List.toArray (cd.data.toList ++ [0]))

/-- The four revert bytes the render's own constant table assigns to an ERR_* name: the emitted fail
    stores 'sel <<< 224' and returns 4, so the payload is the big-endian low 32 bits of the code. -/
def errPayload (name : String) : List UInt8 :=
  match (constTableOf poseidonM).find? fun p => p.1 == name with
  | some (_, v) => (natToBytesBE (v % 2 ^ 32) 4).data.toList
  | none => []

/-- The proof region starts at byte 100: selector (4) + three 32-byte head words, and each repacked
    G1 point is 128 bytes (16 zero pad + 48 x + 16 zero pad + 48 y). -/
def proofStart : Nat := 100
def g1Slot : Nat := 128

/-- THE MUTANT CORPUS: label, mutated calldata, expected revert payload. Every entry is a one-bit
    flip or a one-byte shape change of the REAL calldata, and every expected payload is computed
    from the constant table. -/
def mutantsOf (cd : Bytes) : List (String × Bytes × List UInt8) :=
  let shape := errPayload "ERR_BAD_CALLDATA_SHAPE"
  let point := errPayload "ERR_BAD_POINT_ENCODING"
  [("head.proofOffset.bit0", xorByte cd 35 0x01, shape),
   ("head.instancesOffset.bit0", xorByte cd 67 0x01, shape),
   ("head.proofLength.bit0", xorByte cd 99 0x01, shape),
   ("tail.instanceCount.bit0", xorByte cd 4451 0x01, shape),
   ("shape.truncated-by-1", dropLast cd 1, shape),
   ("shape.trailing-byte", withTrailingByte cd, shape),
   ("proof.point0.x-pad.bit0", xorByte cd proofStart 0x01, point),
   ("proof.point10.x-pad.bit0", xorByte cd (proofStart + 10 * g1Slot + 8) 0x01, point)]

/-! ## 4. The gates -/

/-- **GATE 1 - THE CALLDATA IS THE FIXTURE'S.** The Lean repack-then-encode reproduces 'calldata.bin'
    byte for byte (4,484 bytes, keccak pinned), and it carries the 'verifyProof' selector the entry
    frame demands. 34 ms. -/
def fixtureCalldata_isTheBundleBytes_ok : IO Bool := do
  let cd ← fixtureCdM
  let rust ← calldataBin
  pure (cd.size == 4484 && rust.size == 4484 && cd.data.toList == rust.data.toList &&
    Midfall.keccak256 cd == 0x434221dcb184cdb7e1145de7fe684d1e777f04b035ddfea8fbeff75680505da3 &&
    bytesTake cd 0 4 == some fnSigVerifyProof)
#eval fixtureCalldata_isTheBundleBytes_ok -- expect true

/-- **GATE 2 - THE FRAME IS THE THEOREM'S ENTRY FRAME, AS FAR AS A 'Bool' CAN SAY.** Selector
    ('EntryFrame.selector'), zero call value ('EntryFrame.callvalue'), the VK runtime at the address
    the program reads and its codehash under the frame's own hash ('DeploymentV2.vkCode'/'vkHash'/
    'vkNonEmpty'), a free memory pointer of 0 with the TRANSCRIPT_MPTR constant present (the
    'EntryFrame.fmp' witness 'entryFrame_inhabited' uses: 'loadWord st.memory 0x40 = 0 ≤ t'), the
    D-P64 length bound ('EntryFrame.cdSize'), and 'DeploymentV2.disjoint'. -/
def entryFrame_shape_ok : IO Bool := do
  let cd ← fixtureCdM
  let st := entryState cd
  pure (bytesTake cd 0 4 == some fnSigVerifyProof && st.env.callvalue == 0 &&
    exhibitW.extCodeOf vkAddr == vkRuntimeBytes && vkRuntimeBytes.length != 0 &&
    loadWord st.memory 0x40 == 0 && cd.size < 2 ^ 256 &&
    ! ([0x0b, 0x0c, 0x0f, 0x05].contains (accountKey vkAddr)) &&
    (constTableOf poseidonM).any fun p => p.1 == "TRANSCRIPT_MPTR")
#eval entryFrame_shape_ok -- expect true

/-- **GATE 3 - THE PROGRAM IS THE PINNED OBJECT.** 'exhibitProg' is structurally the program OBJ.5
    fingerprints ('asmOf poseidonPv poseidonM 0 0'), so the run below is a run of the object the
    headline quantifies over and not of a nearby program. -/
def exhibitProg_isThePinnedObject_ok : Bool :=
  SyntaxEq.stmtsBeq exhibitProg ObjectFingerprint.objectProgram &&
    SyntaxEq.stmtsBeq exhibitProg (asmOf poseidonPv poseidonM 0 0)
#eval exhibitProg_isThePinnedObject_ok -- expect true

/-- **GATE 4 - THE FIXTURE RUN REACHES THE INTENDED OUTCOME.** The emitted program, at the open
    honest dialect, from the entry-like frame, on the real calldata: 'return(abiTrue)'. Measured
    22.4 s at fuel 10,000,000; 'stuck' and 'outOfFuel' both read as 'none' and so fail this gate. -/
def fixture_returns_abiTrue_ok : IO Bool := do
  let cd ← fixtureCdM
  pure (cd.size == 4484 && returnsAbiTrue cd)
#eval fixture_returns_abiTrue_ok -- expect true

/-- **GATE 5 - AND A MUTANT DOES NOT.** Each of the eight byte-flip mutants of the same calldata
    reverts, with the four bytes the render's own ERR_* constant assigns; none returns abiTrue; and
    each mutant really differs from the calldata it was made from. Measured: every mutant reverts in
    under 90 ms, because each fails a guard the program reaches before any real work. -/
def mutants_revert_ok : IO Bool := do
  let cd ← fixtureCdM
  let ms := mutantsOf cd
  pure (ms.length == 8 && (ms.all fun (nm, m, sel) =>
    nm != "" && m != cd && m.size > 0 && revertsToSelector m sel && ! returnsAbiTrue m))
#eval mutants_revert_ok -- expect true

end Midfall.Instances.PoseidonExhibit
