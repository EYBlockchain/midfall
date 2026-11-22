-- |
-- Midfall.Instances.PoseidonExhibit
--
-- T3.11 (PLAN-V3, D-P71): **THE W14 EXECUTABLE EXHIBIT - RUN THE THEOREM'S PROGRAM BEFORE PROVING
-- ABOUT IT.** A TEST, NEVER A PREMISE OF A PROOF. Nothing in this file may enter the cone of
-- 'lowering_equivalence_poseidon'. The Yul-side half is 'Bool' / 'IO Bool' gates that
-- 'scripts/kat_gate.py' runs; the Lean-verifier half (REF.12, section 5) is two theorems proved by
-- 'native_decide' over the same F1 bundle. 'native_decide' is permitted HERE and only here
-- (Midfall/Instances), and no declaration below mentions the root or a block row. No 'sorry'.
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
-- 'verifyMsgs' at the real pairing). They belong to REF.12 and are section 5 below: the F1 proof
-- through the tree's 'verifyNative' at the public test-SRS trapdoor, and every mutant in
-- 'mutations.json' through the same verifier, comparing Lean's verdict class with the Rust one.
-- Both are THEOREMS proved by 'native_decide' at this fixture (the computation is far too slow for
-- the 'kat_gate' interpreter); the theorem is the exhibit, so the report reads 4 PRESENT.
--
-- WHY THE FIXTURE ARRIVES BY IO. 'proof.bin' and 'calldata.bin' are BINARY, so 'include_str' refuses
-- them; this is the same channel PoseidonCoherence (F.1) uses, with the same two-candidate path list
-- so the gate runs from 'formal/' (kat_gate) and from the repo root alike. A failed read yields the
-- EMPTY bundle and every gate below goes FALSE on empty rather than passing on a default.

import Midfall.Instances.PoseidonValid
import Midfall.Instances.Bls12_381
import Midfall.Instances.NativeReplay
import Midfall.Instances.ObjectFingerprint
import Midfall.Lowering.Calldata
import Midfall.LoweringV2.HonestExec

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option linter.unusedVariables false

namespace Midfall.Instances.PoseidonExhibit

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonV2 Midfall.Lowering
open Midfall.LoweringV2 Midfall.Yul Midfall.Yul.Bridge Midfall.Halo2 Midfall.Conformance
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
def entryState (cd : Bytes) : EvmState :=
  LoweringV2.initState exhibitW exhibitLyt keccak256 cd (fun _ => 0)

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
    byte for byte (4,484 bytes, keccak pinned), it carries the 'verifyProof' selector the entry
    frame demands, and the proof it was built from IS the pure proof term the Lean-verifier
    exhibits of section 5 run on ('trace.json' proof_hex, the tracked 'proof.bin'). 34 ms. -/
def fixtureCalldata_isTheBundleBytes_ok : IO Bool := do
  let cd ← fixtureCdM
  let rust ← calldataBin
  let π ← proofBin
  pure (cd.size == 4484 && rust.size == 4484 && cd.data.toList == rust.data.toList &&
    Midfall.keccak256 cd == 0x434221dcb184cdb7e1145de7fe684d1e777f04b035ddfea8fbeff75680505da3 &&
    bytesTake cd 0 4 == some fnSigVerifyProof &&
    π.size == 2640 && π.data.toList == NativeReplay.proofBytes.data.toList)
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

/-! ## 5. The Lean verifier's side (REF.12): the other two exhibits Report.lean reads -/

/-- The F1 verifier parameters at the bundle's PUBLIC trapdoor (D-P63; REF.11/REF.12):
    `ParamsVerifierKZG.ofParams (g2foldExp 1) (ofAdd s)`, with `s` read from params.json by
    `NativeReplay.sTrapdoor`. `check_iff_g1` (REF.12, proved in D6_Render) is what makes the final
    dual-MSM check at this term the scalar equation `s • left = right` in G₁z. -/
def paramsAtTrapdoor : ParamsVerifierKZG G₁z G2fold :=
  ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd NativeReplay.sTrapdoor)

/-- `instances.json`'s public column as `verifyNative` takes it: F1 has one proof row, one public
    column and one value. A parse failure yields `#[]`, and every gate below goes FALSE on it. -/
def fixturePublicInstance : Array (Fr blsR) :=
  match NativeReplay.instancesArr[0]? with
  | some row => (row[0]?).getD #[]
  | none => #[]

/-- Lean's verdict class in the Rust taxonomy (`proofs/src/plonk/error.rs`): the four classes the
    F1 corpus records plus catch-alls that match no recorded class. -/
def leanVerdictClass : Except Fault Unit → String
  | .ok () => "accept"
  | .error (.error .opening) => "opening"
  | .error (.error (.transcript .unexpectedEof)) => "transcript:UnexpectedEof"
  | .error (.error (.transcript .notFound)) => "transcript_notFound"
  | .error (.error (.transcript .other)) => "transcript:Other"
  | .error (.error _) => "other-error"
  | .error (.panic _) => "panic"

/-- **THE FIXTURE ACCEPTANCE, AS A BOOL.** The tree's `verifyNative`, with no shims, at the real F1
    key (`NativeReplay.vkF1`: the 27 commitments decoded through the computable codec), the
    deployment environment (`NativeReplay.envReal`: `g1CodecC`, `poseidonFc`, `poseidonDelta`), the
    parameters at the exported trapdoor, the parsed public instance and the F1 proof. The proof bytes
    are `trace.json`'s `proof_hex`; gate 1 above pins those to the tracked `proof.bin`. -/
def fixtureLeanAccepts : Bool :=
  fixturePublicInstance.size == 1 && NativeReplay.proofBytes.size == 2640 &&
    match NativeReplay.vkF1 with
    | none => false
    | some vk =>
      match verifyNative (Gₜ := G₁z) NativeReplay.envReal Features.solidity paramsAtTrapdoor
          vk fixturePublicInstance NativeReplay.proofBytes with
      | .ok () => true
      | .error _ => false

/-- **EXHIBIT 3 OF 4 (REF.12): THE LEAN VERIFIER ACCEPTS THE F1 PROOF OUTRIGHT.** `verifyNative`
    returns `.ok ()` on the tracked proof at the public test-SRS trapdoor. This is the Lean half of
    the W14 pair whose Yul half is `fixture_returns_abiTrue_ok` (gate 4). Proved by `native_decide`
    in `Midfall/Instances` (the card's own allowance, D-P71): the run is ~9 s in the VM, too slow for
    the `kat_gate` interpreter, and the theorem is the stronger statement anyway. -/
theorem fixture_leanAccepts_ok : fixtureLeanAccepts = true := by native_decide

/-! ### The mutation corpus (REF.12) -/

/-- One recorded mutant: the tag, the kind, the byte offset, the recorded length, the Rust error
    class (`none` for the control) and the Rust verdict. -/
structure Mutation where
  tag : String
  kind : String
  byteOffset : Option Nat
  len : Nat
  errorClass : Option String
  verdict : String

/-- `mutations.json` (REF.11 schema 1), parsed from the tracked bundle. A parse failure leaves the
    empty array, and the length gate below goes FALSE on it. -/
def mutationsJson : JValue :=
  match jParse (include_str "../../fixtures/conformance/poseidon-testsrs/mutations.json") with
  | .ok j => j
  | .error _ => Lean.Json.null

def jsonNat? : JValue → Option Nat
  | .num n => n.toString.toNat?
  | _ => none

def jsonString? : JValue → Option String
  | .str s => some s
  | _ => none

def jsonField? (j : JValue) (k : String) : Option JValue :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

def parseMutation (j : JValue) : Option Mutation := do
  let tag ← jsonString? (← jsonField? j "tag")
  let kind ← jsonString? (← jsonField? j "kind")
  let len ← jsonNat? (← jsonField? j "len")
  let verdict ← jsonString? (← jsonField? j "verdict")
  let byteOffset := Option.bind (← jsonField? j "byte_offset") jsonNat?
  let errorClass := Option.bind (← jsonField? j "error") jsonString?
  pure { tag, kind, byteOffset, len, errorClass, verdict }

def mutationRecords : List Mutation :=
  match mutationsJson.getObjVal? "mutants" with
  | .ok (.arr a) => a.toList.filterMap parseMutation
  | _ => []

/-- The mutation recipe of `conformance_export.rs`: a single-bit flip is `byte ^= 1` at the read's
    first byte; the structural set is a truncation to the recorded length, an appended zero byte,
    and the empty proof. The unmutated control is the identity. -/
def applyMutation (π : Bytes) (m : Mutation) : Bytes :=
  match m.kind with
  | "single_bit_flip" =>
      match m.byteOffset with
      | some o =>
          ByteArray.mk (List.toArray
            (π.data.toList.set o (UInt8.xor π.data.toList[o]! 1)))
      | none => π
  | "truncation" => ByteArray.mk (List.toArray (π.data.toList.take m.len))
  | "trailing_byte" =>
      ByteArray.mk (List.toArray (π.data.toList.take (m.len - 1) ++ [0]))
  | _ => π

def expectedVerdictClass (m : Mutation) : String :=
  match m.errorClass with
  | some e => e
  | none => "accept"

/-- One mutant through the tree's verifier: the mutated bytes really have the recorded length, and
    Lean's verdict class is the Rust one. Any divergence reddens the gate. -/
def mutationVerdictOk (vk : VerifyingKey (Fr blsR) G₁z) (π : Bytes) (m : Mutation) : Bool :=
  let cand := applyMutation π m
  cand.size == m.len &&
    leanVerdictClass (verifyNative (Gₜ := G₁z) NativeReplay.envReal Features.solidity
      paramsAtTrapdoor vk fixturePublicInstance cand) == expectedVerdictClass m

/-- A chunk of the corpus, eight mutants at a time. The chunking is a proof-engineering device only:
    `native_decide` per chunk keeps each tactic call well under the 60 s bound, and the exhibition
    theorem below assembles the chunks. The chunk predicates are the SAME computation. -/
def mutationChunkOk (k : Nat) : Bool :=
  match NativeReplay.vkF1 with
  | none => false
  | some vk => (mutationRecords.drop k |>.take 8).all (mutationVerdictOk vk NativeReplay.proofBytes)

theorem mutationRecords_length : mutationRecords.length = 77 := by native_decide

theorem mutationChunk_0 : mutationChunkOk 0 = true := by native_decide
theorem mutationChunk_8 : mutationChunkOk 8 = true := by native_decide
theorem mutationChunk_16 : mutationChunkOk 16 = true := by native_decide
theorem mutationChunk_24 : mutationChunkOk 24 = true := by native_decide
theorem mutationChunk_32 : mutationChunkOk 32 = true := by native_decide
theorem mutationChunk_40 : mutationChunkOk 40 = true := by native_decide
theorem mutationChunk_48 : mutationChunkOk 48 = true := by native_decide
theorem mutationChunk_56 : mutationChunkOk 56 = true := by native_decide
theorem mutationChunk_64 : mutationChunkOk 64 = true := by native_decide
theorem mutationChunk_72 : mutationChunkOk 72 = true := by native_decide

/-- The whole corpus check, as one Bool: 77 records, and every chunk green. -/
def mutantsLeanRejects : Bool :=
  mutationRecords.length == 77 &&
    mutationChunkOk 0 && mutationChunkOk 8 && mutationChunkOk 16 && mutationChunkOk 24 &&
    mutationChunkOk 32 && mutationChunkOk 40 && mutationChunkOk 48 && mutationChunkOk 56 &&
    mutationChunkOk 64 && mutationChunkOk 72

/-- **EXHIBIT 4 OF 4 (REF.12): EVERY MUTANT OF THE F1 PROOF IS REJECTED WITH THE RUST CLASS.** The
    corpus is `mutations.json`'s own 77 entries - one single-bit flip per transcript read plus the
    truncation, trailing-byte, empty and unmutated control - and Lean's `verifyNative` class is
    compared with the class the Rust verifier recorded for that same byte string. Proved by
    `native_decide` in ten chunks, each under the 60 s tactic bound; the assembly is by rewriting the
    ten proved chunk facts, so nothing is assumed. -/
theorem mutants_leanRejects_ok : mutantsLeanRejects = true := by
  rw [mutantsLeanRejects]
  simp only [mutationRecords_length, mutationChunk_0, mutationChunk_8, mutationChunk_16,
    mutationChunk_24, mutationChunk_32, mutationChunk_40, mutationChunk_48, mutationChunk_56,
    mutationChunk_64, mutationChunk_72]
  decide

#print axioms fixture_leanAccepts_ok
#print axioms mutants_leanRejects_ok

end Midfall.Instances.PoseidonExhibit
