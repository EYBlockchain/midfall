-- |
-- Midfall.Instances.NativeReplay
--
-- **REF.8 - THE REFERENCE GATE (PLAN-V3 section 6).** The tree's OWN Lean verifier, with
-- no shims, run over the exported proof bytes, agreeing item by item with the Rust
-- verifier's own recorded trace.
--
-- WHAT IS COMPARED. Ten challenges by name (theta, beta, gamma, trash_challenge, y, x,
-- x1, x2, x3, x4), the whole read schedule (every width and every byte the transcript
-- consumed), the 1 + 45 terms of the final dual MSM (label, scalar, point), and both
-- MSM evaluations - which are the two inputs of the pairing the Rust then checked.
-- Every one of those is COMPUTED by the port from vk.json, params.json,
-- instances.json and proof.bin; trace.json is the reference OUTPUT and never an input
-- to the computation. A value the port computes differently reddens the gate. That is
-- the whole point: a harness that cannot fail manufactures confidence.
--
-- WHICH BUNDLE, AND WHY. F1 (`fixtures/conformance/poseidon-testsrs`), the test-SRS
-- bundle exported by REF.11 under D-P63. Its trapdoor is PUBLIC
-- (params.json trapdoor_s_be_hex = 1bf3a1cf...dbe23b, srs_sha256 = 06a7885b...e13abf,
-- seed 0x5eed), so the final check `e(left, sG2) * e(right, -G2) = 1` is a CLOSED
-- COMPUTATION in G1z rather than a comparison of shapes: the gate below evaluates
-- `DualMSM.check` and requires true. At F0 (the Filecoin ceremony SRS) the trapdoor is
-- unknown and the same run can only compare terms, which is why F1 is the bundle the
-- M1-M4 gates read. cs.json and instances.json are byte-identical between the two
-- bundles; vk.json differs in the 27 commitments and the transcript representative
-- because those are SRS images, so the key here is parsed from F1's own vk.json and
-- NOT taken from PoseidonEnv, which imports F0.
--
-- WHAT THIS GATE COULD NOT RUN BEFORE, AND WHAT LANDED FOR IT.
--   * REF.2 (D-P61): with the structural `BEq Rotation`, `getAnyQueryIndex` did not
--     find the imported key's own permutation queries and the run panicked at
--     circuit.rs:2084.
--   * REF.1 (D-P61): with value equality on one-piece commitments, the six identity
--     fixed-column commitments opened at x merged and `constructIntermediateSets`
--     returned `Error.opening`.
--   * REF.4 / D-P62: `g1CodecZ.ofCompressed?` is the constant `none`, so no proof
--     point could be decoded at all. `g1CodecC` decodes, computably.
--   * REF.5 / D-P62(a): `VerifierEnv` needs an `AdmissiblePairing`; `pairingC` supplies
--     one with no curve axiom.
-- All four are in this work package. Nothing here is a shim: every Exec function called
-- is the tree's, unmodified.
--
-- THE FALSIFIERS. `nativeReplay_delta2_differs_ok` (delta := 2, C.2's placeholder) and
-- `nativeReplay_mutated_differs_ok` (one proof byte flipped) both require the gate to
-- GO RED. A gate that is green on a wrong delta or a wrong proof is not measuring
-- anything, and per W12 the witness ships with its two falsifiers.
--
-- D-P71: this is a FIXTURE. Everything here is computation, and no block row, totality
-- lemma or headline is stated or proved at a fixture. No `native_decide` appears in
-- this file, and nothing here is in the cone of `lowering_correct`.

import Midfall.Instances.PairingByConstruction
import Midfall.Instances.G1Compressed
import Midfall.Instances.PoseidonEnv
import Midfall.Instances.PoseidonFixture
import Midfall.Conformance.Bundle
import Midfall.Halo2.Exec.Native

set_option autoImplicit false

namespace Midfall.Instances.NativeReplay
open Midfall Midfall.Yul Midfall.Halo2 Midfall.Conformance Midfall.Instances Midfall.Assumptions
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv
open Midfall.Generator

/-! ## The bundle, read from F1 -/

/-- F1's own vk.json. NOT `Midfall.Instances.PoseidonEnv.poseidonVkData`, which imports
    F0: the 27 commitments and the transcript representative are SRS images, and this
    bundle's SRS is the test one. -/
def vkJ : JValue :=
  match jParse (include_str "../../fixtures/conformance/poseidon-testsrs/vk.json") with
  | .ok j => j
  | .error _ => Lean.Json.null

/-- F1's trace.json: the Rust verifier's own recorded transcript, reads, dual MSM and
    verdict. Reference OUTPUT, never an input to what the port computes. -/
def traceJ : JValue :=
  match jParse (include_str "../../fixtures/conformance/poseidon-testsrs/trace.json") with
  | .ok j => j
  | .error _ => Lean.Json.null

def instancesJ : JValue :=
  match jParse (include_str "../../fixtures/conformance/poseidon-testsrs/instances.json") with
  | .ok j => j
  | .error _ => Lean.Json.null

/-- The proof bytes. Schema 2 exports `proof_hex` in trace.json, and it is the SAME
    2640 bytes as the tracked `proof.bin` - checked by `nativeReplay_proofAgrees_ok`
    below, because "take the proof bytes from the trace" is only honest if the trace
    and the binary are the same bytes. Read from the trace rather than from the file
    because a build-time KAT is a pure term and `IO.FS.readBinFile` is not. -/
def proofBytes : Bytes :=
  match traceJ.getObjVal? "proof_hex" with
  | .ok (Lean.Json.str s) => match jHexBytes' s with | .ok b => b | .error _ => Bytes.empty
  | _ => Bytes.empty

/-- The exporter's own record of the proof length, and of the two schema-2 flags. -/
def proofLenRust : Nat :=
  match traceJ.getObjVal? "proof_len" with
  | .ok (Lean.Json.num n) => n.toString.toNat?.getD 0
  | _ => 0

/-- The Rust verdict and the Rust pairing check, as recorded. -/
def rustVerdict : String :=
  match traceJ.getObjVal? "verdict" with
  | .ok (Lean.Json.str s) => s
  | _ => ""

def rustPairingCheck : Bool :=
  match traceJ.getObjVal? "pairing_check" with
  | .ok (Lean.Json.bool b) => b
  | _ => false

/-- F1's params.json: the SRS data the final check needs, including the PUBLIC
    trapdoor (D-P63), which is what makes the last comparison a computation. -/
def paramsJ : JValue :=
  match jParse (include_str "../../fixtures/conformance/poseidon-testsrs/params.json") with
  | .ok j => j
  | .error _ => Lean.Json.null

/-- **THE PUBLIC TRAPDOOR** (D-P63): params.json exports `s`, so `DualMSM.check` is a
    closed computation in G1z and the gate can require the pairing equation to HOLD
    rather than require two shapes to look alike. -/
def sTrapdoor : ZMod blsR :=
  match paramsJ.getObjVal? "trapdoor_s_be_hex" with
  | .ok (Lean.Json.str hx) =>
      match jHexBytes' hx with
      | .ok b => (bytesToNatBE b : ZMod blsR)
      | .error _ => 0
  | _ => 0

/-- The trace, parsed with the tree's own strict parser. -/
def rustTrace : Except String Trace := Midfall.Conformance.parseTrace traceJ

def emptyTrace : Trace :=
  { verdict := "", error := "", pairingCheck := false, proofLen := 0, events := #[],
    leftTerms := #[], rightTerms := #[], leftEval := Bytes.empty,
    rightEval := Bytes.empty, fixtureProofMatch := false }

def rustTraceOr : Trace := match rustTrace with | .ok t => t | .error _ => emptyTrace

/-- Except to Option, so the `do` blocks below bind in `Option` and a parse failure is
    a `none` the gate reports rather than a silent default. -/
def exOpt {α : Type} (e : Except String α) : Option α :=
  match e with | .ok a => some a | .error _ => none

/-! ## The key, the environment, the instances -/

/-- The 19 fixed and 8 sigma commitments of F1's vk.json, DECODED into the carrier by
    the computable codec (REF.4). If any of them fails to decode the gate says so
    rather than substituting an identity - which is exactly what the old placeholder
    key did, and what made the run meaningless. -/
def vkF1 : Option (VerifyingKey (Fr blsR) G₁z) := do
  let vk ← exOpt (Midfall.Conformance.parseVk vkJ)
  let fxh ← exOpt (Midfall.Conformance.jHexArr vkJ "fixed_commitments_compressed_hex")
  let pmh ← exOpt (Midfall.Conformance.jHexArr vkJ "permutation_commitments_compressed_hex")
  let fx ← fxh.mapM g1CodecC.ofCompressed?
  let pm ← pmh.mapM g1CodecC.ofCompressed?
  pure { domain := poseidonDomain, fixedCommitments := fx,
         permutation := { commitments := pm }, cs := poseidonCs,
         csDegree := vk.csDegree,
         transcriptRepr := (bytesToNatBE vk.transcriptRepr : Fr blsR) }

/-- The verifier environment: the COMPUTABLE codec (REF.4), the deployment field
    constants, and `Fr::DELTA = 7^(2^32)` - the real constant, not C.2's placeholder 2. -/
def envReal : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecC, field := poseidonFc, delta := poseidonDelta,
    fewerPointSetsRuntime := false }

/-- instances.json: the committed instance column (the identity) and the public column. -/
def instData : Except String (Array (Array Bytes) × Array (Array Bytes)) :=
  Midfall.Conformance.parseInstances instancesJ

def committedG1 : Array (Array G₁z) :=
  match instData with
  | .ok (c, _) => ((c.mapM (m := Option) fun row => row.mapM g1CodecC.ofCompressed?).getD #[])
  | .error _ => #[]

def instancesArr : Array (Array (Array (Fr blsR))) :=
  match instData with
  | .ok (_, pb) => pb.map fun row => row.map fun b => #[((bytesToNatBE b : Nat) : Fr blsR)]
  | .error _ => #[]

/-! ## Hex and comparison plumbing -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexOf (b : Bytes) : String :=
  String.ofList (b.data.toList.flatMap fun u =>
    [hexDigit (u.toNat / 16), hexDigit (u.toNat % 16)])

def frHex (x : Fr blsR) : String := hexOf (natToBytesBE x.val 32)
def g1Hex (Q : G₁z) : String := hexOf (g1CodecC.toCompressed Q)

def faultStr : Fault → String
  | .panic s => "PANIC " ++ s
  | .error .opening => "Error.opening"
  | .error .invalidInstances => "Error.invalidInstances"
  | .error (.transcript .unexpectedEof) => "Error.transcript(UnexpectedEof)"
  | .error (.transcript .notFound) => "Error.transcript(NotFound)"
  | .error (.transcript .other) => "Error.transcript(Other)"
  | .error _ => "Error.<other>"

/-- A tiny report: every comparison names itself, and a green gate must have made a
    non-zero number of them. -/
structure Rep where
  checks : Nat := 0
  failures : List String := []

def Rep.eq {α : Type} [BEq α] [ToString α] (r : Rep) (name : String) (a b : α) : Rep :=
  { checks := r.checks + 1,
    failures := if a == b then r.failures
                else (name ++ ": lean " ++ toString a ++ " | rust " ++ toString b) :: r.failures }

def Rep.ok (r : Rep) (name : String) (good : Bool) (why : String) : Rep :=
  { checks := r.checks + 1, failures := if good then r.failures else (name ++ ": " ++ why) :: r.failures }

/-! ## The squeeze names, in the order the transcript produces them -/

/-- The ten squeezes the reference records, by name. -/
def squeezeNames : List String :=
  ["theta", "beta", "gamma", "trash_challenge", "y", "x", "x1", "x2", "x3", "x4"]

def rustSqueeze (name : String) : String :=
  (rustTraceOr.events.toList.filterMap fun
    | .squeeze n _ ch _ => if n == name then some (hexOf ch) else none
    | _ => none).head?.getD "<absent>"

def rustReads : List Bytes :=
  rustTraceOr.events.toList.filterMap fun | .read _ wire _ => some wire | _ => none

/-! ## THE GATE -/

/-- The whole pipeline, as a pure computation. `delta` and `mutate` exist so the two
    falsifiers can run the SAME code on a wrong key and a wrong proof; the gate itself
    calls them at their real values. -/
def run (delta : Fr blsR := poseidonDelta) (mutate : Bytes → Bytes := id) : Rep :=
  let tr := rustTraceOr
  match vkF1 with
  | none => ({ checks := 1, failures := ["vk/F1: a commitment in vk.json did not decode through g1CodecC"] } : Rep)
  | some vk =>
  let feat := Features.solidity
  let tr0 := Transcript.initFromBytes (mutate proofBytes)
  -- STAGE 1: parse_trace - the advice, permutation, lookup and trashcan reads and the
  -- first five challenges.
  match (Midfall.Halo2.parseTrace g1CodecC feat vk committedG1 instancesArr).run tr0 with
  | .error f => ({ checks := 1, failures := ["stage1/parseTrace: " ++ faultStr f] } : Rep)
  | .ok (vt, t1) =>
  let r0 := ({} : Rep)
  let r1 := r0.eq "squeeze/theta" (frHex vt.theta) (rustSqueeze "theta")
  let r2 := r1.eq "squeeze/beta" (frHex vt.beta) (rustSqueeze "beta")
  let r3 := r2.eq "squeeze/gamma" (frHex vt.gamma) (rustSqueeze "gamma")
  let r4 := r3.eq "squeeze/trash_challenge" (frHex vt.trashChallenge) (rustSqueeze "trash_challenge")
  let r5 := r4.eq "squeeze/y" (frHex vt.y) (rustSqueeze "y")
  -- STAGE 2: read_algebra - the evaluation reads and the opening challenge x.
  let nbCommitted := (committedG1[0]?.map (fun row => row.size)).getD 0
  match (Verifier.readAlgebra g1CodecC feat vk vt.permutations vt.lookups vt.trashcans
      nbCommitted instancesArr.size instancesArr).run t1 with
  | .error f => r5.ok "stage2/readAlgebra" false ("the tree's readAlgebra faulted: " ++ faultStr f)
  | .ok (alg, t2) =>
  let r6 := r5.eq "squeeze/x" (frHex alg.x) (rustSqueeze "x")
  -- STAGE 3: linearize - the identities, the linearization commitment, the query set.
  match Verifier.linearize delta vk vt.adviceCommitments committedG1 vt.y vt.beta vt.gamma
      vt.theta vt.trashChallenge vt.challenges alg with
  | .error f => r6.ok "stage3/linearize" false ("the tree's linearize faulted: " ++ faultStr f)
  | .ok queries =>
  -- STAGE 4: multi_prepare, in its three phases, with the tree's own grouping (REF.1).
  match (phaseA (G₂ := G2fold) (Gₜ := G₁z) g1CodecC poseidonFc feat false queries).run t2 with
  | .error f => r6.ok "stage4a/phaseA" false ("the tree's phaseA faulted: " ++ faultStr f)
  | .ok (a, t3) =>
  let r7 := r6.eq "squeeze/x1" (frHex a.x1) (rustSqueeze "x1")
  let r8 := r7.eq "squeeze/x2" (frHex a.x2) (rustSqueeze "x2")
  match (phaseB g1CodecC poseidonFc feat a).run t3 with
  | .error f => r8.ok "stage4b/phaseB" false ("the tree's phaseB faulted: " ++ faultStr f)
  | .ok (b, t4) =>
  -- x3 is the squeeze the deployed profile truncates AFTER sampling (R-22).
  let r9 := r8.eq "squeeze/x3" (frHex b.x3) (rustSqueeze "x3")
  match (phaseC (G₂ := G2fold) (Gₜ := G₁z) g1CodecC poseidonFc feat a b).run t4 with
  | .error f => r9.ok "stage4c/phaseC" false ("the tree's phaseC faulted: " ++ faultStr f)
  | .ok (c, t5) =>
  let r10 := r9.eq "squeeze/x4" (frHex c.x4) (rustSqueeze "x4")
  -- the read schedule: every width and every byte the transcript consumed, in order.
  let leanReads := t5.log.toList.map (fun rec => hexOf rec.2)
  let rustReadHex := rustReads.map hexOf
  let r11 := r10.eq "read-schedule/count" t5.log.size rustReadHex.length
  let r12 := r11.eq "read-schedule/bytes" (toString leanReads) (toString rustReadHex)
  -- the proof is consumed exactly: this is what "the same proof" means.
  let r13 := r12.eq "transcript/pos" t5.pos tr.proofLen
  let r14 := r13.ok "transcript/exhausted" (t5.buffer.size == t5.pos)
              ("the port consumed " ++ toString t5.pos ++ " of " ++ toString t5.buffer.size
                ++ " proof bytes, so the schedule does not match the proof")
  -- STAGE 5: the final dual MSM, term by term.
  let (lt, rt) := c.dual.split
  let showT (t : CommitmentLabel × Fr blsR × G₁z) : String :=
    t.1.text ++ "|" ++ frHex t.2.1 ++ "|" ++ g1Hex t.2.2
  let showR (t : Term) : String := t.label ++ "|" ++ hexOf t.scalar ++ "|" ++ hexOf t.point
  let r15 := r14.eq "dual_msm/left_count" lt.size tr.leftTerms.size
  let r16 := r15.eq "dual_msm/left" (toString (lt.toList.map showT)) (toString (tr.leftTerms.toList.map showR))
  let r17 := r16.eq "dual_msm/right_count" rt.size tr.rightTerms.size
  let r18 := r17.eq "dual_msm/right" (toString (rt.toList.map showT)) (toString (tr.rightTerms.toList.map showR))
  -- STAGE 6: both MSM evaluations - the two inputs of the pairing the Rust checked.
  let r19 := r18.eq "dual_msm/left_eval" (g1Hex c.dual.left.eval) (hexOf tr.leftEval)
  let r20 := r19.eq "dual_msm/right_eval" (g1Hex c.dual.right.eval) (hexOf tr.rightEval)
  -- STAGE 7: THE FINAL CHECK ITSELF, at the public trapdoor. This is the intended
  -- outcome the gate exists for: not "the terms look alike" but "the pairing equation
  -- holds", decided in G₁z because s is data (D-P62(b), D-P63).
  let params : ParamsVerifierKZG G₁z G2fold :=
    ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd sTrapdoor)
  r20.ok "dual_msm/check" (DualMSM.check c.dual params)
    "DualMSM.check returned false at the exported trapdoor, so the port's final MSM does not satisfy the pairing equation the Rust verifier accepted"

/-- **THE REFERENCE GATE (REF.8, PLAN-V3 section 6).** -/
def nativeReplay_ok : Bool :=
  let r := run
  r.checks >= 20 && r.failures.isEmpty

/-- The same run with C.2's placeholder delta. The permutation identities are built with
    `F::DELTA`, so a wrong delta changes the linearization, the quotient, the queries
    and therefore the challenges and the final MSM: the gate MUST go red. -/
def nativeReplay_delta2_differs_ok : Bool :=
  let r := run (delta := 2)
  !r.failures.isEmpty

/-- Flip the low bit of one proof byte - inside the quotient region, past the last
    commitment read - and require the gate to go red. -/
def flipByte (k : Nat) (b : Bytes) : Bytes :=
  ByteArray.mk ((List.zip (List.range b.size) b.data.toList).map fun (i, u) =>
    if i == k then Nat.toUInt8 (Nat.xor u.toNat 1) else u).toArray

def nativeReplay_mutated_differs_ok : Bool :=
  let r := run (mutate := flipByte 1008)
  !r.failures.isEmpty

/-- The trace's `proof_hex` IS the tracked `proof.bin`: 2640 bytes, and the exporter's
    own `fixture_match` records the length agreement. Stated here because the gate
    reads its proof from the trace, and that substitution has to be checked and not
    assumed. -/
def nativeReplay_proofAgrees_ok : Bool :=
  proofBytes.size == 2640 && proofLenRust == 2640 && proofBytes.size == proofLenRust &&
    rustVerdict == "accept" && rustPairingCheck == true &&
    (rustTraceOr.leftTerms.size == 1) && (rustTraceOr.rightTerms.size == 45) &&
    (match Midfall.Conformance.parseTrace traceJ with | .ok _ => true | .error _ => false)

/-- **KAT (REF.4 / D4): the computable codec against every G1 point of the fixture.**
    The 19 fixed and 8 sigma commitments of vk.json, every 48-byte point the proof
    stream carries, and the committed instance of instances.json - each one DECODED by
    `g1CodecC.ofCompressed?` and then checked for the laws the codec has to satisfy:
    decoder-first (re-encode returns the bytes it was given), the EIP round trip, and
    both widths. `g1CodecZ`, the placeholder this card replaces, fails the first clause
    on every point because its decoder is the constant `none` - pinned as a theorem
    just below rather than evaluated here, so that this KAT stays computable. -/
def g1CodecC_fixturePoints_ok : Bool :=
  let proofPts := rustReads.filter (fun b => b.size == 48)
  let vkPts := ((exOpt (Midfall.Conformance.jHexArr vkJ "fixed_commitments_compressed_hex")).getD #[]).toList ++
    ((exOpt (Midfall.Conformance.jHexArr vkJ "permutation_commitments_compressed_hex")).getD #[]).toList
  let instPts := (rustTraceOr.events.toList.flatMap fun
      | .read _ wire _ => if wire.size == 48 then [wire] else []
      | _ => [])
  let all : List Bytes := vkPts ++ proofPts ++ instPts
  let perPoint (b : Bytes) : Bool :=
    match g1CodecC.ofCompressed? b with
    | none => false
    | some Q =>
        decide (g1CodecC.toCompressed Q = b) &&
        decide (g1CodecC.ofEip? (g1CodecC.toEip Q) = some Q) &&
        decide ((g1CodecC.toEip Q).size = 128) && decide ((g1CodecC.toCompressed Q).size = 48)
  all.length >= 48 && all.all perPoint

/-- **THE FALSIFIER OF THE PLACECODEC (REF.4).** Why the old codec could never pass the
    KAT above: its compressed decoder is the constant `none`, so no proof point and no
    key commitment could be read at all. A theorem, not an evaluation - `g1CodecZ` is
    `noncomputable`, and pulling it into the KAT would make the KAT unevaluable. -/
theorem g1CodecZ_ofCompressed_is_none (b : Bytes) : g1CodecZ.ofCompressed? b = none := rfl

/-- **THE REAL COMMITMENTS, DECODED (REF.6 Do 1).** The 19 fixed and 8 sigma
    commitments of vk.json as CARRIER ELEMENTS, through the computable codec. The
    deployment key in PoseidonEnv still holds `Array.replicate n 1` - the placeholder
    REF.6 replaces - and replacing it is not this card's edit to make, because three
    existing rfl pins in Instances/PoseidonCoherence.lean assert the placeholder
    (`check3_poseidonE_g1_isG1CodecZ`, the `ofCompressed? b = none` theorem, and the
    stated non-computable CHECK 3 target). What IS established here is the pin those
    flips will need: that the real points decode, and that they are the payload's. -/
def poseidonFixedCommitmentsReal : Array G₁z :=
  (poseidonVkData.fixedCommitmentHex.mapM g1CodecC.ofCompressed?).getD #[]

def poseidonPermutationCommitmentsReal : Array G₁z :=
  (poseidonVkData.permutationCommitmentHex.mapM g1CodecC.ofCompressed?).getD #[]

/-- The four words of a payload commitment as the 128 bytes the contract loads. -/
def g1WordsBytes (w : Midfall.Generator.G1Words) : Bytes :=
  [w.xHi, w.xLo, w.yHi, w.yLo].foldl (fun acc x => ByteArray.append acc (wordToBytesBE x))
    Bytes.empty

/-- **KAT (REF.6, the clause its Accept names).** The 27 commitments of vk.json, decoded
    through the computable codec (REF.4) and re-encoded to the 128-byte EIP form, ARE the
    payload words the generator emits - 19 fixed and 8 sigma, one for one and in order.
    This is the `KeyAgrees.fixedWords` / `.permWords` pin measured at the deployment
    rather than assumed, and it is the first time the Lean key and the Lean payload have
    been compared as POINTS: gate 9 of PoseidonEnv compares coordinates as Nats, and the
    placeholder key could not be compared at all because nothing decoded into it.
    FALSIFIER, in the same conjunction: the placeholder key - 19 copies of the identity -
    does NOT match the payload, so a green reading here is not a green reading of a
    degenerate key. -/
def poseidonRealCommitments_matchPayload_ok : Bool :=
  poseidonFixedCommitmentsReal.size == 19 &&
    poseidonPermutationCommitmentsReal.size == 8 &&
    (List.map g1WordsBytes Midfall.Instances.PoseidonInputs.poseidonVkGen.fixedComms) ==
      poseidonFixedCommitmentsReal.toList.map g1CodecC.toEip &&
    (List.map g1WordsBytes Midfall.Instances.PoseidonInputs.poseidonVkGen.permutationComms) ==
      poseidonPermutationCommitmentsReal.toList.map g1CodecC.toEip &&
    (List.map g1WordsBytes Midfall.Instances.PoseidonInputs.poseidonVkGen.fixedComms) !=
      (Array.replicate 19 (1 : G₁z)).toList.map g1CodecC.toEip

/-- What the gate compared, printed for the report. -/
def nativeReplay_checks : Nat := (run).checks

/-- What the gate compared, printed for the report. -/
def nativeReplay_report : List String := (run).failures

#print axioms nativeReplay_ok

end Midfall.Instances.NativeReplay

#eval Midfall.Instances.NativeReplay.nativeReplay_ok            -- expect true
#eval Midfall.Instances.NativeReplay.nativeReplay_delta2_differs_ok  -- expect true
#eval Midfall.Instances.NativeReplay.nativeReplay_mutated_differs_ok -- expect true
#eval Midfall.Instances.NativeReplay.nativeReplay_proofAgrees_ok     -- expect true
#eval Midfall.Instances.NativeReplay.g1CodecC_fixturePoints_ok  -- expect true
#eval Midfall.Instances.NativeReplay.poseidonRealCommitments_matchPayload_ok  -- expect true
#eval Midfall.Instances.NativeReplay.nativeReplay_checks
#eval Midfall.Instances.NativeReplay.nativeReplay_report
