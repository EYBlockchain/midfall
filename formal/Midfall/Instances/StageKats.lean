/-
  StageKats.lean — the executable evidence for Midfall/Lowering/Stage.lean (SIM.1).

  Two of these three gates are copied VERBATIM from section 7 ('Evidence') of the design-evidence
  scratch file docs/plans/V3-evidence/lean/soundness/SoundnessV3.lean (lines 1399-1457), where they
  print true; the third, 'pcsReadsKats_ok', is SIM.1 Do step 4 and is new here. They live under
  Midfall/Instances/ rather than beside the definitions for one reason: D-P17 keeps 'native_decide'
  and the concrete-model fixtures inside Instances/, and 'Midfall/Lowering/Stage.lean' states theorems
  (checks.sh reddens a theorem-bearing file that imports Instances/). Nothing here needs a model:
  the fixtures are the pairing-free toy codecs the scratch already used.

  THE THREE GATES
    rawDecodeAgreesKats_ok  the split 'decodeCalldata_eq_raw' is not vacuous: on the tree's own
                            calldata fixture and nine perturbations the two sides agree, the good
                            case decodes, and an in-range non-point frame is raw-OK / decode-NONE.
                            THE FALSIFIER the card's Accept names: replacing 'if g1WordsOk cd cur'
                            by 'if true' in 'rawSlots' turns this gate false (measured; see the
                            ticket report).
    xZeroCollapseKats_ok    the x = 0 divergence: constructIntermediateSets deduplicates opening
                            points BY VALUE, so at x = 0 the read schedule shrinks by one q_eval.
    pcsReadsKats_ok         'pcsReads' run on a pairing-free fixture, eight values pinned.
-/
import Midfall.Lowering.Calldata
import Midfall.Lowering.Stage
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Halo2.Exec.Verifier

set_option autoImplicit false

namespace Midfall.Instances.StageKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Lowering.Stage
open Midfall.Lowering.CdKats

local instance fact17ev : Fact (Nat.Prime 17) := ⟨by decide⟩

def rawThenLift (L : ProofCalldataLayout) (n : Nat) (cd : Bytes) :
    Option (List (Nat × Nat) × List Nat) :=
  (rawDecode (p := 17) L n cd).bind fun r =>
    (r.1.mapM (liftRaw toyCodec)).map fun ms => (ms.map msgCode, r.2.toList.map (·.toNat))

def decodeCode (L : ProofCalldataLayout) (n : Nat) (cd : Bytes) :
    Option (List (Nat × Nat) × List Nat) :=
  (decodeCalldata (p := 17) L n toyCodec cd).map fun r =>
    (r.1.map msgCode, r.2.toList.map (·.toNat))

/-- FALSIFIER FOR THE LEAF `decodeCalldata_eq_raw`: the two sides agree on the tree's own
    calldata fixture and on every perturbation `decodeCalldataGuards_ok` uses, PLUS the case the
    split exists for: a frame that passes the parser's range check and is not a group element
    (raw walk succeeds, lift fails, decode fails). -/
def rawDecodeAgreesKats_ok : Bool :=
  let cd := Midfall.Lowering.calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 7]
  let nats := Midfall.Generator.bytesToNats cd
  let replace (pos : Nat) (v : List Nat) : Bytes :=
    Midfall.Generator.bytesFromNats
      ((List.take pos nats) ++ v ++ (List.drop (pos + v.length) nats))
  let cases : List (ProofCalldataLayout × Nat × Bytes) :=
    [ (katLayout, 1, cd),
      (katLayout, 1, cd ++ Midfall.natToBytesBE 0 32),
      (katLayout, 1, replace 0 [0xde, 0xad, 0xbe, 0xef]),
      (katLayout, 1, replace 0x44 (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 415 32))),
      (katLayout, 2, cd),
      (katLayout, 1, Midfall.Lowering.calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 17]),
      (katLayout, 1, replace (100 + 128)
        (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 17 32))),
      ({ katLayout with proofCptr := 0x84 }, 1, cd),
      -- an in-range frame that is not a point of the toy group: byte 100+127 (low y byte)
      (katLayout, 1, replace (100 + 127) [9]) ]
  cases.all (fun t => rawThenLift t.1 t.2.1 t.2.2 == decodeCode t.1 t.2.1 t.2.2) &&
  -- the good case really decodes, and the last case is raw-ok / decode-none
  (decodeCode katLayout 1 cd).isSome &&
  (rawDecode (p := 17) katLayout 1 (replace (100 + 127) [9])).isSome &&
  (decodeCode katLayout 1 (replace (100 + 127) [9])).isNone

#eval rawDecodeAgreesKats_ok   -- expect true

/-- EVIDENCE FOR THE NEW DIVERGENCE (fault table, row "x = 0"). `constructIntermediateSets`
    deduplicates opening points BY VALUE (Kzg/Utils.lean:137; Rust: a HashMap keyed on the point,
    kzg/utils.rs:46-52). With rotations {0, 1} and omega = 2 over Fr 17:
      * x = 3, a commitment opened at both rotations plus two single openings: THREE point sets;
      * x = 0, the same shape: `Error.opening` (DuplicatedQuery);
      * x = 3, only single openings at the two rotations: TWO point sets;
      * x = 0, the same shape: ONE point set - the read schedule shrinks by one q_eval. -/
def xZeroCollapseKats_ok : Bool :=
  let run (x : Fr 17) (multi : Bool) :=
    let p0 := x
    let p1 := x * 2
    constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRef
      ((if multi then #[vq17 p0 5 1, vq17 p1 5 2] else #[]) ++ #[vq17 p0 7 3, vq17 p1 9 4])
  (match run 3 true with | .ok (_, ps) => ps.size == 3 | .error _ => false) &&
  (match run 0 true with | .error (Fault.error Error.opening) => true | _ => false) &&
  (match run 3 false with | .ok (_, ps) => ps.size == 2 | .error _ => false) &&
  (match run 0 false with | .ok (_, ps) => ps.size == 1 | .error _ => false)

#eval xZeroCollapseKats_ok   -- expect true

/-- DO STEP 4: 'pcsReads' run on a PAIRING-FREE fixture — 'Fr 17' with 'natG1Codec'
    (Verifier.lean:357: the 48-byte compressed slot read as a big-endian Nat) and 'fc17'
    (Domain.lean:317: numBits 5). No Group, no module, no pairing, which is exactly what
    'phaseB''s docstring advertises of the transcript half of the three phases.

    THE EIGHT VALUES PINNED: x1 = 14, x2 = 7, fCom = 42, x3raw = 2, x3 = 2,
    qEvalsOnX3 = [1, 2, 3], x4 = 10, pi = 7.

    Four further facts the pin holds fixed:
      * the READ SCHEDULE is [48, 32, 32, 32, 48] and the cursor ends exactly at the buffer end:
        the q_eval block consumes precisely 'nSets' words between 'fCom' and 'pi', and 'nSets'
        is the only datum the algebra used to supply (the card's Guidance: use
        'R.plan.proofLayout.qEvals.itemCount', which is what 'Render.nSets' now computes —
        'plan.meta_.numPointSets' is 0 at the deployment).
      * the q_eval words are read LITTLE-endian ('frOfRepr?', Common/Codec.lean:38) while the G1
        slots are big-endian ('natG1Codec'): the fixture writes them that way, and a word at or
        above p is REJECTED, so instance/eval canonicality stays visible (R-26.7).
      * 'nSets' really drives the schedule: at nSets = 2 the block is [48, 32, 32, 48], the q_eval
        list is [1, 2] and x4 moves (10 -> 15) because the absorbed state moved.
      * at numBits = 5 the truncation branch is INVISIBLE: 'truncate 5' keeps one byte and every
        element of 'Fr 17' is below 256, so x3 = x3raw = 2 under 'truncatedChallenges := true'
        AND under 'false'. Both runs are pinned to the same eight values to say so out loud —
        this fixture cannot distinguish them, and a gate that pretends otherwise is not a gate.
-/
def pcsReadsFixture (feat : Features) (nSets : Nat) (buf : Bytes) : Bool :=
  match (pcsReads (p := 17) natG1Codec fc17 feat nSets).run (Transcript.initFromBytes buf) with
  | .ok (r, t) =>
      r.x1 == 14 && r.x2 == 7 && r.fCom == 42 && r.x3raw == 2 && r.x3 == 2 &&
      r.qEvalsOnX3 == [1, 2, 3] && r.x4 == 10 && r.pi == 7 &&
      t.log.toList.map (·.1) == [48, 32, 32, 32, 48] && t.pos == buf.size
  | .error _ => false

def pcsReadsKats_ok : Bool :=
  let buf := natToBytesBE 42 48 ++ natToBytesLE 1 32 ++ natToBytesLE 2 32 ++
             natToBytesLE 3 32 ++ natToBytesBE 7 48
  let buf2 := natToBytesBE 42 48 ++ natToBytesLE 1 32 ++ natToBytesLE 2 32 ++ natToBytesBE 7 48
  let buf0 := natToBytesBE 42 48 ++ natToBytesBE 7 48
  -- the eight values, at the production feature set and again with truncation off
  pcsReadsFixture Features.solidity 3 buf &&
  pcsReadsFixture { Features.solidity with truncatedChallenges := false } 3 buf &&
  -- nSets = 2: one q_eval fewer, and x4 changes with the absorbed state
  (match (pcsReads (p := 17) natG1Codec fc17 Features.solidity 2).run (Transcript.initFromBytes buf2) with
   | .ok (r, t) => r.qEvalsOnX3 == [1, 2] && r.x4 == 15 && r.pi == 7 &&
                    t.log.toList.map (·.1) == [48, 32, 32, 48] && t.pos == buf2.size
   | .error _ => false) &&
  -- nSets = 0: the empty block, x4 back on the fCom-absorbed state
  (match (pcsReads (p := 17) natG1Codec fc17 Features.solidity 0).run (Transcript.initFromBytes buf0) with
   | .ok (r, t) => r.qEvalsOnX3 == [] && r.x4 == 3 && r.pi == 7 && t.pos == buf0.size
   | .error _ => false) &&
  -- a q_eval word at or above p is rejected: the raw walk does not silently reduce mod p
  ((pcsReads (p := 17) natG1Codec fc17 Features.solidity 3).run
      (Transcript.initFromBytes (natToBytesBE 42 48 ++ natToBytesLE 1 32 ++ natToBytesLE 2 32 ++
        natToBytesLE 17 32 ++ natToBytesBE 7 48))).isOk == false &&
  -- a truncated buffer is an unexpectedEof, not a silent short read
  ((pcsReads (p := 17) natG1Codec fc17 Features.solidity 3).run
      (Transcript.initFromBytes (natToBytesBE 42 48 ++ natToBytesLE 1 32))).isOk == false

#eval pcsReadsKats_ok   -- expect true

end Midfall.Instances.StageKats
