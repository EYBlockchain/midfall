/-
  Midfall.Instances.PoseidonCoherence

  D.3 (GEN - KAT, box 2 h, branch t/D.3 @ bd22659). Five checks that the poseidon fixture proof
  really does go through the Lean verifier at the RENDER'S OWN layout, and that a corrupted proof
  fails at the right place. Nothing here is a restatement of the Rust verdict: every compared value
  is recomputed by Lean from `proof.bin`, `vk.json` and `instances.json`, and `trace.json` is used
  only as the reference OUTPUT and as the read/squeeze SCHEDULE (which is exactly the channel
  `Midfall/Conformance/Replay.lean` was built on, and the same one hazard 6 warns about).

  ORDER OF WORK, and why it is not the card's numbering. The card runs 1, 2, 4, 5, 3: check 3 needs
  the DECODE direction of the render's G1 codec and the orchestrator already logged that codec as a
  v1 placeholder, so the four checks that do not need it are landed first. That is what happened.
  Checks 1, 2, 4 and 5 are measured and reported below; check 3 is BLOCKED, and the block is the
  placeholder, not anything D.3 can fix without editing a v1 file (forbidden by the card).

  WHAT PASSED. Check 4 and check 5, the two that decide whether the fixture proof goes through the
  Lean side at all. `Midfall.Conformance.replay` on the bundle reports 327 comparisons and ZERO
  failures, and the ten Fiat-Shamir challenges Lean squeezes for itself out of `proof.bin` - theta,
  beta, gamma, trash_challenge, y, x, x1, x2, x3, x4 - are byte-for-byte the exporter's ten, at the
  real BLS12-381 modulus, with the x3 truncation the deployed profile asks for. Check 5 gives that
  its teeth: flipping ONE byte of `proof.bin` moves the challenges from a computable index onward
  and leaves every earlier one bit-identical, at three different offsets, including the offset that
  lies after the last squeeze and must therefore move nothing.

  WHAT FAILED, and it is a finding rather than an obstacle. Checks 1 and 2 both fail, and they fail
  for ONE reason with two faces: `DeployedProfile.poseidonMeta` is typed in over
  `constraintSystemMetaDefault`, so its `protocol` field is the DEFAULT protocol plan, and its
  counts are a hand-set bag of observations (numEvals 48, numQuotients 4, numPermutationZs 3,
  numLookups 1, numTrashcans 1, numUserAdvices [8]) that no `ConstraintSystem` in the tree produces.
  So:

  * `Valid.layout` cannot hold. `ProofCalldataLayout.fromProtocol` derives the commitment sections
    from `meta_.protocol`, and the default protocol has none, so the derived layout is the plan's
    layout with every commitment section emptied: proofLen 1792 against the plan's 4320, and
    `advicePhases` = `(0, 0, 0, 0)` against `(0x64, 8, 128, 1024)` - the first differing value.
  * `Valid.circuitMeta` cannot hold either, and in BOTH directions: `ConstraintSystemMeta.new
    Features.solidity poseidonVkExec.cs 1` returns `.ok` but with numLookups 0 / numTrashcans 0 /
    numPermutationZs 0 / numQuotients 2 / numEvals 27 against the typed-in 1 / 1 / 3 / 4 / 48, and
    with numFixeds 19 / permutationChunkLen 1 / adviceQueries 11 / instanceQueries 2 against the
    typed-in 0 / 0 / 0 / 0. The first half of that list is D.2's gap A (vk.json carries no gates,
    lookups, trashcans or permutation.columns, so the CS cannot say them); the second half is the
    typed-in meta simply not recording them. Neither was patched.
  * The card's own second clause for check 1 - "its proof length equals `proof_len`" - is FALSE AS
    WRITTEN, and the reason is a conflation worth naming because C.1 will hit it: `proofLayout.proofLen`
    is the REPACKED contract proof (4320 bytes: every G1 slot at the 128-byte EIP-2537 width) while
    `trace.json.proof_len` is the COMPRESSED Rust proof (2640 bytes: every G1 slot at 48). The two
    are the same layout read at two widths, and the layout predicts BOTH exactly -
    `RepackedProofLayoutPlan.fromProofLayout planL` gives compressedLen 2640, repackedLen 4320,
    72 slots and g1Groups [8,1,3,1,1,1,4], which is the trace's own read schedule (21 point reads
    and 51 scalar reads, 2640 bytes). So the substance of check 1 survives; the literal clause does
    not, and the honest verdict on the literal clause is FAIL.

  CHECK 3, stated precisely. `poseidonE.g1 = g1CodecZ` (D.2's own rfl pin), and `g1CodecZ` is
  declared `noncomputable` with `ofCompressed? := fun _ => none`. Two consequences, and the second
  is worse than the card anticipated. (i) The decode direction accepts NOTHING: `repackPushG1` - the
  step `repackProof` uses for every G1 slot - refuses at the FIRST compressed read, offset 0, bytes
  `b5a493f87e5d23cf8401856bab9d7e52c117ee1e2859be550a27821e92515b15c1882c756d5680c672098140f6c92e4b`,
  which IS `proof.bin[0..47]` - the first advice commitment, and the byte string the exporter's own
  first `read` event records - and it is a perfectly good BLS12-381 point that
  `g1AffineCodec.ofCompressed?` takes. So the fixture CALADATA cannot even be produced at the render's codec, let alone
  accepted. (ii) Because the record is `noncomputable`, `decodeCalldata ... poseidonE.g1 cd` cannot
  be evaluated at all - `lean.dependsOnNoncomputable` - so the check is not merely false, it is not
  executable, and no `decide`/`native_decide` can reach it. `check3_target` below states it as the
  Prop it is; `check3_repackRefuses` proves the refusal for every offset, by rfl off the placeholder.
  The codec was NOT swapped and the fixture was NOT bent. The DIAGNOSTIC gates at the VM-decodable
  codec are labelled as diagnostics and decide nothing about check 3: they localise the blocker to
  the codec by showing the layout and the decoder are fine - `decodeCalldata` at `g1AffineCodec`
  accepts the fixture calldata and returns 72 messages and 1 instance.

  WHAT CONSUMES THIS. C.1's headline `lowering_equivalence_poseidon` needs a `Render` whose `Valid`
  holds. `Valid.circuitMeta` and `Valid.layout` are the two clauses that fail here, and they fail on
  the SAME typed-in meta, so the gate C.1 needs does not currently close at the deployed profile. The
  opening is not a fixture edit and not a codec edit: it is a `poseidonMeta` whose `protocol` is the
  real `ProtocolPlan` - which needs the constraint system D.2 named as gap A.

  WHY THE FIXTURE ARRIVES BY IO AND NOT BY `include_str`. `vk.json`, `instances.json` and
  `trace.json` are text and D.2 already bakes two of them in; `proof.bin` is BINARY (byte 0 is 0xb5,
  so `include_str` refuses it: it is not UTF-8). The bundle therefore comes from one IO read, the
  same channel `Conformance.lean`'s `loadBundle` uses, with the candidate-path shape D.1 uses for
  its `.sol` fixtures. That makes the check-4/5 gates `IO Bool` like D.1's four IO gates, and it
  makes them honest: the bytes compared are the bytes on disk.
-/
import Midfall.Instances.PoseidonEnv
import Midfall.Conformance.Replay
import Midfall.Lowering.Calldata

namespace Midfall.Instances.PoseidonCoherence

open Midfall Midfall.Halo2 Midfall.Conformance Midfall.Instances Midfall.Lowering
open Midfall.Generator Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonEnv

/-- The scalar modulus the replay runs at - the same `Midfall.Conformance.R` the Replay module
    abbreviates, restated here because its `Fact` instance is `local` to that file. -/
abbrev Rmod : ℕ := Midfall.Assumptions.r

local instance factRmod : Fact (Nat.Prime Rmod) := inferInstance

/-- The render's own calldata layout: `poseidonPlanV2.proofLayout`, i.e. the deployed profile's
    `poseidonProofLayout`. -/
def planL : ProofCalldataLayout := poseidonPlanV2.proofLayout

/-- The render's own circuit meta: `poseidonPlanV2.meta_`, i.e. the deployed profile's typed-in
    `poseidonMeta`. -/
def planM : ConstraintSystemMeta := poseidonPlanV2.meta_

/-- The repack plan the layout implies: the slot schedule the contract's parser walks. -/
def repackedPlan : RepackedProofLayoutPlan :=
  RepackedProofLayoutPlan.fromProofLayout planL

/-! ## 0. The bundle -/

def fixtureDirs : List String :=
  ["fixtures/conformance/poseidon", "formal/fixtures/conformance/poseidon"]

def readTextOrEmpty (path : String) : IO String := do
  try
    IO.FS.readFile path
  catch
    _ => pure ""

def readBinOrEmpty (path : String) : IO Bytes := do
  try
    IO.FS.readBinFile path
  catch
    _ => pure Bytes.empty

def readTextFirst (cs : List String) : IO String :=
  cs.foldl (fun acc p => acc >>= fun got => if got != "" then pure got else readTextOrEmpty p) (pure "")

def readBinFirst (cs : List String) : IO Bytes :=
  cs.foldl (fun acc p => acc >>= fun got => if got.size > 0 then pure got else readBinOrEmpty p)
    (pure Bytes.empty)

/-- The conformance bundle, read from the tracked fixture directory. `.error` on any parse failure,
    and every gate below goes FALSE on `.error` rather than passing on an empty bundle. -/
def coherenceBundle : IO (Except String Bundle) := do
  let vkj ← readTextFirst (fixtureDirs.map (fun d => d ++ "/vk.json"))
  let inj ← readTextFirst (fixtureDirs.map (fun d => d ++ "/instances.json"))
  let trj ← readTextFirst (fixtureDirs.map (fun d => d ++ "/trace.json"))
  let prf ← readBinFirst (fixtureDirs.map (fun d => d ++ "/proof.bin"))
  pure <| do
    let (committed, pubCols) ← parseInstances (← jParse inj)
    let vkInfo ← parseVk (← jParse vkj)
    let trace ← parseTrace (← jParse trj)
    .ok { vk := vkInfo, committed := committed, publicCols := pubCols,
          proof := prf, trace := trace }

/-- Run a bundle-producing gate, with `.error` folded to `false`. -/
def onBundle (f : Bundle → Bool) : IO Bool :=
  coherenceBundle >>= fun bb => pure (match bb with | .error _ => false | .ok b => f b)

/-! ## CHECK 1 - the layout clause -/

/-- THE LITERAL CLAUSE. `Render.Valid.layout` (LoweringV2/Statements.lean:146-147) read at the
    plan's own meta: `ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr
    meta_.numEvals meta_.numPointSets = .ok plan.proofLayout`. VERIFY-FIRST (b), ANSWERED: the
    clause IS computable - `ProofCalldataLayout` derives `BEq` (Abi.lean:250) and the derivation is
    a plain `Nat`/`List` walk - so no `native_decide` is needed anywhere in this file. What it is NOT
    is satisfiable: the derived layout empties every commitment section, because `meta_.protocol` is
    `protocolPlanDefault`. Measured first difference: `advicePhases[0]` = (start 0, count 0,
    itemBytes 0, byteLen 0) against the plan's (0x64, 8, 128, 1024); proofLen 1792 against 4320. -/
def check1_validLayout_holds : Bool :=
  match ProofCalldataLayout.fromProtocol planM.protocol abiVerifyProofProofCptr
      planM.numEvals planM.numPointSets with
  | .ok L => L == planL
  | .error _ => false

/-- The derived layout's proof length, for the report line. -/
def check1_derivedProofLen : Nat :=
  match ProofCalldataLayout.fromProtocol planM.protocol abiVerifyProofProofCptr
      planM.numEvals planM.numPointSets with
  | .ok L => L.proofLen
  | .error _ => 0

/-- THE CARD'S SECOND CLAUSE, LITERALLY: `proofLayout.proofLen == trace.proof_len`. FALSE AS
    WRITTEN - 4320 against 2640 - and false by construction, not by drift: `proofLen` is the
    REPACKED contract length (G1 slots at 128 bytes) and `proof_len` is the COMPRESSED Rust length
    (G1 slots at 48). See the header. -/
def check1_proofLen_eq_traceProofLen : IO Bool :=
  onBundle fun b => planL.proofLen == b.trace.proofLen

/-- THE SUBSTANCE OF CHECK 1, repaired. The layout predicts the fixture proof exactly, at BOTH
    widths, and its slot schedule IS the trace's read schedule: 72 slots, 21 of them G1, 51 of them
    words, compressedLen = 2640 = proof.bin = trace.proof_len, repackedLen = 4320 = proofLen. -/
def check1_layoutPredictsFixtureProof_ok : IO Bool := onBundle fun b =>
  repackedPlan.compressedLen == b.proof.size
    && repackedPlan.compressedLen == b.trace.proofLen
    && repackedPlan.compressedLen == 2640
    && repackedPlan.repackedLen == planL.proofLen
    && repackedPlan.repackedLen == 4320
    && repackedPlan.slots.length == (b.trace.events.filter fun e =>
          match e with | .read _ _ _ => true | _ => false).size
    && repackedPlan.slots.length == 72
    && repackedPlan.g1Groups == [8, 1, 3, 1, 1, 1, 4]
    && repackedPlan.prefixG1Count == 19
    && repackedPlan.numEvals == 48
    && repackedPlan.numPointSets == 3
    && planL.proofCptr == abiVerifyProofProofCptr
    && planL.proofEnd == planL.proofCptr + planL.proofLen

/-- The section-shape identity between the two widths: 21 G1 slots and 51 word slots tile the
    repacked proof at 128/32 and the compressed proof at 48/32. This is the clause the card wanted
    by "proof length equals proof_len", stated at the width where it is true. -/
def check1_twoWidths_ok : Bool :=
  let g1s := (planL.advicePhases.map (fun s => s.itemCount)).foldl (· + ·) 0
    + planL.lookupMultiplicities.itemCount + planL.permutationProducts.itemCount
    + (planL.lookups.map (fun l => l.helpers.itemCount + l.accumulator.itemCount)).foldl (· + ·) 0
    + planL.trash.itemCount + planL.quotientLimbs.itemCount + planL.fCom.itemCount
    + planL.pi.itemCount
  let ws := planL.evals.itemCount + planL.qEvals.itemCount
  g1s == 21 && ws == 51 && g1s * 48 + ws * 32 == 2640 && g1s * 128 + ws * 32 == 4320

/-! ## CHECK 2 - the meta clause -/

/-- What the ported constructor makes of the deployment's constraint system. It SUCCEEDS - the
    failure is in the data, not in a fault. -/
def derivedMeta : Except Fault ConstraintSystemMeta :=
  ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1

/-- GATE: the constructor returns `.ok`. True, so the mismatch below is a content mismatch and not
    a refusal, which is what makes the attribution in `check2_failureAttribution_ok` meaningful. -/
def check2_constructor_isOk : Bool :=
  match derivedMeta with | .ok _ => true | .error _ => false

/-- THE LITERAL CLAUSE. `Render.Valid.circuitMeta` (Statements.lean:143-144) at the deployment:
    `ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 = .ok poseidonPlanV2.meta_`.
    FALSE, and the card named this as a FINDING rather than an obstacle. -/
def check2_circuitMeta_holds : Bool :=
  match derivedMeta with | .ok m => m == planM | .error _ => false

/-- THE ATTRIBUTION, RE-MEASURED BY F.1 HALF 2. D.3's version of this gate pinned the derived meta
    against a TYPED-IN one and listed eleven places where they disagreed, and every one of those
    disagreements was the missing constraint system. Now the plan's meta IS the derived meta, so the
    gate reads the other way: the two are the same record, and the numbers that used to be zeros on
    the derived side are the deployment's own. Each is still spelled out, because a gate that only
    said `m == planM` would not say WHICH field moved if it ever stopped holding. -/
def check2_failureAttribution_ok : Bool :=
  match derivedMeta with
  | .error _ => false
  | .ok m =>
      m == planM
      -- the four structures cs.json supplied, non-zero on the derived side and equal to the plan's.
      && m.numLookups == 1 && m.numTrashcans == 1 && m.numPermutationZs == 3
      && m.permutationColumns.length == 8
      -- the counts that used to be the gap, now derived rather than observed.
      && m.numFixeds == 19 && m.permutationChunkLen == 3
      && m.adviceQueries.length == 11 && m.instanceQueries.length == 2
      && m.numEvals == 48 && m.numQuotients == 4 && m.rotationLast == -9
      && m.simpleSelectorCols == [13, 14, 15, 17] && m.numCommittedInstances == 1
      -- and the field D.3 called the crux: the protocol is the real plan, not the default.
      && (m.protocol != Midfall.Generator.protocolPlanDefault)
      && m.protocol.pcsQueries.length == 49 && m.protocol.numFixeds == 19

/-- **THE CRUX, FLIPPED BY F.1.** What D.3 proved by `rfl` - that the plan's protocol field IS
    `protocolPlanDefault` - is now FALSE, and that is the card's whole point. `poseidonMeta` is
    `ConstraintSystemMeta.new Features.solidity poseidonCs 1`, and `poseidonCs` now carries the
    gates, lookups, trashcans and permutation columns that `cs.json` exports, so the plan carries
    a real `ProtocolPlan`: 19 fixeds, 8 permutation columns, 11 advice queries, a 49-entry PCS
    query schedule. Proved by a field the default cannot fake. -/
theorem check2_typedInProtocolIsReal : planM.protocol ≠ Midfall.Generator.protocolPlanDefault := by
  intro h
  have h1 : planM.protocol.numFixeds = 19 := by native_decide
  have h2 : (Midfall.Generator.protocolPlanDefault : Midfall.Generator.ProtocolPlan).numFixeds = 0 := rfl
  rw [h] at h1
  omega

/-- The three counts D.2 gate 14 already pinned as agreeing, restated so this file does not read as
    "nothing agrees": numLookups and numTrashcans agree with vk.json on the DERIVED side only
    through the CS, and numSimpleSelectors agrees on both. -/
def check2_agreeingCounts_ok : Bool :=
  match derivedMeta with
  | .error _ => false
  | .ok m => m.numSimpleSelectors == planM.numSimpleSelectors
    && m.numSimpleSelectors == 4 && m.numUserChallenges.length == planM.numUserChallenges.length

/-! ## CHECK 4 - the transcript -/

/-- The exporter's ten recorded challenges, in order. -/
def traceChallengeList (b : Bundle) : Array (String × Bytes) :=
  b.trace.events.filterMap fun e =>
    match e with | .squeeze n _ c _ => some (n, c) | _ => none

/-- The same list lifted into `Option` so a refused read can be represented at its own index. -/
def traceChallengeListO (b : Bundle) : Array (String × Option Bytes) :=
  (traceChallengeList b).map fun (n, c) => (n, some c)

structure ChSt where
  t : Transcript
  idx : Nat
  out : Array (String × Option Bytes)

/-- **LEAN'S OWN CHALLENGES**, squeezed from `proof` at the render's transcript. The trace supplies
    only the schedule - which read, which squeeze, in what order - and every absorbed byte and every
    squeezed scalar is computed here: the prefix from `vk.json` + `instances.json` through
    `derivePrefix`, the reads through the real BLS12-381 codecs, the squeeze through keccak and
    `frOfDigest` at `Rmod`, with the `x3` truncation the VK's `truncated_challenges` asks for. A
    read Lean refuses leaves NO entry, which is what `coherenceChallenges` turns into a `none`. -/
def leanChallenges (b : Bundle) (proof : Bytes) : Array (String × Option Bytes) :=
  let pre : Array (String × Abs) := match derivePrefix b with | .ok p => p | .error _ => #[]
  let st := b.trace.events.foldl (fun (st : ChSt) (e : Ev) =>
    match e with
    | .absorb _ _ =>
        match pre[st.idx]? with
        | some (_, abs) => { t := abs.apply st.t, idx := st.idx + 1, out := st.out }
        | none => st
    | .read _ wire _ =>
        if wire.size == 48 then
          match st.t.read hG1 with
          | .ok (_, t2) => { t := t2, idx := st.idx, out := st.out }
          | .error _ => st
        else if wire.size == 32 then
          match st.t.read hFr with
          | .ok (_, t2) => { t := t2, idx := st.idx, out := st.out }
          | .error _ => st
        else st
    | .squeeze n _ _ _ =>
        let (d, t2) := st.t.squeeze
        let raw : Fr Rmod := frOfDigest (p := Rmod) (bytesToWordBE d)
        let c := if n == "x3" && b.vk.truncatedChallenges then
          truncate b.vk.scalarNumBits raw else raw
        { t := t2, idx := st.idx, out := st.out.push (n, some (hFr.toInput c)) })
    ({ t := Transcript.initFromBytes proof, idx := 0, out := #[] } : ChSt)
  st.out

/-- Aligned to the trace's challenge list by NAME, so a desynchronised schedule shows as `none` at
    the index where it diverged rather than as a shifted list. -/
def coherenceChallenges (b : Bundle) (proof : Bytes) : Array (String × Option Bytes) :=
  let got := leanChallenges b proof
  let tc := traceChallengeList b
  (List.range tc.size).toArray.map fun i =>
    let name := (tc[i]!).1
    match got[i]? with
    | some (n, c) => (name, if n == name then c else none)
    | none => (name, none)

/-- CHECK 4. Every challenge Lean squeezes equals the exporter's, byte for byte, and the names are
    the exporter's names in the exporter's order. -/
def check4_challenges_match_ok : IO Bool := onBundle fun b =>
  let lc := coherenceChallenges b b.proof
  let tc := traceChallengeListO b
  lc.size == 10 && lc == tc
    && (lc.toList.map (fun p => p.1))
        == ["theta", "beta", "gamma", "trash_challenge", "y", "x", "x1", "x2", "x3", "x4"]

/-- CHECK 4, the whole replay: every comparison `Midfall.Conformance.replay` makes - prefix tags,
    absorbed bytes, wire bytes, digests, challenges, absorb-before lists, the MSM terms, the
    verdict, proof_len, the Rust pairing flag and the error class - passes with an empty failure
    list. Measured: 327 comparisons, 0 failures. -/
def check4_replay_clean_ok : IO Bool := onBundle fun b =>
  let r := replay b
  r.failures.isEmpty && r.checks == 327 && r.absorbs == 4 && r.reads == 72 && r.squeezes == 10
    && r.terms == 46 && b.trace.leftTerms.size == 1 && b.trace.rightTerms.size == 45

/-- The prefix Lean derives from vk.json + instances.json is the four absorbs the trace records,
    and it is consumed exactly: this is the half of check 4 that a typed-in VK could not fake. -/
def check4_prefix_derived_ok : IO Bool := onBundle fun b =>
  match derivePrefix b with
  | .error _ => false
  | .ok p => p.size == 4
    && p.toList.map (fun q => q.1)
        == ["vk_repr", "committed_instance[0]", "instance_len[0]", "instance[0][0]"]

/-! ## CHECK 5 - the negative control -/

/-- Flip the parity of one byte of a proof. Total: an out-of-range index leaves the bytes alone,
    which the gates below rule out by construction. -/
def flipByte (p : Bytes) (i : Nat) : Bytes :=
  let l := p.data.toList
  match (l.drop i).head? with
  | some b =>
      ByteArray.mk ((l.take i ++
        [UInt8.ofNat (if b.toNat % 2 == 0 then b.toNat + 1 else b.toNat - 1)] ++
        l.drop (i + 1)).toArray)
  | none => p

/-- The first index at which two challenge lists differ. -/
def firstChallengeDiff
    (a b : Array (String × Option Bytes)) : Option Nat :=
  ((List.range (Nat.min a.size b.size)).filter (fun i => a[i]! ≠ b[i]!)).head?

/-- Every index below the first difference is bit-identical. -/
def allBefore (a b : Array (String × Option Bytes)) (upto : Nat) : Bool :=
  (List.range upto).all (fun i => a[i]! == b[i]!)

def nDiff (a b : Array (String × Option Bytes)) : Nat :=
  ((List.range a.size).filter (fun i => a[i]! ≠ b[i]!)).length

/-- CHECK 5a, THE PRIMARY FLIP. Byte 943 is the LAST byte of the first scalar read
    (`proof_committed_instance_eval`, offset 912..943), which is squeezed into nothing until `x1`
    - the seventh challenge, index 6. So: indices 0..5 (theta, beta, gamma, trash_challenge, y, x)
    MUST be untouched and indices 6..9 (x1, x2, x3, x4) MUST all change. Measured: first differing
    challenge index = 6, four challenges differ, none before. -/
def check5_flipFirstEval_ok : IO Bool := onBundle fun b =>
  let base := coherenceChallenges b b.proof
  let bad := coherenceChallenges b (flipByte b.proof 943)
  firstChallengeDiff bad base == some 6 && allBefore bad base 6 && nDiff bad base == 4
    && b.proof.size == 2640

/-- CHECK 5b, the flip at the FRONT of the proof. Byte 0 is the first byte of the first advice
    commitment, absorbed before `theta`, so EVERY challenge from index 0 onward must change and
    there is nothing before it to protect. This is the case that would silently pass a replay whose
    transcript never advanced. -/
def check5_flipFirstPoint_ok : IO Bool := onBundle fun b =>
  let base := coherenceChallenges b b.proof
  let bad := coherenceChallenges b (flipByte b.proof 0)
  firstChallengeDiff bad base == some 0 && nDiff bad base == 10

/-- CHECK 5c, the flip AFTER the last squeeze. Byte 2592 is the first byte of `proof_pi`, the 72nd
    read, which is absorbed after `x4` - so no challenge may move. A harness that recomputed the
    challenges from the trace instead of from the bytes would move here, and that is the bug class
    this control exists to catch. -/
def check5_flipAfterLastSqueeze_ok : IO Bool := onBundle fun b =>
  let base := coherenceChallenges b b.proof
  let bad := coherenceChallenges b (flipByte b.proof 2592)
  firstChallengeDiff bad base == none && nDiff bad base == 0

/-- CHECK 5d, the whole corrupted bundle through the replay: the failures are non-empty, and the
    first failure names a squeeze. So check 4 cannot be green by comparing nothing. -/
def check5_replayReddens_ok : IO Bool := onBundle fun b =>
  let r := replay { b with proof := flipByte b.proof 943 }
  ¬ r.failures.isEmpty && r.checks == 327

/-! ## CHECK 3 - the decode direction, attempted last -/

/-- poseidonE's G1 codec IS `g1CodecZ` - D.2's own pin, cited rather than restated. -/
theorem check3_poseidonE_g1_isG1CodecZ : poseidonE.g1 = g1CodecZ := rfl

/-- **THE BLOCKER, PROVED.** The render's codec decodes NO compressed point at all: the v1
    placeholder `g1CodecZ.ofCompressed? := fun _ => none` (G1Agreement.lean:2006) is what the
    deployment inherits. By `rfl`, i.e. by the kernel and not by a tactic. -/
theorem check3_codec_decodes_no_compressed_point :
    ∀ b : Bytes, poseidonE.g1.ofCompressed? b = none := fun _ => rfl

/-- The refusal, one step up: `repackPushG1` is the step `repackProof` runs for every G1 slot, and
    at the render's codec it refuses at EVERY offset, for EVERY proof, with
    `RepackError.invalidCompressedG1`. So the fixture CALADATA cannot be produced at `poseidonE.g1`
    - the check has no input to be run on. -/
theorem check3_repackRefuses (compressed : Bytes) (cursor : Nat) (b : Bytes)
    (hb : bytesTake compressed cursor g1CompressedBytes = some b) :
    repackPushG1 poseidonE.g1 compressed cursor Bytes.empty =
      .error (ApiFault.error (GeneratorError.repack
        (RepackError.invalidCompressedG1 (offset := cursor) (bytesHex := hexEncodeLower b)))) := by
  unfold repackPushG1
  simp only [hb, check3_codec_decodes_no_compressed_point]

/-- THE CHECK 3 TARGET, stated. It elaborates as a Prop and it cannot be COMPUTED: `poseidonE.g1`
    is a `noncomputable def`, so any attempt to evaluate this - `decide`, `native_decide`, `#eval` -
    is refused with `lean.dependsOnNoncomputable: ... it depends on 'g1CodecZ', which is
    'noncomputable'` (measured on this branch). That is the precise sense in which check 3 is
    BLOCKED rather than FALSE: the proposition is not decidable in this tree, and its compressed
    decoder answers `none` for every input even where the type would allow a decision. -/
def check3_target (cd : Bytes) : Prop :=
  (decodeCalldata (p := Rmod) planL 1 poseidonE.g1 cd).isSome

/-- The first differing value, as a term the VM CAN run: the bytes at the head of `proof.bin` are a
    real BLS12-381 point at the one computable compressed codec in the tree, so the fixture is not
    the problem and the render's codec is. -/
def firstProofPoint : Bytes :=
  match jHexBytes
      "b5a493f87e5d23cf8401856bab9d7e52c117ee1e2859be550a27821e92515b15c1882c756d5680c672098140f6c92e4b"
      48 with
  | .ok bs => bs
  | .error _ => Bytes.empty

/-- DIAGNOSTIC, NOT THE GATE. The fixture's first compressed point decodes at `g1AffineCodec` and
    is 48 bytes wide, while `poseidonE.g1.ofCompressed?` of the SAME bytes is `none` by the theorem
    above. This is the first differing value check 3 would report. -/
def check3_firstDifferingValue_ok : Bool :=
  firstProofPoint.size == 48 && (g1AffineCodec.ofCompressed? firstProofPoint).isSome

/-- DIAGNOSTIC, NOT THE GATE. The layout and the decoder are sound: at a codec that can decode, the
    fixture proof repacks to exactly `proofLayout.proofLen` bytes, the calldata built from it
    decodes through `decodeCalldata` at the render's OWN layout, and it yields the layout's 72
    slots and the one public instance. Nothing here substitutes for check 3 - the codec is not
    `poseidonE.g1` - it localises the failure to the codec and away from the layout. -/
def check3_decoderAndLayout_ok : IO Bool := onBundle fun b =>
  match repackProof g1AffineCodec repackedPlan b.proof with
  | .error _ => false
  | .ok rp =>
      let w := BitVec.ofNat 256
        (bytesToNatBE ((b.publicCols.getD 0 (#[] : Array Bytes)).getD 0 Bytes.empty))
      rp.size == planL.proofLen
        && match decodeCalldata (p := Rmod) planL 1 g1AffineCodec
               (Midfall.Generator.encodeCalldata rp [w]) with
           | none => false
           | some (ms, inst) => ms.length == 72 && inst.size == 1

end Midfall.Instances.PoseidonCoherence

/-! ## THE GATES -/

-- CHECK 1
#eval Midfall.Instances.PoseidonCoherence.check1_validLayout_holds -- expect false
#eval Midfall.Instances.PoseidonCoherence.check1_derivedProofLen -- expect 4224 (was 1792 at the default protocol)
#eval Midfall.Instances.PoseidonCoherence.check1_proofLen_eq_traceProofLen -- expect false
#eval Midfall.Instances.PoseidonCoherence.check1_layoutPredictsFixtureProof_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check1_twoWidths_ok -- expect true

-- CHECK 2
#eval Midfall.Instances.PoseidonCoherence.check2_constructor_isOk -- expect true
#eval Midfall.Instances.PoseidonCoherence.check2_circuitMeta_holds -- expect true since F.1
#eval Midfall.Instances.PoseidonCoherence.check2_failureAttribution_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check2_agreeingCounts_ok -- expect true

-- CHECK 4
#eval Midfall.Instances.PoseidonCoherence.check4_challenges_match_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check4_replay_clean_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check4_prefix_derived_ok -- expect true

-- CHECK 5
#eval Midfall.Instances.PoseidonCoherence.check5_flipFirstEval_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check5_flipFirstPoint_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check5_flipAfterLastSqueeze_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check5_replayReddens_ok -- expect true

-- CHECK 3
#eval Midfall.Instances.PoseidonCoherence.check3_firstDifferingValue_ok -- expect true
#eval Midfall.Instances.PoseidonCoherence.check3_decoderAndLayout_ok -- expect true
