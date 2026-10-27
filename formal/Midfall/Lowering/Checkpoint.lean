-- |
-- Midfall.Lowering.Checkpoint
--
-- P-SE stage 3, file 1 of 3 (docs/plans/P-SE-stage3.md file row 1; design0.md
-- section "Midfall.Lowering.Checkpoint / Partial / Checkpoint.liveAt").
--
-- WHAT THIS FILE IS FOR. The seven per-partial correctness theorems
-- (vkLoading_spec, transcriptParser_spec, lagrange_spec, quotientLin_spec,
-- pcs_spec, finalPairing_spec, traceReturn_spec) are each of the shape: every run
-- of partial q starting from the memory invariant at checkpoint q.pre ends either
-- reverted or in the invariant at q.post. That needs three things, and this file
-- supplies all three: a name for the boundary between two partials (Checkpoint),
-- a name for the partial that lives between two boundaries (Partial), and a
-- decision procedure for which memory regions may be mentioned at all at a given
-- boundary (Checkpoint.liveAt).
--
-- WHY liveAt IS NOT JUST (lifetime == permanent). D-P18: the deployed layout
-- registers 54 same-byte different-phase pairs, so a phase-scoped region is
-- normally dead the moment its phase ends, and an invariant that mentioned it
-- would be asserting bytes the next partial is free to overwrite. The one
-- exception is forced by the layout itself and is attack finding 12:
-- selector_accumulators is registered with lifetime
-- (MemoryLifetime.phase MemoryPhase.pcsFinalMsm) (LayoutMemory.lean:268-270) but
-- it is WRITTEN by the quotient partial (QuotientAndLinearization.yul:47-49) and
-- READ by the PCS lowering (kzg/mod.rs:1373, :1785). A blanket
-- (liveAt _ (.phase _) = false) therefore forbids the one clause the
-- quotient-to-pcs handoff needs, and a blanket grant for that lifetime would
-- assert those bytes at .pairing, after the PCS has consumed them and with the
-- accumulator MSM scratch rooted at the same base. So liveness is a function of
-- BOTH the lifetime and the checkpoint, and this file is where that function
-- lives.
--
-- WHAT IS NOT HERE. The snapshot the invariant relates memory to (Snapshot.lean),
-- the invariant itself (Inv.lean), and any Yul AST: no Lean function returns the
-- block of a verifier partial yet (P-13 is unlanded), so Partial names the
-- partials, it does not carry their code.

import Midfall.Generator.Layout
import Midfall.Generator.LayoutMemory

namespace Midfall.Lowering
open Midfall.Generator

/-- The seven boundaries between verifier partials, in the order the main assembly
    block runs them (Halo2Verifier.sol:217-229 include order). These are the
    indices of PLAN 9.5 Inv k.

    This is deliberately NOT Generator.MemoryPhase (Layout.lean:407): those
    sixteen constructors are scratch-buffer lifetimes used by the memory planner,
    there are more of them than there are partials, several partials share one
    phase, and the phase a region was allocated in is not the boundary at which the
    region is live. Finding 12 is exactly that mismatch. -/
inductive Checkpoint
  /-- Before any partial has run: the dispatcher has returned and memory holds only
      what the deployment put there. -/
  | start
  /-- After VkLoading.yul: the VK payload image is in memory. -/
  | vk
  /-- After TranscriptProofParser.yul: challenges, commitments and evals. -/
  | transcript
  /-- After Lagrange.yul: x_n, the three Lagrange slots and the instance eval. -/
  | lagrange
  /-- After QuotientAndLinearization.yul: quotient eval and selector buckets. -/
  | quotient
  /-- After Pcs.yul: f_eval, v, final_com and the two pairing inputs. -/
  | pcs
  /-- After FinalPairing.yul: the decision has been taken. -/
  | pairing
  deriving DecidableEq, Repr, BEq

/-- The seven production partials in include order (Halo2Verifier.sol:217-229).
    The two helper partials P1 Partial carried (assemblyHelpers,
    accumulatorHelpers) are not boundaries: they are hoisted functions, not slices
    of the main block, so they get no checkpoint (design0: production partials
    only). -/
inductive Partial
  | vkLoading
  | transcriptParser
  | lagrange
  | quotientLin
  | pcs
  | finalPairing
  | traceReturn
  deriving DecidableEq, Repr, BEq

/-- The boundary a partial starts at. -/
def Partial.pre : Partial → Checkpoint
  | .vkLoading => .start
  | .transcriptParser => .vk
  | .lagrange => .transcript
  | .quotientLin => .lagrange
  | .pcs => .quotient
  | .finalPairing => .pcs
  | .traceReturn => .pairing

/-- The boundary after k. Saturating at .pairing, which has no successor: the only
    thing that runs after the pairing decision is the return. -/
def Checkpoint.next : Checkpoint → Checkpoint
  | .start => .vk
  | .vk => .transcript
  | .transcript => .lagrange
  | .lagrange => .quotient
  | .quotient => .pcs
  | .pcs => .pairing
  | .pairing => .pairing

/-- The boundary a partial hands off at. For traceReturn this is the saturated last
    checkpoint: that partial does not establish an invariant, it returns abiTrue or
    reverts, which is why its spec is a postcondition on the halt record and not an
    Inv-next form (design0, traceReturn_sound). -/
def Partial.post : Partial → Checkpoint := fun q => q.pre.next

/-- Position in the run order. LE on Checkpoint is defined through this, so the
    clause guards in Inv are plain index comparisons and the order is pinned in one
    place. -/
def Checkpoint.idx : Checkpoint → Nat
  | .start => 0
  | .vk => 1
  | .transcript => 2
  | .lagrange => 3
  | .quotient => 4
  | .pcs => 5
  | .pairing => 6

instance : LE Checkpoint := ⟨fun a b => a.idx ≤ b.idx⟩

/-- The checkpoints in run order, for the gates below and for any later file that
    has to quantify over all of them. -/
def checkpoints : List Checkpoint :=
  [.start, .vk, .transcript, .lagrange, .quotient, .pcs, .pairing]

/-- The production partials in include order. -/
def partials : List Partial :=
  [.vkLoading, .transcriptParser, .lagrange, .quotientLin, .pcs, .finalPairing,
    .traceReturn]

/-- The sixteen scratch phases the memory planner knows about, written out rather
    than derived: MemoryPhase has no FinEnum, and listing them is itself a gate -
    a seventeenth constructor would leave this list stale and the exhaustive
    liveness check below would silently stop covering it. -/
def memoryPhases : List MemoryPhase :=
  [ .vkConstructorPayload, .constructorSmoke, .transcript, .scalarInv,
    .lagrangeBatchInvert, .quotientVm, .pcsFixed, .pcsQEvalSourceTable,
    .pcsQComTrace, .pcsFinalMsm, .pcsPairing, .accumulatorMsm,
    .accumulatorPairingBatch, .finalPairing, .verifierReturn, .quotientReturn ]

/-- Which region lifetimes still carry facts AT CHECKPOINT k.

    Permanent regions are live everywhere: the layout planner refuses to let a
    permanent region overlap anything (Layout.lean:444, memoryLifetimeIntersects),
    so nothing may overwrite them between partials.

    Phase-scoped regions are dead everywhere EXCEPT the one lifetime the layout
    mislabels, and that exception is the whole reason this function takes a
    checkpoint. selector_accumulators is registered as
    (MemoryLifetime.phase MemoryPhase.pcsFinalMsm) (LayoutMemory.lean:268-270)
    although the quotient partial writes it and the PCS lowering reads it; so those
    bytes are live at .quotient (just written) and at .pcs (about to be read) and
    dead before and after. Every other phase lifetime is dead at every checkpoint,
    which is what D-P18 says about scratch memory.

    Note what the exception is keyed on: the LIFETIME, not the region name. Two
    regions carry that lifetime - selector_accumulators (LayoutMemory.lean:268-270)
    and pcs_final_msm (:303-304) - so granting the lifetime grants both. That is
    harmless and it is not sloppy: Inv mentions only the selector base, and
    selectorAccLifetimeKats_ok pins which two regions the grant covers, so a third
    region joining the class reddens a gate instead of silently widening it. -/
def Checkpoint.liveAt (k : Checkpoint) : MemoryLifetime → Bool
  | .permanent => true
  | .phase .pcsFinalMsm => k == .quotient || k == .pcs
  | .phase _ => false

/-- liveAt applied to a whole region, for callers that have a MemoryRegion rather
    than a MemoryLifetime. -/
def Checkpoint.liveRegionAt (k : Checkpoint) (r : MemoryRegion) : Bool :=
  Checkpoint.liveAt k r.lifetime

/-- The lifetime a named region was registered with in a given layout, or none when
    the layout has no such region. Inv uses this so that a clause about a
    phase-scoped region is guarded by the SAME table the planner produced rather
    than by a lifetime copy-pasted into the invariant. -/
def regionLifetime (l : VerifierMemoryLayout) (name : String) : Option MemoryLifetime :=
  (l.map.region name).map fun r => r.lifetime

/-- Is the named region of this layout live at checkpoint k? A missing region
    answers false, so a clause guarded by this is dropped rather than asserted over
    an address the planner never reserved. -/
def Checkpoint.liveRegionNamed (k : Checkpoint) (l : VerifierMemoryLayout)
    (name : String) : Bool :=
  match regionLifetime l name with
  | some lt => Checkpoint.liveAt k lt
  | none => false

/-! ### Known-answer checks

    Executable booleans in the style of Exec/Accumulator.lean: each one is a
    def ... : Bool evaluated by scripts/kat_gate.py, and each one is written so
    that a plausible wrong design choice reddens it rather than leaving it green. -/

/-- Every permanent region is live at every checkpoint, and no phase region other
    than the selector class is live anywhere. Refuted by a liveAt that returns
    false for .permanent (which would make Inv empty at every checkpoint) or that
    grants a scratch phase (which would let Inv assert dead bytes). -/
def liveAtKats_ok : Bool :=
  -- permanent: live at all seven boundaries
  (checkpoints.all fun k => Checkpoint.liveAt k .permanent) &&
  -- every scratch phase except the one finding 12 forces: dead at all seven
  (memoryPhases.filter (fun ph => ph != MemoryPhase.pcsFinalMsm)).all fun ph =>
    checkpoints.all fun k => ! Checkpoint.liveAt k (.phase ph)

/-- FINDING 12, PINNED. The selector-accumulator lifetime is live at exactly the two
    boundaries between which the contract reads it: written by the quotient partial,
    consumed by the PCS partial, dead at .start, .vk, .transcript and .lagrange (not
    written yet) and dead at .pairing (consumed, and the accumulator MSM scratch
    allocator is rooted at the same base - LayoutMemory.lean:297, :307-310).

    A liveAt that returns false here is the bug the attack names: Inv would drop its
    selector clause at .quotient and quotientLin_spec could not be proved. A liveAt
    that returns true at .pairing is the mirror bug: Inv would assert bytes the
    accumulator path is free to clobber. -/
def liveAtSelectorKats_ok : Bool :=
  let lt := MemoryLifetime.phase MemoryPhase.pcsFinalMsm
  checkpoints.all fun k => Checkpoint.liveAt k lt == (k == .quotient || k == .pcs)

/-- The liveness grant is keyed on the lifetime, so it covers exactly two regions of
    the deployed layout. This reads the artifact at gate time rather than repeating a
    pasted string (the standing rule from D-P19), and it fails if a third region is
    ever registered under that lifetime: that would widen the grant silently, which
    is what this gate exists to prevent. -/
def selectorAccLifetimeKats_ok : Bool :=
  let l := Midfall.Generator.LayoutMemoryKats.poseidonLayout
  -- the region finding 12 is about, with the lifetime the attack records
  (match regionLifetime l "selector_accumulators" with
   | some (.phase MemoryPhase.pcsFinalMsm) => true
   | _ => false) &&
  -- and the only other carrier of that lifetime
  (match regionLifetime l "pcs_final_msm" with
   | some (.phase MemoryPhase.pcsFinalMsm) => true
   | _ => false) &&
  -- exactly two regions in the whole map carry it
  (l.map.regions.filter fun r =>
      r.lifetime == MemoryLifetime.phase MemoryPhase.pcsFinalMsm).length == 2 &&
  -- the batch-inversion scratch that shares the selector base is a DIFFERENT
  -- phase, so it is not covered by the grant (LayoutMemory.lean:276-278)
  (match regionLifetime l "batch_invert_scratch" with
   | some (.phase MemoryPhase.lagrangeBatchInvert) => true
   | _ => false)

/-- The boundary map is a chain: pre is strictly increasing along the partials,
    post is the successor of pre, and the seven pre-checkpoints are the first seven
    boundaries in order. Refuted by an off-by-one in pre (which would state every
    partial against the invariant of its neighbour) or by next wrapping. -/
def checkpointChainKats_ok : Bool :=
  (partials.all fun q => q.post == q.pre.next) &&
  partials.zipIdx.all fun (q, i) =>
    q.pre.idx == i && q.pre ≤ q.post &&
    -- the first six partials each advance the boundary by exactly one; traceReturn
    -- saturates because the return establishes no invariant
    (if i < 6 then q.post.idx == i + 1 && q.pre.next != q.pre
     else q.post == q.pre && q.pre.next == q.pre) &&
    -- and the pre-checkpoints are pairwise distinct, so no two partials share a
    -- starting boundary
    (partials.all fun q2 => q2.pre != q.pre || q2 == q)

/-- MemoryPhase is not Checkpoint: the two enumerations are different sizes and
    conflating them is the mistake design0 names as a hazard. This pins the sizes so
    that a future edit cannot quietly identify them. -/
def checkpointNotMemoryPhaseKats_ok : Bool :=
  checkpoints.length == 7 && memoryPhases.length == 16 && partials.length == 7 &&
    -- distinct constructors, no accidental aliasing in the enumerations
    checkpoints.length == checkpoints.eraseDups.length &&
    memoryPhases.length == memoryPhases.eraseDups.length &&
    partials.length == partials.eraseDups.length

#eval liveAtKats_ok                       -- expect true
#eval liveAtSelectorKats_ok               -- expect true
#eval selectorAccLifetimeKats_ok          -- expect true
#eval checkpointChainKats_ok              -- expect true
#eval checkpointNotMemoryPhaseKats_ok     -- expect true

end Midfall.Lowering
