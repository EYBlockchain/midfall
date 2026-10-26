-- |
-- Midfall.Generator.LayoutMemory
--
-- `VerifierMemoryLayout::new` (MEM:591-973) and the three free helpers of
-- `lowering/layout/memory.rs` that it calls and that `Layout.lean` left unported:
-- `commitment_g1_count` (MEM:1080-1088), `batch_invert_input_words`
-- (MEM:1099-1105) and `batch_invert_scratch_bytes` (MEM:1107-1117).
--
-- WHY A NEW FILE AND NOT `Layout.lean`. The deferral note at Layout.lean:716-726
-- (corrected by docs/REVIEW.md R-49) said the only obstacle was the 383 lines of
-- arena planning. That is still not the whole story. `new`'s first parameter is
-- `&ConstraintSystemMeta`, and `ConstraintSystemMeta` is declared in
-- `Encoding.lean:364` - a file that IMPORTS `Layout.lean`, directly at
-- Encoding.lean:158 and again through `Abi.lean:99` and `Protocol.lean:93`. So `new`
-- cannot be stated in `Layout.lean` at all without reversing that edge: Lean is
-- order-sensitive and `Layout.lean` cannot see a type defined downstream of it.
-- The record, its config and its validator live in `Layout.lean` because they do
-- not mention `ConstraintSystemMeta`; the constructor has to live here, where both
-- halves are in scope. This is also why `Vk.lean`, which is downstream of
-- `Encoding.lean`, could name the type in the `VkBuildEnv` shim.
--
-- Citation prefixes are the ones `Layout.lean` introduces and records at its
-- header:19-22 (`VP:`, `MEM:`, `LM:`, `M:`); `ENC:` is
-- `lowering/encoding/mod.rs` and `AP:` is `lowering/abi/proof.rs`. Every cite
-- below names the file it came from, per docs/REVIEW.md R-40 F6.
--
-- Porting decisions recorded rather than taken silently:
--
-- * R2 exception: the Rust binder `meta` cannot be a Lean binder, so it is
--   `meta_`, the convention `Vk.lean` sets (Vk.lean:945, :1011). Four defs here
--   take it.
-- * R6 / the Generator row: `Vec` is `List`. The only Vec operations the ported
--   scope performs are `.iter().sum()` (MEM:697-698, MEM:1081, MEM:1084) and
--   `.len()` (MEM:682, MEM:688, MEM:694, MEM:874), all order-independent, so a
--   `Nat` fold and `List.length` are exact.
-- * Item order. R1 wants source order, and in the Rust the three helpers come
--   AFTER `new` (MEM:1080-1117). Lean needs a callee before its caller, so all
--   three are moved above `new` and each says so at its own site. Nothing else
--   moves: the body of `new` is in MEM:597-970 order, let for let, with the arena
--   threaded functionally the way `VkConstructorMemoryLayout.new`
--   (Layout.lean:642-648) already threads it.
-- * `usize` is `Nat`, which cannot wrap (rule R5, and Layout.lean:30-38 for the
--   same argument in the file this one extends). The reference profile is release
--   (docs/REVIEW.md R-6), so `+` and `*` wrap rather than panic and
--   `debug_assert!` is compiled out; `saturating_sub` is `Nat` subtraction, which
--   is exactly equal to it on `usize`.
-- * The two `.max().expect(..)` sites (MEM:606-615 and MEM:865-892) are
--   UNREACHABLE panics on a non-empty array literal and are argued at the site
--   rather than ported as a default - see `natMaximumNonempty`.
-- * `Ptr + usize` is word-wise (ENC:652-662 `Value::add`), so the Rust `+`
--   becomes the ported `Ptr.add` (ENC:723-731) explicitly: Lean has no
--   `HAdd Ptr Nat Ptr` instance and none is invented here.
-- * `vk_mptr.value().as_usize()` (MEM:668) and the four other `.as_usize()` reads
--   in this function are `Value.asUsizeNat` (Layout.lean:1010-1013), the total
--   adapter already introduced for MEM:1039. The Rust would abort the process on a
--   symbolic `Value::Identifier`; no call path in the reference reaches that arm
--   (Layout.lean:994-997 counts all 49 `Ptr::memory`/`Ptr::calldata` sites as
--   concrete), and the adapter's agreement with the partial version is pinned by
--   `asUsizeNat_agrees_ok` there.

import Midfall.Generator.Encoding
import Midfall.Generator.Layout

namespace Midfall.Generator

/-- A modelling helper rather than a Rust item: `.into_iter().max()` on a
    NON-EMPTY array literal. `head` is the literal's first element and `rest` the
    remaining ones, so the fold IS the maximum of the array and there is no default
    to invent.

    HAZARD 2. MEM:615's `.expect("constructor G1MSM smoke bounds are non-empty")`
    and MEM:892's `.expect("trace scratch bounds are non-empty")` are both
    unreachable: the first is `.max()` over a five-element array literal
    (MEM:606-612) and the second over a twenty-three-element one (MEM:865-889), and
    `Iterator::max` on an array of known non-zero length returns `Some` for every
    input value, including every `usize`. Rule R4 turns a REACHABLE panic into a
    `Fault.panic`; rule R5 says an unreachable one is argued at the site instead.
    Porting it as `Option` with a `.getD 0` default would be the silent-zero
    failure this package was warned about, because a zero
    `constructor_g1msm_smoke_len` is a smoke-test buffer that allocates nothing and
    still validates - `constructorG1msmSmokeLen_ok` is what closes that. -/
def natMaximumNonempty (head : Nat) (rest : List Nat) : Nat :=
  rest.foldl Nat.max head

/-- rust: MEM:1080-1088 (`commitment_g1_count`) @formal-baseline. Moved above
    `new` (MEM:597 is its first caller); see the header.

    HAZARD 4, and the plan's pointer was wrong. This is NOT the Abi.lean function
    P-05 ported. `Abi.lean:432` ports `ProofCalldataLayout::commitment_g1_count`
    (AP:261-263), a method on a `ProofCalldataLayout` that takes no meta and
    returns `non_quotient_g1_count() + quotient_limbs.item_count`. The Rust call at
    MEM:597 resolves to this free function in `memory.rs`, which reads the
    `ConstraintSystemMeta` fields directly. The two are parallel formulas over
    different sources: they agree only when the layout was built from this meta by
    `ProofCalldataLayout::from_protocol`, and nothing in the reference asserts that
    they must. So this is a new def, not a re-export, and
    `commitmentG1Count_matchesLayout_ok` measures the relationship instead of
    assuming it.

    The doubled `meta.num_lookups` (MEM:1082 and MEM:1085 - once for the
    multiplicity commitments, once for the accumulators) is the term a port is most
    likely to drop, and is the one `commitmentG1Count_ok` is built to catch. -/
def commitmentG1Count (meta_ : ConstraintSystemMeta) : Nat :=
  let adviceSum := meta_.numUserAdvices.foldl (fun acc n => acc + n) 0
  let lookupChunkSum := meta_.lookupChunks.foldl (fun acc n => acc + n) 0
  adviceSum + meta_.numLookups + meta_.numPermutationZs + lookupChunkSum
    + meta_.numLookups + meta_.numTrashcans + meta_.numQuotients

/-- rust: MEM:1090-1105 (`batch_invert_input_words`) @formal-baseline. Moved above
    `new` (MEM:617 is its caller) and above `batchInvertScratchBytes` (MEM:1114 is
    its other caller). `rotation_last.unsigned_abs()` is `Int.natAbs`: the field is
    `i32` in the Rust (ENC:131) and negative for every real circuit, and
    `unsigned_abs` on `i32::MIN` is 2^31, which `Int.natAbs` also gives. -/
def batchInvertInputWords (meta_ : ConstraintSystemMeta) (numInstances : Nat) : Nat :=
  if numInstances == 0 then meta_.rotationLast.natAbs + 2
  else numInstances + meta_.rotationLast.natAbs + 1

/-- rust: MEM:1107-1117 (`batch_invert_scratch_bytes`) @formal-baseline. Private in
    the reference (`fn`, not `pub(crate) fn`), and moved above `new` because
    MEM:616 calls it. `saturating_sub` is `Nat` subtraction. The comment at
    MEM:1108-1113 is why the frame is added to `input_words - 2` and not to
    `input_words`: a batch inversion of N inputs stores N-2 prefix products and
    overlays one modexp frame at the current prefix pointer, and a singleton uses
    only the frame. -/
def batchInvertScratchBytes (meta_ : ConstraintSystemMeta) (numInstances : Nat) : Nat :=
  let inputWords := batchInvertInputWords meta_ numInstances
  modexpFrameBytes + (inputWords - 2) * wordBytes

/-- rust: MEM:585-971 (`impl VerifierMemoryLayout { fn new .. }`) @formal-baseline.
    Infallible in the Rust, so no `Except` - which is also the type the
    `VkBuildEnv.newVerifierMemoryLayout` field (Vk.lean:408-410) already expects,
    so retiring that shim is a substitution and not a re-typing.

    The arena is threaded by value: `arenaN` is the Rust's `&mut arena` after the
    Nth registration, and the four `scratch_allocator` blocks (MEM:797-810,
    MEM:812-825, MEM:831-849, MEM:852-855) hand their arena back through
    `ScratchAllocator.arena` when the block ends, which is the Rust's borrow
    ending. Registration ORDER is preserved exactly, because `MemoryMap::validate`
    reports the first offending pair in that order. -/
def VerifierMemoryLayout.new (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) : VerifierMemoryLayout :=
  -- MEM:597-618: the sizing block. Every length the planner later registers is
  -- computed here and nowhere else.
  let commitmentsLen := commitmentG1Count meta_ * g1Bytes
  let selectorLen := meta_.numSimpleSelectors * wordBytes
  let quotientStateLen := config.quotientStateWords * wordBytes
  let quotientStackLen := config.quotientStackWords * wordBytes
  let qEvalSourceLen := config.pcs.qEvalSourceTableWords * wordBytes
  let qComTraceLen := config.pcs.qComTraceMsm.inputBytes
  let finalMsmLen := config.pcs.finalMsm.inputBytes
  let accMsmLen := config.accMsmTerms * g1MsmPairBytes
  let linTraceLen := (meta_.numQuotients + meta_.numSimpleSelectors) * g1MsmPairBytes
  -- MEM:606-615. Five bounds; the floor is one G1MSM pair, so the smoke scratch is
  -- never empty even for an empty circuit. See `natMaximumNonempty` for the
  -- unreachable `expect`.
  let constructorG1msmSmokeLen :=
    natMaximumNonempty g1MsmPairBytes [qComTraceLen, finalMsmLen, accMsmLen, linTraceLen]
  let batchInvertLen := batchInvertScratchBytes meta_ config.numInstances
  let lagrangeDenomsLen := batchInvertInputWords meta_ config.numInstances * wordBytes
  let quotientReturnLen := (2 + meta_.numSimpleSelectors) * wordBytes
  -- MEM:620-621.
  let arena0 := memoryArenaDefault
  let thetaWindows := ThetaWindowLayout.compatibility
  -- MEM:623-660: the six low-memory helpers. The Rust comment at MEM:623-624 is
  -- hazard 1 in one sentence - they are phase-scoped because the transcript buffer
  -- is no longer live once algebra begins, which is why five of them may share the
  -- single address 0x1000.
  let (arena1, constructorSmokeScratchMptr) :=
    arena0.allocPhaseScratch "constructor_smoke_scratch" lowMemoryScratchStart
      pairingTwoPairBytes MemoryPhase.constructorSmoke
  let (arena2, transcriptMptr) :=
    arena1.allocPhaseScratch "transcript_buffer" transcriptBufferStart
      (config.transcriptWords * wordBytes) MemoryPhase.transcript
  let (arena3, pcsPairingScratchMptr) :=
    arena2.allocPhaseScratch "pcs_pairing_static_working" pcsPairingScratchStart
      (pcsStaticWorkingWords * wordBytes) MemoryPhase.pcsPairing
  let (arena4, verifierReturnMptr) :=
    arena3.allocPhaseScratch "verifier_return" verifierReturnBufferStart wordBytes
      MemoryPhase.verifierReturn
  let (arena5, quotientReturnMptr) :=
    arena4.allocPhaseScratch "quotient_return" quotientReturnBufferStart quotientReturnLen
      MemoryPhase.quotientReturn
  let (arena6, finalPairingScratchMptr) :=
    arena5.allocPhaseScratch "final_pairing_scratch" finalPairingScratchStart
      (pairingStaticWorkingWords * wordBytes) MemoryPhase.finalPairing
  -- MEM:662-695: the VK payload, the scalar-inversion frame below it, and the
  -- challenge and theta blocks above it. `saturating_sub` at MEM:674 is `Nat`
  -- subtraction; a `vk_mptr` below `MODEXP_SCRATCH_BYTES` clamps to 0 here and is
  -- then caught by `validate`'s spill-window arm rather than wrapping.
  let (arena7, vkStart) :=
    arena6.allocFixed "vk_payload" ((ptrValue vkMptr).asUsizeNat) vk.len
      MemoryLifetime.permanent
  let (arena8, scalarInvScratchMptr) :=
    arena7.allocPhaseScratch "scalar_inv_scratch" (vkStart - modexpScratchBytes)
      modexpFrameBytes MemoryPhase.scalarInv
  let (arena9, challengeStart) :=
    arena8.allocAfter "challenge_slots" vkStart vk.len
      (meta_.challengeIndices.length * wordBytes) MemoryLifetime.permanent
  let (arena10, thetaStart) :=
    arena9.allocAfter "theta_scalar_and_g1_slots" challengeStart
      (meta_.challengeIndices.length * wordBytes)
      (thetaWindows.rotPointsWord * wordBytes) MemoryLifetime.permanent
  let challengeMptr := ptrMemory (valueFromNat challengeStart)
  let atTheta : Nat → Nat := fun words => thetaStart + words * wordBytes
  let ptrAtTheta : ThetaSlot → Ptr := fun slot => ptrMemory (valueFromNat (atTheta
  slot.word))
  let thetaMptr := ptrAtTheta ThetaSlot.theta
  -- MEM:697-708: the commitment census, by category. `num_lookups` enters twice.
  let totalAdvices := meta_.numUserAdvices.foldl (fun acc n => acc + n) 0
  let lookupHelperChunksTotal := meta_.lookupChunks.foldl (fun acc n => acc + n) 0
  let nonQuotientG1s := totalAdvices + meta_.numLookups + meta_.numPermutationZs
    + lookupHelperChunksTotal + meta_.numLookups + meta_.numTrashcans
  let committedG1s := nonQuotientG1s + meta_.numQuotients
  -- MEM:709-750: the historical theta-rooted windows. Four are `PcsFixed`
  -- phase-scratch and three are permanent.
  let (arena11, rotPointsAddr) :=
    arena10.allocFixed "rot_points" (atTheta thetaWindows.rotPointsWord)
      (config.pcs.rotPointsWords * wordBytes) (MemoryLifetime.phase MemoryPhase.pcsFixed)
  let rotPointsMptr := ptrMemory (valueFromNat rotPointsAddr)
  let (arena12, x1PowersAddr) :=
    arena11.allocFixed "x1_powers" (atTheta thetaWindows.x1PowersWord)
      (config.pcs.x1PowersWords * wordBytes) (MemoryLifetime.phase MemoryPhase.pcsFixed)
  let x1PowersMptr := ptrMemory (valueFromNat x1PowersAddr)
  let (arena13, qComAddr) :=
    arena12.allocFixed "q_com_fixed_window" (atTheta thetaWindows.qComWord)
      (config.pcs.qComWords * wordBytes) (MemoryLifetime.phase MemoryPhase.pcsFixed)
  let qComMptr := ptrMemory (valueFromNat qComAddr)
  let (arena14, qEvalSetAddr) :=
    arena13.allocFixed "q_eval_set" (atTheta thetaWindows.qEvalSetWord)
      (config.pcs.qEvalSetWords * wordBytes) (MemoryLifetime.phase MemoryPhase.pcsFixed)
  let qEvalSetMptr := ptrMemory (valueFromNat qEvalSetAddr)
  let (arena15, qEvalCptrAddr) :=
    arena14.allocFixed "q_eval_cptr_slot" (atTheta thetaWindows.qEvalCptrWord)
      wordBytes MemoryLifetime.permanent
  let qEvalCptrMptr := ptrMemory (valueFromNat qEvalCptrAddr)
  let (arena16, g1IdentityAddr) :=
    arena15.allocFixed "g1_identity" (atTheta thetaWindows.g1IdentityWord)
      g1Bytes MemoryLifetime.permanent
  let g1IdentityMptr := ptrMemory (valueFromNat g1IdentityAddr)
  let (arena17, reversedEvalsAddr) :=
    arena16.allocFixed "decoded_evals" (atTheta thetaWindows.reversedEvalsWord)
      (meta_.numEvals * wordBytes) MemoryLifetime.permanent
  let reversedEvalsMptr := ptrMemory (valueFromNat reversedEvalsAddr)
  -- MEM:751-767: the decompressed commitments and the eight category bases derived
  -- from them. These are `Ptr` arithmetic (word-wise, ENC:723-731), not byte
  -- arithmetic, which is why the stride is `G1_WORDS` and not `G1_BYTES`.
  let (arena18, commsAddr) :=
    arena17.allocAfter "decompressed_commitments"
      ((ptrValue reversedEvalsMptr).asUsizeNat) (meta_.numEvals * wordBytes)
      commitmentsLen MemoryLifetime.permanent
  let commsMptrBase := ptrMemory (valueFromNat commsAddr)
  let adviceCommsMptrBase := commsMptrBase
  let lookupMCommsMptrBase := Ptr.add adviceCommsMptrBase (g1WordsCount * totalAdvices)
  let permZCommsMptrBase := Ptr.add lookupMCommsMptrBase (g1WordsCount * meta_.numLookups)
  let lookupHelperCommsMptrBase :=
    Ptr.add permZCommsMptrBase (g1WordsCount * meta_.numPermutationZs)
  let lookupZCommsMptrBase :=
    Ptr.add lookupHelperCommsMptrBase (g1WordsCount * lookupHelperChunksTotal)
  let trashcanCommsMptrBase := Ptr.add lookupZCommsMptrBase (g1WordsCount * meta_.numLookups)
  let quotientLimbCommsMptrBase :=
    Ptr.add trashcanCommsMptrBase (g1WordsCount * meta_.numTrashcans)
  -- MEM:769-784: the end of the commitment run, the constructor's largest G1MSM
  -- smoke frame, and the selector accumulators.
  let afterComms := ((ptrValue commsMptrBase).asUsizeNat) + committedG1s * g1Bytes
  let (arena19, constructorG1msmSmokeScratchMptr) :=
    arena18.allocPhaseScratch "constructor_g1msm_smoke_scratch"
      (alignUp afterComms wordBytes) constructorG1msmSmokeLen MemoryPhase.constructorSmoke
  let (arena20, selectorAccMptr) :=
    arena19.allocAfter "selector_accumulators" ((ptrValue commsMptrBase).asUsizeNat)
      commitmentsLen selectorLen (MemoryLifetime.phase MemoryPhase.pcsFinalMsm)
  -- MEM:785-810: the two Lagrange-phase regions from ONE allocator, so the second
  -- lands after the first. The Rust comment at MEM:785-796 is explicit that a fresh
  -- allocator would reset the per-phase cursor onto `selector_acc_mptr` and
  -- register a same-phase overlap, and that the order pins `batch_invert_scratch`
  -- to the selector base.
  let (lagrangeScratch0, batchInvertScratchMptr) :=
    (arena20.scratchAllocator selectorAccMptr).allocPhaseScratch "batch_invert_scratch"
      batchInvertLen MemoryPhase.lagrangeBatchInvert
  let (lagrangeScratch1, lagrangeDenomsMptr) :=
    lagrangeScratch0.allocPhaseScratch "lagrange_denoms" lagrangeDenomsLen
      MemoryPhase.lagrangeBatchInvert
  let arena21 := lagrangeScratch1.arena
  -- MEM:811-825: the quotient VM state and stack, again one allocator, one phase.
  -- `quotient_stack_len.max(MODEXP_FRAME_BYTES)` (MEM:821) is the native-callback
  -- floor: a callback may share the VM stack base, so the stack region is never
  -- smaller than one modexp frame.
  let quotientTmpBase := alignUp (selectorAccMptr + selectorLen) wordBytes
  let (quotientScratch0, quotientTmpMptr) :=
    (arena21.scratchAllocator quotientTmpBase).allocPhaseScratch "quotient_state"
      quotientStateLen MemoryPhase.quotientVm
  let (quotientScratch1, quotientStackMptr) :=
    quotientScratch0.allocPhaseScratch "quotient_stack"
      (Nat.max quotientStackLen modexpFrameBytes) MemoryPhase.quotientVm
  let arena22 := quotientScratch1.arena
  -- MEM:826-849: the three PCS scratch regions, all rooted at the quotient VM base
  -- and all in DIFFERENT phases, which is the intentional aliasing hazard 1 is about.
  let pcsScratchMptr := quotientTmpMptr
  let (pcsScratch0, pcsQEvalSourceTableMptr) :=
    (arena22.scratchAllocator pcsScratchMptr).allocPhaseScratch "pcs_q_eval_source_table"
      qEvalSourceLen MemoryPhase.pcsQEvalSourceTable
  let (pcsScratch1, pcsQComTraceScratchMptr) :=
    pcsScratch0.allocPhaseScratch "pcs_q_com_trace_msm" qComTraceLen MemoryPhase.pcsQComTrace
  let (pcsScratch2, pcsFinalMsmScratchMptr) :=
    pcsScratch1.allocPhaseScratch "pcs_final_msm" finalMsmLen MemoryPhase.pcsFinalMsm
  let arena23 := pcsScratch2.arena
  -- MEM:850-855: the accumulator MSM, floored at 0x7000 historically.
  let accMsmScratchBase := alignUp (Nat.max afterComms accMsmMinScratchBytes) wordBytes
  let (accScratch, accMsmScratch) :=
    (arena23.scratchAllocator accMsmScratchBase).allocPhaseScratch "accumulator_msm"
      accMsmLen MemoryPhase.accumulatorMsm
  let arena24 := accScratch.arena
  -- MEM:856-861.
  let (arena25, accumulatorPairingBatchMptr) :=
    arena24.allocPhaseScratch "accumulator_pairing_batch" accumulatorPairingBatchPtr
      accumulatorPairingBatchHashBytes MemoryPhase.accumulatorPairingBatch
  -- MEM:862-893: the trace LOG word, placed after EVERY registered region because
  -- `trace_u256` may be called between long-lived reads. Twenty-three candidate
  -- ends, the maximum aligned up.
  let traceU256Bound := natMaximumNonempty
    (constructorSmokeScratchMptr + pairingTwoPairBytes)
    [ transcriptMptr + config.transcriptWords * wordBytes,
      pcsPairingScratchMptr + pcsStaticWorkingWords * wordBytes,
      verifierReturnMptr + wordBytes,
      quotientReturnMptr + quotientReturnLen,
      finalPairingScratchMptr + pairingStaticWorkingWords * wordBytes,
      scalarInvScratchMptr + modexpFrameBytes,
      vkStart + vk.len,
      challengeStart + meta_.challengeIndices.length * wordBytes,
      thetaStart + thetaWindows.rotPointsWord * wordBytes,
      ((ptrValue g1IdentityMptr).asUsizeNat) + g1Bytes,
      ((ptrValue reversedEvalsMptr).asUsizeNat) + meta_.numEvals * wordBytes,
      ((ptrValue commsMptrBase).asUsizeNat) + commitmentsLen,
      selectorAccMptr + selectorLen,
      batchInvertScratchMptr + batchInvertLen,
      lagrangeDenomsMptr + lagrangeDenomsLen,
      quotientStackMptr + Nat.max quotientStackLen modexpFrameBytes,
      pcsQEvalSourceTableMptr + qEvalSourceLen,
      pcsQComTraceScratchMptr + qComTraceLen,
      pcsFinalMsmScratchMptr + finalMsmLen,
      constructorG1msmSmokeScratchMptr + constructorG1msmSmokeLen,
      accMsmScratch + accMsmLen,
      accumulatorPairingBatchMptr + accumulatorPairingBatchHashBytes ]
  let traceU256Mptr := alignUp traceU256Bound wordBytes
  let (arena26, _) :=
    arena25.allocFixed "trace_u256_log_word" traceU256Mptr wordBytes MemoryLifetime.permanent
  -- MEM:901-970: the record, in the Rust's field order.
  { map := arena26.intoMap,
    thetaWindows := thetaWindows,
    constructorSmokeScratchMptr := constructorSmokeScratchMptr,
    constructorG1msmSmokeScratchMptr := constructorG1msmSmokeScratchMptr,
    constructorG1msmSmokeInputBytes := constructorG1msmSmokeLen,
    transcriptMptr := transcriptMptr,
    pcsPairingScratchMptr := pcsPairingScratchMptr,
    verifierReturnMptr := verifierReturnMptr,
    quotientReturnMptr := quotientReturnMptr,
    vkMptr := vkMptr,
    scalarInvScratchMptr := scalarInvScratchMptr,
    challengeMptr := challengeMptr,
    thetaMptr := thetaMptr,
    betaMptr := ptrAtTheta ThetaSlot.beta,
    gammaMptr := ptrAtTheta ThetaSlot.gamma,
    trashChallengeMptr := ptrAtTheta ThetaSlot.trashChallenge,
    yMptr := ptrAtTheta ThetaSlot.y,
    xMptr := ptrAtTheta ThetaSlot.x,
    x1Mptr := ptrAtTheta ThetaSlot.x1,
    x2Mptr := ptrAtTheta ThetaSlot.x2,
    x3Mptr := ptrAtTheta ThetaSlot.x3,
    x4Mptr := ptrAtTheta ThetaSlot.x4,
    fComMptr := ptrAtTheta ThetaSlot.fCom,
    piMptr := ptrAtTheta ThetaSlot.pi,
    accLhsMptr := ptrAtTheta ThetaSlot.accLhs,
    accRhsMptr := ptrAtTheta ThetaSlot.accRhs,
    xNMptr := ptrAtTheta ThetaSlot.xN,
    xNMinus1InvMptr := ptrAtTheta ThetaSlot.xNMinus1Inv,
    lLastMptr := ptrAtTheta ThetaSlot.lLast,
    lBlindMptr := ptrAtTheta ThetaSlot.lBlind,
    l0Mptr := ptrAtTheta ThetaSlot.l0,
    instanceEvalMptr := ptrAtTheta ThetaSlot.instanceEval,
    quotientEvalMptr := ptrAtTheta ThetaSlot.quotientEval,
    quotientMptr := ptrAtTheta ThetaSlot.quotient,
    fEvalMptr := ptrAtTheta ThetaSlot.fEval,
    vMptr := ptrAtTheta ThetaSlot.v,
    finalComMptr := ptrAtTheta ThetaSlot.finalCom,
    pairingLhsMptr := ptrAtTheta ThetaSlot.pairingLhs,
    pairingRhsMptr := ptrAtTheta ThetaSlot.pairingRhs,
    rotPointsMptr := rotPointsMptr,
    x1PowersMptr := x1PowersMptr,
    qComMptr := qComMptr,
    qEvalSetMptr := qEvalSetMptr,
    qEvalCptrMptr := qEvalCptrMptr,
    g1IdentityMptr := g1IdentityMptr,
    reversedEvalsMptr := reversedEvalsMptr,
    commsMptrBase := commsMptrBase,
    adviceCommsMptrBase := adviceCommsMptrBase,
    lookupMCommsMptrBase := lookupMCommsMptrBase,
    permZCommsMptrBase := permZCommsMptrBase,
    lookupHelperCommsMptrBase := lookupHelperCommsMptrBase,
    lookupZCommsMptrBase := lookupZCommsMptrBase,
    trashcanCommsMptrBase := trashcanCommsMptrBase,
    quotientLimbCommsMptrBase := quotientLimbCommsMptrBase,
    selectorAccMptr := selectorAccMptr,
    batchInvertScratchMptr := batchInvertScratchMptr,
    lagrangeDenomsMptr := lagrangeDenomsMptr,
    quotientTmpMptr := quotientTmpMptr,
    quotientStackMptr := quotientStackMptr,
    quotientStackHi := quotientStackMptr + Nat.max quotientStackLen modexpFrameBytes,
    pcsQEvalSourceTableMptr := pcsQEvalSourceTableMptr,
    pcsQComTraceScratchMptr := pcsQComTraceScratchMptr,
    pcsFinalMsmScratchMptr := pcsFinalMsmScratchMptr,
    accMsmScratch := accMsmScratch,
    accumulatorPairingBatchMptr := accumulatorPairingBatchMptr,
    finalPairingScratchMptr := finalPairingScratchMptr,
    traceU256Mptr := traceU256Mptr,
    pcs := config.pcs }

end Midfall.Generator


/-! # Known-answer tests for `VerifierMemoryLayout::new` and its helpers

    Gates come in three kinds, in the order docs/REVIEW.md R-38 ranks them. The
    strongest are transcriptions of `memory.rs`'s own `#[cfg(test)]` assertions
    (MEM:1131-1602): every expected number in gates 5 to 12 is copied from an
    `assert_eq!` in the reference, so those gates are evidence and not restatement.
    The second kind is arithmetic derived here and pinned against the ported
    definitions (gates 1 to 4, 16 to 18). The third is the hazard set: gates 13 to
    15 and 19 to 21 exist to answer the six hazards in
    `docs/plans/P-03e-memory-layout.md`, and each says which.

    FIXTURE PROVENANCE, and a deliberate departure from the plan's wording (R-48).
    The plan asked for "the poseidon-shaped fixture". The poseidon circuit's
    `ConstraintSystemMeta` counts are NOT recorded anywhere in this tree - the
    fixture test asserts three qualitative facts about it
    (`tests/poseidon_fixture.rs:401-406`: one trash identity, three lookup
    identities, permutation identities > 0) and no advice or eval counts - so
    hand-typing a "poseidon meta" would be a paste checking a paste, which is R-40
    F2. What is used instead is the two halves that ARE recorded:
    `poseidonShapedVk` takes its constant and commitment COUNTS from the committed
    poseidon artifact as `Templates.lean:740-808` transcribes them (35 constants,
    19 fixed commitments), and `poseidonShapedMeta` is the tree's only
    machine-constructed meta, `EncodingKats.metaFixture`, built by the ported
    `ConstraintSystemMeta.new` from a real `ConstraintSystem`. Every count that
    drives an allocation in `new` is non-zero and the commitment categories land on
    distinct addresses, which is what the shared `LayoutKats.verifierLayoutFixture`
    (all bases 0, empty map) cannot give a pointer comparison. Gate 18 asserts the
    distinctness before any comparison relies on it. -/

namespace Midfall.Generator.LayoutMemoryKats

open Midfall Midfall.Generator
open Midfall.Generator.LayoutKats

/-- The VK of `memory.rs`'s own `synthetic_vk()` (MEM:1260-1279): 31 header
    constants, one fixed commitment, no permutation commitments, no quotient
    sections. `len` is therefore 31*32 + 128 = 0x460. -/
def referenceSyntheticVk : Halo2VerifyingKey :=
  { constructorPayloadMptr := vkConstructorPayloadStart,
    constants := (List.range vkHeaderWords).map fun _ => ("c", 0),
    fixedComms := [{ xHi := 0, xLo := 0, yHi := 0, yLo := 0 }],
    permutationComms := [],
    quotientConstOffsetWords := none,
    quotientConstWords := 0,
    quotientProgramOffsetWords := none,
    quotientProgramWords := 0,
    quotientConstLabels := [],
    quotientConstHeaders := [] }

/-- The meta of MEM:1283-1292, verbatim: seven fields set, the rest
    `ConstraintSystemMeta::default()`, so `num_simple_selectors` is 0,
    `challenge_indices` is empty and `rotation_last` is 0. -/
def referenceSyntheticMeta : ConstraintSystemMeta :=
  { constraintSystemMetaDefault with
    numUserAdvices := [2], numLookups := 1, numPermutationZs := 1,
    lookupChunks := [2], numTrashcans := 1, numQuotients := 3, numEvals := 5 }

/-- The meta of MEM:1343-1347: three simple selectors and nothing else. -/
def selectorMeta : ConstraintSystemMeta :=
  { constraintSystemMetaDefault with numSimpleSelectors := 3 }

/-- The meta of MEM:1476-1481. -/
def traceMeta : ConstraintSystemMeta :=
  { constraintSystemMetaDefault with
    numUserAdvices := [8], numQuotients := 4, numEvals := 16 }

/-- The meta of MEM:1506-1509 and MEM:1533-1536: `rotation_last = -3`, the only
    fixture here with a negative rotation and the one the batch-inversion sizing
    gates use. -/
def rotationMeta : ConstraintSystemMeta :=
  { constraintSystemMetaDefault with rotationLast := -3 }

/-- The poseidon fixture VK's counts, from the committed artifact as
    `Templates.lean:740-808` transcribes it: 35 constants and 19 fixed
    commitments, no permutation commitments, so `len` is 35*32 + 19*128 = 0xDE0.
    The POINT VALUES are placeholders because `new` reads only `vk.len()`
    (MEM:669, MEM:681, MEM:873) and never a coordinate. -/
def poseidonShapedVk : Halo2VerifyingKey :=
  { constructorPayloadMptr := vkConstructorPayloadStart,
    constants := (List.range 35).map fun _ => ("c", 0),
    fixedComms := (List.range 19).map fun _ => { xHi := 0, xLo := 0, yHi := 0, yLo := 0 },
    permutationComms := [],
    quotientConstOffsetWords := none,
    quotientConstWords := 0,
    quotientProgramOffsetWords := none,
    quotientProgramWords := 0,
    quotientConstLabels := [],
    quotientConstHeaders := [] }

/-- The tree's real meta: `Encoding.lean:1290`, built by the ported
    `ConstraintSystemMeta.new` from a real `ConstraintSystem`. The counts
    `Encoding.lean:1303-1326` pins are what make it non-degenerate here: four
    advice columns in one phase, one lookup chunked into two, one trashcan, two
    permutation products, four quotient limbs, 21 evals, no challenges, and
    `rotation_last = -10`. -/
def poseidonShapedMeta : ConstraintSystemMeta := Midfall.Generator.EncodingKats.metaFixture

/-- A PCS requirement set that sits exactly ON the four `ThetaWindowLayout`
    capacities (28, 65, 0, 56), so the fixed windows tile the theta region with no
    gap and no overflow: `validate`'s capacity arms pass at the boundary and fail
    one word past it. -/
def poseidonShapedPcs : PcsMemoryRequirements :=
  { rotPointsWords := 28, x1PowersWords := 65, qComWords := 0, qEvalSetWords := 56,
    qEvalSourceTableWords := 16, qComTraceMsm := FinalMsmShape.fromTerms 9,
    finalMsm := FinalMsmShape.fromTerms 12 }

/-- A full production-shaped config: a live 64-word transcript, one public
    instance, a quotient VM with state and stack, four accumulator MSM terms and
    the PCS windows at their caps. -/
def poseidonShapedConfig : VerifierMemoryLayoutConfig :=
  { transcriptWords := 64, numInstances := 1, quotientStateWords := 8,
    quotientStackWords := 64, accMsmTerms := 4, pcs := poseidonShapedPcs }

/-- THE HEADLINE FIXTURE (hazard 5): a real `VerifierMemoryLayout` built by the
    ported `new` from a real meta, a real VK, a real `vk_mptr` and a full config.
    Every gate that needs a non-degenerate layout reads this one. -/
def poseidonLayout : VerifierMemoryLayout :=
  VerifierMemoryLayout.new poseidonShapedMeta poseidonShapedVk
    (ptrMemory (valueFromNat 0x4000)) poseidonShapedConfig

/-- The reference's own fixture of MEM:1294-1299: `new` with the synthetic meta
    and VK, `Ptr::memory(0x2000)` and a default config. -/
def referenceLayout : VerifierMemoryLayout :=
  VerifierMemoryLayout.new referenceSyntheticMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000)) verifierMemoryLayoutConfigDefault

/-- The fixture of MEM:1349-1354. -/
def selectorLayout : VerifierMemoryLayout :=
  VerifierMemoryLayout.new selectorMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000)) verifierMemoryLayoutConfigDefault

/-- The fixture of MEM:1492. -/
def traceLayout : VerifierMemoryLayout :=
  VerifierMemoryLayout.new traceMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000))
    { verifierMemoryLayoutConfigDefault with
      accMsmTerms := 4,
      pcs := { pcsMemoryRequirementsDefault with
        qComTraceMsm := FinalMsmShape.fromTerms 9,
        finalMsm := FinalMsmShape.fromTerms 10 } }

/-- The fixture of MEM:1515 and MEM:1542: `rotation_last = -3`, five instances. -/
def rotationLayout : VerifierMemoryLayout :=
  VerifierMemoryLayout.new rotationMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000))
    { verifierMemoryLayoutConfigDefault with numInstances := 5 }

/-- The layout of gate 15(b) and gate 16: a `q_com_trace_msm` whose `input_bytes`
    is 0x21, which is not a whole number of words. Reachable because
    `FinalMsmShape.input_bytes` is a public field (MEM:384) a caller may set
    without going through `from_terms`; `from_terms` itself can only produce
    multiples of 160. -/
def oddSizedConfig : VerifierMemoryLayoutConfig :=
  { verifierMemoryLayoutConfigDefault with
    pcs := { pcsMemoryRequirementsDefault with
      qComTraceMsm := { terms := 0, inputBytes := 0x21 } } }

def oddSizedLayout : VerifierMemoryLayout :=
  VerifierMemoryLayout.new rotationMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000)) oddSizedConfig

/-- `(start, len)` of a named region, with a sentinel no real region can have so a
    missing registration fails the gate rather than passing it. -/
def regionOf (l : VerifierMemoryLayout) (name : String) : Nat × Nat :=
  match l.map.region name with
  | some r => (r.start, r.len)
  | none => (0xFFFFF, 0xFFFFF)

/-- The lifetime of a named region, or `permanent` when it is missing - the
    strictest reading, so a dropped registration cannot make a disjointness claim
    easier to satisfy. -/
def lifetimeOf (l : VerifierMemoryLayout) (name : String) : MemoryLifetime :=
  match l.map.region name with
  | some r => r.lifetime
  | none => MemoryLifetime.permanent

/-- Two non-empty byte ranges sharing at least one byte: `MemoryRegion::overlaps`
    (MEM:211-213) spelled on raw numbers rather than on regions. -/
def sharesBytes (s1 l1 s2 l2 : Nat) : Bool :=
  l1 != 0 && l2 != 0 && s1 < s2 + l2 && s2 < s1 + l1

/-- A COUNTERFACTUAL, not a Rust item and not part of the statement surface: what
    "pairwise disjoint" would mean if PLAN 9.5's `Supported.layout` were read as a
    GLOBAL byte-disjointness test, ignoring lifetimes. Gate 14 uses it to show that
    reading rejects every layout `new` produces. -/
def naiveGlobalByteDisjoint : List MemoryRegion → Bool
  | [] => true
  | a :: rest =>
    (rest.all fun b => ! (sharesBytes a.start a.len b.start b.len))
      && naiveGlobalByteDisjoint rest

/-- The smoke bound of a layout built from the given sizing inputs: q_com trace
    bytes, final MSM bytes, accumulator MSM TERMS, quotient count, selector count. -/
def smokeLenFor (qc fm terms nq ns : Nat) : Nat :=
  (VerifierMemoryLayout.new
    { referenceSyntheticMeta with numQuotients := nq, numSimpleSelectors := ns }
    referenceSyntheticVk (ptrMemory (valueFromNat 0x2000))
    { verifierMemoryLayoutConfigDefault with
      accMsmTerms := terms,
      pcs := { pcsMemoryRequirementsDefault with
        qComTraceMsm := { terms := 0, inputBytes := qc },
        finalMsm := { terms := 0, inputBytes := fm } } }).constructorG1msmSmokeInputBytes


/-- 1 (MEM:1080-1088). THE COMMITMENT CENSUS, INCLUDING THE DOUBLED LOOKUP TERM.
    `referenceSyntheticMeta` is the reference's own shape and 11 is
    2 + 1 + 1 + 2 + 1 + 1 + 3; the second `num_lookups` is the lookup ACCUMULATORS
    and the first the multiplicities, so dropping it gives 10. The empty meta gives
    0, which is what makes the 11 a count and not a constant.
    PERTURBATIONS RUN: P01 (delete the second `meta_.numLookups` term) reddens this gate,
    gate 2 and
    gate 14 - the commitment run shrinks by one G1, which moves every later base
    and changes the same-byte pair count; P02 (delete `meta_.numQuotients`) reddens
    the same three. -/
def commitmentG1Count_ok : Bool :=
  commitmentG1Count referenceSyntheticMeta == 11
    && commitmentG1Count constraintSystemMetaDefault == 0
    && commitmentG1Count poseidonShapedMeta == 15
    && commitmentG1Count { referenceSyntheticMeta with numLookups := 2 } == 13

/-- 2 (hazard 4). THE TWO `commitment_g1_count`s ARE DIFFERENT FUNCTIONS. The plan
    said to call the Abi.lean one; the Rust at MEM:597 does not - it calls the free
    `memory.rs` function on the meta, while AP:261-263 is a method on a
    `ProofCalldataLayout` that never sees a meta. They agree on
    `poseidonShapedMeta` (both 15) because that meta's protocol and its fields were
    built together by `ProtocolPlan::from_constraint_system`, and they DISAGREE on
    `referenceSyntheticMeta` (11 here, 0 there) because that meta was hand-written
    over an empty protocol. A port that had called the Abi function would have
    silently planned a zero-length commitment run for every hand-built meta, and no
    gate on the shared all-zero fixture would have noticed.
    PERTURBATIONS RUN: P01 and P02 - each perturbs only the meta-side formula, leaving the
    layout-side
    one alone - both redden this gate, which is the shape of the claim: the two
    counts are independent and agree only when the meta and its protocol were built
    together by `from_constraint_system`. -/
def commitmentG1Count_matchesLayout_ok : Bool :=
  let agree (m : ConstraintSystemMeta) : Bool :=
    match ProofCalldataLayout.fromProtocol m.protocol 0 m.numEvals m.numPointSets with
    | .ok layout => layout.commitmentG1Count == commitmentG1Count m
    | .error _ => false
  agree poseidonShapedMeta && ! agree referenceSyntheticMeta

/-- 3 (MEM:1099-1105). THE BATCH-INVERSION INPUT RUN, including the two branches the
    reference tests separately: 5 instances with `rotation_last = -3` gives
    5 + 3 + 1 = 9 (MEM:1523), zero instances gives the fallback word,
    `|rotation_last| + 2 = 5` (MEM:1575), and 500 gives 504 (MEM:1598). The
    `numInstances == 0` arm is the one a port writes backwards: it is NOT "one
    fewer", it is the fallback slot for `L_0` recovery, so it adds 2 where the
    other arm adds 1 and the instance count itself disappears.
    PERTURBATIONS RUN: P03 (swap the two arms' `+ 2` and `+ 1`) reddens this gate and gates
    4, 10,
    11, 12 and 14. -/
def batchInvertInputWords_ok : Bool :=
  batchInvertInputWords rotationMeta 5 == 9
    && batchInvertInputWords rotationMeta 0 == 5
    && batchInvertInputWords rotationMeta 500 == 504
    && batchInvertInputWords constraintSystemMetaDefault 0 == 2
    && batchInvertInputWords constraintSystemMetaDefault 1 == 2

/-- 4 (MEM:1107-1117). THE SCRATCH BYTES: one modexp frame plus `input_words - 2`
    prefix products, and the subtraction SATURATES - a one-word batch stores no
    prefix products at all and still needs the frame. 416 is MEM:1523's own
    arithmetic (192 + (5+3+1-2)*32); 192 is the floor for any input of two words or
    fewer, which is what an empty circuit with `rotation_last = 0` produces.
    PERTURBATIONS RUN: P04 (drop the `- 2`) reddens this gate and gates 10, 11, 12 and 14; P03
    reaches it too. -/
def batchInvertScratchBytes_ok : Bool :=
  batchInvertScratchBytes rotationMeta 5 == 416
    && batchInvertScratchBytes rotationMeta 0 == 288
    && batchInvertScratchBytes constraintSystemMetaDefault 0 == 192
    && batchInvertScratchBytes constraintSystemMetaDefault 1 == 192
    && batchInvertScratchBytes rotationMeta 500 == 16256

/-- 5 (MEM:1282-1340). THE REFERENCE'S OWN OFFSET REGRESSION TEST, ported: seven
    `assert_eq!`s that tie the PCS windows and the commitment base to `theta_mptr`
    through the window layout. Every number is copied from the reference's
    assertion, and the absolute addresses are the ones that test's
    `Ptr::memory(0x2000)` produces: theta at 0x2460, because the 0x460-byte VK ends
    there and the challenge block is empty.
    PERTURBATIONS RUN: P05 (`atTheta` reading words as bytes) reddens this gate and ten
    others;
    P27 (point the q_eval_set window at `qEvalCptrWord`) reddens this gate, gate 13
    and gate 14. -/
def new_preservesCurrentOffsets_ok : Bool :=
  let l := referenceLayout
  let theta := (ptrValue l.thetaMptr).asUsizeNat
  let w := l.thetaWindows
  theta == 0x2460
    && (ptrValue l.rotPointsMptr).asUsizeNat == theta + w.rotPointsWord * wordBytes
    && (ptrValue l.x1PowersMptr).asUsizeNat == theta + w.x1PowersWord * wordBytes
    && (ptrValue l.qEvalSetMptr).asUsizeNat == theta + w.qEvalSetWord * wordBytes
    && (ptrValue l.qEvalCptrMptr).asUsizeNat == theta + w.qEvalCptrWord * wordBytes
    && (ptrValue l.g1IdentityMptr).asUsizeNat == theta + w.g1IdentityWord * wordBytes
    && (ptrValue l.reversedEvalsMptr).asUsizeNat == theta + w.reversedEvalsWord * wordBytes
    && (ptrValue l.commsMptrBase).asUsizeNat
        == theta + (w.reversedEvalsWord + referenceSyntheticMeta.numEvals) * wordBytes

/-- 6 (MEM:1343-1436). THE SEVEN FIXED LOW-MEMORY REGIONS ARE REGISTERED, NOT JUST
    RETURNED, at the addresses and lengths the reference asserts: five of them share
    0x1000 (that IS hazard 1 - see gate 14), the pairing frames sit at 0x1240 and
    run 800 bytes, the transcript is zero-length under a default config, and the
    constructor's largest G1MSM smoke frame is
    `num_simple_selectors * G1_MSM_PAIR_BYTES = 480`. The scalar-inversion frame
    sits at `0x2000 - 0x100 = 0x1f00`, and the whole layout validates.
    PERTURBATIONS RUN: P08 (drop the `+ 2` in `quotientReturnLen`) reddens THIS GATE ALONE,
    which is
    what makes the fifth line a test of that `+ 2` and not of everything around it;
    P06 (`final_pairing_scratch` at the batch pointer) and P07 (scalar-inversion
    frame at `vkStart`) each redden this gate and eight others, and P28 (the smoke
    bound reading `selectorLen` instead of `linTraceLen`) reddens this gate and
    gate 17. -/
def new_fixedLowMemoryRegions_ok : Bool :=
  regionOf selectorLayout "constructor_smoke_scratch" == (0x1000, 768)
    && regionOf selectorLayout "transcript_buffer" == (0x1000, 0)
    && regionOf selectorLayout "pcs_pairing_static_working" == (0x1000, 1024)
    && regionOf selectorLayout "verifier_return" == (0x1000, 32)
    && regionOf selectorLayout "quotient_return" == (0x1000, 160)
    && regionOf selectorLayout "accumulator_pairing_batch" == (0x1000, 576)
    && regionOf selectorLayout "final_pairing_scratch" == (0x1240, 800)
    && selectorLayout.constructorG1msmSmokeInputBytes == 480
    && selectorLayout.scalarInvScratchMptr == 0x1f00
    && isOk selectorLayout.validate

/-- 7 (MEM:1439-1457). THE THREE PCS CAPACITY FAILURES, through `new` rather than
    through a hand-built record: the reference asserts `contains(..)` on the window
    name, and the gate pins the whole message, which is what also pins the DECIMAL
    formatting of the numbers (MEM:1050-1051 uses `{}`, not `{:#x}`). The fixture
    sits exactly on the caps, so one word past each is the smallest possible
    overflow.
    PERTURBATIONS RUN: both inside `Layout.lean`'s `validate`, rebuilt and restored: L1 (the
    rot_points arm made never-to-fire) reddens THIS GATE ALONE plus one LayoutKats
    gate, and L2 (`hashHex` in place of `toString` in the first message) likewise
    reddens this gate alone plus one LayoutKats gate - which is what makes the
    DECIMAL-formatting claim measured rather than asserted. -/
def new_pcsCapacity_err_ok : Bool :=
  errIs ((VerifierMemoryLayout.new referenceSyntheticMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000))
    { verifierMemoryLayoutConfigDefault with
      pcs := { pcsMemoryRequirementsDefault with rotPointsWords := 29 } }).validate)
    "PCS scratch layout mismatch: ROT_POINTS_MPTR needs 29 word(s), capacity is 28"
    && errIs ((VerifierMemoryLayout.new referenceSyntheticMeta referenceSyntheticVk
      (ptrMemory (valueFromNat 0x2000))
      { verifierMemoryLayoutConfigDefault with
        pcs := { pcsMemoryRequirementsDefault with x1PowersWords := 66 } }).validate)
      "PCS scratch layout mismatch: X1_POWERS_MPTR needs 66 word(s), capacity is 65"
    && errIs ((VerifierMemoryLayout.new referenceSyntheticMeta referenceSyntheticVk
      (ptrMemory (valueFromNat 0x2000))
      { verifierMemoryLayoutConfigDefault with
        pcs := { pcsMemoryRequirementsDefault with qEvalSetWords := 57 } }).validate)
      "PCS scratch layout mismatch: Q_EVAL_SET_MPTR needs 57 word(s), capacity is 56"

/-- 8 (MEM:1460-1472 with MEM:850-851). THE ACCUMULATOR MSM IS SIZED FROM ITS SHAPE
    AND FLOORED AT 0x7000. Four terms give 4*160 = 640 bytes, and with the empty
    meta the commitment run ends far below the floor, so the region starts at 0x7000
    exactly - the historical address the field comment at MEM:506 names.
    PERTURBATIONS RUN: P09 (drop the `Nat.max afterComms accMsmMinScratchBytes` floor)
    reddens this
    gate and gate 9: the region moves to 0x4600 and the trace word follows it down.
    Sizing from `terms * g1Bytes` instead of `g1MsmPairBytes` is the other half and
    is covered by gate 1's census perturbations reaching this layout. -/
def new_accMsmSized_ok : Bool :=
  let l := VerifierMemoryLayout.new constraintSystemMetaDefault referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000))
    { verifierMemoryLayoutConfigDefault with accMsmTerms := 4 }
  regionOf l "accumulator_msm" == (0x7000, 640) && l.accMsmScratch == 0x7000
    && isOk l.validate

/-- 9 (MEM:1475-1502). THE TRACE LOG WORD IS PLACED AFTER EVERY OTHER REGION. The
    reference asserts the registration, the one-word length, the inequality against
    the final-MSM end, and that the layout validates; the gate adds the absolute
    address (0x7280) so a dropped candidate in the 23-element maximum cannot hide
    behind the inequality. Note WHICH candidate wins here: the accumulator MSM end
    at 0x7000 + 640, not the final MSM the reference's own assert names - the
    reference's inequality is a lower bound, not the maximum.
    PERTURBATIONS RUN: P10 (delete the `acc_msm_scratch + acc_msm_len` candidate) reddens
    this gate
    and gate 8. NON-REDDENING CONTROL: P23, deleting the final `alignUp`, reddens
    NOTHING in this file - every candidate end in this fixture is already a whole
    number of words, so the alignment step is invisible here, and gate 16 is what
    tests the rounding on a size that is not. -/
def new_traceWord_ok : Bool :=
  regionOf traceLayout "trace_u256_log_word" == (0x7280, 32)
    && traceLayout.traceU256Mptr == 0x7280
    && traceLayout.traceU256Mptr
        >= traceLayout.pcsFinalMsmScratchMptr + 10 * g1MsmPairBytes
    && isOk traceLayout.validate

/-- 10 (MEM:1505-1525). THE BATCH-INVERT SCRATCH TRACKS THE INSTANCE SHAPE: 416
    bytes for five instances and `rotation_last = -3`, registered under the name
    the reference looks it up by.
    PERTURBATIONS RUN: P04 (drop the `- 2`) and P26 (swap the two Lagrange allocations) each
    redden
    this gate; P29 (a transcript length that ignores `config.transcriptWords`)
    reaches it too. -/
def new_batchInvertTracks_ok : Bool :=
  regionOf rotationLayout "batch_invert_scratch" == (0x3fe0, 416)

/-- 11 (MEM:1532-1577). THE LAGRANGE DENOMINATOR RUN: length, lifetime, and the
    sequential same-phase placement the Rust comment at MEM:785-790 insists on
    (`region.start == scratch.start + scratch.len`, which is only true because BOTH
    allocations come from ONE scratch allocator). Five instances give
    (5+3+1)*32 = 288 bytes above the 416-byte prefix-product scratch; zero instances
    give (3+2)*32 = 160. Both layouts validate.
    PERTURBATIONS RUN: P11 (a FRESH allocator for the second allocation) reddens this gate
    and gates
    10, 12, 13, 14 and 21 - `lagrange_denoms` returns to 0x3fe0, a same-phase
    overlap with `batch_invert_scratch`, so the `isOk` line and the placement line
    go red together; P12 (cap the run at a fixed 100 words) reddens this gate and
    gate 12. -/
def new_lagrangeDenoms_ok : Bool :=
  regionOf rotationLayout "lagrange_denoms" == (0x4180, 288)
    && lifetimeOf rotationLayout "lagrange_denoms"
        == MemoryLifetime.phase MemoryPhase.lagrangeBatchInvert
    && rotationLayout.lagrangeDenomsMptr
        == (regionOf rotationLayout "batch_invert_scratch").1
            + (regionOf rotationLayout "batch_invert_scratch").2
    && isOk rotationLayout.validate
    && isOk ((VerifierMemoryLayout.new rotationMeta referenceSyntheticVk
      (ptrMemory (valueFromNat 0x2000)) verifierMemoryLayoutConfigDefault).validate)


/-- 12 (MEM:1583-1602). THE REGISTERED RUN REMOVES THE OLD INSTANCE CLIFF: 500
    public instances is 16128 bytes of denominators at 0x7f60 - above the 0x7000
    accumulator floor, which is exactly the spill into other people's memory the
    reference's comment at MEM:792-796 says the registered region exists to prevent -
    and the layout still validates and is still well-formed.
    PERTURBATIONS RUN: P12 (replace the computed length with a fixed 100-word cap) reddens
    this gate
    and gate 11; P11 and P03 reach it too. -/
def new_scalesBeyondCliff_ok : Bool :=
  let l := VerifierMemoryLayout.new rotationMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x2000))
    { verifierMemoryLayoutConfigDefault with numInstances := 500 }
  regionOf l "lagrange_denoms" == (0x7f60, 16128) && isOk l.validate
    && decide l.map.WellFormed

/-- 13 (HAZARD 5, the headline). THE CONSTRUCTOR'S OUTPUT IS WELL-FORMED: the
    poseidon-shaped layout satisfies `MemoryMap.WellFormed` - the Prop PLAN 9.5
    reads as `Supported.layout` - and passes the reference's own
    `VerifierMemoryLayout::validate`, over 30 registered regions of which 28 are
    non-empty. The `regions.length == 30` conjunct is what stops this gate from
    being satisfied by an empty map, which is what the shared
    `verifierLayoutFixture` carries and which would make both well-formedness
    claims vacuous (R-48).
    PERTURBATIONS RUN: P13 (delete the `trace_u256_log_word` registration) reddens this
    gate's count
    line along with gates 9 and 21; P14 (give `quotient_state` the
    LagrangeBatchInvert phase, a real same-phase collision) and P19 (re-root the PCS
    allocator) each redden this gate, gate 14 and gate 19. -/
def new_wellFormed_ok : Bool :=
  decide poseidonLayout.map.WellFormed
    && isOk poseidonLayout.validate
    && poseidonLayout.map.regions.length == 30
    && (poseidonLayout.map.regions.filter fun r => r.len != 0).length == 28

/-- The same-byte / different-phase pairs of a region list, as data, so gate 14 can
    count them instead of only exhibiting three. -/
def sameByteDifferentPhasePairs : List MemoryRegion → List (String × String)
  | [] => []
  | a :: rest =>
    (rest.filterMap fun b =>
      if sharesBytes a.start a.len b.start b.len
           && ! (memoryLifetimeIntersects a.lifetime b.lifetime)
      then some (a.name, b.name) else none) ++ sameByteDifferentPhasePairs rest

/-- 14 (HAZARD 1, the finding). PHASE-SCOPED DISJOINTNESS IS NOT GLOBAL
    DISJOINTNESS, and `MemoryMap.WellFormed` is the right predicate for it.
    `wellFormedBool` (Layout.lean:1114-1119) routes its disjointness condition
    through `memoryRegionsPairwiseDisjoint`, which conjoins
    `memoryLifetimeIntersects` exactly as MEM:274 does - so two regions may share
    bytes when their phases are disjoint. This is not a corner the planner grazes:
    the poseidon layout has FIFTY-FOUR such pairs, and three named ones are asserted
    here - the low-memory helpers that all start at 0x1000, the selector accumulators
    that the batch-invert scratch reuses, and the quotient VM state that lands inside
    the batch-invert scratch. Meanwhile the counterfactual `naiveGlobalByteDisjoint`
    - what "disjoint" reads as if lifetimes were ignored - is FALSE on the same map.
    So if PLAN 9.5's `Supported.layout` is ever implemented as a global pairwise
    test, `new` fails it on every real input, and the correct response is to fix the
    statement, not the planner. It does not need fixing on that axis: it is already
    the lifetime-aware predicate.
    PERTURBATIONS RUN: L3 (drop the `memoryLifetimeIntersects` conjunct from
    `memoryRegionsPairwiseDisjoint` in `Layout.lean`, rebuilt and restored) reddens
    this gate - the map stops being well-formed - together with gates 12, 13 and 15,
    while the counterfactual's own predicate is untouched by it; P14 and P19, which
    create real same-phase collisions inside `new`, redden it too. NON-REDDENING
    CONTROL: P24, dropping the two `len != 0` exemptions from `sharesBytes`, reddens
    NOTHING - the only zero-length regions this fixture has (`challenge_slots`,
    `q_com_fixed_window`) sit at addresses no other region touches, so the strict
    inequalities already exclude them. The exemptions are kept because MEM:212 has
    them, not because a gate needs them. -/
def new_phaseScopedOverlap_ok : Bool :=
  decide poseidonLayout.map.WellFormed
    && ! naiveGlobalByteDisjoint poseidonLayout.map.regions
    && (sameByteDifferentPhasePairs poseidonLayout.map.regions).length == 54
    && sharesBytes (regionOf poseidonLayout "constructor_smoke_scratch").1
      (regionOf poseidonLayout "constructor_smoke_scratch").2
      (regionOf poseidonLayout "verifier_return").1 (regionOf poseidonLayout
      "verifier_return").2
    && lifetimeOf poseidonLayout "constructor_smoke_scratch"
        != lifetimeOf poseidonLayout "verifier_return"
    && sharesBytes (regionOf poseidonLayout "selector_accumulators").1
      (regionOf poseidonLayout "selector_accumulators").2
      (regionOf poseidonLayout "batch_invert_scratch").1
      (regionOf poseidonLayout "batch_invert_scratch").2
    && sharesBytes (regionOf poseidonLayout "batch_invert_scratch").1
      (regionOf poseidonLayout "batch_invert_scratch").2
      (regionOf poseidonLayout "quotient_state").1 (regionOf poseidonLayout
      "quotient_state").2

/-- 15 (HAZARD 1's second half, and the finding PLAN 9.5 needs). `WellFormed` IS
    STRICTLY WEAKER THAN `validate` IN TWO WAYS THAT MATTER HERE, and both are
    reachable from `new`.
    (a) SPILL WINDOW. `wellFormedBool` bounds a region start by
    `SOLIDITY_RESERVED_MEMORY_BYTES` (0x80), which is what `MemoryMap::validate`
    checks (MEM:239). The solc via-IR spill guard the hazard is about is
    `LOW_MEMORY_SCRATCH_START` (0x1000), and it lives in
    `VerifierMemoryLayout::validate` (MEM:1028-1036), NOT in the map. A layout
    built at `vk_mptr = 0x180` is therefore `WellFormed` and rejected by
    `validate` at the same time. So `Supported.layout = g.plan.memory.WellFormed`
    does NOT deliver the "above solc spill window" clause of PLAN 9.5's comment:
    that clause needs the record-level validator, or a second bound in the predicate.
    (b) LENGTH ALIGNMENT. `wellFormedBool` checks `start % WORD_BYTES` only;
    MEM:262-267 also rejects a length that is not a whole number of words, and
    `new` can register one (gate 16).
    PERTURBATIONS RUN: L4 (raise the predicate's bound from `solidityReservedMemoryBytes` to
    `lowMemoryScratchStart`, the one-line change that would make PLAN 9.5's wording
    true) reddens THIS GATE ALONE, and so does L5 (delete the unaligned-length arm
    from `memoryMapValidateReserved`) - which is the evidence that both halves of
    this gate answer to the divergence they name. P07 (scalar-inversion frame at
    `vkStart`), P15 (rounding the q_com trace length) and P30 (renaming the
    vk_payload registration) reach it too. -/
def new_wellFormed_weakerThanValidate_ok : Bool :=
  let lowVk := VerifierMemoryLayout.new rotationMeta referenceSyntheticVk
    (ptrMemory (valueFromNat 0x180))
    { verifierMemoryLayoutConfigDefault with numInstances := 5 }
  decide lowVk.map.WellFormed
    && errIs lowVk.validate
      ("memory region vk_payload starts at 0x180, below LOW_MEMORY_SCRATCH_START"
        ++ " (0x1000); it can overlap solc's via-IR stack-to-memory spill window"
        ++ " [0x80, reserved_end)")
    && decide oddSizedLayout.map.WellFormed
    && errIs oddSizedLayout.validate
      "memory region pcs_q_com_trace_msm has unaligned length 0x21"

/-- 16 (HAZARD 3). ROUNDING INSIDE THE SCRATCH ALLOCATOR, on a size that is not a
    multiple of `WORD_BYTES`. `ScratchAllocator::alloc_phase_scratch`
    (MEM:372-375) advances the cursor with `next_multiple_of(WORD_BYTES)` but
    registers the RAW length - the asymmetry Layout.lean:622-625 records. So a
    0x21-byte allocation at 0x400 puts the next same-phase allocation at 0x440 while
    the region itself stays 33 bytes long. Inside `new` the two effects separate:
    the unrounded length is what `MemoryMap::validate` then rejects (gate 15(b)),
    and the rounded cursor is what keeps a same-phase successor from colliding. Note
    that `new` cannot route a non-word size into a same-phase successor at all -
    every length it computes is a multiple of 32 except the three that come from
    `FinalMsmShape.input_bytes`, and each of those owns its phase alone - so the
    successor check is done at the allocator, which is the level the asymmetry lives
    at, and the `pcs_final_msm` line shows the aliasing that replaces it.
    PERTURBATIONS RUN: L6 (the cursor advancing to `start + len` instead of
    `next_multiple_of`, in
    `Layout.lean`, rebuilt and restored) reddens THIS GATE ALONE; L7 (registering
    the rounded length instead of the raw one) reddens this gate and gate 15; P15
    (rounding `qComTraceLen` inside `new`) reddens this gate and gate 15. -/
def new_alignmentRounding_ok : Bool :=
  let s0 := memoryArenaDefault.scratchAllocator 0x400
  let (s1, a) := s0.allocPhaseScratch "a" 0x21 MemoryPhase.quotientVm
  let (s2, b) := s1.allocPhaseScratch "b" 0x21 MemoryPhase.quotientVm
  a == 0x400 && b == 0x440
    && (match s2.arena.intoMap.region "a" with
        | some r => r.len == 0x21 && r.start == 0x400
        | none => false)
    && regionOf oddSizedLayout "pcs_q_com_trace_msm" == (0x3fe0, 0x21)
    && regionOf oddSizedLayout "pcs_final_msm" == (0x3fe0, 0)

/-- 17 (HAZARD 2). THE CONSTRUCTOR G1MSM SMOKE BOUND IS A MAXIMUM, NOT A DEFAULT.
    MEM:615's `.expect("constructor G1MSM smoke bounds are non-empty")` cannot
    fire - the array literal has five elements - so the port folds over the literal
    instead of inventing a fallback (see `natMaximumNonempty`). What the gate pins
    is that the fold really is the maximum: each of the five bounds is made the
    largest in turn and the field follows it, including the floor
    `G1_MSM_PAIR_BYTES = 160`, which is what stops an empty circuit from planning a
    zero-length smoke buffer. A port that had written `.getD 0` would report 0 here
    and still validate, which is exactly the silent-zero failure the hazard warns
    about.
    PERTURBATIONS RUN: P16 (seed the fold with 0 instead of the literal's first element)
    reddens this
    gate and gate 15 - the all-zero config then reports 0, which is exactly the
    silent-zero failure the hazard names, and it is the ONLY way the first line can
    be reddened; P17 (drop `linTraceLen` from the array) reddens this gate and gate
    6; P25 (make the fold stop at the first element) reddens this gate and eight
    others. -/
def constructorG1msmSmokeLen_ok : Bool :=
  smokeLenFor 0 0 0 0 0 == 160
    && smokeLenFor 1440 0 0 0 0 == 1440
    && smokeLenFor 0 1920 0 0 0 == 1920
    && smokeLenFor 0 0 20 0 0 == 3200
    && smokeLenFor 0 0 0 0 3 == 480
    && smokeLenFor 1440 320 4 2 1 == 1440

/-- 18 (R-48). NON-VACUITY FOR EVERY POINTER COMPARISON IN THIS FILE. The shared
    `LayoutKats.verifierLayoutFixture` has every PCS base at 0, so on it "these two
    bases differ" is false and "these two bases are the same" is trivially true. This
    fixture has SEVEN distinct commitment-category bases among the eight fields (the
    eighth is `advice_comms_mptr_base`, which MEM:758 pins EQUAL to
    `comms_mptr_base` by construction) and TWENTY-SEVEN distinct theta-slot
    pointers, and the gate asserts the distinctness itself rather than relying on
    it - and then shows the shared fixture would have failed the same assertion.
    PERTURBATIONS RUN: P18 (point `lookupMCommsMptrBase` at `adviceCommsMptrBase`, dropping
    the
    advice stride) reddens THIS GATE ALONE - the only perturbation in this file that
    changes a pointer without moving a single byte address, which is what makes the
    distinctness claim a test and not a description. -/
def new_distinctBases_ok : Bool :=
  ((List.map (fun p => (ptrValue p).asUsizeNat)
      [poseidonLayout.commsMptrBase, poseidonLayout.adviceCommsMptrBase,
       poseidonLayout.lookupMCommsMptrBase, poseidonLayout.permZCommsMptrBase,
       poseidonLayout.lookupHelperCommsMptrBase, poseidonLayout.lookupZCommsMptrBase,
       poseidonLayout.trashcanCommsMptrBase,
       poseidonLayout.quotientLimbCommsMptrBase]).eraseDups.length == 7)
    && ((List.map (fun p => (ptrValue p).asUsizeNat)
        [poseidonLayout.thetaMptr, poseidonLayout.betaMptr, poseidonLayout.gammaMptr,
        poseidonLayout.trashChallengeMptr, poseidonLayout.yMptr, poseidonLayout.xMptr,
        poseidonLayout.x1Mptr, poseidonLayout.x2Mptr, poseidonLayout.x3Mptr,
        poseidonLayout.x4Mptr, poseidonLayout.fComMptr, poseidonLayout.piMptr,
        poseidonLayout.accLhsMptr, poseidonLayout.accRhsMptr, poseidonLayout.xNMptr,
        poseidonLayout.xNMinus1InvMptr, poseidonLayout.lLastMptr,
        poseidonLayout.lBlindMptr, poseidonLayout.l0Mptr, poseidonLayout.instanceEvalMptr,
        poseidonLayout.quotientEvalMptr, poseidonLayout.quotientMptr,
        poseidonLayout.fEvalMptr, poseidonLayout.vMptr, poseidonLayout.finalComMptr,
        poseidonLayout.pairingLhsMptr, poseidonLayout.pairingRhsMptr]).eraseDups.length == 27)
    && (ptrValue poseidonLayout.commsMptrBase).asUsizeNat
        == (ptrValue poseidonLayout.adviceCommsMptrBase).asUsizeNat
    && (ptrValue
    Midfall.Generator.LayoutKats.verifierLayoutFixture.commsMptrBase).asUsizeNat == 0

/-- 19 (MEM:826-849, and the cursor model). THE THREE PCS SCRATCH REGIONS SHARE ONE
    BASE BECAUSE THEY ARE IN THREE PHASES. `pcs_scratch_mptr` is
    `quotient_tmp_mptr`, and the q_eval source table, the q_com trace MSM and the
    fused final MSM each start there with their own phase cursor - while
    `quotient_state` and `quotient_stack`, which share the QuotientVm phase,
    advance sequentially from `selector_acc + selector_len`. This is the
    per-phase-cursor rule of MEM:337-342 read out of a real layout, and the
    `batch_invert_scratch == selector_acc` line is the pinning the comment at
    MEM:789-790 says the order exists to keep.
    PERTURBATIONS RUN: P19 (root the PCS allocator at `selectorAccMptr`) reddens this gate
    and gates
    13 and 14; P26 (swap the two Lagrange allocations) reddens this gate and five
    others including the last line; P14 (quotient_state sharing the Lagrange phase)
    reddens this gate and gates 13 and 14. -/
def new_scratchAliasing_ok : Bool :=
  poseidonLayout.pcsQEvalSourceTableMptr == poseidonLayout.pcsQComTraceScratchMptr
    && poseidonLayout.pcsQComTraceScratchMptr == poseidonLayout.pcsFinalMsmScratchMptr
    && poseidonLayout.pcsFinalMsmScratchMptr == poseidonLayout.quotientTmpMptr
    && poseidonLayout.quotientStackMptr > poseidonLayout.quotientTmpMptr
    && poseidonLayout.quotientStackHi
        == poseidonLayout.quotientStackMptr + poseidonShapedConfig.quotientStackWords *
        wordBytes
    && poseidonLayout.batchInvertScratchMptr == poseidonLayout.selectorAccMptr

/-- 20 (HAZARD 6). EVERYTHING `new` PLANS IS ABOVE THE SOLC VIA-IR SPILL WINDOW.
    The minimum region start in the poseidon layout is exactly
    `LOW_MEMORY_SCRATCH_START` = 0x1000, so the margin against the constant is ZERO
    by design - the low-memory helpers are meant to sit on the floor - and the real
    margin is against the largest reservation the reference has observed, `0x8e0`
    (LM:34-36, the same number in the comment above
    `compiled_memoryguard_does_not_overlap_generated_layout` at test.rs:1624), which
    is `0x1000 - 0x8e0 = 0x720` bytes. The binding constraint `new` puts on its
    CALLER is `vk_mptr >= LOW_MEMORY_SCRATCH_START + MODEXP_SCRATCH_BYTES = 0x1100`,
    because the scalar-inversion frame is placed at `vk_mptr - 0x100` and is the
    only region that can go below the floor - gate 15(a) is what shows the floor is
    enforced by `validate` and not by `WellFormed`. The complementary bound - that
    solc's reservation really ends at or below 0x1000 - is checked against compiled
    bytecode by the Rust test named above and is NOT checkable from here; this gate
    is the generated-layout half only.
    PERTURBATIONS RUN: P20 (the low-memory floor at 0x800) reddens this gate and nine
    others; P07
    (scalar-inversion frame at `vkStart`) reddens this gate and gate 6 among others.
    The `0x1000 - 0x8e0 == 0x720` line is arithmetic about a constant pair and is
    NOT reddened by any perturbation of the planner - it is stated so the margin is
    checkable, not claimed as a test. -/
def new_spillWindowMargin_ok : Bool :=
  (poseidonLayout.map.regions.map (fun r => r.start)).foldl min 0xFFFFFFFF == 0x1000
    && poseidonLayout.map.regions.all (fun r => lowMemoryScratchStart <= r.start)
    && poseidonLayout.scalarInvScratchMptr == 0x4000 - modexpScratchBytes
    && 0x1000 - 0x8e0 == 0x720

/-- 21 (R1 order). THE THIRTY REGISTRATIONS ARE IN THE RUST'S ORDER. This is not
    decoration: `MemoryMap::validate` walks the strict upper triangle of the region
    list and reports the FIRST offending pair (MEM:272-286), so the order decides
    which message a broken layout produces, and a re-ordered port can pass every "it
    errors" gate while naming a different region. The list below is the registration
    order of MEM:625-899 read straight off the source.
    PERTURBATIONS RUN: P21 (swap the `q_com_fixed_window` and `q_eval_set` registrations)
    reddens
    THIS GATE ALONE: the two regions alias the same bytes and share a phase, so
    `validate` cannot see the swap, which is precisely why the order needs its own
    gate. P11, P13, P26 and P30 also reach it. -/
def new_registrationOrder_ok : Bool :=
  poseidonLayout.map.regions.map (fun r => r.name) ==
    ["constructor_smoke_scratch", "transcript_buffer", "pcs_pairing_static_working",
     "verifier_return", "quotient_return", "final_pairing_scratch", "vk_payload",
     "scalar_inv_scratch", "challenge_slots", "theta_scalar_and_g1_slots", "rot_points",
     "x1_powers", "q_com_fixed_window", "q_eval_set", "q_eval_cptr_slot", "g1_identity",
     "decoded_evals", "decompressed_commitments", "constructor_g1msm_smoke_scratch",
     "selector_accumulators", "batch_invert_scratch", "lagrange_denoms", "quotient_state",
     "quotient_stack", "pcs_q_eval_source_table", "pcs_q_com_trace_msm", "pcs_final_msm",
     "accumulator_msm", "accumulator_pairing_batch", "trace_u256_log_word"]

#eval commitmentG1Count_ok -- expect true
#eval commitmentG1Count_matchesLayout_ok -- expect true
#eval batchInvertInputWords_ok -- expect true
#eval batchInvertScratchBytes_ok -- expect true
#eval new_preservesCurrentOffsets_ok -- expect true
#eval new_fixedLowMemoryRegions_ok -- expect true
#eval new_pcsCapacity_err_ok -- expect true
#eval new_accMsmSized_ok -- expect true
#eval new_traceWord_ok -- expect true
#eval new_batchInvertTracks_ok -- expect true
#eval new_lagrangeDenoms_ok -- expect true
#eval new_scalesBeyondCliff_ok -- expect true
#eval new_wellFormed_ok -- expect true
#eval new_phaseScopedOverlap_ok -- expect true
#eval new_wellFormed_weakerThanValidate_ok -- expect true
#eval new_alignmentRounding_ok -- expect true
#eval constructorG1msmSmokeLen_ok -- expect true
#eval new_distinctBases_ok -- expect true
#eval new_scratchAliasing_ok -- expect true
#eval new_spillWindowMargin_ok -- expect true
#eval new_registrationOrder_ok -- expect true

end Midfall.Generator.LayoutMemoryKats
