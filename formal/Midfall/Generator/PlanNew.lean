-- |
-- Midfall.Generator.PlanNew
--
-- OBJ.6 (PLAN-V3, V3 row 40): THE QUOTIENT GLUE OF LoweringPlan::new.
--
-- WHAT THIS FILE IS. plan.rs:235-329 is the generator's constructor, and the quotient.rs
-- items it calls had never been ported: compact_quotient_program_for
-- (QRS:165-181), quotient_template_program (QRS:189-238), quotient_opcode_usage
-- (QRS:259-294) and quotient_mem_usage (QRS:297-310), quotient_stack_words_for_build
-- (QRS:314-322), quotient_program_plan (QRS:425-526) with its execution_manifest /
-- validate_execution_manifest bridge (QVM:367-489), native_callback_scratch_words
-- (QRS:1447-1464) with the two scratch-width helpers beside it (QRS:1401-1417,
-- :1441-1445), and build_quotient_program_items / build_quotient_program_items_with_limb_ops
-- (QRS:2101-2112, :2114-2146). Everything THEY call was already in the tree - the Evaluator,
-- the builder, the recognizers, quotient_identity_parts, selector_fold_plan,
-- native_gate_indices, structured_lookup_max_parallel, quotient_vm_guards,
-- PackedProgramCodec - so the gap was the glue and nothing else. That is worth saying
-- plainly, because the tree said otherwise: LoweringPlan.lean:49-51 and :63-72 recorded
-- these as blocked on the Evaluator and on the halo2 ConstraintSystem, and both blockers
-- were stale - F.1 landed the ConstraintSystem at PoseidonFixture.lean:394 and P-09f landed
-- the Evaluator's consumers. Those docstrings are corrected in this commit.
--
-- WHY PlanNew AND NOT LoweringPlan. LoweringPlan.lean is P-11's port of plan.rs's RECORD,
-- accessors and validators; the constructor is a different unit of work with a different
-- fixture, and OBJ.7 (newFromVk, compactBlocksOf, generateAll) lands on top of this file.
-- The namespace is the one the card names.
--
-- THE RECEIVER DEVIATION, STATED ONCE (R1 arity; the precedent is trashManifestName at
-- QuotientBlocks.lean:942-958, which takes the ConstraintSystem for the same reason). Every
-- item here is a method on impl<'params, 'meta> VerifierBuildInputs<'params, 'meta>
-- (QRS:164) or on impl QuotientProgramPlan (QVM:382), and the Rust reaches the circuit
-- through self.vk.cs(). Lean has no self, so the port takes the two things the bodies
-- actually read - a FieldCtx F and a ConstraintSystem F - as explicit arguments. Nothing
-- about VerifierBuildInputs is imported and nothing is added to it. VkBuildEnv
-- (Vk.lean:398-421) is the same relation spelled as data for the four callbacks vk.rs
-- threads; OBJ.7 fills its quotientProgramPlan and compactQuotientProgramFor fields from
-- these defs.
--
-- compactQuotientProgramFor returns the FULL pair the Rust returns - (QuotientProgramBuild,
-- Vec<usize>) - and not VkQuotientBuild, the two-field view VkBuildEnv asks for. The Rust's
-- own caller at VK:379 destructures and discards the second component, so the projection is
-- one line at the call site; dropping data here to match a projection would restate the
-- consumer instead of the producer.
--
-- THE PANIC SITES (R4, WITH ONE DEVIATION, STATED). R4 says a panic becomes
-- .panic "<path>:<line>", and P-11 applied it literally: every Fault.panic in
-- LoweringPlan.lean carries the path:line and NOTHING ELSE, so those five messages are lost
-- (LoweringPlan.lean:83-95 records the loss). This file does not follow P-11 there: it uses
-- siteQ, the helper the neighbouring quotient package already built for exactly this purpose
-- (QuotientBlocks.lean:144-148), which renders path:line (message). The message is therefore
-- PRESERVED rather than lost, which is strictly more evidence and is what lets gate 10 assert
-- the site AND the text of each of the five aborts. The five:
-- * QRS:202  expect("VK must carry quotient constants")
-- * QRS:204  expect("VK must carry quotient program")
-- * QRS:205  assert!("quotient const table exceeded VK payload reservation")
-- * QRS:209  assert!("quotient program length exceeded VK payload reservation")
-- * QRS:524  expect("quotient execution plan must preserve the identity stream")
-- The line cited is the line the panic fires on: for .expect the line holding the call, for
-- assert! the line holding the macro. NOTE FOR OBJ.7, which predicts "PANIC quotient.rs:204"
-- for a payload with NO reservation fields: with both offsets none the FIRST abort is the
-- constant offset, which is QRS:202; :204 is the program offset. The sites here are what the
-- file says - quotient.rs:202 is the line holding quotient_const_offset_words.expect - and
-- templateProgramPanicSites_areTheRecordedOnes_ok reads quotient.rs and pins all five lines
-- plus the two lines of quotient_identity_expr, so a re-cite cannot drift silently.
--
-- THE Err MESSAGES ARE NOT LOST. execution_manifest and validate_execution_manifest return
-- Result<_, String> and the plan's .expect at QRS:523-524 is the only place their payload is
-- discarded, so both format! strings are ported verbatim. The Rust renders source and target
-- with {:?}; showSourceDebug and showTargetDebug reproduce that rendering by hand, because
-- this tree derives no Debug and a String carries text.
--
-- COMPUTABILITY (D-P17). Every item here is a def the VM can run on a concrete FieldCtx.
-- There is no native_decide and no theorem in this file: a proof living here would have to
-- import the concrete fixture it is about, and checks.sh reddens a theorem-bearing file that
-- imports Midfall/Instances/. The gates are in Midfall/Instances/PlanNewKats.lean.
--
-- PORT RULES. R1 cites every def to a Rust line. R2: meta -> meta_ (Lean command modifier);
-- 'data' and 'show' cannot be binder names here, so the Rust's 'data' parameter is 'dat' and
-- the Debug renderers are 'show...Debug'; the Rust's 'identity' binding is kept where it does
-- not shadow the constructor it matches. R3 keeps iterator order: zipIdx for .enumerate(),
-- ++ for .chain(), List.lookup for HashMap::get, listNth for Vec::get. R4 as above. R5:
-- usize -> Nat, and num_sets.saturating_sub(1) at QRS:1416 is Nat.sub - truncation IS
-- saturation for a usize. R6: Vec -> List in the Generator row (plans README standing note
-- 4), and the one HashMap (QRS:454-460) is read only by get, so a List of pairs is exact and
-- its iteration order is unobservable. R9: the Field/PrimeField dictionary is FieldCtx
-- (Evaluator.lean:175-195) and frFieldCtx is its Fr p instance. R10: everything is
-- computable; nothing here is partial.

import Midfall.Common.Codec
import Midfall.Generator.Encoding
import Midfall.Generator.Layout
import Midfall.Generator.LoweringPlan
import Midfall.Generator.Quotient.Evaluator
import Midfall.Generator.Quotient.FoldCompute
import Midfall.Generator.Quotient.FoldTypes
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmTypes

set_option autoImplicit false

namespace Midfall.Generator.PlanNew

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientFold
  Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientEvaluator
  Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientBlocks
  Midfall.Generator.QuotientRecognizers
/-- A Ptr read as a byte address: the Rust's .value().as_usize() (QRS:215-216).
    Lean-side scaffolding, not a Rust item - Value carries no BEq, so every pointer
    comparison that consumes one of these values goes through this total adapter. -/
def pn (q : Ptr) : Nat := Value.asUsizeNat q.value

/-- **R9.** The Field + PrimeField dictionary of Fr p that the reference resolves
    automatically for a concrete field, spelled as the FieldCtx record Evaluator.lean:175-195
    asks for. Lean-side scaffolding - there is no Rust item - and the ten fields are exactly
    the ten methods of that record.

    'repr' is PrimeField::to_repr: the canonical value in 32 LITTLE-endian bytes
    (Common/Codec.lean:29-33, citing implementors.rs:322-324 for the wire order), which is
    what the Evaluator's fe_to_u256 path expects. 'powNat' is Field::pow over one u64 limb,
    and b ^ e IS that: Fr p = ZMod p carries a Monoid.Pow instance, and
    frFieldCtx_matchesArtifact_ok pins it against a square-and-multiply loop written out by hand
    rather than leaving the equation to be read off an instance.

    DELTA is a PARAMETER and not a literal: PrimeField::DELTA for bls12_381::Fr is
    curves/src/bls12_381/fq.rs:492 and the caller supplies it. The value is separately
    observable in the artifact (DeployedProfile.lean:154, VerifierPartials.lean:1108). -/
def frFieldCtx {p : ℕ} [Fact (Nat.Prime p)] (delta : Fr p) : FieldCtx (Fr p) :=
  { zero := 0
    one := 1
    add := fun a b => a + b
    mul := fun a b => a * b
    neg := fun a => -a
    eqF := fun a b => a == b
    isZero := fun a => a == 0
    powNat := fun b e => b ^ e
    repr := fun v => bytesToNats (frToRepr v)
    delta := delta }

/-! ## The plan-to-manifest bridge (rust: QVM:367-489): the last two methods of
    impl QuotientProgramPlan, which VmTypes.lean:865-867 records as unported. -/

/-- rust: QVM:367-380 (struct QuotientExecutionManifestEntry). "One identity after
    representation choices have been applied." Five fields in source order. -/
structure QuotientExecutionManifestEntry where
  /-- rust: QVM:370-371 (global_index: usize) - "Position in the original global y-batch." -/
  globalIndex : Nat
  /-- rust: QVM:372-373 (source: QuotientIdentitySource) - "Original source metadata." -/
  source : QuotientIdentitySource
  /-- rust: QVM:374-375 (target: QuotientTarget) - "Original fold target." -/
  target : QuotientTarget
  /-- rust: QVM:376-377 (execution: QuotientExecutionKind) - "How this identity is executed
      in the generated verifier." -/
  execution : QuotientExecutionKind
  /-- rust: QVM:378-379 (expr: QuotientExpr) - "Typed expression evaluated for this
      identity." -/
  expr : QuotientExpr
  deriving BEq

/-- The {:?} rendering of QuotientTarget (api.rs:356-367 derives Debug), so the manifest's
    mismatch message is the Rust's message. Lean-side scaffolding: this tree derives no Debug
    and a Fault carries text. -/
def showTargetDebug (t : QuotientTarget) : String :=
  match t with
  | QuotientTarget.main => "Main"
  | QuotientTarget.selector i => "Selector(" ++ toString i ++ ")"

/-- The {:?} rendering of QuotientIdentitySource (api.rs:317-353), same reason. Variant
    and field order are the Rust's declaration order, and a Rust String renders quoted; showSourceDebug_shapes_ok pins the four shapes. -/
def showSourceDebug (src : QuotientIdentitySource) : String :=
  match src with
  | QuotientIdentitySource.gate gateIndex gateName constraintIndex constraintName
      polynomialIndex =>
      "Gate { gate_index: " ++ toString gateIndex ++ ", gate_name: \"" ++ gateName ++
        "\", constraint_index: " ++ toString constraintIndex ++ ", constraint_name: \"" ++
        constraintName ++ "\", polynomial_index: " ++ toString polynomialIndex ++ " }"
  | QuotientIdentitySource.permutation identityIndex =>
      "Permutation { identity_index: " ++ toString identityIndex ++ " }"
  | QuotientIdentitySource.lookup identityIndex lookupIndex lookupName =>
      "Lookup { identity_index: " ++ toString identityIndex ++ ", lookup_index: " ++
        toString lookupIndex ++ ", lookup_name: \"" ++ lookupName ++ "\" }"
  | QuotientIdentitySource.trash trashIndex trashName =>
      "Trash { trash_index: " ++ toString trashIndex ++ ", trash_name: \"" ++ trashName ++
        "\" }"

/-- rust: QVM:476-489 (quotient_execution_entry). "Convert one planned identity plus
    chosen execution mode into the public execution manifest shape." The three fields the
    validator compares are COPIED out of the identity, which is the point: the manifest is
    the identity stream with an execution mode spliced in, and nothing here may re-derive
    them. -/
def quotientExecutionEntry (identity : QuotientIdentity) (execution : QuotientExecutionKind) :
    QuotientExecutionManifestEntry :=
  { globalIndex := identity.meta_.globalIndex
    source := identity.meta_.source
    target := identity.target
    execution := execution
    expr := identity.expr }
/-- rust: QVM:382-439 (QuotientProgramPlan::execution_manifest). "Reconstruct the
    generated execution stream back into per-identity folds."

    R3 order: inline prefix, then the item stream, then the structured tail - the three push
    and extend sites in the Rust's order. A NativePermutation marker EXPANDS to the whole
    permutation range and a NativeLookup to the whole lookup range, which is why either is an
    Err when its range is empty (QVM:404-408, :414-416): an empty range would silently delete
    identities from the stream the validator is about to check. NativeIdentity(n) indexes
    native_identities with .get() + ok_or_else (QVM:421-424), so an out-of-range marker is an
    Err and not a panic - List.getD? is that bounds check.

    The Vec accumulator becomes a List threaded through foldlM; the Rust pushes in order and
    so does this, so the list that comes out is the same list. -/
def executionManifest (self : QuotientProgramPlan) :
    Except String (List QuotientExecutionManifestEntry) :=
  let step (out : List QuotientExecutionManifestEntry) :
      QuotientProgramItem -> Except String (List QuotientExecutionManifestEntry)
    | QuotientProgramItem.identity identity =>
        .ok (out ++ [quotientExecutionEntry identity QuotientExecutionKind.interpreted])
    | QuotientProgramItem.nativePermutation =>
        if self.nativePermutationIdentities.isEmpty then
          .error "native permutation marker has empty identity range"
        else
          .ok (out ++ self.nativePermutationIdentities.map
            (fun identity =>
              quotientExecutionEntry identity QuotientExecutionKind.nativePermutation))
    | QuotientProgramItem.nativeLookup =>
        if self.nativeLookupIdentities.isEmpty then
          .error "native lookup marker has empty identity range"
        else
          .ok (out ++ self.nativeLookupIdentities.map
            (fun identity =>
              quotientExecutionEntry identity QuotientExecutionKind.nativeLookup))
    | QuotientProgramItem.nativeIdentity nativeIndex =>
        match listNth self.nativeIdentities nativeIndex with
        | none => .error ("native identity marker " ++ toString nativeIndex ++
            " has no callback body")
        | some identity =>
            .ok (out ++ [quotientExecutionEntry identity
              (QuotientExecutionKind.nativeIdentity nativeIndex)])
  let inline := self.inlineIdentities.map
    (fun identity => quotientExecutionEntry identity QuotientExecutionKind.inline)
  self.items.foldlM step inline >>= fun out =>
    .ok (out ++ self.structuredTailIdentities.map
      (fun identity => quotientExecutionEntry identity QuotientExecutionKind.structuredTail))

/-- rust: QVM:441-473 (QuotientProgramPlan::validate_execution_manifest). "Check that
    representation choices preserve the original identity stream."

    Two checks in the Rust's order: the length, then a position-by-position comparison of
    global_index, source and target - and ONLY those three. The execution kind and the
    expression travel with the entry and are NOT compared, which is what makes this a
    stream-preservation check and not an equality check, and what lets a native marker stand
    in for the identities it replaces. Both format! payloads are ported verbatim: this is an
    Err and not a panic, so the text survives (header). -/
def validateExecutionManifest (self : QuotientProgramPlan)
    (expected : List QuotientIdentity) : Except String Unit := do
  let manifest <- executionManifest self
  if manifest.length != expected.length then
    .error ("quotient execution manifest length mismatch: got " ++ toString manifest.length ++
      ", expected " ++ toString expected.length)
  else
    (manifest.zip expected).zipIdx.forM fun ((actual, expect), pos) =>
      if actual.globalIndex != expect.meta_.globalIndex || actual.source != expect.meta_.source
          || actual.target != expect.target then
        .error ("quotient execution manifest mismatch at position " ++ toString pos ++
          ": got index " ++ toString actual.globalIndex ++ ", source " ++
          showSourceDebug actual.source ++ ", target " ++ showTargetDebug actual.target ++
          "; expected index " ++ toString expect.meta_.globalIndex ++ ", source " ++
          showSourceDebug expect.meta_.source ++ ", target " ++ showTargetDebug expect.target)
      else .ok ()

/-! ## The bytecode lowering (rust: QRS:971-974, :2101-2146) -/

/-- rust: QRS:971-974 (quotient_identity_expr). "Return the typed quotient expression."
    A one-line accessor, identity.expr.clone(). Ported because R1 asks for one Lean def per
    Rust fn including private helpers, and because the card's guidance names it: the builder
    must read identity.expr and NOT re-parse identity.lines - the two are tied at
    construction time by the assert_eq! at QRS:827-831, and re-parsing here would silently
    re-open that gap. -/
def quotientIdentityExpr (identity : QuotientIdentity) : QuotientExpr := identity.expr

/-- rust: QRS:2114-2146 (build_quotient_program_items_with_limb_ops). "Lower the same item
    stream under an explicit limb-opcode policy."

    The Rust builder methods mutate &mut self and PANIC on a broken invariant - identity_expr
    ends with assert_eq!(self.stack_depth, 0, "quotient VM stack leak") at QVM:1134 - while
    the Lean builder is a value threaded through foldlM and those panics are the Except
    QVMFault the builder already returns (VmBuilder.lean:131). The loop is therefore a foldlM
    that short-circuits at the first fault, which is the same left-to-right abort the Rust
    has, and liftQVM carries the site string across.

    limb_vm_ops is the ONLY difference between this and the rendering path, and it is a
    policy and not a knob the template varies: QRS:2116-2119 says "Rendering always uses the
    crate default. The false build exists so the generator can cross-check the limb
    superinstructions against a program that uses only generic Fr opcodes" - that cross-check
    is certify_quotient_builds_agree, which OBJ.7's dual-build certification feeds by calling
    this def with false. -/
def buildQuotientProgramItemsWithLimbOps (items : List QuotientProgramItem)
    (selectorFold : SelectorFoldPlan) (limbVmOps : Bool) : Except Fault QuotientProgramBuild :=
  liftQVM do
    let s <- items.foldlM (fun s item =>
      match item with
      | QuotientProgramItem.identity identity =>
          identityExpr shapeRecognizers s (quotientIdentityExpr identity) identity.target
            (selectorFold.gapFor identity)
      | QuotientProgramItem.nativePermutation => nativePermutation s
      | QuotientProgramItem.nativeLookup => nativeLookup s
      | QuotientProgramItem.nativeIdentity n => nativeIdentity s n) (withLimbVmOps limbVmOps)
    finish s

/-- rust: QRS:2101-2112 (build_quotient_program_items). "Lower a logical quotient item
    stream into compact VM bytecode." The wrapper that supplies the crate default
    (DEFAULT_QUOTIENT_LIMB_VM_OPS, VmBuilder.lean:213, true) - the path the rendering and
    compact_quotient_program_for both take. -/
def buildQuotientProgramItems (items : List QuotientProgramItem)
    (selectorFold : SelectorFoldPlan) : Except Fault QuotientProgramBuild :=
  buildQuotientProgramItemsWithLimbOps items selectorFold defaultQuotientLimbVmOps
/-! ## quotient_program_plan (rust: QRS:425-526) -/

/-- rust: QRS:425-526 (quotient_program_plan). "Choose inline, VM, and native-callback
    representation for identities." THE ITEM the constructors were said to be blocked on.

    R3, the four iterator sites:
    * native_identities (QRS:448-453) is remaining_gates.iter().enumerate().filter(..) -
      enumerate BEFORE filter, so the survivors keep their GATE index; zipIdx then filter is
      exactly that.
    * native_index_by_gate (QRS:454-460) enumerates the filtered list a SECOND time, which is
      what turns a gate index into a native-callback index: (gate_idx, native_idx). The
      HashMap is a List (Nat × Nat) read only by get (R6, header).
    * gate_items (QRS:462-468) maps over the unfiltered enumerate again, so a gate that was
      not selected keeps its identity and a selected one becomes NativeIdentity(native_index).
    * the four chains (QRS:489-493) are the four ++s below, in order.

    The three flags are read off meta and not off the parts (QRS:444-446):
    num_permutation_zs > 0, num_lookups > 0, num_trashcans > 0. structured_trash_tail is
    INVERTED in the item stream (QRS:479-488): when the tail is structured the trash identities
    get no VM item at all and travel in structured_tail_identities instead.

    QRS:523-524 is the abort: the plan is validated against the identity stream it was built
    from and .expects, so a plan that loses or reorders an identity is a panic and not a
    silent shortening. Site QRS:524, and siteQ keeps the message (header). -/
def quotientProgramPlan {F : Type} [BEq F] (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (dat : Data) : Except Fault QuotientProgramPlan := do
  let parts <- quotientIdentityParts field cs meta_ dat
  let allIdentities := parts.allIdentities
  let selectorFold <- liftQVM (selectorFoldPlan allIdentities parts.sortedSimple.length)
  let inlineCount := min parts.gates.length defaultHybridQuotientInlineIdentities
  let inlineIdentities := parts.gates.take inlineCount
  let remaining := parts.gates.drop inlineCount
  let nativeIdx <- liftQVM (nativeGateIndices remaining)
  let nativePermutation := meta_.numPermutationZs > 0
  let nativeLookup := meta_.numLookups > 0
  let structuredTrashTail := meta_.numTrashcans > 0
  -- QRS:448-453: enumerate, then filter on the index.
  let selected := remaining.zipIdx.filter (fun q => nativeIdx.contains q.2)
  -- QRS:454-460: enumerate the survivors a second time to get the callback index.
  let nativeIndexByGate : List (Nat × Nat) := selected.zipIdx.map (fun q => (q.1.2, q.2))
  -- QRS:462-468
  let gateItems := remaining.zipIdx.map fun q =>
    match nativeIndexByGate.lookup q.2 with
    | some n => QuotientProgramItem.nativeIdentity n
    | none => QuotientProgramItem.identity q.1
  -- QRS:469-488
  let permItems := if nativePermutation then [QuotientProgramItem.nativePermutation]
    else parts.permutation.map QuotientProgramItem.identity
  let lookupItems := if nativeLookup then [QuotientProgramItem.nativeLookup]
    else parts.lookup.map QuotientProgramItem.identity
  let trashItems := if structuredTrashTail then []
    else parts.trash.map QuotientProgramItem.identity
  let plan : QuotientProgramPlan :=
    { inlineIdentities := inlineIdentities
      items := gateItems ++ permItems ++ lookupItems ++ trashItems
      nativeIdentities := selected.map (fun q => q.1)
      nativePermutationIdentities := if nativePermutation then parts.permutation else []
      nativeLookupIdentities := if nativeLookup then parts.lookup else []
      structuredTailIdentities := if structuredTrashTail then parts.trash else []
      sortedSimple := parts.sortedSimple
      hasNativePermutation := nativePermutation
      hasNativeLookup := nativeLookup
      selectorFold := selectorFold }
  -- QRS:523-524: the plan must preserve the stream it was built from.
  match validateExecutionManifest plan allIdentities with
  | .error _ => panicF (siteQ 524 "quotient execution plan must preserve the identity stream")
  | .ok () => pure plan

/-! ## compact_quotient_program_for (rust: QRS:165-181) -/

/-- rust: QRS:165-181 (compact_quotient_program_for). "Build the compact quotient VM artifact
    for a metadata/data snapshot."

    Four statements, and the third is the one a reviewer stops on: let _quotient_max_stack =
    build.max_stack; binds and DROPS the high-water mark. It is not dead by accident - the doc
    comment says the output "must be deterministic for a fixed VK base and proof shape", and
    the binding is where the caller's own stack budget used to be read before the reservation
    moved into quotient_stack_words_for_build (QRS:314-322). The port keeps the pair and drops
    nothing, so the value reaches the caller instead of a wildcard. sorted_simple is CLONED out
    of the plan before the build (QRS:175) and is the second component; the build never touches
    it. -/
def compactQuotientProgramFor {F : Type} [BEq F] (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (dat : Data) :
    Except Fault (QuotientProgramBuild × List Nat) := do
  let plan <- quotientProgramPlan field cs meta_ dat
  let build <- buildQuotientProgramItems plan.items plan.selectorFold
  pure (build, plan.sortedSimple)

/-! ## The native-callback scratch table (rust: QRS:1401-1464) -/

/-- rust: QRS:1401-1417 (structured_permutation_scratch_words). "Scratch table width used by
    the native permutation callback."

    The early return 0 on num_permutation_zs == 0 is kept as an early return (R3). The
    arithmetic is (2 * num_cols) + (2 * num_sets) + num_sets.saturating_sub(1) + 1:
    permutation values, sigma values, z_cur and z_next for every set, z_last for every
    NON-FINAL set, and one spill slot for the running delta base - the four comments at
    QRS:1413-1415 are the derivation of the four terms and the reason the third saturates.
    R5: usize::saturating_sub and Nat.sub agree. -/
def structuredPermutationScratchWords (meta_ : ConstraintSystemMeta) : Nat :=
  if meta_.numPermutationZs == 0 then 0
  else
    let numCols := meta_.permutationColumns.length
    let numSets := meta_.numPermutationZs
    (2 * numCols) + (2 * numSets) + (numSets - 1) + 1

/-- rust: QRS:1441-1445 (structured_lookup_scratch_words). "Scratch table width used by the
    native lookup callback." One line: structured_lookup_max_parallel(meta) * 3, because the
    callback stages f + beta values plus a prefix and a suffix product.

    structured_lookup_max_parallel (QRS:1419-1439) is ALREADY ported as
    structuredLookupMaxParallel (QuotientBlocks.lean:492-501), and it is a method on the
    evaluator state because it walks self.vk.cs().lookups() and needs cs.degree(). The
    .unwrap_or(1) at QRS:1438 is getD 1 there - a system whose every lookup has zero chunks
    yields 1 and not 0, which that port's own docstring flags. The max is a PARAMETER here
    because the caller has to run the evaluator to get it (see nativeCallbackScratchWords);
    the def is the *3 and nothing else, which is what the Rust's body is. -/
def structuredLookupScratchWords (maxParallel : Nat) : Nat := maxParallel * 3

/-- rust: QRS:1447-1464 (native_callback_scratch_words). "Largest scratch table needed by any
    enabled native VM callback."

    Two ifs on the PLAN's flags and a max. Each table is computed only when its callback is
    enabled - the Rust's if plan.has_native_permutation { ... } else { 0 } - so the lookup walk
    over the constraint system does not run at all when has_native_lookup is false.
    structured_permutation_scratch_words is an associated fn (QRS:1402, Self::) and needs no
    evaluator; structured_lookup_scratch_words is a method (QRS:1442, self.) and needs the
    circuit, so the port runs the existing structuredLookupMaxParallel on a FRESH
    Evaluator.new field cs meta_ dat - the same state the Rust's self.vk.cs() supplies, and
    the same construction quotientIdentityParts makes internally (QuotientBlocks.lean:979).

    This is the number that feeds quotient_stack_words_for_build, i.e. the reason the
    registered stack region is max build.max_stack native_words and not build.max_stack. -/
def nativeCallbackScratchWords {F : Type} [BEq F] (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (dat : Data) (plan : QuotientProgramPlan) :
    Except Fault Nat := do
  let permWords :=
    if plan.hasNativePermutation then structuredPermutationScratchWords meta_ else 0
  let lookupWords <-
    if plan.hasNativeLookup then
      do
        let (maxParallel, _) <- (structuredLookupMaxParallel (F := F) meta_).run
          (Evaluator.new field cs meta_ dat)
        pure (structuredLookupScratchWords maxParallel)
    else pure 0
  pure (max permWords lookupWords)

/-- rust: QRS:312-322 (quotient_stack_words_for_build). "Return stack/scratch words needed by
    interpreted VM and native callbacks." One max, and the comment is the finding:
    build.max_stack "only describes the interpreted operand stack", while native callbacks
    SHARE quotient_stack_mptr as their scratch base, so the registered region must cover both
    users. A port that returned build.max_stack would build a layout whose stack region is too
    small for the permutation table - and the layout assert at QRS:246-250 is downstream of the
    number, not a check on it. -/
def quotientStackWordsForBuild (build : QuotientProgramBuild)
    (nativeCallbackScratchWords : Nat) : Nat :=
  max build.maxStack nativeCallbackScratchWords

/-! ## The template handoff (rust: QRS:183-238) and its two usage tables -/

/-- The Rust's closure let has = |op| used_ops.contains(&op) (QRS:260, :298), over a Vec<u8>.
    Lean Bytes is a ByteArray, so the check goes through the byte list. Scaffolding, not a
    Rust item of its own - it is the body of the two defs below. -/
def usedHas (bs : Bytes) (op : Nat) : Bool := (bytesToNats bs).contains op

/-- rust: QRS:258-294 (quotient_opcode_usage). "Convert finalized bytecode usage into
    template switch-arm flags." Thirty-one has(Q_OP_*) fields in declaration order - the
    record has thirty-one and the Rust sets thirty-one, and quotientOpcodeUsage_table_ok
    counts them so a field added to either side reddens. The opcode constants are the tree's
    own (VmTypes.lean), so nothing here re-derives a number. -/
def quotientOpcodeUsage (u : Bytes) : QuotientVmOpcodeUsage :=
  { pushConst := usedHas u qOpPushConst
    pushMemLiteral := usedHas u qOpPushMemLiteral
    pushMemToken := usedHas u qOpPushMemToken
    pushMemTokenOffset := usedHas u qOpPushMemTokenOffset
    pushMemU16 := usedHas u qOpPushMemU16
    add := usedHas u qOpAdd
    mul := usedHas u qOpMul
    neg := usedHas u qOpNeg
    pushConstU8 := usedHas u qOpPushConstU8
    foldMain := usedHas u qOpFoldMain
    foldSelector := usedHas u qOpFoldSelector
    addConstU8 := usedHas u qOpAddConstU8
    mulConstU8 := usedHas u qOpMulConstU8
    addConst := usedHas u qOpAddConst
    mulConst := usedHas u qOpMulConst
    addMemU16 := usedHas u qOpAddMemU16
    mulMemU16 := usedHas u qOpMulMemU16
    addMulMemMemConstU8 := usedHas u qOpAddMulMemMemConstU8
    addMulConstU8MemU16 := usedHas u qOpAddMulConstU8MemU16
    addMulMemMem := usedHas u qOpAddMulMemMem
    runAddMulMemMemConstU8 := usedHas u qOpRunAddMulMemMemConstU8
    runAddMulConstU8MemU16 := usedHas u qOpRunAddMulConstU8MemU16
    affineSum := usedHas u qOpAffineSum
    nativePermutation := usedHas u qOpNativePermutation
    nativeLookup := usedHas u qOpNativeLookup
    nativeIdentity := usedHas u qOpNativeIdentity
    lin7 := usedHas u qOpLin7
    bilin7Row := usedHas u qOpBilin7Row
    bilin7Pairwise := usedHas u qOpBilin7Pairwise
    modarith7 := usedHas u qOpModarith7
    pow5 := usedHas u qOpPow5 }

/-- rust: QRS:296-310 (quotient_mem_usage). "Convert finalized memory-token usage into
    template switch-arm flags." Nine fields, same has helper, same declaration order. -/
def quotientMemUsage (u : Bytes) : QuotientVmMemUsage :=
  { l0 := usedHas u qMemL0
    lLast := usedHas u qMemLLast
    lBlind := usedHas u qMemLBlind
    beta := usedHas u qMemBeta
    gamma := usedHas u qMemGamma
    x := usedHas u qMemX
    theta := usedHas u qMemTheta
    trashChallenge := usedHas u qMemTrashChallenge
    instanceEval := usedHas u qMemInstanceEval }
/-- rust: QRS:183-238 (quotient_template_program). "Convert a finalized VM build into the
    template's VK-backed program model." The doc comment calls it "the single handoff point
    between the quotient bytecode compiler, VK payload reservation, and the generated Yul
    interpreter", and says the bounds checks live here so the standalone evaluator and the
    in-verifier VM paths cannot drift - which is why all four aborts are in this one function,
    and why the KAT that matters is the one that runs it on the DEPLOYED payload.

    The four aborts, with the line each fires on (header): QRS:202, :204, :205, :209. The two
    reservations are read off the VK and the two lengths off the build, and the comparison is
    <= on both sides: a const table that exactly fills the reservation is fine.

    Twelve fields, in the Rust's literal order (QRS:222-235). 'len' is build.bytes.len() -
    the BYTE length before word padding and not the chunk count, while the reservation the
    program is checked against is in CHUNKS, so the two numbers differ (88 bytes, 3 words at
    the fixture) and a port that wrote chunks.length here would still pass a length check
    against the wrong field. const_mptr and program_mptr are
    (vk_mptr + offset).value().as_usize(), i.e. pointer arithmetic through Ptr.add and not a
    Nat add - the location must survive (Encoding.lean:270-276 is the whole reason). guards
    come from quotient_vm_guards (QRS:242-256, already ported at LoweringPlan.lean:368), and
    the triple this returns is what plan.rs:296-300 destructures into the plan's program,
    stack_mptr and state_slots. -/
def quotientTemplateProgram (build : QuotientProgramBuild) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (memory : VerifierMemoryLayout) (selectorFold : SelectorFoldPlan)
    (opModel : QuotientValidator.QuotientOperandModel) :
    Except Fault (QuotientProgram × Nat × QuotientStateSlots) := do
  let chunks := PackedProgramCodec.encodeWords build.bytes
  let constOff <- match vk.quotientConstOffsetWords with
    | some o => pure o
    | none => throw (Fault.panic (siteQ 202 "VK must carry quotient constants"))
  let progOff <- match vk.quotientProgramOffsetWords with
    | some o => pure o
    | none => throw (Fault.panic (siteQ 204 "VK must carry quotient program"))
  unless build.consts.length ≤ vk.quotientConstWords do
    throw (Fault.panic (siteQ 205 "quotient const table exceeded VK payload reservation"))
  unless chunks.length ≤ vk.quotientProgramWords do
    throw (Fault.panic (siteQ 209 "quotient program length exceeded VK payload reservation"))
  let stateSlots := QuotientStateSlots.new memory.quotientTmpMptr
  let guards <- quotientVmGuards opModel memory
  pure ({ len := build.bytes.size
          opUsage := quotientOpcodeUsage build.usedOps
          memUsage := quotientMemUsage build.usedMemTokens
          constMptr := pn (vkMptr.add constOff)
          evalNumerMptr := stateSlots.evalNumerMptr
          traceIdMptr := stateSlots.traceIdMptr
          selectorPowerMptr := stateSlots.selectorPowerMptr
          selectorMaxPower := selectorFold.maxPower
          selectorTailUpdates := selectorTailUpdates selectorFold
          stackMptr := memory.quotientStackMptr
          programMptr := pn (vkMptr.add progOff)
          guards := guards },
        memory.quotientStackMptr, stateSlots)

end Midfall.Generator.PlanNew
