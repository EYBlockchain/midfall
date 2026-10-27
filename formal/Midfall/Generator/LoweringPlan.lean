-- |
-- Midfall.Generator.LoweringPlan
--
-- THE CONVERGED LOWERING PLAN: the one value that holds the finalized VK payload,
-- proof layout, memory layout and quotient-program facts a single verifier render
-- and proof repacking both consume. Ported from
-- proofs/solidity-verifier/src/lowering/plan.rs (643 lines at HEAD, cited below as
-- PL), with the two `quotient_direct.rs` records the brief carves out (QDIR) and the
-- `mod.rs` row (MOD). Work package P-11.
--
-- WHY THIS FILE MATTERS. PLAN 9.5's `Supported` record and D-P20's per-stream fold
-- statement both quantify over `L.plan` and `L.plan.qprog`, and neither name had a
-- denotation before this file: `QuotientOperandModel` (VmValidator.lean:496) existed but
-- nothing in the tree could BUILD one from a converged plan, so `Supported.qvm` stood for
-- an unconstructible predicate. PL:626-643 (`quotient_operand_model`) is that builder; it
-- is ported here and the bridge is gated end to end
-- (`supportedQvm_bridgeAcceptsTheBuiltProgram_ok`).
--
-- CORRECTIONS TO THE BRIEF (plans/P-11-lowering-plan.md).
-- 1. The brief names `lowering/mod.rs` (51) as in scope and asks for reconciliation with
--    Vk.lean. There is nothing to reconcile: MOD:37-45 (`VerifierBuildInputs`) is ALREADY
--    ported at Vk.lean:359-377 and this file imports it (hazard 1). The rest of mod.rs is
--    15 `pub(crate) mod` declarations, two `use` lines, a test re-export (MOD:47-48) and
--    `#[cfg(test)] mod tests` (MOD:50-51): nothing portable. mod.rs contributes ZERO new
--    Lean items.
-- 2. The carve-out says port BOTH `DirectQuotientPlanned` (QDIR:35) and
--    `DirectQuotientRendering` (QDIR:57). `DirectQuotientRendering` was already ported by
--    P-04 at Models.lean:697 (its cite is QDIR:56-65, the same record). Only
--    `DirectQuotientPlanned` is new; re-declaring the rendering record would be a duplicate
--    name in `Midfall.Generator`.
-- 3. The brief lists `lowering/config.rs` (27) as in scope. All three of its items are
--    ALREADY ported, by other packages, in three different namespaces:
--    `defaultQuotientLimbVmOps` (VmBuilder.lean:213), `defaultQuotientNativeGates`
--    (FoldCompute.lean:745) and `defaultHybridQuotientInlineIdentities`
--    (FoldCompute.lean:748). Nothing is re-declared; `configConstants_matchConfigRs_ok`
--    gates the three values against config.rs instead. The split is itself a finding: one
--    Rust file's three constants now live in three Lean modules, so no single file is where a
--    reviewer looks for the pinned defaults.
-- 4. Hazard 2 asked whether P-10's field-by-field pin of `QuotientComputationBlocks::default()`
--    is actually used here. It is, twice: PL:79-81 routes BOTH the External and the Direct arm
--    through `default().helper_flags()`, and PL:98 and PL:105 route the same two arms through
--    `default()` again inside `into_template_parts`. Two gates pin it.
-- 5. Hazard 6 (do not pull in the Evaluator or `direct/emit.rs`) is honoured, but the
--    survey's blocked list mis-files items it puts under "the evaluator frame builders"
--    (P-SE-evidence/survey.md:2085): `quotient_vm_guards` (QRS:242-256) and
--    `quotient_external_frame` / `quotient_external_frame_from_bounds` (QRS:760-794) are
--    small pure functions over records this tree already has. They are NOT blocked on the
--    Evaluator. plan.rs needs all three, so they are ported here with their QRS cites and the
--    mis-filing is reported. What IS genuinely blocked and is therefore NOT ported:
--    `compact_quotient_computation_blocks` (QRS:2000, renders Yul through the Evaluator) and
--    everything in `direct/` (M10).
--
-- NOT PORTED, WITH THE BLOCKER NAMED (hazard 6; context for required finding (b)).
-- * PL:124-137 `lowering_plan` / `lowering_plan_for`, PL:235-329 `LoweringPlan::new` and
--   PL:165-231 `LoweringPlan::new_direct`. These are the CONSTRUCTORS: they run the whole
--   pipeline. Three blockers, all already named in the tree:
--   `VerifierMemoryLayout::new` (MEM:591-973) is declined by Layout.lean:716-721 and exists
--   only as the `VkBuildEnv.newVerifierMemoryLayout` stub (Vk.lean:405-421 - and the plans
--   README already rules that `memoryLayoutFor_config_ok` tests the stub, not the real
--   constructor); `quotient_program_plan` (QRS:426) and `build_quotient_program_items`
--   (QRS:2102) are unported (survey:2083-2084); and the direct row
--   (`direct_quotient_program`, `plan_direct_quotient`, `direct_scratch_requirements`) is
--   deferred to M10. Porting `new` on top of the stub would produce a plan whose `memory`
--   field is a stub artifact - the exact vacuity class the P-SE attack pass is about. So the
--   record, the accessors and the validators are ported; the pipeline is not, and no gate
--   pretends otherwise.
-- * PL:151-154 `vm_quotient_mut`: a `&mut self` test accessor with no Lean analogue (its
--   only Rust callers corrupt a finalized program before re-rendering it).
-- * PL:392-406 `compact_quotient_blocks`: needs QRS:2000 (above). It is the one hole in
--   `quotient_rendering`, which is ported with that emitter passed in as an argument - the
--   `VkBuildEnv` pattern (Vk.lean:398-421) spelled for a single callee.
--
-- DEVIATIONS AND HAZARD NOTES.
-- * R2: `meta` is a Lean command modifier, so the field is `meta_` (the convention
--   Vk.lean:357 and VmTypes.lean:662 set).
-- * R6: `Vec` -> `List` in the Generator row (plans README standing note 4).
-- * R4, hazard 5, and P-04 finding F2. Every panic site below becomes a `Fault.panic` whose
--   ONLY content is the path:line, because `Fault` carries no payload (Exec/Error.lean:56).
--   The Rust messages that are therefore LOST are:
--   PL:146 "compact quotient VM plan (QuotientLowering::Vm)",
--   PL:153 (same text, test-only accessor, not ported),
--   PL:230 and PL:310 "generator invariant violation: {err}",
--   PL:326 "quotient dual-build certification failed: {err}" (all three inside the unported
--   constructors), PL:558 "accumulator encoding validated by GeneratorConfig", and
--   QRS:249 "quotient VM stack guard and operand model disagree on the stack region".
--   `panicSites_areTheRecordedOnes_ok` reads plan.rs at #eval time and pins the set of sites
--   and the lost strings (D-P19). The `format!` payloads of `Err` are NOT lost -
--   `validate_generator_invariants` returns `Result<(), String>` and all sixteen messages
--   are ported verbatim.
-- * R5: PL:640 `(memory.quotient_stack_hi - memory.quotient_stack_mptr) / WORD_BYTES` is a
--   `usize` subtraction that WRAPS in the release profile when hi < mptr, then divides; `Nat`
--   truncates at 0 instead, so the port reports 0 where the reference would report about 2^59.
--   The layout always plans hi above mptr, and WORD_BYTES is 32 so the division is never by
--   zero. Recorded at the site and pinned by `quotientOperandModel_stackWords_ok`.
-- * PL:577 and PL:613 read TWO DIFFERENT `theta` pointers: the `challenge_and_common_slots`
--   window starts at `data.theta_mptr` while the `Q_MEM_THETA ` token base is
--   `memory.theta_mptr`. That is what the reference does and it is easy to "fix" by accident;
--   `quotientReadModel_twoThetas_ok` pins it.
-- * `DirectQuotientPlanned`'s `program` and `layout` fields name types from the deferred M10
--   row (`DirectQuotientProgram`, `DirectLayout`), so the record is parameterised over them -
--   the precedent is `VerifierCodegenLayout (Proof : Type)` at Models.lean:708, declined for the
--   same reason. `LoweringPlan` carries the two parameters through because its `direct` field
--   names the record.
-- * Hazard 1, Vk.lean's projection. `VkQuotientBuild` (Vk.lean:386-388) is the two-field view of
--   `QuotientProgramBuild` that vk.rs reads, and its own doc says it "should become an alias of
--   [the full record] when it lands". P-09a made the full record land (VmTypes.lean:636) and said
--   so at VmTypes.lean:630-635; this file is the second consumer to confirm it: `PlannedQuotient.build`
--   is the FULL record, so `VkQuotientBuild` is now a strict projection of a type that exists
--   rather than a stand-in for one that does not. Vk.lean is NOT edited (hazard 1); the alias is
--   queued in plans README.
-- * D-P16, D-P18, D-P19 are honoured: `accEncoding` is the Generator's `AccumulatorEncoding
--   (Api.lean:413, the faithful one, not the Exec stand-in), the layout gate is
--   `validate = .ok ()` (the `WellFormed` half is a P-SE obligation that does not exist
--   yet), and every artifact gate reads the .rs at #eval time.
-- * HAZARD 1, answered with a deliberate deviation. `VerifierBuildInputs` (MOD:37-45) is NOT
--   re-declared here - it is Vk.lean:359's, and this file imports nothing from Vk at all. The only
--   plan.rs item that touches it is `acc_msm_terms` (PL:552-562), and that body reads exactly
--   two of its fields, so the port takes those two as arguments instead of a receiver (see the
--   def). The reason is D-P17: Vk.lean:289 imports `Instances.ExponentModel`, the P-SE constraint
--   list says "no theorem file imports `Generator.Vk`", and P-SE section M states Surface.lean
--   "never imports `Generator.Vk`". This module is the thing Surface.lean must import to get
--   `Supported.qvm`, so importing Vk here would have poisoned the exact downstream files this
--   package exists to unblock. If the reviewer prefers the literal receiver form the change is
--   two lines plus the import - and the P-SE statement surface then cannot import this file from
--   a theorem-bearing module.
-- * D-P17 consequence, stated plainly: this file imports no `Instances/*` and states no theorem,
--   so it is safe for theorem files to import. That is a property of the import list, not of the
--   `Prop` definitions here: `supportedQvm` is stated as `supportedQvmBool = true`, so a downstream
--   theorem file can discharge it by computation or `decide` without this file gaining an axiom.

import Midfall.Common.Bytes
import Midfall.Generator.Models
import Midfall.Generator.Encoding
import Midfall.Generator.Abi
import Midfall.Generator.Layout
import Midfall.Generator.Api
import Midfall.Generator.Kzg
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmValidator
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldTypes
import Midfall.Generator.Quotient.FoldCompute

namespace Midfall.Generator

open Midfall.Generator.QuotientFold
open Midfall.Generator.QuotientValidator

/-! ## The records (rust: PL:27-119, QDIR:33-53) -/

/-- rust: QDIR:33-53 (`struct DirectQuotientPlanned`) @formal-baseline. "Direct quotient
    program bound to the converged verifier memory, validated against the source trees,
    rendered and fold-checked." Seven fields in the Rust's order.

    `program` (QDIR:36) and `layout` (QDIR:39) are the deferred M10 types
    `DirectQuotientProgram` and `DirectLayout`, so they are parameters (header). The three
    `#[cfg_attr(not(test), allow(dead_code))]` fields (`layout`, `selector_acc_mptr`,
    `folds`) are kept: dead in the shipped build, read by the plan tests, and the record is one
    type rather than a per-consumer projection. `table` is `Vec<U256>` -> `List Word256`.
    The Rust derives Clone + Debug (QDIR:34), not Eq, so nothing is derived here. -/
structure DirectQuotientPlanned (Program Layout : Type) where
  /-- QDIR:36: program: DirectQuotientProgram - the memory-independent direct program. -/
  program : Program
  /-- QDIR:39: layout: DirectLayout - the bound direct memory layout. -/
  layout : Layout
  /-- QDIR:41: table: Vec<U256> - "VK constant table words, as deployed." Read by PL:444 and
      PL:452, i.e. by the invariant checker below. -/
  table : List Word256
  /-- QDIR:45: selector_acc_mptr: usize - "`SELECTOR_ACC_MPTR` of the verifier memory (bucket `s` is read by the PCS at `+ 32 s`)." -/
  selectorAccMptr : Nat
  /-- QDIR:47: rendering: DirectQuotientRendering - "Production render (fold-checked)." Already
      ported at Models.lean:697; imported, not duplicated. -/
  rendering : DirectQuotientRendering
  /-- QDIR:49: trace_rendering: DirectQuotientRendering - "Trace render (fold-checked)." -/
  traceRendering : DirectQuotientRendering
  /-- QDIR:52: folds: FoldRecord - "Fold sites and section calls of the production render."
      FoldRecord is P-10a's (FoldTypes.lean:280). -/
  folds : FoldRecord

/-- rust: PL:49-55 (`struct PlannedQuotient`) @formal-baseline. "Quotient VM and rendering
    metadata tied to the finalized memory layout." The Rust derives Clone + Debug;
    `QuotientProgram` (Models.lean:666) and `QuotientStateSlots` (FoldTypes.lean:614) carry
    no BEq either, so nothing is derived. -/
structure PlannedQuotient where
  /-- PL:50: plan: QuotientProgramPlan - the identity stream and fold schedule. -/
  plan : QuotientProgramPlan
  /-- PL:51: build: QuotientProgramBuild - the emitted bytecode, constants and usage. THE FULL
      record, not Vk.lean:386's two-field view (header, hazard 1). -/
  build : QuotientProgramBuild
  /-- PL:52: program: QuotientProgram - the template's VK-backed model of the same program
      (QRS:189-238 builds it; that builder is not ported, so this is a field a caller must
      supply). -/
  program : QuotientProgram
  /-- PL:53: stack_mptr: usize - operand-stack base the program was bound to. -/
  stackMptr : Nat
  /-- PL:54: state_slots: QuotientStateSlots - the three persistent y-batch words. -/
  stateSlots : QuotientStateSlots

/-- rust: PL:29-45 (`struct LoweringPlan`) @formal-baseline. "Finalized, reusable codegen
    facts for one verifier render/repack operation." Eleven fields in the Rust's order. The Rust
    derives Debug only (PL:28), so there is no BEq here either: the gates compare fields, never
    whole plans.

    INVARIANT the reference enforces at PL:434-437 and PL:461: exactly one of `quotient` and
    Btdirect` is `some`, and which one is decided by `lowering`. Nothing here enforces it by
    type - the Rust does not either, which is why `vmQuotient` can panic. -/
structure LoweringPlan (Program Layout : Type) where
  /-- PL:30: vk: Halo2VerifyingKey - the finalized payload model. -/
  vk : Halo2VerifyingKey
  /-- PL:31: vk_mptr: Ptr - where that payload lives in verifier memory. -/
  vkMptr : Ptr
  /-- PL:32: meta: ConstraintSystemMeta - R2: `meta_`. -/
  meta_ : ConstraintSystemMeta
  /-- PL:33: data: Data - the working-memory handles. -/
  data : Data
  /-- PL:34: proof_layout: ProofCalldataLayout -/
  proofLayout : ProofCalldataLayout
  /-- PL:36: lowering: QuotientLowering - "Quotient numerator lowering this plan was built
      for." Api.lean:886. -/
  lowering : QuotientLowering
  /-- PL:38: sorted_simple: Vec<usize> - "Sorted simple-selector fixed columns (selector bucket
      order)." Read by PL:387 to size the external frame's output. -/
  sortedSimple : List Nat
  /-- PL:40: quotient: Option<PlannedQuotient> - "Compact VM quotient plan
      (`QuotientLowering::Vm`)." -/
  quotient : Option PlannedQuotient
  /-- PL:42: direct: Option<DirectQuotientPlanned> - "Direct quotient plan
      (`QuotientLowering::Direct`)." -/
  direct : Option (DirectQuotientPlanned Program Layout)
  /-- PL:43: pcs_memory_requirements: PcsMemoryRequirements - the plan-time PCS sizing, re-derived
      and compared at PL:427-433. -/
  pcsMemoryRequirements : PcsMemoryRequirements
  /-- PL:44: memory: VerifierMemoryLayout - the converged layout. -/
  memory : VerifierMemoryLayout

/-- rust: PL:59-73 (`enum QuotientRendering`) @formal-baseline. "Quotient rendering mode for
    the main verifier." THREE arms, exactly as hazard 2 says: `External`, `Compact`,
    `Direct`. The Rust's `Box<QuotientComputationBlocks>` (PL:66) and
    `Box<DirectQuotientRendering>` (PL:71) are heap indirection with no Lean analogue, so the
    payloads are stored directly. The Rust derives Clone + Debug (PL:58); no BEq is derived here
    because `QuotientProgram` and `QuotientExternal` do not have one - the gates discriminate
    by pattern match instead. -/
inductive QuotientRendering
  /-- PL:60-62: External { external } - "The main verifier delegates quotient reconstruction to a
      pinned evaluator and therefore renders no local quotient VM program." -/
  | external (external : QuotientExternal)
  /-- PL:63-68: Compact { blocks, program } - "The main verifier runs the compact quotient VM and
      any native callbacks locally." -/
  | compact (blocks : QuotientComputationBlocks) (program : QuotientProgram)
  /-- PL:69-72: Direct { rendering } - "The main verifier runs the direct per-identity Yul
      functions." -/
  | direct (rendering : DirectQuotientRendering)

/-- rust: PL:77-84 (`QuotientRendering::helper_flags`) @formal-baseline. "Helper flags needed
    by the Solidity/Yul templates." HAZARD 2: the External and Direct arms do NOT carry their own
    flags - they take `QuotientComputationBlocks::default().helper_flags()`, i.e. the default
    P-10 pinned field by field at FoldTypes.lean:726. -/
def QuotientRendering.helperFlags (self : QuotientRendering) : QuotientHelperFlags :=
  match self with
  | QuotientRendering.external _ | QuotientRendering.direct _ =>
      quotientComputationBlocksDefault.helperFlags
  | QuotientRendering.compact blocks _ => blocks.helperFlags

/-- rust: PL:87-110 (`QuotientRendering::into_template_parts`) @formal-baseline. "Decompose
    into the legacy template fields from one coordinated value." The four components are the four
    Askama slots the templates used to fill independently; the arms that do not apply contribute
    `none`, and BOTH the External and the Direct arm contribute
    `QuotientComputationBlocks::default()` (PL:98, PL:105). -/
def QuotientRendering.intoTemplateParts (self : QuotientRendering) :
    Option QuotientExternal × QuotientComputationBlocks ×
      Option QuotientProgram × Option DirectQuotientRendering :=
  match self with
  | QuotientRendering.external ext =>
      (some ext, quotientComputationBlocksDefault, none, none)
  | QuotientRendering.compact blocks prog => (none, blocks, some prog, none)
  | QuotientRendering.direct rend =>
      (none, quotientComputationBlocksDefault, none, some rend)

/-- rust: PL:115-119 (`struct QuotientEvaluatorRendering`) @formal-baseline. "Quotient
    rendering facts for the standalone evaluator artifact." Unlike the enum above this one has no
    mode split: the evaluator always gets the external frame, the compact blocks and the compact
    program. -/
structure QuotientEvaluatorRendering where
  /-- PL:116: external: QuotientExternal -/
  external : QuotientExternal
  /-- PL:117: blocks: QuotientComputationBlocks -/
  blocks : QuotientComputationBlocks
  /-- PL:118: program: QuotientProgram -/
  program : QuotientProgram

/-! ## The accessors (rust: PL:140-154, 332-334) -/

/-- rust: PL:145-147 (`LoweringPlan::vm_quotient`) @formal-baseline. "Compact VM quotient plan.
    Panics for a direct-lowering plan; callers on VM-only paths (the external evaluator, VM
    diagnostics) only ever build VM plans."

    R4: `.expect(...)` is a panic, so this is `Except Fault` and NOT an `Option` with a
    default - a port may not soften a panic site (the same call Models.lean:423-435 makes). The
    lost message is "compact quotient VM plan (QuotientLowering::Vm)" (finding F2). THIS IS
    HAZARD 4: the projection from `LoweringPlan` to the quotient program is FAULTING here and
    partial (`Option`) one level earlier at the `quotient` field. -/
def LoweringPlan.vmQuotient {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Except Midfall.Halo2.Fault PlannedQuotient :=
  match L.quotient with
  | some q => .ok q
  | none => .error (Midfall.Halo2.Fault.panic
      "proofs/solidity-verifier/src/lowering/plan.rs:146")

/-- rust: PL:332-334 (`LoweringPlan::repacked_proof_layout_plan`) @formal-baseline. "Repacking
    plan derived from the same proof layout used for rendering." Total:
    `RepackedProofLayoutPlan::from_proof_layout` (QVM:177-187) is a field copy. -/
def LoweringPlan.repackedProofLayoutPlan {Program Layout : Type} (L : LoweringPlan Program Layout) :
    RepackedProofLayoutPlan :=
  RepackedProofLayoutPlan.fromProofLayout L.proofLayout

/-- rust: QRS:778-794 (`VerifierBuildInputs::quotient_external_frame_from_bounds`)
    @formal-baseline. "Compute an external quotient frame from already-known range bounds."
    CROSS-ROW: a quotient.rs item survey:2085 files under "the evaluator frame builders" as
    blocked on the Evaluator. It is not: five `usize`s and a `max` (header). Ported because
    PL:382-388 needs it. `frame_end - frame_base` cannot underflow: `frame_end` is the max of
    `frame_base + vk_len` and `evals_end`, so it is at least `frame_base`. -/
def quotientExternalFrameFromBounds (frameBase vkLen evalsBase numEvals
    simpleSelectorCount : Nat) : QuotientExternal :=
  let vkEnd := frameBase + vkLen
  let evalsEnd := evalsBase + numEvals * wordBytes
  let frameEnd := max vkEnd evalsEnd
  { frameBase := frameBase
    frameLen := frameEnd - frameBase
    outputLen := 2 * wordBytes + simpleSelectorCount * wordBytes
    magic := quotientExternalMagic }

/-- rust: QRS:760-775 (`VerifierBuildInputs::quotient_external_frame`) @formal-baseline.
    "Compute the copied-memory frame required by the external evaluator." Both
    `.value().as_usize()` calls are ENC:599's `unreachable!()` on a symbolic pointer
    (Layout.lean:987-1003), so this is `Except Fault`; the port does not swallow one of them
    into a default. -/
def quotientExternalFrame (vkMptr : Ptr) (vkLen : Nat) (meta_ : ConstraintSystemMeta)
    (memory : VerifierMemoryLayout) (simpleSelectorCount : Nat) :
    Except Midfall.Halo2.Fault QuotientExternal := do
  let frameBase <- (ptrValue vkMptr).asUsize
  let evalsBase <- (ptrValue memory.reversedEvalsMptr).asUsize
  pure (quotientExternalFrameFromBounds frameBase vkLen evalsBase
    meta_.numEvals simpleSelectorCount)

/-- rust: PL:381-389 (`LoweringPlan::quotient_external_frame`) @formal-baseline. "Expected
    external evaluator frame for this finalized layout." -/
def LoweringPlan.quotientExternalFrame {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Except Midfall.Halo2.Fault QuotientExternal :=
  Midfall.Generator.quotientExternalFrame L.vkMptr L.vk.len L.meta_ L.memory
    L.sortedSimple.length

/-- rust: QRS:242-256 (`VerifierBuildInputs::quotient_vm_guards`) @formal-baseline. "Runtime
    interpreter guard constants (QVM-01), derived from the same operand model the build-time
    validator checks the program against." CROSS-ROW, see the header: a quotient.rs item the
    survey files as blocked and that is not.

    R4: the `assert_eq!` at QRS:246-250 is a panic whose message ("quotient VM stack guard and
    operand model disagree on the stack region") F2 loses; site QRS:246. R5:
    `num_consts.saturating_sub(1)` is `Nat.sub` - truncation IS saturation here.
    `quotient_stack_hi - WORD_BYTES` wraps in the release profile if hi < 32; the layout always
    reserves at least one word. -/
def quotientVmGuards (model : QuotientOperandModel) (memory : VerifierMemoryLayout) :
    Except Midfall.Halo2.Fault QuotientVmGuards :=
  if memory.quotientStackHi - memory.quotientStackMptr != model.stackWords * wordBytes then
    .error (Midfall.Halo2.Fault.panic
      "proofs/solidity-verifier/src/lowering/quotient.rs:246")
  else
    .ok { constMax := model.numConsts - 1
          numSelectorBuckets := model.numSelectorBuckets
          stackLast := memory.quotientStackHi - wordBytes }

/-! ## The operand model (rust: PL:570-643) - HAZARD 3'S BRIDGE -/

/-- rust: PL:570-621 (`quotient_read_model`) @formal-baseline. "The memory windows the compact
    quotient VM may load from. Checked exactly, per window and with word alignment, by the
    build-time operand validator (`vm::validate_quotient_program_operands`, QVM-01); the
    interpreter has no runtime pointer clamp."

    Four windows in the Rust's order, then nine token bases in the Rust's order. Every address
    goes through `Value::as_usize`, which panics on a symbolic pointer, so the whole builder is
    `Except Fault`.

    R5: PL:598's `saturating_sub` is `Nat.sub` - the same truncation, so it is not emulated
    separately. PL:589's `iter().sum::<usize>()` is an order-independent fold over
    `num_user_challenges`. -/
def quotientReadModel (meta_ : ConstraintSystemMeta) (data : Data)
    (vk : Halo2VerifyingKey) (vkMptr : Ptr) (memory : VerifierMemoryLayout) :
    Except Midfall.Halo2.Fault QuotientReadModel := do
  let theta <- (ptrValue data.thetaMptr).asUsize
  let instanceEval <- (ptrValue memory.instanceEvalMptr).asUsize
  let vkBase <- (ptrValue vkMptr).asUsize
  let challengeBase <- (ptrValue data.challengeMptr).asUsize
  let evalsBase <- (ptrValue memory.reversedEvalsMptr).asUsize
  let l0 <- (ptrValue memory.l0Mptr).asUsize
  let lLast <- (ptrValue memory.lLastMptr).asUsize
  let lBlind <- (ptrValue memory.lBlindMptr).asUsize
  let beta <- (ptrValue memory.betaMptr).asUsize
  let gamma <- (ptrValue memory.gammaMptr).asUsize
  let x <- (ptrValue memory.xMptr).asUsize
  let memTheta <- (ptrValue memory.thetaMptr).asUsize
  let trash <- (ptrValue memory.trashChallengeMptr).asUsize
  let windows : List QuotientReadWindow :=
      [ { name := "vk_payload", start := vkBase, len := vk.len },
        { name := "user_challenges", start := challengeBase,
          len := meta_.numUserChallenges.foldl (fun a b => a + b) 0 * wordBytes },
        { name := "challenge_and_common_slots", start := theta,
          len := (instanceEval + wordBytes) - theta },
        { name := "decoded_proof_evals", start := evalsBase,
          len := meta_.numEvals * wordBytes } ]
  pure { windows := windows
         tokenBases :=
        [(qMemL0, l0), (qMemLLast, lLast), (qMemLBlind, lBlind), (qMemBeta, beta),
         (qMemGamma, gamma), (qMemX, x), (qMemTheta, memTheta),
         (qMemTrashChallenge, trash), (qMemInstanceEval, instanceEval)] }

/-- rust: PL:626-643 (`quotient_operand_model`) @formal-baseline. "Operand bounds for one
    finalized quotient program (QVM-01): read windows, constant-table length, selector bucket
    count, largest selector By` power, and the planned stack region."

    THIS IS THE BRIDGE P-09e NAMED. `validateQuotientProgramOperands`
    (VmValidator.lean:1162) takes `(bytes, model)` and P-09e could only build the model from a
    hand-written fixture, which is why PLAN 9.5's one-argument
    `validateQuotientProgramOperands g.plan` had no Lean denotation. With this def the predicate
    is writable from a plan alone: see `LoweringPlan.supportedQvm`.

    R5, recorded at the site: `(hi - mptr) / WORD_BYTES` is a wrapping `usize` subtraction in
    the release profile when the region is empty or inverted, and a truncating `Nat` subtraction
    here. `quotientOperandModel_stackWords_ok` pins what the port does when it is handed an
    inverted region anyway. -/
def quotientOperandModel (meta_ : ConstraintSystemMeta) (data : Data)
    (vk : Halo2VerifyingKey) (vkMptr : Ptr) (memory : VerifierMemoryLayout)
    (build : QuotientProgramBuild) (selectorFold : SelectorFoldPlan) :
    Except Midfall.Halo2.Fault QuotientOperandModel := do
  let readModel <- quotientReadModel meta_ data vk vkMptr memory
  -- `pure { read := ... }` cannot be written inside `do`: `read` is a reserved
  -- term in do-notation, so the field is set through the explicit constructor. Lean-side
  -- syntax only; the field order is VmValidator.lean:496-511's.
  pure (QuotientOperandModel.mk readModel build.consts.length meta_.numSimpleSelectors
    selectorFold.maxPower
    ((memory.quotientStackHi - memory.quotientStackMptr) / wordBytes))

/-- rust: PL:539-549 (`LoweringPlan::quotient_operand_model`) @formal-baseline. "Everything the
    finalized quotient program's operands are checked against, at build time and (through
    `QuotientVmGuards`) at run time." Faults twice over: through `vm_quotient` (PL:146) and
    through the pointer reads inside `quotient_read_model`. -/
def LoweringPlan.quotientOperandModel {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Except Midfall.Halo2.Fault QuotientOperandModel := do
  let q <- L.vmQuotient
  Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
    q.build q.plan.selectorFold

/-- rust: PL:532-535 (`LoweringPlan::quotient_read_model`) @formal-baseline. TEST-ONLY
    (`#[cfg(test)]`, PL:532): "Addresses the compact quotient VM is allowed to load from."
    Ported and marked, per the Api.lean:637 precedent. Unlike `vm_quotient` this one does NOT
    touch the quotient field, so it is total in the lowering mode and faults only on a symbolic
    pointer. Named `...Method` because the free function at PL:570 already owns
    `quotientReadModel` in this namespace. -/
def LoweringPlan.quotientReadModelMethod {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Except Midfall.Halo2.Fault QuotientReadModel :=
  quotientReadModel L.meta_ L.data L.vk L.vkMptr L.memory

/-! ## The invariant checker (rust: PL:413-523) -/

/-- rust: PL:428 (`self.pcs_memory_requirements != planned_pcs`). `Layout.lean:885`
    derives no `BEq` on `VerifierMemoryLayout`/`PcsMemoryRequirements` - the Rust derives
    `PartialEq` (MEM:396) - so the comparator is spelled out field by field here rather than
    added to Layout.lean, which this package does not own. Same class as the plans README's F5
    note (`Location`/`Value`/`Ptr` carry no `BEq` and every later package re-invents a
    comparator). Not a Rust item. -/
def pcsMemoryRequirementsBeq (a b : PcsMemoryRequirements) : Bool :=
  a.rotPointsWords == b.rotPointsWords && a.x1PowersWords == b.x1PowersWords
    && a.qComWords == b.qComWords && a.qEvalSetWords == b.qEvalSetWords
    && a.qEvalSourceTableWords == b.qEvalSourceTableWords
    && a.qComTraceMsm.terms == b.qComTraceMsm.terms
    && a.qComTraceMsm.inputBytes == b.qComTraceMsm.inputBytes
    && a.finalMsm.terms == b.finalMsm.terms
    && a.finalMsm.inputBytes == b.finalMsm.inputBytes

/-- The Rust's derived `Debug` for `PcsMemoryRequirements` (MEM:397-414), spelled out because
    Lean has no `Debug`. Reached only from PL:429-432's `planned {:?}, recomputed {:?}`.
    Precedent: `certifyFrDebug` (VmCertify.lean:329) and `payloadSectionKindDebug`
    (Layout.lean:246). The field names printed are the RUST ones, because that is what `{:?}`
    emits. -/
def pcsMemoryRequirementsDebug (p : PcsMemoryRequirements) : String :=
  "PcsMemoryRequirements { rotPointsWords: " ++ toString p.rotPointsWords ++
  ", x1PowersWords: " ++ toString p.x1PowersWords ++
  ", qComWords: " ++ toString p.qComWords ++
  ", qEvalSetWords: " ++ toString p.qEvalSetWords ++
  ", qEvalSourceTableWords: " ++ toString p.qEvalSourceTableWords ++
  ", qComTraceMsm: FinalMsmShape { terms: " ++ toString p.qComTraceMsm.terms ++
  ", inputBytes: " ++ toString p.qComTraceMsm.inputBytes ++
  " }, finalMsm: FinalMsmShape { terms: " ++ toString p.finalMsm.terms ++
  ", inputBytes: " ++ toString p.finalMsm.inputBytes ++ " } }"

/-- The Rust's derived `Debug` for `QuotientVmGuards` (M:751-760), reached only from PL:510's
    `rendered {rendered:?}, expected {expected:?}`. Same precedent note as
    `pcsMemoryRequirementsDebug`. -/
def quotientVmGuardsDebug (g : QuotientVmGuards) : String :=
  "QuotientVmGuards { const_max: " ++ toString g.constMax ++
  ", num_selector_buckets: " ++ toString g.numSelectorBuckets ++
  ", stack_last: " ++ toString g.stackLast ++ " }"

/-- Sequencing for `validateGeneratorInvariants`'s two-layer result: the Rust returns
    `Result<(), String>` and ABORTS on a panic, so the port keeps the String layer inside and
    the panic layer outside - the same shape Kzg.lean:1099-1101 uses for the callee at PL:420.
    Not a Rust item. -/
def invThen (x : Except String Unit)
    (k : Unit -> Except Midfall.Halo2.Fault (Except String Unit)) :
    Except Midfall.Halo2.Fault (Except String Unit) :=
  match x with
  | .error m => .ok (.error m)
  | .ok u => k u

/-- rust: PL:413-523 (`LoweringPlan::validate_generator_invariants`) @formal-baseline.
    "Re-check cross-module invariants after convergence. This catches drift between independently
    computed protocol, memory, quotient, and precompile-coverage facts before any Solidity
    template is rendered."

    SIXTEEN checks in the Rust's source order with the Rust's own message strings: every `format!`
    here is a String-layer payload, so unlike the panic sites these messages survive (F2 applies
    to `Fault.panic`, not to `Err`). The `{}`-vs-`{:#x}` choices are load-bearing:
    PL:486-494 renders addresses as hex and PL:464-482 renders counts as decimal.

    The panic layer appears at three points: PL:420's callee (the Fault the Lean port of
    `validate_absorbed_g1_precompile_coverage` carries), PL:461's `self.vm_quotient()`, and
    PL:503's `self.quotient_operand_model()`, which re-enters `vm_quotient` and then the
    `as_usize` reads. -/
def LoweringPlan.validateGeneratorInvariants {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Except Midfall.Halo2.Fault (Except String Unit) :=
  invThen (L.meta_.validateAgainstProtocol
    |>.mapError (fun err => "protocol invariant failed: " ++ err)) fun () =>
  invThen (L.memory.validate
    |>.mapError (fun err => "memory-region non-overlap invariant failed: " ++ err)) fun () =>
  match validateAbsorbedG1PrecompileCoverage L.meta_ L.data L.memory L.proofLayout with
  | .error f => .error f
  | .ok inner => invThen (inner
      |>.mapError (fun err => "absorbed-G1 precompile coverage invariant failed: " ++ err))
      fun () =>
  match memoryRequirements L.meta_ L.data with
  | .error f => .error f
  | .ok plannedPcs =>
  invThen
    (if pcsMemoryRequirementsBeq L.pcsMemoryRequirements plannedPcs then .ok () else
      .error ("PCS memory requirements drifted: planned " ++
        pcsMemoryRequirementsDebug L.pcsMemoryRequirements ++
        ", recomputed " ++ pcsMemoryRequirementsDebug plannedPcs)) fun () =>
  match L.direct with
  | some d =>
    -- PL:434-459: the direct branch returns Ok early and never reaches the VM checks below. This
    -- is the arm PLAN 9.5's repaired `Supported.qvm` cites: a Direct plan has no QVM program to
    -- validate (PL:224 stores `quotient: None`).
    .ok (do
      if L.quotient.isSome || L.lowering != QuotientLowering.direct then
        .error "direct plan also carries a compact VM plan"
      else if L.vk.quotientProgramWords != 0 then
        .error ("direct lowering must not reserve VM program words (got " ++
          toString L.vk.quotientProgramWords ++ ")")
      else if L.vk.quotientConstWords != d.table.length then
        .error ("direct constant table drifted: VK reserves " ++
          toString L.vk.quotientConstWords ++ " words, program has " ++
          toString d.table.length)
      else
        let offset := L.vk.quotientConstOffsetWords.getD usizeMax
        match ((List.range d.table.length).zip d.table).find? fun (i, word) =>
            (listNth L.vk.constants (offset + i)).map (fun (_, v) => v) != some word with
        | some (i, _) =>
            .error ("direct constant table word " ++ toString i ++
              " differs from the VK payload")
        | none => .ok ())
  | none => do
    let q <- L.vmQuotient
    invThen
      (do
        if q.program.len != q.build.bytes.data.size then
          .error ("quotient program length drifted: model=" ++ toString q.program.len ++
            " build=" ++ toString q.build.bytes.data.size)
        else if q.build.consts.length > L.vk.quotientConstWords then
          .error ("quotient const table exceeds VK reservation: consts=" ++
            toString q.build.consts.length ++ " words=" ++ toString L.vk.quotientConstWords)
        else if PackedProgramCodec.wordLenForBytes q.build.bytes.data.size >
            L.vk.quotientProgramWords then
          .error ("quotient bytecode exceeds VK reservation: program_words=" ++
            toString (PackedProgramCodec.wordLenForBytes q.build.bytes.data.size) ++
            " reserved=" ++ toString L.vk.quotientProgramWords)
        else if q.program.stackMptr != q.stackMptr then
          .error ("quotient stack pointer drifted: model=" ++ hashHex q.program.stackMptr ++
            " planned=" ++ hashHex q.stackMptr)
        else if q.program.evalNumerMptr != q.stateSlots.evalNumerMptr then
          .error ("quotient state pointer drifted: model=" ++
            hashHex q.program.evalNumerMptr ++ " planned=" ++
            hashHex q.stateSlots.evalNumerMptr)
        else .ok ()) fun () =>
    match Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr L.memory
        q.build q.plan.selectorFold with
    | .error f => .error f
    | .ok operandModel =>
      invThen
        ((validateQuotientProgramOperands (bytesToList q.build.bytes) operandModel)
          |>.mapError (fun err =>
            "quotient VM operand validation failed: " ++ err.message)) fun () =>
      match quotientVmGuards operandModel L.memory with
      | .error f => .error f
      | .ok expected =>
        invThen
          (if q.program.guards == expected then .ok () else
            .error ("quotient VM runtime guards drifted from the operand model: rendered " ++
              quotientVmGuardsDebug q.program.guards ++ ", expected " ++
              quotientVmGuardsDebug expected)) fun () =>
        -- PL:516-521: the certifier's own Err is WRAPPED here, not returned bare.
        Midfall.Generator.QuotientCertify.certifyQuotientProgram q.plan q.build L.vk
          |>.mapError (fun err => "quotient program certification failed: " ++ err)
          |> fun r => .ok r

/-! ## The rendering builders (rust: PL:337-378) and acc_msm_terms (PL:552-562) -/

/-- rust: PL:337-365 (`LoweringPlan::quotient_rendering`) @formal-baseline. "Build quotient
    rendering for the main verifier." All THREE arms are here, so hazard 2's gate can reach them:
    External when `external_quotient`, Direct when the plan carries a direct payload (choosing
    Btrace_rendering` or `rendering`, PL:351-355), Compact otherwise.

    DEVIATION (header): the Rust reaches the compact arm through
    `self.compact_quotient_blocks(inputs, trace)` (PL:362 -> QRS:2000), which renders Yul
    through the Evaluator and IS blocked. Rather than import around it (hazard 6) the emitter is
    passed in as the first argument, so the arm structure is ported and the hole is a named
    parameter. The Rust's `inputs` parameter disappears with it: PL:339 is its only use. -/
def LoweringPlan.quotientRendering {Program Layout : Type}
    (compactBlocks : LoweringPlan Program Layout -> Bool -> QuotientComputationBlocks)
    (L : LoweringPlan Program Layout) (trace externalQuotient : Bool) :
    Except Midfall.Halo2.Fault QuotientRendering := do
  if externalQuotient then
    let ext <- L.quotientExternalFrame
    .ok (QuotientRendering.external (external := ext))
  else
    match L.direct with
    | some d => .ok (QuotientRendering.direct
        (rendering := if trace then d.traceRendering else d.rendering))
    | none => do
        let q <- L.vmQuotient
        .ok (QuotientRendering.compact (blocks := compactBlocks L trace)
          (program := q.program))

/-- rust: PL:368-378 (`LoweringPlan::quotient_evaluator_rendering`) @formal-baseline. "Build
    quotient rendering for the standalone evaluator artifact." Same injected emitter as above;
    the evaluator has no Direct arm, which is why this returns a record and not the enum. -/
def LoweringPlan.quotientEvaluatorRendering {Program Layout : Type}
    (compactBlocks : LoweringPlan Program Layout -> Bool -> QuotientComputationBlocks)
    (L : LoweringPlan Program Layout) (trace : Bool) :
    Except Midfall.Halo2.Fault QuotientEvaluatorRendering := do
  let q <- L.vmQuotient
  let ext <- L.quotientExternalFrame
  pure { external := ext
         blocks := compactBlocks L trace
         program := q.program }

/-- rust: PL:552-562 (`LoweringPlan::acc_msm_terms`) @formal-baseline. "Number of
    (`G1, scalar`) terms required by the optional accumulator MSM." A private associated
    function of `VerifierBuildInputs` in the Rust, reached from both plan constructors when
    they fill `VerifierMemoryLayoutConfig.acc_msm_terms` (PL:195, PL:266).

    DEVIATION, deliberate and load-bearing (hazard 1): the port takes the TWO FIELDS the body
    reads - `acc_encoding` (PL:554) and `num_instances` (PL:557) - instead of a
    `VerifierBuildInputs` receiver, so that this file does not import `Generator.Vk`.
    Vk.lean:289 imports `Instances.ExponentModel`, and D-P17 plus the P-SE constraint list
    forbid a theorem-bearing file from importing it - and P-SE section M states Surface.lean
    "never imports `Generator.Vk`". This file exists to be the module the P-SE statement
    surface can import, so importing Vk here would poison it. `VerifierBuildInputs` is NOT
    re-declared anywhere here, which is what hazard 1 actually protects.
    D-P16: `accEncoding` is the GENERATOR's `AccumulatorEncoding` (Api.lean:413), so
    `fixedScalarCount` is Api.lean:622's, returning `Except ApiFault`. The Rust's
    `.expect("accumulator encoding validated by GeneratorConfig")` at PL:558 is a panic: an
    encoding that did not survive `GeneratorConfig::validate` aborts the build rather than
    planning a wrong region. R4 keeps it a panic; F2 loses the message. -/
def accMsmTerms (accEncoding : Option Midfall.Generator.AccumulatorEncoding)
    (numInstances : Nat) : Except Midfall.Halo2.Fault Nat :=
  match accEncoding with
  | none => .ok 0
  | some enc =>
      match enc.fixedScalarCount numInstances with
      | .error _ => .error (Midfall.Halo2.Fault.panic
          "proofs/solidity-verifier/src/lowering/plan.rs:558")
      | .ok n => .ok (n + 1)

/-! ## The statement surface PLAN 9.5 needs

    Everything in this block exists to give PLAN 9.5's `L.plan`, `L.plan.qprog` and
    `Supported.qvm` a denotation. They are named after the PLAN's identifiers, not after Rust
    ones, and each says so. None of them is a Rust item. -/

/-- PLAN 9.5's `L.plan.qprog` (docs/PLAN.md:514-516), spelled out. survey:2499 already ruled
    that "PLAN's `L.plan.qprog` corresponds to `quotient.build.bytes`", and D-P20's addendum
    (docs/design.md:594) named this file as the blocker.

    REQUIRED FINDING (b): FAULTING, not total and not `Option`. The reference's own accessor
    (`vm_quotient`, PL:146) `expect`s, so a Direct plan aborts the process rather than
    answering `None`; the `Option` is one level earlier, on the `quotient` field.
    `qprogOpt` is the total form for statements that do not want to talk about aborts. -/
def LoweringPlan.qprog {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Except Midfall.Halo2.Fault (List Nat) := do
  let q <- L.vmQuotient
  pure (bytesToList q.build.bytes)

/-- The total reading of the same projection: `none` for a Direct plan instead of the
    reference's abort. -/
def LoweringPlan.qprogOpt {Program Layout : Type} (L : LoweringPlan Program Layout) : Option (List Nat) :=
  L.quotient.map fun q => bytesToList q.build.bytes

/-- The decidable form of `supportedQvm` (P-SE decision D2 wants `Supported` fields decidable;
    P-09e's `supportedQvmBool` is the two-argument version this mirrors). Declared FIRST so
    the Prop below can be stated as `this = true` and one gate can cover both. -/
def LoweringPlan.supportedQvmBool {Program Layout : Type} (L : LoweringPlan Program Layout) : Bool :=
  match L.lowering with
  | QuotientLowering.direct => true
  | QuotientLowering.vm =>
      match L.quotient with
      | none => false
      | some q =>
          match Midfall.Generator.quotientOperandModel L.meta_ L.data L.vk L.vkMptr
                L.memory q.build q.plan.selectorFold with
          | .error _ => false
          | .ok model =>
              match validateQuotientProgramOperands (bytesToList q.build.bytes) model with
              | .ok _ => true
              | .error _ => false

/-- PLAN 9.5's `Supported.qvm` (docs/PLAN.md:424-430), repaired per the round-25 note:
    QVM-01 applies to the VM lowering only, because a Direct plan stores `quotient: None`
    (PL:224), so an unconditional clause is ill-formed rather than merely over-strict.

    REQUIRED FINDING (a): YES - this is writable from a plan alone, in ONE argument, which is
    exactly what P-09e could not do. It is `validateQuotientProgramOperands L.qprog
    (L.quotientOperandModel) = .ok ()` with the model built by PL:626-643 from the same
    converged fields the reference uses. Stated as the decidable form equated to `true`
    so the Prop and the Bool cannot drift apart and one gate covers both. -/
def LoweringPlan.supportedQvm {Program Layout : Type} (L : LoweringPlan Program Layout) :
    Prop :=
  L.supportedQvmBool = true

/-- D-P18's `Supported.layout`, portable half only: `validate = .ok ()` from
    Layout.lean:1023. The `WellFormed` half is a P-SE obligation (the Inv/Layout layer) that
    does not exist in the tree yet, so this is NOT the whole of D-P18 and is named for the half it
    is. -/
def LoweringPlan.supportedLayoutValidate {Program Layout : Type} (L : LoweringPlan Program Layout) : Prop :=
  match L.memory.validate with
  | .ok _ => True
  | .error _ => False


end Midfall.Generator

/-! ====================================================================
    ## Known-answer tests
    ====================================================================

    R-41: every gate below was RUN, and the ones that failed to redden are reported in
    the package report. R-48: the fixture is this package's own - a real
    `QuotientProgramBuild` emitted by P-09c's builder (VmCertify.lean's
    `threeIdentityBuild`) bound to a converged memory layout - and
    `loweringPlanFixture_nonDegenerate_ok` asserts its distinctness before any gate
    leans on it. D-P19: the three artifact gates open plan.rs, config.rs and
    quotient_direct.rs at #eval time, and `planArtifactReachable_ok` is the FIRST #eval
    in the section so a wrong path is diagnosed rather than silently matching nothing.

    WHY THE FIXTURE IS ASSEMBLED AND NOT GENERATED. The reference builds a `LoweringPlan`
    only through `LoweringPlan::new` (PL:235-329), which needs the memory-layout
    constructor this tree declined (header). So the fixture is assembled from the same
    pieces the reference's own plan tests assemble from: a built program, a layout whose
    `validate` passes, and a VK whose reservations cover the program. The gates that
    matter are then the reference's own checks over that assembly - including
    `certifyQuotientProgram`, which really runs the interpreter over the real bytecode -
    so `validateGeneratorInvariants_acceptsTheConvergedFixture_ok` is not a tautology:
    it fails if any of the sixteen checks is dropped, reordered or inverted. -/

namespace Midfall.Generator.LoweringPlanKats

open Midfall.Generator
open Midfall.Generator.QuotientFold
open Midfall.Generator.QuotientValidator
open Midfall.Generator.KzgKats
open Midfall.Generator.EncodingKats
open Midfall.Generator.QuotientCertifyKats

/-! ### Artifact readers (D-P19) -/

/-- Count non-overlapping occurrences of `needle`. -/
def countMatches (haystack needle : String) : Nat :=
  ((haystack.splitOn needle).length - 1)

/-- The two candidate paths to PL, so the gate resolves from `formal/` (where checks.sh
    and kat_gate.py run) and from the repo root - the pattern FoldTypes.lean:798 sets. -/
def planPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/plan.rs",
   "proofs/solidity-verifier/src/lowering/plan.rs"]

def configPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/config.rs",
   "proofs/solidity-verifier/src/lowering/config.rs"]

def qdirPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_direct.rs",
   "proofs/solidity-verifier/src/lowering/quotient_direct.rs"]

/-- Read one of the three sources, trying both candidate paths. Reuses VmTypes' reader
    rather than re-implementing it (the FoldTypes.lean:802 precedent). -/
def readArtifact (candidates : List String) : IO String :=
  candidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got
        else Midfall.Generator.QuotientVmKats.readFileOrEmpty path)
    (pure "")

def readPlanRs : IO String := readArtifact planPathCandidates
def readConfigRs : IO String := readArtifact configPathCandidates
def readQdirRs : IO String := readArtifact qdirPathCandidates

/-- The n-th line of a source, 1-based, or the empty string. -/
def lineOf (src : String) (n : Nat) : String :=
  match (src.splitOn "\n").drop (n - 1) |>.head? with
  | some l => l
  | none => ""

/-- GATE 1 (reachability, FIRST #eval in the section). plan.rs is 643 lines / ~26 KB at
    HEAD; anything much smaller is a wrong path and must not be allowed to satisfy a
    needle check by accident. -/
def planArtifactReachable_ok : IO Bool :=
  readPlanRs >>= fun src => pure (src.length > 24000 && src.contains "struct LoweringPlan")

/-- Both needles present on one line of a source. -/
def lineHas (src : String) (n : Nat) (a b : String) : Bool :=
  let l := lineOf src n
  l.contains a && l.contains b

/-- GATE 2 (hazard 5, finding F2). Every `.expect` / `panic!` / `unwrap_or_else` in
    plan.rs, with the message each one loses on the way to `Fault.panic`. The set is
    pinned BOTH ways: each recorded site must be present with its text, and the total count
    of panic-forming calls must be exactly six, so a seventh cannot be added to the Rust
    without reddening this gate. -/
def panicSites_areTheRecordedOnes_ok : IO Bool :=
  readPlanRs >>= fun src => pure (
        lineHas src 146 ".expect(" "compact quotient VM plan (QuotientLowering::Vm)"
     && lineHas src 153 ".expect(" "compact quotient VM plan (QuotientLowering::Vm)"
     && lineHas src 229 "map_err" "generator invariants"
     && lineHas src 310 "unwrap_or_else" "generator invariant violation"
     && lineHas src 326 "unwrap_or_else" "quotient dual-build certification failed"
     && lineHas src 558 ".expect(" "accumulator encoding validated by GeneratorConfig"
     && countMatches src ".expect(" == 3
     && countMatches src "panic!(" == 2
     && countMatches src "unwrap_or_else" == 2
     && (src.splitOn "\n").length == 644)

/-- GATE 3 (brief correction 3). config.rs's three constants, read from the file, and the
    three Lean defs that already own them - in three different packages' namespaces, which
    is the finding. -/
def configConstants_matchConfigRs_ok : IO Bool :=
  readConfigRs >>= fun src => pure (
        src.contains "pub(crate) const DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES: usize = 4;"
     && src.contains "pub(crate) const DEFAULT_QUOTIENT_NATIVE_GATES: usize = 4;"
     && src.contains "pub(crate) const DEFAULT_QUOTIENT_LIMB_VM_OPS: bool = true;"
     && Midfall.Generator.QuotientFoldCompute.defaultHybridQuotientInlineIdentities == 4
     && Midfall.Generator.QuotientFoldCompute.defaultQuotientNativeGates == 4
     && Midfall.Generator.QuotientBuilder.defaultQuotientLimbVmOps == true)

/-- GATE 4 (brief correction 2). The carve-out's two records, and the fact that only one
    of them is new here: `DirectQuotientRendering` is QDIR:56-65 and was P-04's;
    `DirectQuotientPlanned` is QDIR:33-53 and is this package's. -/
def qdirRecords_areTheCarvedOutOnes_ok : IO Bool :=
  readQdirRs >>= fun src => pure (
        lineHas src 35 "struct DirectQuotientPlanned" ""
     && lineHas src 57 "struct DirectQuotientRendering" ""
     && (src.splitOn "\n").length == 395)

/-! ### The fixture -/

/-- The Kzg fixture meta with TWO simple-selector buckets, because the built program's
    `foldFSelector` addresses bucket 1 (VmValidator.lean:1146-1151 rejects a bucket at or
    above the count, so a one-bucket meta cannot host this program). -/
def planMeta : ConstraintSystemMeta := { metaF with numSimpleSelectors := 2 }

/-- The Kzg fixture memory - the one triple (meta, data, memory) that passes
    `validateAbsorbedG1PrecompileCoverage` - with the two overrides the plan layer needs:
    `pcsPairingScratchMptr` back to its constant (KzgKats.memF deliberately breaks it for
    its own gate, which is why `memF.validate` is NOT reusable as-is), and the quotient
    stack / temp / eval windows placed so the read model covers the program's three
    literal pointers 0x100, 0x120, 0x140. -/
def planMemory : VerifierMemoryLayout :=
  { memF with
    pcsPairingScratchMptr := pcsPairingScratchStart,
    thetaMptr := ptrMemory (valueFromNat 0x2400),
    reversedEvalsMptr := ptrMemory (valueFromNat 0x100),
    instanceEvalMptr := ptrMemory (valueFromNat 0x3000),
    quotientStackMptr := 0xA000,
    quotientStackHi := 0xA020,
    quotientTmpMptr := 0xB000 }

/-- The VK the certifier uses (VmCertify.lean:887), with the two reservations the plan's
    steps 8 and 9 compare against filled to cover the built program: 2 constants and 1
    program word (23 bytes packs into one word). -/
def planVk : Halo2VerifyingKey :=
  { certVk with
    quotientConstWords := 2,
    quotientProgramWords := 1,
    quotientConstOffsetWords := some 39,
    quotientProgramOffsetWords := some 41 }

/-- The real emitted program: P-09c's builder, three identities with a selector fold
    (VmCertify.lean:863). The `.error` arm is unreachable - the certifier's own gate
    GATE 8 accepts this build - but Lean needs a total term, and the fallback is the empty
    build so a regression shows up as a red gate rather than a stuck elaborator. -/
def planBuild : QuotientProgramBuild :=
  match threeIdentityBuild with
  | .ok b => b
  | .error _ => { bytes := Midfall.Bytes.empty, consts := [], maxStack := 0,
                  usedOps := Midfall.Bytes.empty, usedMemTokens := Midfall.Bytes.empty }

/-- The three identities' plan, with `selectorFold.maxPower` raised to 5: the emitted
    fold addresses gap 5 (PL:639 reads the power from the fold plan, and
    VmValidator.lean:1153-1155 rejects a larger gap), and VmCertify's fixture leaves the
    power at 0 because the certifier never consults it. -/
def planPlan : QuotientProgramPlan :=
  { threeIdentityPlan with
    selectorFold := { threeIdentityPlan.selectorFold with maxPower := 5 } }

/-- The plan's own pointer, matching the memory the layout names (PL:238 destructures
    `meta_data_for_stable_static_layout` into exactly this pair). -/
def planVkMptr : Ptr := planMemory.vkMptr

/-- The operand model PL:626-643 builds from the fixture. The `.error` arm is the
    sentinel that makes every gate that reads it go red rather than pass on defaults. -/
def planModel : QuotientOperandModel :=
  match quotientOperandModel planMeta dataF planVk planVkMptr planMemory planBuild
      planPlan.selectorFold with
  | .ok m => m
  | .error _ => { read := quotientReadModelDefault, numConsts := 999,
                  numSelectorBuckets := 999, selectorMaxPower := 999, stackWords := 999 }

/-- The template's program model (QRS:189-238 builds this in the reference; that builder
    is not ported, so the fixture supplies the same eleven fields). `guards` is computed
    by PL:507's own function so step 14 is a real comparison and not a tautology: the
    guards gate below breaks it by changing ONE field. -/
def planProgram : QuotientProgram :=
  { len := planBuild.bytes.data.size,
    opUsage := quotientVmOpcodeUsageDefault,
    memUsage := quotientVmMemUsageDefault,
    constMptr := 0xC000,
    evalNumerMptr := 0xB000,
    traceIdMptr := 0xB020,
    selectorPowerMptr := 0xB040,
    selectorMaxPower := 5,
    selectorTailUpdates := [],
    stackMptr := 0xA000,
    programMptr := 0xC100,
    guards := match quotientVmGuards planModel planMemory with
              | .ok g => g
              | .error _ => { constMax := 999, numSelectorBuckets := 999,
                              stackLast := 999 } }

def plannedQ : PlannedQuotient :=
  { plan := planPlan, build := planBuild, program := planProgram, stackMptr := 0xA000,
    stateSlots := QuotientStateSlots.new 0xB000 }

/-- THE VM PLAN. `pcsMemoryRequirements` is the value PL:427 recomputes, so step 4
    passes; every other field is the fixture above. -/
def planVM : LoweringPlan Unit Unit :=
  { vk := planVk, vkMptr := planVkMptr, meta_ := planMeta, data := dataF,
    proofLayout := proofLayoutF, lowering := QuotientLowering.vm,
    sortedSimple := planPlan.sortedSimple, quotient := some plannedQ, direct := none,
    pcsMemoryRequirements :=
      match memoryRequirements planMeta dataF with
      | .ok p => p
      | .error _ => pcsMemoryRequirementsDefault,
    memory := planMemory }

/-- The direct payload: two table words, both present in the VK at the declared offset
    (PL:452-457 compares them one by one), and two distinct renderings so the trace arm of
    `quotientRendering` cannot pass on a copy-paste. -/
def directF : DirectQuotientPlanned Unit Unit :=
  { program := (), layout := (), table := [101, 102], selectorAccMptr := 0xD000,
    rendering := { constants := ["const q_main_acc"], functions := ["fn q_0"],
                   block := ["block production"] },
    traceRendering := { constants := ["const q_main_acc_trace"],
                        functions := ["fn q_0_trace"], block := ["block trace"] },
    folds := foldRecordDefault }

/-- A direct-lowering plan: PL:216-228 stores `quotient: None` and
    `lowering: Direct`, and reserves no VM program words (PL:438-443). -/
def planDirect : LoweringPlan Unit Unit :=
  { planVM with
    vk := { certVk with
            quotientConstWords := 2,
            quotientProgramWords := 0,
            quotientConstOffsetWords := some 2,
            constants := certVk.constants ++ [("q_direct_0", 101), ("q_direct_1", 102)] },
    lowering := QuotientLowering.direct,
    quotient := none,
    direct := some directF }

/-- A plan with NEITHER payload: the state the reference cannot build but the type allows,
    which is what makes `vm_quotient`'s panic reachable. -/
def planNeither : LoweringPlan Unit Unit := { planVM with quotient := none }

/-- The blocks with a `q_pow5(` call, for the helper-flag gates. -/
def blocksPow5 : QuotientComputationBlocks :=
  { quotientComputationBlocksDefault with
    inlineComputations := [["  let z := q_pow5(f)"]] }

/-- The blocks with the WIDE limb helper only - the case FoldTypes.lean:767 says must set
    `wideLimb7` and NOT `limb7`. -/
def blocksLimb7Wide : QuotientComputationBlocks :=
  { quotientComputationBlocksDefault with
    evalNumerComputations := [["  q_limb7_wide(a, b)"]] }

/-- The three rendering arms over the fixture. -/
def renderingExternal : QuotientRendering :=
  match planVM.quotientExternalFrame with
  | .ok ext => QuotientRendering.external ext
  | .error _ => QuotientRendering.direct directF.rendering

def renderingCompact : QuotientRendering :=
  QuotientRendering.compact blocksPow5 planProgram

def renderingDirect : QuotientRendering := QuotientRendering.direct directF.rendering

/-- The String-layer verdict of the invariant checker, flattened for the gates. -/
def invResult (L : LoweringPlan Unit Unit) : String :=
  match L.validateGeneratorInvariants with
  | .error (Midfall.Halo2.Fault.panic s) => "PANIC " ++ s
  | .error _ => "PANIC-other"
  | .ok (.ok ()) => "ok"
  | .ok (.error m) => m

/-- Does the invariant checker's message start with this prefix? -/
def msgStarts (L : LoweringPlan Unit Unit) (want : String) : Bool :=
  (invResult L).startsWith want

/-- The fault site of an `Except Fault` verdict, or `"ok"`. -/
def faultSite {alpha : Type} (x : Except Midfall.Halo2.Fault alpha) : String :=
  match x with
  | .ok _ => "ok"
  | .error (Midfall.Halo2.Fault.panic s) => s
  | .error _ => "other"

/-! ### GATE 5: the fixture is not degenerate (R-48) -/

/-- Every address the fixture names is distinct, the two renderings differ, the built
    program is non-empty, and the VM and direct plans really are the two modes. Without
    this, a wrong field assignment in `quotientReadModel` is invisible because all the
    pointers are 0 (the same argument Encoding.lean:1404 makes for its own fixture). -/
def loweringPlanFixture_nonDegenerate_ok : Bool :=
  let addrs := [planVkMptr.value.asUsizeNat, (ptrValue planMemory.thetaMptr).asUsizeNat,
                (ptrValue planMemory.instanceEvalMptr).asUsizeNat,
                (ptrValue planMemory.reversedEvalsMptr).asUsizeNat,
                planMemory.quotientStackMptr, planMemory.quotientTmpMptr]
  addrs.length == 6
    && addrs.all (fun a => (addrs.filter (fun b => b == a)).length == 1)
    && planBuild.bytes.data.size == 23
    && planBuild.consts.length == 2
    && planBuild.maxStack == 1
    && planModel.numConsts == 2 && planModel.numSelectorBuckets == 2
    && planModel.selectorMaxPower == 5 && planModel.stackWords == 1
    && planProgram.constMptr != planProgram.programMptr
    && planProgram.evalNumerMptr != planProgram.traceIdMptr
    && directF.rendering.block != directF.traceRendering.block
    && directF.table != planBuild.consts
    && planVM.lowering != planDirect.lowering
    && planVM.quotient.isSome && planVM.direct.isNone
    && planDirect.quotient.isNone && planDirect.direct.isSome
    && planNeither.quotient.isNone
    && (match planMemory.validate with | .ok _ => true | .error _ => false)

/-! ### GATE 6-7: `vm_quotient` and the `qprog` projection (hazard 4) -/

/-- PL:145-147. The VM plan answers; the Direct plan and the neither plan abort at the
    reference's own site, and the site string is the one the reference writes. -/
def vmQuotient_arms_ok : Bool :=
  (match planVM.vmQuotient with
   | .ok q => q.build.bytes.data.size == 23 && q.stackMptr == 0xA000
   | .error _ => false)
    && faultSite planDirect.vmQuotient
         == "proofs/solidity-verifier/src/lowering/plan.rs:146"
    && faultSite planNeither.vmQuotient
         == "proofs/solidity-verifier/src/lowering/plan.rs:146"

/-- REQUIRED FINDING (b), gated. `qprog` is FAULTING (PL:146's `expect`), `qprogOpt`
    is the total `Option` reading, and the two agree exactly where the reference does not
    abort. The bytes are the built program's, not a copy. -/
def qprog_projection_ok : Bool :=
  (match planVM.qprog with
   | .ok bs => bs == bytesToList planBuild.bytes && bs.length == 23
   | .error _ => false)
    && planVM.qprogOpt == planVM.qprog.toOption
    && faultSite planDirect.qprog == "proofs/solidity-verifier/src/lowering/plan.rs:146"
    && planDirect.qprogOpt == none
    && planNeither.qprogOpt == none

/-! ### GATES 8-10: the three `QuotientRendering` arms (hazard 2) -/

/-- PL:77-84. The Compact arm reads its OWN blocks; External and Direct read the pinned
    default. The three answers are pairwise different, which is what makes the arm split
    observable rather than decorative. -/
def helperFlags_threeArms_ok : Bool :=
  renderingCompact.helperFlags == { pow5 := true, limb7 := false, wideLimb7 := false }
    && (QuotientRendering.compact blocksLimb7Wide planProgram).helperFlags
         == { pow5 := false, limb7 := false, wideLimb7 := true }
    && renderingExternal.helperFlags == quotientComputationBlocksDefault.helperFlags
    && renderingDirect.helperFlags == quotientComputationBlocksDefault.helperFlags
    && renderingExternal.helperFlags != renderingCompact.helperFlags

/-- PL:79-81, the pin P-10 left for this package: the default's flags are all false, so
    BOTH non-compact arms inherit "no optional helper needed". If FoldTypes.lean:726 ever
    gains a field value, this reddens and the Direct path's shape changes with it. -/
def helperFlags_usesThePinnedDefault_ok : Bool :=
    quotientComputationBlocksDefault.helperFlags
      == { pow5 := false, limb7 := false, wideLimb7 := false }
    && renderingExternal.helperFlags
         == { pow5 := false, limb7 := false, wideLimb7 := false }
    && renderingDirect.helperFlags
         == { pow5 := false, limb7 := false, wideLimb7 := false }
    && (quotientComputationBlocksDefault.anyLineContains "q_pow5(") == false

/-- PL:87-110. Each arm fills exactly one of the four template slots, and the two arms that
    fill none of the blocks slot get the default blocks (PL:98, PL:105). -/
def intoTemplateParts_threeArms_ok : Bool :=
  let (e1, b1, p1, d1) := renderingExternal.intoTemplateParts
  let (e2, b2, p2, d2) := renderingCompact.intoTemplateParts
  let (e3, b3, p3, d3) := renderingDirect.intoTemplateParts
  b1 == quotientComputationBlocksDefault && b2 == blocksPow5
    && b3 == quotientComputationBlocksDefault
    && e1.isSome && e2.isNone && e3.isNone
    && p1.isNone && p2.isSome && p3.isNone
    && d1.isNone && d2.isNone && d3.isSome
    && d3.map (fun r => r.block) == some directF.rendering.block

/-! ### GATES 11-13: the rendering builders (PL:337-378) -/

/-- The injected emitter (PL:362 -> QRS:2000 is the blocked callee). All three arms, plus
    the trace/production choice PL:351-355 makes inside the Direct arm - which is only
    observable because the fixture's two renderings differ. -/
def quotientRendering_threeArms_ok : Bool :=
  let fake : LoweringPlan Unit Unit -> Bool -> QuotientComputationBlocks :=
    fun _ trace => if trace then blocksLimb7Wide else blocksPow5
  (match planVM.quotientRendering fake false false,
          planVM.quotientRendering fake true false,
          planVM.quotientRendering fake false true with
    | .ok (.compact b p), .ok (.compact b2 _), .ok (.external ext) =>
        b == blocksPow5 && b2 == blocksLimb7Wide
          && p.len == planBuild.bytes.data.size
          && ext.frameBase == 0x4000 && ext.magic == quotientExternalMagic
    | _, _, _ => false)
    && (match planDirect.quotientRendering fake false false with
        | .ok (.direct r) => r.block == directF.rendering.block
        | _ => false)
    && (match planDirect.quotientRendering fake true false with
        | .ok (.direct r) => r.block == directF.traceRendering.block
        | _ => false)
    && (match planNeither.quotientRendering fake false false with
        | .error _ => true
        | .ok _ => false)

/-- PL:368-378: the evaluator rendering has no Direct arm, so a direct plan faults here
    through `vm_quotient` rather than answering with the direct Yul. -/
def quotientEvaluatorRendering_ok : Bool :=
  (match planVM.quotientEvaluatorRendering (fun _ _ => blocksPow5) false with
   | .ok r => r.blocks == blocksPow5 && r.program.len == planProgram.len
               && r.program.programMptr == planProgram.programMptr
               && r.external.frameLen == (0x4000 + planVk.len) - 0x4000
   | .error _ => false)
    && (match planDirect.quotientEvaluatorRendering (fun _ _ => blocksPow5) false with
        | .error _ => true
        | .ok _ => false)

/-- QRS:760-794 via PL:381-389. `frame_len` is `max(vk_end, evals_end) - frame_base`:
    the fixture's evals end (0x100 + 21*32 = 0x3A0) is BELOW the VK end (0x4140), so the
    max takes the VK leg; flipping `numEvals` above it must take the evals leg. -/
def quotientExternalFrame_bounds_ok : Bool :=
  match planVM.quotientExternalFrame with
  | .ok ext => ext.frameBase == 0x4000 && ext.frameLen == planVk.len
                 && ext.outputLen == 2 * wordBytes + planVM.sortedSimple.length * wordBytes
                 && ext.magic == quotientExternalMagic
                 && ext.containsRange 0x4000 planVk.len
                 && ! ext.containsRange 0x4000 (planVk.len + 1)
  | .error _ => false
    && (match quotientExternalFrameFromBounds 0x4000 0x100 0x8000 0x40 3 with
        | { frameLen := fl, outputLen := ol, .. } => fl == 0x4800 && ol == 0xA0)
    && faultSite (planNeither.quotientExternalFrame) == "ok"

/-! ### GATES 14-16: the read model (PL:570-621) -/

/-- The four windows, in the Rust's order, with hand-computed bounds a reviewer can redo:
    `vk_payload` is `[vk_mptr, +vk.len)` = [0x4000, 0x4140); `user_challenges` is
    `[challenge_mptr, +sum num_user_challenges * 32)` and the fixture's list is `[0]`
    so the window is EMPTY (VmValidator.lean:459 rejects any pointer into a zero-length
    window); `challenge_and_common_slots` starts at `data.theta_mptr` and ends one word
    past `instance_eval_mptr` (PL:593-596's comment); `decoded_proof_evals` is
    `[reversed_evals_mptr, +num_evals * 32)`. -/
def quotientReadModel_windows_ok : Bool :=
  planModel.read.windows.length == 4
    && (planModel.read.windows.drop 0 |>.head?).map (fun w => (w.name, w.start, w.len))
         == some ("vk_payload", 0x4000, 320)
    && (planModel.read.windows.drop 1 |>.head?).map (fun w => (w.name, w.start, w.len))
         == some ("user_challenges", 0x2000, 0)
    && (planModel.read.windows.drop 2 |>.head?).map (fun w => (w.name, w.start, w.len))
         == some ("challenge_and_common_slots", 0x2200, 0x3020 - 0x2200)
    && (planModel.read.windows.drop 3 |>.head?).map (fun w => (w.name, w.start, w.len))
         == some ("decoded_proof_evals", 0x100, 21 * 32)
    && planModel.read.windowFor 0x140 == some "decoded_proof_evals"
    && planModel.read.windowFor 0x120 == some "decoded_proof_evals"
    && planModel.read.windowFor 0x2000 == none
    && planModel.read.windowFor 0x4140 == none

/-- The nine token bases in PL:607-619's order, each resolving to the address the layout
    names. `tokenBase` is VmValidator.lean:482's first-match lookup. -/
def quotientReadModel_tokenBases_ok : Bool :=
  planModel.read.tokenBases.length == 9
    && planModel.read.tokenBases.map Prod.fst
         == [qMemL0, qMemLLast, qMemLBlind, qMemBeta, qMemGamma, qMemX, qMemTheta,
             qMemTrashChallenge, qMemInstanceEval]
    && planModel.read.tokenBase qMemInstanceEval == some 0x3000
    && planModel.read.tokenBase qMemTheta == some 0x2400
    && planModel.read.tokenBase 0x20 == none

/-- PL:577 vs PL:613: the `challenge_and_common_slots` window starts at
    `data.theta_mptr` (0x2200) while the `Q_MEM_THETA` token base is
    `memory.theta_mptr` (0x2400). The fixture deliberately makes them differ so a port
    that "unifies" the two reddens here instead of silently validating a different window. -/
def quotientReadModel_twoThetas_ok : Bool :=
  (ptrValue planMemory.thetaMptr).asUsizeNat != (ptrValue dataF.thetaMptr).asUsizeNat
    && (planModel.read.windows.drop 2 |>.head?).map (fun w => w.start) == some 0x2200
    && planModel.read.tokenBase qMemTheta == some 0x2400

/-! ### GATES 17-18: the operand model (PL:626-643) -/

/-- Each bound comes from the field PL:637-641 names, and from nowhere else:
    `num_consts` from the build, `num_selector_buckets` from the meta,
    `selector_max_power` from the fold plan, `stack_words` from the planned region. -/
def quotientOperandModel_bounds_ok : Bool :=
  planModel.numConsts == planBuild.consts.length
    && planModel.numSelectorBuckets == planMeta.numSimpleSelectors
    && planModel.selectorMaxPower == planPlan.selectorFold.maxPower
    && planModel.stackWords == (planMemory.quotientStackHi - planMemory.quotientStackMptr)
                                 / wordBytes
    && planModel.read.windows == (match quotientReadModel planMeta dataF planVk planVkMptr
                                             planMemory with
                                   | .ok r => r.windows
                                   | .error _ => [])
    && (match quotientOperandModel { planMeta with numSimpleSelectors := 7 } dataF planVk
              planVkMptr planMemory planBuild planPlan.selectorFold with
        | .ok m => m.numSelectorBuckets == 7 && m.numConsts == 2
        | .error _ => false)

/-- R5 at the site (header): an inverted stack region is a wrapping subtraction in the
    reference and a truncating one here, so the port reports 0 words. Pinned rather than
    hidden, because a 0-word region makes every stack check reject - which is the safe
    direction and is what `supportedQvm_rejectsEachBrokenBound_ok` leans on. -/
def quotientOperandModel_stackWords_ok : Bool :=
  (match quotientOperandModel planMeta dataF planVk planVkMptr
              { planMemory with quotientStackHi := 0x9FFF } planBuild
              planPlan.selectorFold with
   | .ok m => m.stackWords == 0
   | .error _ => false)
    && (match quotientOperandModel planMeta dataF planVk planVkMptr
                  { planMemory with quotientStackHi := 0xA060 } planBuild
                  planPlan.selectorFold with
       | .ok m => m.stackWords == 3
       | .error _ => false)

/-! ### GATE 19: the guard constants (QRS:242-256) -/

/-- The three guards come from the model, not from the layout: `const_max` is
    `num_consts - 1` (saturating), `stack_last` is `hi - 32`, and the
    `assert_eq!`'s precondition is exactly the identity PL:640 used to size the region,
    so it holds by construction here and faults when the two are pulled apart. -/
def quotientVmGuards_agreesWithModel_ok : Bool :=
  (match quotientVmGuards planModel planMemory with
   | .ok g => g.constMax == planModel.numConsts - 1
                && g.numSelectorBuckets == planModel.numSelectorBuckets
                && g.stackLast == planMemory.quotientStackHi - wordBytes
                && g == planProgram.guards
   | .error _ => false)
    && faultSite (quotientVmGuards { planModel with stackWords := 4 } planMemory)
         == "proofs/solidity-verifier/src/lowering/quotient.rs:246"
    && (match quotientVmGuards { planModel with numConsts := 0 } planMemory with
        | .ok g => g.constMax == 0
        | .error _ => false)

/-! ### GATES 20-21: the `Supported.qvm` bridge (hazard 3, required finding (a)) -/

/-- THE BRIDGE. The model PL:626-643 builds from the converged plan validates the plan's
    own emitted bytecode - the reference's QVM-01 predicate, in one argument, over a
    program P-09c's builder really emitted. This is what P-09e could not write: it had the
    predicate and a hand-built model but no way to get the model from a plan. -/
def supportedQvm_bridgeAcceptsTheBuiltProgram_ok : Bool :=
  planVM.supportedQvmBool
    && (match planVM.qprog, planVM.quotientOperandModel with
        | .ok bs, .ok model =>
            match validateQuotientProgramOperands bs model with
            | .ok _ => true
            | .error e => false
        | _, _ => false)

/-- The same predicate with ONE bound broken at a time: too few stack words, too few
    selector buckets, too small a `y` power, too short a constant table, and a read
    window that no longer covers the program's pointers. Each of the five must reject, and
    the unbroken fixture must accept - so none of the five bounds is decorative. -/
def supportedQvm_rejectsEachBrokenBound_ok : Bool :=
  let broken : List (LoweringPlan Unit Unit × String) :=
    [ ({ planVM with memory := { planMemory with quotientStackHi := 0xA000 } },
        "stack region"),
      ({ planVM with meta_ := { planMeta with numSimpleSelectors := 1 } },
        "selector bucket 1 is outside the 1-bucket table"),
      ({ planVM with meta_ := { planMeta with numSimpleSelectors := 0 } },
        "selector bucket"),
      ({ planVM with quotient := some { plannedQ with plan :=
          { planPlan with selectorFold := { planPlan.selectorFold with maxPower := 0 } } } },
        "gap 5"),
      ({ planVM with quotient := some { plannedQ with build :=
          { planBuild with consts := [11] } } },
        "const slot"),
      ({ planVM with memory := { planMemory with
          reversedEvalsMptr := ptrMemory (valueFromNat 0x5000) } },
        "outside every read window"),
      ({ planVM with vkMptr := ptrMemory (Value.identifier "vk" 0) },
        "the model itself cannot be built")]
  broken.length == 7
    && broken.all fun (l, why) => ! l.supportedQvmBool && why != ""
    && planVM.supportedQvmBool

/-- The Direct arm of PLAN 9.5's repaired `qvm` field: True, because PL:224 stores
    `quotient: None` and there is no program to validate. Gated so the arm cannot be
    silently dropped. -/
def supportedQvm_directArm_isTrue_ok : Bool :=
  planDirect.supportedQvmBool && ! planNeither.supportedQvmBool

/-! ### GATES 22-25: the invariant checker (PL:413-523) -/

/-- THE HEADLINE GATE. All sixteen checks pass on the converged fixture, which means: the
    protocol meta agrees with its plan, the memory layout validates, the absorbed-G1
    coverage holds against the proof layout, the PCS sizing did not drift, the program
    length / reservations / stack and state pointers agree with the build, QVM-01 accepts
    the emitted bytecode against the model built from the same fields, the rendered guards
    agree with PL:507's recomputation, and `certifyQuotientProgram` really ran the
    interpreter over the real bytecode and matched the planned identities. Dropping,
    reordering or inverting any check reddens a gate below. -/
def validateGeneratorInvariants_acceptsTheConvergedFixture_ok : Bool :=
  invResult planVM == "ok" && invResult planDirect == "ok"

/-- Each String-layer arm of the VM path, fired one at a time, with the reference's own
    message. The order is load-bearing: PL:462's length check must fire before PL:504's
    operand validation, so the `len := 0` perturbation reports the length message even
    though it also breaks the operand bounds. -/
def validateGeneratorInvariants_eachVmArmFires_ok : Bool :=
  let cases : List (LoweringPlan Unit Unit × String) :=
    [ ({ planVM with meta_ := constraintSystemMetaDefault },
        "protocol invariant failed: "),
      ({ planVM with memory := { planMemory with transcriptMptr := 0 } },
        "memory-region non-overlap invariant failed: "),
      ({ planVM with data := { dataF with
          adviceComms := dataF.adviceComms ++ [EcPoint.new (ptrMemory (valueFromNat 0x1234))] } },
        "absorbed-G1 precompile coverage invariant failed: "),
      ({ planVM with pcsMemoryRequirements := { (pcsMemoryRequirementsDefault) with
                                                rotPointsWords := 999 } },
        "PCS memory requirements drifted: planned "),
      ({ planVM with quotient := some { plannedQ with program := { planProgram with len := 0 } } },
        "quotient program length drifted: model=0 build=23"),
      ({ planVM with vk := { planVk with quotientConstWords := 1 } },
        "quotient const table exceeds VK reservation: consts=2 words=1"),
      ({ planVM with vk := { planVk with quotientProgramWords := 0 } },
        "quotient bytecode exceeds VK reservation: program_words=1 reserved=0"),
      ({ planVM with quotient := some { plannedQ with stackMptr := 0xA020 } },
        "quotient stack pointer drifted: model=0xa000 planned=0xa020"),
      ({ planVM with quotient := some { plannedQ with program :=
          { planProgram with evalNumerMptr := 0xB040 } } },
        "quotient state pointer drifted: model=0xb040 planned=0xb000"),
      ({ planVM with quotient := some { plannedQ with build := { planBuild with consts := [] } } },
        "quotient VM operand validation failed: "),
      ({ planVM with memory := { planMemory with quotientStackHi := 0xA000 } },
        "quotient VM operand validation failed: "),
      ({ planVM with quotient := some { plannedQ with program :=
          { planProgram with
            guards := { constMax := 99, numSelectorBuckets := 99, stackLast := 99 } } } },
        "quotient VM runtime guards drifted from the operand model: rendered "),
      ({ planVM with quotient := some { plannedQ with build := { planBuild with consts := [11, 12] } } },
        "quotient program certification failed: ")]
  cases.length == 13 && cases.all fun (l, want) => msgStarts l want

/-- The four Direct-arm checks (PL:434-458), each fired alone, plus the arm that PL:451-458
    takes when the offset is absent (`unwrap_or(usize::MAX)`, so no VK word matches and
    word 0 is reported). -/
def validateGeneratorInvariants_directArms_ok : Bool :=
  invResult { planDirect with quotient := some plannedQ }
    == "direct plan also carries a compact VM plan"
    && invResult { planDirect with lowering := QuotientLowering.vm }
         == "direct plan also carries a compact VM plan"
    && invResult { planDirect with vk := { planDirect.vk with
                                           quotientProgramWords := 1 } }
         == "direct lowering must not reserve VM program words (got 1)"
    && invResult { planDirect with vk := { planDirect.vk with
                                           quotientConstWords := 3 } }
         == "direct constant table drifted: VK reserves 3 words, program has 2"
    && invResult { planDirect with vk := { planDirect.vk with
                                           quotientConstOffsetWords := none } }
         == "direct constant table word 0 differs from the VK payload"
    && invResult { planDirect with direct := some { directF with table := [101, 77] } }
         == "direct constant table word 1 differs from the VK payload"

/-- Where the reference aborts, the port reports a Fault: a plan with no quotient payload
    reaches PL:461's `self.vm_quotient()` and panics at PL:146 - it does NOT degrade to
    a String error (R4). The symbolic-pointer panic is PL:577's, reached through
    `Value::as_usize` at ENC:599. -/
def validateGeneratorInvariants_faultsWhereTheReferencePanics_ok : Bool :=
  invResult planNeither
    == "PANIC proofs/solidity-verifier/src/lowering/plan.rs:146"
    && msgStarts ({ planVM with vkMptr := ptrMemory (Value.identifier "vk" 0) })
         "PANIC proofs/solidity-verifier/src/lowering/encoding/mod.rs:599"
    && faultSite (planVM.quotientOperandModel) == "ok"

/-- The two Debug renderers PL:430 and PL:510 interpolate. Pinned against the reference's
    own shape: struct name, Rust field names, nested structs inline. -/
def debugRenderers_matchTheRustShape_ok : Bool :=
  pcsMemoryRequirementsDebug pcsMemoryRequirementsDefault
    == "PcsMemoryRequirements { rotPointsWords: 0, x1PowersWords: 0, qComWords: 0, " ++
       "qEvalSetWords: 0, qEvalSourceTableWords: 0, qComTraceMsm: FinalMsmShape " ++
       "{ terms: 0, inputBytes: 0 }, finalMsm: FinalMsmShape { terms: 0, inputBytes: 0 } }"
    && quotientVmGuardsDebug { constMax := 1, numSelectorBuckets := 2, stackLast := 0xA000 }
         == "QuotientVmGuards { const_max: 1, num_selector_buckets: 2, stack_last: 40960 }"

/-- The hand-written PCS comparator (Layout.lean:885 has no `BEq`): every field must
    participate, so a drift in any one of the nine is caught. -/
def pcsMemoryRequirementsBeq_distinguishesEveryField_ok : Bool :=
  let base := match memoryRequirements planMeta dataF with
              | .ok p => p
              | .error _ => pcsMemoryRequirementsDefault
  let variants : List PcsMemoryRequirements :=
    [ { base with rotPointsWords := base.rotPointsWords + 1 },
      { base with x1PowersWords := base.x1PowersWords + 1 },
      { base with qComWords := base.qComWords + 1 },
      { base with qEvalSetWords := base.qEvalSetWords + 1 },
      { base with qEvalSourceTableWords := base.qEvalSourceTableWords + 1 },
      { base with qComTraceMsm := { base.qComTraceMsm with terms := base.qComTraceMsm.terms + 1 } },
      { base with qComTraceMsm := { base.qComTraceMsm with
                                    inputBytes := base.qComTraceMsm.inputBytes + 1 } },
      { base with finalMsm := { base.finalMsm with terms := base.finalMsm.terms + 1 } },
      { base with finalMsm := { base.finalMsm with
                                inputBytes := base.finalMsm.inputBytes + 1 } } ]
  variants.length == 9 && variants.all (fun v => ! pcsMemoryRequirementsBeq base v)
    && pcsMemoryRequirementsBeq base base

/-! ### GATES 26-27: the remaining accessors -/

/-- PL:332-334: the repacking plan is the same three numbers the proof layout already
    carries (QVM:177-187), so a plan and its layout cannot disagree. -/
def repackedProofLayoutPlan_agreesWithTheLayout_ok : Bool :=
  planVM.repackedProofLayoutPlan.numEvals == proofLayoutF.evals.itemCount
    && planVM.repackedProofLayoutPlan.numPointSets == proofLayoutF.qEvals.itemCount
    && planVM.repackedProofLayoutPlan.g1Groups == proofLayoutF.commitmentReadGroups
    && planVM.repackedProofLayoutPlan.prefixG1Count
         == proofLayoutF.commitmentReadGroups.foldl (fun a b => a + b) 0

/-- PL:552-562, three arms: no encoding gives 0 terms; a valid encoding gives
    `fixed_scalar_count + 1` (the extra term is the accumulator point itself); and an
    encoding that `fixedScalarCount` rejects ABORTS at PL:558 rather than planning a wrong
    region. D-P16: the encoding is the GENERATOR record, and the fixture is this package's own
    copy of the reference shape (offset 4, 7 limbs of 56 bits, point-and-scalar) - the same
    numbers Api.lean:1195-1203 gates, so the +1 arm and the abort arm are both reachable.
    Note the 19: at the reference fixture's own length of 3 even the point-and-scalar arm fails
    check, which is the second abort case below. -/
def accMsmTerms_threeArms_ok : Bool :=
  (match accMsmTerms (some accPs) 19 with
   | .ok n => n == 4
   | .error _ => false)
    && (match accMsmTerms none 19 with | .ok n => n == 0 | .error _ => false)
    && faultSite (accMsmTerms (some accPair) 19)
         == "proofs/solidity-verifier/src/lowering/plan.rs:558"
    && faultSite (accMsmTerms (some accPair) 3)
         == "proofs/solidity-verifier/src/lowering/plan.rs:558"
    && faultSite (accMsmTerms (some accPs) 3)
         == "proofs/solidity-verifier/src/lowering/plan.rs:558"
  where
    accPs : Midfall.Generator.AccumulatorEncoding :=
      { offset := 4, numLimbs := 7, numLimbBits := 56,
        kind := Midfall.Generator.AccumulatorEncodingKind.pointAndScalar }
    accPair : Midfall.Generator.AccumulatorEncoding :=
      { accPs with kind := Midfall.Generator.AccumulatorEncodingKind.pointPair }

end Midfall.Generator.LoweringPlanKats

#eval Midfall.Generator.LoweringPlanKats.planArtifactReachable_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.panicSites_areTheRecordedOnes_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.configConstants_matchConfigRs_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.qdirRecords_areTheCarvedOutOnes_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.loweringPlanFixture_nonDegenerate_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.vmQuotient_arms_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.qprog_projection_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.helperFlags_threeArms_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.helperFlags_usesThePinnedDefault_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.intoTemplateParts_threeArms_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientRendering_threeArms_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientEvaluatorRendering_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientExternalFrame_bounds_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientReadModel_windows_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientReadModel_tokenBases_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientReadModel_twoThetas_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientOperandModel_bounds_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientOperandModel_stackWords_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.quotientVmGuards_agreesWithModel_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.supportedQvm_bridgeAcceptsTheBuiltProgram_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.supportedQvm_rejectsEachBrokenBound_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.supportedQvm_directArm_isTrue_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.validateGeneratorInvariants_acceptsTheConvergedFixture_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.validateGeneratorInvariants_eachVmArmFires_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.validateGeneratorInvariants_directArms_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.validateGeneratorInvariants_faultsWhereTheReferencePanics_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.debugRenderers_matchTheRustShape_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.pcsMemoryRequirementsBeq_distinguishesEveryField_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.repackedProofLayoutPlan_agreesWithTheLayout_ok -- expect true
#eval Midfall.Generator.LoweringPlanKats.accMsmTerms_threeArms_ok -- expect true
