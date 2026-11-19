-- |
-- Midfall.Instances.QvmFamilyKats
--
-- QEMIT (PG-Q-OBJECT): the acceptance gates for the AST twins of the generated line families in
-- 'Midfall/Lowering/GenAstQvmFamilies.lean'. The pattern is OBJ.14's and OBJ.15's, copied exactly:
-- 'stmtsBeq' against the parse at BOTH contexts, plus teeth that stop the tie from being
-- equal-but-vacuous, plus field-reach gates that stop the emitter from being a transcribed copy of
-- the fixture. 'native_decide' lives nowhere in this file (D-P71): every gate is a 'Bool' the VM
-- computes.
--
-- THE TWO CONTEXTS, AND WHY THE SECOND ONE IS NOT THE ALL-ARMS CONTEXT. For the interpreter
-- template the two contexts are the fixture and every 'opUsage' flag on, because the flags hide
-- twenty-one arms. The line families do not read the flags at all - 'qvmAllArms' carries the same
-- families as 'ctx', which is a clause below and not an assumption - so the second context has to
-- be a context where the families really differ. There are two such contexts in the tree: the
-- artifact-sliced families the deployed 'PartialCtx' carries, and the families the DERIVED
-- generator run produces. They differ in the inline family's BLOCK PARTITION - one block of 99
-- lines against four of 44/20/17/18 (GeneratedKats gate 8) - so a twin that ties to both is not
-- keying on the fixture's slicing. The third context, with teeth on the fold, is 'trace := true',
-- which the template's fence excludes but the producers do not.
--

import Midfall.Instances.M2BatchKats
import Midfall.Instances.GeneratedKats
import Midfall.Lowering.GenAstQvmFamilies
import Midfall.Instances.ObjectFingerprint

set_option autoImplicit false

namespace Midfall.Instances.QvmFamilyKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientFold
open Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientBlocks
open Midfall.Generator.QuotientEvaluator Midfall.Generator.PlanNew
open Midfall.Instances Midfall.Instances.M2BatchKats Midfall.Instances.GeneratedKats
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.Lowering Midfall.Lowering.GenAst Midfall.Lowering.YulParse
open Midfall.LoweringV2
open Midfall.Halo2
open YulSemantics YulSemantics.EVM

/-- How many times a variable name occurs anywhere in a tree: used to pin that the trash challenge
    is loaded ONCE for the whole block, which is the one place this producer differs from the
    Evaluator's own trashcan path. -/
def countName (nm : String) (b : Block EVM.Op) : Nat :=
  ((EVM.print b).splitOn nm).length - 1

/-! ## The inputs the twins consume -/

/-- The generator run at the fixture, or 'none' on any fault: every gate below reddens rather than
    passing on a default. -/
def genOut? : Option GenOut :=
  match gen with | .ok o => some o | .error _ => none

def pq? : Option PlannedQuotient := match genOut? with | some o => qOf o | none => none

/-- THE PLAN IS THERE, AND EVERY GATE BELOW RUNS ON IT. -/
def qemPlanPresent_ok : Bool := genOut?.isSome && pq?.isSome && poseidonVkExec.cs.gates.size == 5
#eval qemPlanPresent_ok -- expect true

def inlineIds : List QuotientIdentity := (pq?.map fun q => q.plan.inlineIdentities).getD []
def nativeIds : List QuotientIdentity := (pq?.map fun q => q.plan.nativeIdentities).getD []
def foldPlan : SelectorFoldPlan :=
  (pq?.map fun q => q.plan.selectorFold).getD selectorFoldPlanDefault
def scratchSlot : Nat := (pq?.map fun q => q.stackMptr).getD 0
def stateSlots : QuotientStateSlots :=
  (pq?.map fun q => q.stateSlots).getD { evalNumerMptr := 0, traceIdMptr := 0,
                                         selectorPowerMptr := 0 }

/-- The Evaluator the family producers are built with: the same field dictionary, the same
    constraint system, the same meta and data, and 'with_pow5_helper(true)', exactly as
    compact_quotient_computation_blocks constructs it (QuotientBlocks.lean:862). -/
def famEv : Evaluator (Fr Yul.blsR) :=
  (Evaluator.new (frFieldCtx delta) poseidonVkExec.cs
    ((genOut?.map fun o => o.plan.meta_).getD poseidonPlanV2.meta_)
    ((genOut?.map fun o => o.plan.data).getD poseidonPlanV2.data)).withPow5Helper true

/-- THE PRODUCER, RUN ON DEMAND: the text side of every tie below is the producer's own output on
    the inputs handed to it, not a transcription of the fixture's lines. -/
def producerDirect (ids : List QuotientIdentity) (fold : SelectorFoldPlan) (sc : Nat)
    (sl : QuotientStateSlots) (tr : Bool) : Block EVM.Op :=
  match ids.mapM (fun id =>
      directQuotientBlock id.lines id.var id.target (fold.gapFor id) sc sl tr) with
  | .ok bs => qGenNested bs
  | .error _ => []

def producerTrash (sl : QuotientStateSlots) (tr : Bool) (ev : Evaluator (Fr Yul.blsR)) :
    Option (Block EVM.Op) :=
  match (structuredTrashLoopBlock (StructuredFold.horner sl tr) 0).run
      { ev := ev, block := [], sites := [] } with
  | .ok (some ls, _) => some (qGenFlat ls)
  | .ok (none, _) => none
  | .error _ => none

/-- The families are FLAG-INDEPENDENT, which is why the all-arms context is stated as a clause and
    not assumed: 'qvmAllArms' changes 'opUsage' and 'memUsage' only. -/
def qemFamiliesIgnoreTheFlags_ok : Bool :=
  qvmAllArms.quotientInlineComputations == ctx.quotientInlineComputations &&
    qvmAllArms.quotientPostVmComputations == ctx.quotientPostVmComputations &&
    qvmAllArms.quotientNativeIdentityComputations == ctx.quotientNativeIdentityComputations &&
    qvmAllArms.quotientNativePermutationComputation == ctx.quotientNativePermutationComputation &&
    qvmAllArms.quotientNativeLookupComputation == ctx.quotientNativeLookupComputation

/-! ## Family 1: the DIRECT INLINE PREFIX ('quotientInlineComputations') -/

/-- ACCEPTANCE 1 OF 3 (THE DEPLOYMENT): the inline family as the artifact slice parses it IS the
    tree 'qEmitInlineFamily' builds from the plan's inline identities. -/
def qemInline_isTheParse_ok : Bool :=
  SyntaxEq.stmtsBeq (qGenNested ctx.quotientInlineComputations)
    (qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false) &&
    (yulTokens (String.intercalate "\n" (ctx.quotientInlineComputations.flatten))).length == 895
#eval qemInline_isTheParse_ok -- expect true

/-- ACCEPTANCE 2 OF 3 (THE DERIVED RUN, a different block partition): the same tree ties to the
    producer's own four-block text AND to the artifact's one-block text, so the emitter is not
    keying on the fixture's slicing. -/
def qemInline_isTheParseDerived_ok : Bool :=
  match genOut? with
  | none => false
  | some o =>
      (o.qblocks.inlineComputations.map fun (l : List String) => l.length) == [44, 20, 17, 18] &&
        (ctx.quotientInlineComputations.map fun (l : List String) => l.length) == [99] &&
        SyntaxEq.stmtsBeq (qGenNested o.qblocks.inlineComputations)
          (qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false) &&
        SyntaxEq.stmtsBeq (producerDirect inlineIds foldPlan scratchSlot stateSlots false)
          (qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false)
#eval qemInline_isTheParseDerived_ok -- expect true

/-- ACCEPTANCE 3 OF 3 (THE ALL-ARMS CONTEXT): the tie holds there too, and the clause above says
    why it is the same text rather than a coincidence. -/
def qemInline_allArms_ok : Bool :=
  qemFamiliesIgnoreTheFlags_ok &&
    SyntaxEq.stmtsBeq (qGenNested qvmAllArms.quotientInlineComputations)
      (qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false)
#eval qemInline_allArms_ok -- expect true

/-- TEETH (INLINE), ON THE TEXT: three SCAFFOLDING tokens mutated in the family text redden the tie
    - the scratch store, the selector pointer, and the fold's y-advance. A twin that merely echoed
    the parse would keep the tie; these redden it, which is what makes the tie a statement about the
    emitter. -/
def qemInline_teethText_ok : Bool :=
  let t := String.intercalate "\n" (ctx.quotientInlineComputations.flatten)
  let ast := qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false
  let t1 := mutateFirst "mstore(0x6960," "mstore(0x6961," t
  let t2 := mutateFirst "q_selector_acc" "q_selector_acc2" t
  let t3 := mutateFirst "mulmod(mload(0x6660), y, r)" "mulmod(mload(0x6660), y, r2)" t
  SyntaxEq.stmtsBeq (reg t) ast && ! SyntaxEq.stmtsBeq (reg t1) ast &&
    ! SyntaxEq.stmtsBeq (reg t2) ast && ! SyntaxEq.stmtsBeq (reg t3) ast &&
    t != t1 && t != t2 && t != t3
#eval qemInline_teethText_ok -- expect true

/-- THE EMITTER IS NOT THE PARSE IN DISGUISE: drop the scaffolding and the twin is a strictly
    different tree from the parse of the identities' own expression lines. If the twin were only
    re-splicing 'id.lines' this would be true-by-accident; it is false, which says the braces, the
    scratch store, the fold and the selector update are really being emitted. -/
def qemInline_emitsMoreThanTheLines_ok : Bool :=
  let innerOnly := qGenNested (inlineIds.map fun id => id.lines)
  let ast := qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false
  ! SyntaxEq.stmtsBeq innerOnly ast && ast.length == 3 * inlineIds.length &&
    inlineIds.length == 4 && (yulTokens (EVM.print ast)).length > 895
#eval qemInline_emitsMoreThanTheLines_ok -- expect true

/-- FIELD REACH (INLINE): each input the producer interpolates is perturbed on its own. The twin
    must still tie to the PRODUCER at the perturbed input (so the field is read the way the text
    port reads it) and the emitted tree must move (so the field is not a fixture value). -/
def qemInline_fieldsReach_ok : Bool :=
  let base := qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false
  let tie (ids : List QuotientIdentity) (fold : SelectorFoldPlan) (sc : Nat)
      (sl : QuotientStateSlots) (tr : Bool) : Bool :=
    SyntaxEq.stmtsBeq (producerDirect ids fold sc sl tr)
      (qEmitInlineFamily ids fold sc sl tr)
  let moves (ids : List QuotientIdentity) (fold : SelectorFoldPlan) (sc : Nat)
      (sl : QuotientStateSlots) (tr : Bool) : Bool :=
    ! SyntaxEq.stmtsBeq (qEmitInlineFamily ids fold sc sl tr) base
  tie inlineIds foldPlan (scratchSlot + 0x20) stateSlots false &&
    moves inlineIds foldPlan (scratchSlot + 0x20) stateSlots false &&
    tie inlineIds foldPlan scratchSlot { stateSlots with evalNumerMptr := stateSlots.evalNumerMptr + 0x20 } false &&
    moves inlineIds foldPlan scratchSlot { stateSlots with evalNumerMptr := stateSlots.evalNumerMptr + 0x20 } false &&
    tie inlineIds foldPlan scratchSlot { stateSlots with selectorPowerMptr := stateSlots.selectorPowerMptr + 0x20 } false &&
    moves inlineIds foldPlan scratchSlot { stateSlots with selectorPowerMptr := stateSlots.selectorPowerMptr + 0x20 } false &&
    tie inlineIds foldPlan scratchSlot stateSlots true &&
    moves inlineIds foldPlan scratchSlot stateSlots true &&
    tie (inlineIds.reverse) foldPlan scratchSlot stateSlots false &&
    moves (inlineIds.reverse) foldPlan scratchSlot stateSlots false &&
    tie (inlineIds.drop 1) foldPlan scratchSlot stateSlots false &&
    moves (inlineIds.drop 1) foldPlan scratchSlot stateSlots false &&
    (match inlineIds with
     | [] => false
     | id :: rest =>
         tie ({ id with var := id.var ++ "z" } :: rest) foldPlan scratchSlot stateSlots false &&
           moves ({ id with var := id.var ++ "z" } :: rest) foldPlan scratchSlot stateSlots false)
#eval qemInline_fieldsReach_ok -- expect true

/-- THE TARGET ARM IS REACHED, NOT ASSUMED: the inline family carries both a main identity and a
    selector identity at the deployment, and flipping one identity's target moves the tree while
    the tie to the producer still holds. A twin that emitted only the main arm would pass every
    gate above at a main-only family and fail this. -/
def qemInline_targetsReach_ok : Bool :=
  let nSel := inlineIds.filter fun id =>
    match id.target with | QuotientTarget.selector _ => true | _ => false
  let nMain := inlineIds.filter fun id =>
    match id.target with | QuotientTarget.main => true | _ => false
  let tie (ids : List QuotientIdentity) : Bool :=
    SyntaxEq.stmtsBeq (producerDirect ids foldPlan scratchSlot stateSlots false)
      (qEmitInlineFamily ids foldPlan scratchSlot stateSlots false)
  let moves (ids : List QuotientIdentity) : Bool :=
    ! SyntaxEq.stmtsBeq (qEmitInlineFamily ids foldPlan scratchSlot stateSlots false)
      (qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false)
  nSel.length == 4 && nMain.length == 0 && tie inlineIds &&
    tie (inlineIds.map fun id => { id with target := QuotientTarget.main }) &&
    moves (inlineIds.map fun id => { id with target := QuotientTarget.main }) &&
    tie (inlineIds.map fun id =>
      match id.target with
      | QuotientTarget.selector k => { id with target := QuotientTarget.selector (k + 1) }
      | t => { id with target := t }) &&
    moves (inlineIds.map fun id =>
      match id.target with
      | QuotientTarget.selector k => { id with target := QuotientTarget.selector (k + 1) }
      | t => { id with target := t })
#eval qemInline_targetsReach_ok -- expect true

/-- THE PANIC ARM IS NOT TAKEN: 'direct_quotient_block' releases when a selector identity has no
    gap, and the twin emits nothing there. Every selector-target identity the compact path reaches
    has a gap, so the fallback is a documented totaliser and not a live divergence. -/
def qemGapPanicArmUnused_ok : Bool :=
  (inlineIds ++ nativeIds).all fun id =>
    match id.target with
    | QuotientTarget.selector _ => (foldPlan.gapFor id).isSome
    | QuotientTarget.main => true &&
        (match id.target with | QuotientTarget.main => true | _ => false)
#eval qemGapPanicArmUnused_ok -- expect true

/-- THE GAP VALUE REACHES THE TREE: a non-zero gap emits the power read and a zero gap does not, and
    the twin follows the producer in both cases. -/
def qemInline_gapReaches_ok : Bool :=
  let sels := inlineIds.filter fun id =>
    match id.target with | QuotientTarget.selector _ => true | _ => false
  sels.all fun id =>
    let one (g : Option Nat) :=
      SyntaxEq.stmtsBeq
        (match directQuotientBlock id.lines id.var id.target g scratchSlot stateSlots false with
         | .ok ls => qGenFlat ls
         | .error _ => [])
        (qEmitDirectBlock id.lines id.var id.target g scratchSlot stateSlots false)
    one (foldPlan.gapFor id) && one (some 0) && one (some 3) &&
      ! SyntaxEq.stmtsBeq (qEmitDirectBlock id.lines id.var id.target (some 0) scratchSlot stateSlots false)
        (qEmitDirectBlock id.lines id.var id.target (some 3) scratchSlot stateSlots false)
#eval qemInline_gapReaches_ok -- expect true

/-! ## Family 2: the NATIVE IDENTITY bodies ('quotientNativeIdentityComputations') -/

/-- ACCEPTANCE 1 OF 3 (THE DEPLOYMENT). -/
def qemNativeId_isTheParse_ok : Bool :=
  SyntaxEq.stmtsBeq (qGenNested ctx.quotientNativeIdentityComputations)
    (qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false) &&
    (yulTokens (String.intercalate "\n" (ctx.quotientNativeIdentityComputations.flatten))).length == 1044
#eval qemNativeId_isTheParse_ok -- expect true

/-- ACCEPTANCE 2 OF 3 (THE DERIVED RUN): the producer's own text, three blocks of 37. -/
def qemNativeId_isTheParseDerived_ok : Bool :=
  match genOut? with
  | none => false
  | some o =>
      (o.qblocks.nativeIdentityComputations.map fun (l : List String) => l.length) == [37, 37, 37] &&
        SyntaxEq.stmtsBeq (qGenNested o.qblocks.nativeIdentityComputations)
          (qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false) &&
        SyntaxEq.stmtsBeq (producerDirect nativeIds foldPlan scratchSlot stateSlots false)
          (qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false)
#eval qemNativeId_isTheParseDerived_ok -- expect true

/-- ACCEPTANCE 3 OF 3 (THE ALL-ARMS CONTEXT), AND THE CASE LIST THE TEMPLATE CONSUMES: the labels
    are the block indices in list order and the bodies are the family's blocks, so the switch the
    twin builds is the switch 'qvmNativeArms' splices - which is the tie to OBJ.15 this card has to
    keep. -/
def qemNativeId_allArmsAndCases_ok : Bool :=
  SyntaxEq.stmtsBeq (qGenNested qvmAllArms.quotientNativeIdentityComputations)
    (qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false) &&
    (qEmitNativeIdentityCases nativeIds foldPlan scratchSlot stateSlots false).map (fun c => c.fst) ==
      [Literal.number 0, Literal.number 1, Literal.number 2] &&
    SyntaxEq.stmtsBeq
      ((qEmitNativeIdentityCases nativeIds foldPlan scratchSlot stateSlots false).map Prod.snd).flatten
      (qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false) &&
    (match ctx.quotientProgram with
     | none => false
     | some p =>
         let cases := switchCasesOn "q_native_idx" (GenAst.emitQuotientNumeratorA qvmAllArms)
         cases.length == nativeIds.length &&
           (cases.zip (qEmitNativeIdentityCases nativeIds foldPlan scratchSlot stateSlots false)).all
             fun (a, b) => a.fst == b.fst && SyntaxEq.stmtsBeq (a.snd : Block EVM.Op) b.snd &&
               p.opUsage.nativeIdentity)
#eval qemNativeId_allArmsAndCases_ok -- expect true

/-- TEETH (NATIVE IDENTITY): a scaffolding token of the family text reddens the tie, and dropping
    one identity from the list moves the case list by exactly one case. -/
def qemNativeId_teeth_ok : Bool :=
  let t := String.intercalate "\n" (ctx.quotientNativeIdentityComputations.flatten)
  let ast := qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false
  (SyntaxEq.stmtsBeq (reg t) ast &&
    ! SyntaxEq.stmtsBeq (reg (mutateFirst "q_selector_ptr" "q_selector_ptr9" t)) ast &&
    ! SyntaxEq.stmtsBeq (reg (mutateFirst "mstore(0x6960," "mstore(0x6962," t)) ast) &&
  (qEmitNativeIdentityCases (nativeIds.drop 1) foldPlan scratchSlot stateSlots false).length ==
    nativeIds.length - 1 &&
    ! SyntaxEq.stmtsBeq
      (qEmitNativeIdentityFamily (nativeIds.drop 1) foldPlan scratchSlot stateSlots false) ast &&
    t != mutateFirst "q_selector_ptr" "q_selector_ptr9" t
#eval qemNativeId_teeth_ok -- expect true

/-- THE SWITCH IS A SWITCH: the twin's case list, spliced into the template's switch, is the switch
    the parse has - same scrutinee, same labels, same bodies, same fail-closed default. -/
def qemNativeId_switchShape_ok : Bool :=
  match qEmitNativeIdentitySwitch nativeIds foldPlan scratchSlot stateSlots false with
  | Stmt.switch scrut cases dflt =>
      (match scrut with | Expr.var x => x == "q_native_idx" | _ => false) &&
        cases.length == nativeIds.length &&
        (match dflt with
         | some ds => SyntaxEq.stmtsBeq ds [yexpr (ycall "q_program_fail" [])]
         | none => false)
  | _ => false
#eval qemNativeId_switchShape_ok -- expect true

/-! ## Family 3: the POST-VM SUFFIX ('quotientPostVmComputations') -/

/-- ACCEPTANCE 1 OF 3 (THE DEPLOYMENT): the trash block the producer writes IS the tree
    'qEmitTrashBlock' builds - and it is the family the deployed context carries. -/
def qemPostVm_isTheParse_ok : Bool :=
  match qEmitPostVmFamily stateSlots false famEv with
  | none => false
  | some b =>
      SyntaxEq.stmtsBeq (qGenNested ctx.quotientPostVmComputations) b &&
        (yulTokens (String.intercalate "\n" (ctx.quotientPostVmComputations.flatten))).length == 1996
#eval qemPostVm_isTheParse_ok -- expect true

/-- ACCEPTANCE 2 OF 3 (THE PRODUCER ITSELF): the twin ties to 'structuredTrashLoopBlock' run on
    the same Evaluator, at trace false AND at trace true - the second context is the fold's, and it
    is a real change of program and not a re-spelling. -/
def qemPostVm_isTheProducer_ok : Bool :=
  match qEmitPostVmFamily stateSlots false famEv, producerTrash stateSlots false famEv with
  | some a, some p =>
      SyntaxEq.stmtsBeq a p &&
        SyntaxEq.stmtsBeq (qGenNested ((genOut?.map fun (o : GenOut) => o.qblocks.postVmComputations).getD [])) a &&
        (match qEmitPostVmFamily stateSlots true famEv, producerTrash stateSlots true famEv with
         | some a2, some p2 => SyntaxEq.stmtsBeq a2 p2 && ! SyntaxEq.stmtsBeq a2 a
         | _, _ => false)
  | _, _ => false
#eval qemPostVm_isTheProducer_ok -- expect true

/-- ACCEPTANCE 3 OF 3 (THE ALL-ARMS CONTEXT) AND THE EMPTY CASE: the tie holds at 'qvmAllArms', and
    with no trashcans BOTH the producer and the twin return 'none' - the gate that says the empty
    arm is computed and not a silent fallback. -/
def qemPostVm_allArmsAndEmpty_ok : Bool :=
  (match qEmitPostVmFamily stateSlots false famEv with
   | some b => SyntaxEq.stmtsBeq (qGenNested qvmAllArms.quotientPostVmComputations) b
   | none => false) &&
    (qEmitPostVmFamily stateSlots false { famEv with meta_ := { famEv.meta_ with numTrashcans := 0 } }).isNone &&
    (producerTrash stateSlots false { famEv with meta_ := { famEv.meta_ with numTrashcans := 0 } }).isNone &&
    (match qEmitPostVmFamily stateSlots false famEv with | some b => b.length == 1 | none => false)
#eval qemPostVm_allArmsAndEmpty_ok -- expect true

/-- TEETH (POST-VM): the three trash scaffolding tokens, mutated in the family text, redden the
    tie; and the challenge load is emitted ONCE for the whole block, which is the one place this
    producer differs from the Evaluator's own trashcan path. -/
def qemPostVm_teeth_ok : Bool :=
  let t := String.intercalate "\n" (ctx.quotientPostVmComputations.flatten)
  match qEmitPostVmFamily stateSlots false famEv with
  | none => false
  | some b =>
      SyntaxEq.stmtsBeq (reg t) b &&
        ! SyntaxEq.stmtsBeq (reg (mutateFirst "q_trash_tau" "q_trash_tau2" t)) b &&
        ! SyntaxEq.stmtsBeq (reg (mutateFirst "q_trash_scaled" "q_trash_scaled2" t)) b &&
        ! SyntaxEq.stmtsBeq (reg (mutateFirst "TRASH_CHALLENGE_MPTR" "BETA_MPTR" t)) b &&
        (countName "let q_trash_tau" b) == 1 &&
        t != mutateFirst "q_trash_tau" "q_trash_tau2" t
#eval qemPostVm_teeth_ok -- expect true

/-- FIELD REACH (POST-VM): the three state slots and the trace flag are read by the twin and not
    transcribed. Perturbing each moves the tree and the tie to the producer follows. -/
def qemPostVm_fieldsReach_ok : Bool :=
  let base := qEmitPostVmFamily stateSlots false famEv
  let tie (sl : QuotientStateSlots) (tr : Bool) : Bool :=
    match qEmitPostVmFamily sl tr famEv, producerTrash sl tr famEv with
    | some a, some p => SyntaxEq.stmtsBeq a p && ! SyntaxEq.stmtsBeq a (base.getD [])
    | _, _ => false
  tie { stateSlots with evalNumerMptr := stateSlots.evalNumerMptr + 0x20 } false &&
    tie { stateSlots with traceIdMptr := stateSlots.traceIdMptr + 0x20 } true &&
    tie stateSlots true &&
    (match base with
     | some b => SyntaxEq.stmtsBeq b (qGenNested ctx.quotientPostVmComputations)
     | none => false)
#eval qemPostVm_fieldsReach_ok -- expect true

/-- THE THREE LANDED FAMILIES ARE THREE, NOT ONE: the inline, native-identity and post-VM trees are
    pairwise different, each has its own emitter, and the two that share a producer ('direct_quotient_block')
    still differ from one another because the identities differ. A single function landed three
    times would fail the first clause and a family whose emitter is a stub would fail the second. -/
def qem_threeFamiliesAreDistinct_ok : Bool :=
  let a := qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false
  let b := qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false
  match qEmitPostVmFamily stateSlots false famEv with
  | none => false
  | some c =>
      ! SyntaxEq.stmtsBeq a b && ! SyntaxEq.stmtsBeq a c && ! SyntaxEq.stmtsBeq b c &&
        a.length == 12 && b.length == 9 && c.length == 1 &&
        inlineIds.length == 4 && nativeIds.length == 3
#eval qem_threeFamiliesAreDistinct_ok -- expect true

/-- THE FINGERPRINT CANNOT HAVE MOVED: nothing here is wired into the deployed program, so the
    numerator the artifact reads is still OBJ.2's parse and OBJ.15's tree still agrees with it. -/
def qem_fingerprintUntouched_ok : Bool :=
  numA_agreesWithParse_ok && numA_isTheParseFixture_ok && numA_isTheParseAllArms_ok &&
    ! (SyntaxEq.stmtsBeq (GenAst.emitQuotientNumerator ctx)
      (qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false))
#eval qem_fingerprintUntouched_ok -- expect true

/-! # QEMIT2: the prerequisite twin and the two native loop families -/

/-! ## THE PREREQUISITE: 'pushMstoreMloadLiteralRuns' as AST.

BOTH remaining families stage tables through this compactor, which is why QEMIT named it as the
dependency. The tie that matters is not the one at the deployment - the deployment exercises two of
the compactor's shapes and not the other six - so the gate below runs the producer and the twin over
a SYNTHETIC battery that covers every rejection path, the 'count < 3' rule, and both 'src_stride'
arms, and requires them to agree statement for statement on each case. -/

abbrev QOp := EVM.Op
def q2mE (n : Nat) : Expr QOp := yop EVM.Op.mload [ylit n]
def q2mS (n : Nat) : String := "mload(" ++ rustHashHex n ++ ")"
/-- One entry, spelled BOTH ways: the string the text producer is handed and the expression the AST
    twin is handed. A case where the two spellings are not the same word is a case the battery would
    not be testing, so they are built together. -/
def q2e (d src : Nat) : Nat × String × Expr QOp := (d, q2mS src, q2mE src)
/-- 'mload(INSTANCE_EVAL_MPTR)': an mload whose argument is not a literal. This is a REAL shape -
    the permutation block's instance column renders exactly this line at the deployment. -/
def q2eNamed : Nat × String × Expr QOp :=
  (0, "mload(INSTANCE_EVAL_MPTR)", yop EVM.Op.mload [yvar "INSTANCE_EVAL_MPTR"])
/-- A calldata word: not an mload at all. -/
def q2eCall (d : Nat) : Nat × String × Expr QOp :=
  (d, "calldataload(0x40)", yop EVM.Op.calldataload [ylit 0x40])
/-- An mload of an 'add': one argument, but not a number literal. -/
def q2eAdd (d src : Nat) : Nat × String × Expr QOp :=
  (d, "mload(add(" ++ rustHashHex src ++ ", 0x20))",
    yop EVM.Op.mload [yop EVM.Op.add [ylit src, ylit 0x20]])
/-- Not an mload: a bare variable. -/
def q2eVar (d : Nat) : Nat × String × Expr QOp := (d, "q_let_1", yvar "q_let_1")

def qem2RunsCases : List (String × List (Nat × String × Expr QOp)) :=
  [ ("empty", []),
    ("one", [q2e 0x0 0x100]),
    ("pair-no-compact", [q2e 0x0 0x100, q2e 0x20 0x120]),
    ("triple-stride20", [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140]),
    ("quad-stride20", [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2e 0x60 0x160]),
    ("triple-stride60", [q2e 0x0 0x100, q2e 0x20 0x160, q2e 0x40 0x1c0]),
    ("triple-stride40", [q2e 0x0 0x100, q2e 0x20 0x140, q2e 0x40 0x180]),
    ("nonliteral-first", [q2eNamed, q2e 0x20 0x120, q2e 0x40 0x140]),
    ("nonliteral-second", [q2e 0x0 0x100, q2eVar 0x20, q2e 0x40 0x140]),
    ("dst-gap", [q2e 0x0 0x100, q2e 0x40 0x120, q2e 0x60 0x140]),
    ("src-underflow", [q2e 0x0 0x200, q2e 0x20 0x100, q2e 0x40 0x120]),
    ("stride-zero", [q2e 0x0 0x200, q2e 0x20 0x200, q2e 0x40 0x200]),
    ("break-mid", [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2e 0x60 0x999,
                   q2e 0x80 0x9a0]),
    ("break-mid7", [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2e 0x60 0x160,
                    q2e 0x80 0x999, q2e 0xa0 0x9a0, q2e 0xc0 0x9c0]),
    ("calldata", [q2eCall 0x0, q2e 0x20 0x120, q2e 0x40 0x140]),
    ("mload-add", [q2eAdd 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140]),
    ("tail-single", [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2e 0x60 0x160, q2eNamed]),
    ("two-runs", [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2eVar 0x60,
                  q2e 0x80 0x400, q2e 0xa0 0x460, q2e 0xc0 0x4c0]),
    ("nonzero-dstbase", [q2e 0xc0 0x100, q2e 0xe0 0x120, q2e 0x100 0x140]) ]

/-- The producer and the twin on one battery case: same entries, same 'dst', same 'loopPrefix',
    and the parse of the producer's text must be the twin's tree. The last clause says the case
    is not vacuous - a case that emitted nothing on both sides would tie for free. -/
def qem2RunsTie (es : List (Nat × String × Expr QOp)) : Bool :=
  let txt := pushMstoreMloadLiteralRuns [] "q_dst" (es.map fun x => (x.fst, x.snd.fst)) "q_ld"
  let ast := qPushMstoreMloadLiteralRunsA [] "q_dst" (es.map fun x => (x.fst, x.snd.snd)) "q_ld"
  let p := qGenFlat txt
  SyntaxEq.stmtsBeq p ast && (if es.isEmpty then p.isEmpty && ast.isEmpty
                              else !p.isEmpty && !ast.isEmpty)

/-- GATE (PREREQUISITE, THE BATTERY): all nineteen shapes tie. -/
def qem2RunsBattery_ok : Bool :=
  qem2RunsCases.length == 19 && qem2RunsCases.all (fun c => qem2RunsTie c.snd)
#eval qem2RunsBattery_ok -- expect true

/-- How many 'for' loops a tree contains: the compactor's ONLY product is a loop, so counting them
    is how the rejection paths are shown to be rejections and not silent compactions. -/
def countFor (b : Block QOp) : Nat := ((EVM.print b).splitOn "for ").length - 1

/-- EVERY REJECTION IS REACHED AND REJECTS. Each of the five single-line rejections, plus the
    'count < 3' rule, is a battery case whose producer text contains NO loop at all - and the twin
    agrees, emitting the same number of singles. A twin that skipped a rejection test would compact
    where the producer does not and this reddens; a twin that tested them in the wrong ORDER would
    still pass the battery above but not this one, because the cases differ in which entry the
    rejection lands on. -/
def qem2RunsRejectionsReach_ok : Bool :=
  let rejects (name : String) : Bool :=
    match qem2RunsCases.find? fun c => c.fst == name with
    | none => false
    | some (_, es) =>
        let txt := pushMstoreMloadLiteralRuns [] "q_dst" (es.map fun x => (x.fst, x.snd.fst)) "q_ld"
        let ast := qPushMstoreMloadLiteralRunsA [] "q_dst" (es.map fun x => (x.fst, x.snd.snd)) "q_ld"
        countFor (qGenFlat txt) == 0 && countFor ast == 0 &&
          ast.length == es.length && txt.length == es.length
  rejects "one" && rejects "pair-no-compact" && rejects "nonliteral-first" &&
    rejects "nonliteral-second" && rejects "dst-gap" && rejects "src-underflow" &&
    rejects "stride-zero" && rejects "calldata" && rejects "mload-add"
#eval qem2RunsRejectionsReach_ok -- expect true

/-- THE TWO 'src_stride' ARMS ARE THE TWO ARMS: the 0x20 case reuses the destination offset
    variable and the other multiplies by the stride literal, and the twin follows in both. Pinned
    by shape, not by count: the src_off binding is 'q_ld_dst_off' in one and 'mul(i, 0x60)' in the
    other. -/
def qem2RunsStrideArmsDiffer_ok : Bool :=
  let arm (stride : Nat) :=
    let es := [q2e 0x0 0x100, q2e 0x20 (0x100 + stride), q2e 0x40 (0x100 + 2 * stride)]
    let txt := pushMstoreMloadLiteralRuns [] "q_dst" (es.map fun x => (x.fst, x.snd.fst)) "q_ld"
    (String.intercalate "\n" txt, qPushMstoreMloadLiteralRunsA [] "q_dst"
      (es.map fun x => (x.fst, x.snd.snd)) "q_ld")
  let (t20, a20) := arm 0x20
  let (t60, a60) := arm 0x60
  t20 != t60 && ! SyntaxEq.stmtsBeq a20 a60 &&
    (t20.contains "q_ld_src_off := q_ld_dst_off") &&
    (t60.contains "q_ld_src_off := mul(q_ld_i, 0x60)") &&
    qem2RunsTie [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140] &&
    qem2RunsTie [q2e 0x0 0x100, q2e 0x20 0x160, q2e 0x40 0x1c0]
#eval qem2RunsStrideArmsDiffer_ok -- expect true

/-- TEETH (PREREQUISITE): four scaffolding tokens of the compactor's OWN emitted text, mutated,
    each reddens the tie - the loop count, the destination-offset binding, the stride literal and
    the store's destination base. And the unmutated text ties, so the mutations are what redden. -/
def qem2RunsTeeth_ok : Bool :=
  let es := [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2e 0x60 0x160, q2e 0x80 0x180]
  let txt := pushMstoreMloadLiteralRuns [] "q_dst" (es.map fun x => (x.fst, x.snd.fst)) "q_ld"
  let ast := qPushMstoreMloadLiteralRunsA [] "q_dst" (es.map fun x => (x.fst, x.snd.snd)) "q_ld"
  let t := String.intercalate "\n" txt
  let m1 := mutateFirst "lt(q_ld_i, 5)" "lt(q_ld_i, 4)" t
  let m2 := mutateFirst "q_ld_src_off := q_ld_dst_off" "q_ld_src_off := q_ld_i" t
  let m3 := mutateFirst "shl(5, q_ld_i)" "shl(6, q_ld_i)" t
  let m4 := mutateFirst "add(add(q_dst, 0x0)," "add(add(q_dst, 0x20)," t
  SyntaxEq.stmtsBeq (reg t) ast && ! SyntaxEq.stmtsBeq (reg m1) ast &&
    ! SyntaxEq.stmtsBeq (reg m2) ast && ! SyntaxEq.stmtsBeq (reg m3) ast &&
    ! SyntaxEq.stmtsBeq (reg m4) ast && t != m1 && t != m2 && t != m3 && t != m4
#eval qem2RunsTeeth_ok -- expect true

/-- THE COMPACTOR IS NOT A NO-OP: on the same entries, emitting one 'mstore' per entry (what a twin
    that ignored the run logic would do) is a strictly different tree from what it produces, and the
    producer's own text is shorter than the singles spelling. Without this the battery could be
    passed by a twin that always took the single path. -/
def qem2RunsCompacts_ok : Bool :=
  let es := [q2e 0x0 0x100, q2e 0x20 0x120, q2e 0x40 0x140, q2e 0x60 0x160]
  let ast := qPushMstoreMloadLiteralRunsA [] "q_dst" (es.map fun x => (x.fst, x.snd.snd)) "q_ld"
  let singles : Block QOp :=
    es.map fun x => yexpr (yop EVM.Op.mstore [yop EVM.Op.add [yvar "q_dst", ylit x.fst], x.snd.snd])
  countFor ast == 1 && countFor singles == 0 && ! SyntaxEq.stmtsBeq ast singles &&
    ast.length < singles.length
#eval qem2RunsCompacts_ok -- expect true

/-! ## Family 4: the NATIVE PERMUTATION block -/

/-- The permutation producer, run on demand at the same three inputs the twin takes. 'base' is a
    fold-site fact the Horner arm never reads (FoldCompute.lean:390-391), so 0 is not a guess here -
    'qemPerm_baseUnused_ok' below pins that the emitted text does not depend on it. -/
def producerPerm (sc : Nat) (sl : QuotientStateSlots) (tr : Bool)
    (ev : Evaluator (Fr Yul.blsR)) : Option (Block EVM.Op) :=
  match (structuredPermutationLoopBlock sc (StructuredFold.horner sl tr) 0).run
      { ev := ev, block := [], sites := [] } with
  | .ok (some ls, _) => some (qGenFlat ls)
  | .ok (none, _) => none
  | .error _ => none

def permAst? : Option (Block EVM.Op) := qEmitNativePermutationA scratchSlot stateSlots false famEv

/-- ACCEPTANCE 1 OF 3 (THE DEPLOYMENT): the permutation family as the artifact slice parses it IS
    the tree 'qEmitNativePermutationA' builds - and the family is the 1,038 tokens the card names. -/
def qemPerm_isTheParse_ok : Bool :=
  match permAst? with
  | none => false
  | some b =>
      SyntaxEq.stmtsBeq (qGenFlat ctx.quotientNativePermutationComputation) b &&
        (yulTokens (String.intercalate "\n" ctx.quotientNativePermutationComputation)).length == 1038 &&
        (yulTokens (EVM.print b)).length ==
          (yulTokens (EVM.print (qGenFlat ctx.quotientNativePermutationComputation))).length
#eval qemPerm_isTheParse_ok -- expect true

/-- ACCEPTANCE 2 OF 3 (THE DERIVED GENERATOR RUN): the twin ties to the producer's own text AND to
    the block list the derived run stored, which is a DIFFERENT slicing of the same program - the
    artifact carries the flat 82-line region, the derived run carries the same lines as produced. -/
def qemPerm_isTheProducerDerived_ok : Bool :=
  match permAst?, producerPerm scratchSlot stateSlots false famEv with
  | some a, some pr =>
      SyntaxEq.stmtsBeq a pr &&
        SyntaxEq.stmtsBeq a (qGenFlat ctx.quotientNativePermutationComputation) &&
        (match genOut? with
         | none => false
         | some o =>
             SyntaxEq.stmtsBeq (qGenFlat o.qblocks.nativePermutationComputation) a &&
               o.qblocks.nativePermutationComputation.length ==
                 ctx.quotientNativePermutationComputation.length)
  | _, _ => false
#eval qemPerm_isTheProducerDerived_ok -- expect true

/-- ACCEPTANCE 3 OF 3 (THE ALL-ARMS CONTEXT): the tie holds there too, and the flag-independence
    clause above says why it is the same text. -/
def qemPerm_allArms_ok : Bool :=
  qemFamiliesIgnoreTheFlags_ok &&
    (match permAst? with
     | some a => SyntaxEq.stmtsBeq (qGenFlat qvmAllArms.quotientNativePermutationComputation) a
     | none => false)
#eval qemPerm_allArms_ok -- expect true

/-- TEETH (PERMUTATION): six scaffolding tokens of the family text, mutated, each reddens the tie -
    the scratch pointer binding, the compactor's loop count, the z-curve stride, the fold's
    y-advance, the delta-base store and the products loop's clamp. -/
def qemPerm_teethText_ok : Bool :=
  let t := String.intercalate "\n" ctx.quotientNativePermutationComputation
  match permAst? with
  | none => false
  | some b =>
      let m1 := mutateFirst "let q_perm_sigmas := 0x6a60" "let q_perm_sigmas := 0x6a61" t
      let m2 := mutateFirst "lt(q_perm_val_load_i, 5)" "lt(q_perm_val_load_i, 6)" t
      let m3 := mutateFirst "mul(q_perm_z_cur_load_i, 0x60)" "mul(q_perm_z_cur_load_i, 0x40)" t
      let m4 := mutateFirst "mulmod(mload(0x6660), y, r)" "mulmod(mload(0x6660), y2, r)" t
      let m5 := mutateFirst "mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR)"
                              "mstore(q_perm_delta_base_ptr, mulmod(mload(GAMMA_MPTR)" t
      let m6 := mutateFirst "if gt(q_perm_end, q_perm_num_cols)" "if gt(q_perm_end, q_perm_num_sets)" t
      SyntaxEq.stmtsBeq (reg t) b && ! SyntaxEq.stmtsBeq (reg m1) b &&
        ! SyntaxEq.stmtsBeq (reg m2) b && ! SyntaxEq.stmtsBeq (reg m3) b &&
        ! SyntaxEq.stmtsBeq (reg m4) b && ! SyntaxEq.stmtsBeq (reg m5) b &&
        ! SyntaxEq.stmtsBeq (reg m6) b &&
        t != m1 && t != m2 && t != m3 && t != m4 && t != m5 && t != m6
#eval qemPerm_teethText_ok -- expect true

/-- THE FAMILY STAGES THROUGH THE PREREQUISITE: the permutation block is the compactor's biggest
    customer - six tables - and the gate says so rather than trusting it. Dropping the compactor
    twin for a naive one-mstore-per-entry spelling reddens the tie, and the family text really does
    contain compacted loops. -/
def qemPerm_usesTheRunsTwin_ok : Bool :=
  match permAst? with
  | none => false
  | some b =>
      countFor b == 7 &&
        (String.intercalate "\n" ctx.quotientNativePermutationComputation).contains
          "for { let q_perm_z_next_load_i := 0 }" &&
        ! SyntaxEq.stmtsBeq b (qGenFlat
          (ctx.quotientNativePermutationComputation.filter fun l => !l.contains "for {"))
#eval qemPerm_usesTheRunsTwin_ok -- expect true

/-- The perturbed evaluators, each ONE field away from 'famEv'. Built as top-level definitions
    rather than inside the gate so the gate itself is a plain conjunction of four-word calls. -/
def permEvChunk : Evaluator (Fr Yul.blsR) :=
  { famEv with meta_ := { famEv.meta_ with
      permutationChunkLen := famEv.meta_.permutationChunkLen + 1 } }
def permEvCols : Evaluator (Fr Yul.blsR) :=
  { famEv with meta_ := { famEv.meta_ with
      permutationColumns := famEv.meta_.permutationColumns.drop 1 } }
def q2w (addr : Nat) : Midfall.Generator.Word := Midfall.Generator.QuotientEvaluatorKats.wmem addr
def permSigmaList : List (Column × Midfall.Generator.Word) :=
  (famEv.data.permutationEvals.head?.map fun (c, _) => [(c, q2w 0x1234)]).getD [] ++
    famEv.data.permutationEvals.drop 1
def permEvSigma : Evaluator (Fr Yul.blsR) :=
  { famEv with «data» := { famEv.data with permutationEvals := permSigmaList } }
def permEvZ : Evaluator (Fr Yul.blsR) :=
  { famEv with «data» := { famEv.data with permutationZEvals :=
      famEv.data.permutationZEvals ++ [(q2w 0x2a00, q2w 0x2a20, some (q2w 0x2a40))] } }
def permEvInst : Evaluator (Fr Yul.blsR) :=
  { famEv with «data» := { famEv.data with instanceEval := q2w 0x7777 } }
def permEvDelta : Evaluator (Fr Yul.blsR) :=
  { famEv with field := { famEv.field with
      delta := famEv.field.add famEv.field.delta famEv.field.one } }
def qemPerm_fieldsReach_ok : Bool :=
  let base := permAst?.getD []
  let tieMoves (sc : Nat) (sl : QuotientStateSlots) (tr : Bool)
      (ev : Evaluator (Fr Yul.blsR)) : Bool :=
    match qEmitNativePermutationA sc sl tr ev, producerPerm sc sl tr ev with
    | some a, some pr => SyntaxEq.stmtsBeq a pr && ! SyntaxEq.stmtsBeq a base
    | _, _ => false
  tieMoves (scratchSlot + 0x20) stateSlots false famEv &&
    tieMoves scratchSlot { stateSlots with
      evalNumerMptr := stateSlots.evalNumerMptr + 0x20 } false famEv &&
    tieMoves scratchSlot { stateSlots with
      traceIdMptr := stateSlots.traceIdMptr + 0x20 } true famEv &&
    tieMoves scratchSlot stateSlots true famEv &&
    tieMoves scratchSlot stateSlots false permEvChunk &&
    tieMoves scratchSlot stateSlots false permEvCols &&
    tieMoves scratchSlot stateSlots false permEvSigma &&
    tieMoves scratchSlot stateSlots false permEvZ &&
    tieMoves scratchSlot stateSlots false permEvInst &&
    tieMoves scratchSlot stateSlots false permEvDelta
#eval qemPerm_fieldsReach_ok -- expect true

/-- THE 'numPermutationZs == 0' ARM IS COMPUTED: with no permutation z BOTH the producer and the
    twin return 'none', and the caller stores '[]' - the arm the render's length guard depends on
    (GenAstQvm.lean:141). -/
def permEvNoZ : Evaluator (Fr Yul.blsR) :=
  ({ famEv with meta_ := { famEv.meta_ with numPermutationZs := 0 } })
def qemPerm_emptyArm_ok : Bool :=
  (qEmitNativePermutationA scratchSlot stateSlots false permEvNoZ).isNone &&
    (producerPerm scratchSlot stateSlots false permEvNoZ).isNone &&
    (match permAst? with | some b => ! b.isEmpty | none => false)
#eval qemPerm_emptyArm_ok -- expect true

/-- THE 'numSets > 1' ARM IS REACHED BOTH WAYS: with a single z set the continuity loop is absent
    from BOTH sides, and the two trees differ. A twin that always emitted the loop would tie at the
    deployment and fail here. -/
def permEvOneSet : Evaluator (Fr Yul.blsR) :=
  ({ famEv with meta_ := { famEv.meta_ with numPermutationZs := 1 },
                «data» := { famEv.data with
                  permutationZEvals := (famEv.data.permutationZEvals.head?.map fun x => [x]).getD [] } })
def qemPerm_continuityArmReaches_ok : Bool :=
  match qEmitNativePermutationA scratchSlot stateSlots false permEvOneSet,
        producerPerm scratchSlot stateSlots false permEvOneSet, permAst? with
  | some a1, some p1, some a0 =>
      SyntaxEq.stmtsBeq a1 p1 && ! SyntaxEq.stmtsBeq a1 a0 &&
        countName "q_perm_i" a1 == 0 && countName "q_perm_i" a0 > 0
  | _, _, _ => false
#eval qemPerm_continuityArmReaches_ok -- expect true

/-- 'base' IS UNUSED BY THE HORNER ARM, and that is what lets the twin drop it: the producer's text
    at base 0 and at base 99 is the same text. -/
def qemPerm_baseUnused_ok : Bool :=
  match (structuredPermutationLoopBlock scratchSlot (StructuredFold.horner stateSlots false) 0).run
          { ev := famEv, block := [], sites := [] },
        (structuredPermutationLoopBlock scratchSlot (StructuredFold.horner stateSlots false) 99).run
          { ev := famEv, block := [], sites := [] } with
  | .ok (some x, _), .ok (some y, _) => x == y && SyntaxEq.stmtsBeq (qGenFlat x) (qGenFlat y)
  | _, _ => false
#eval qemPerm_baseUnused_ok -- expect true

/-! ## Family 5: the NATIVE LOOKUP block -/

def producerLookup (sc : Nat) (sl : QuotientStateSlots) (tr : Bool)
    (ev : Evaluator (Fr Yul.blsR)) : Option (Block EVM.Op) :=
  match (structuredLookupLoopBlock sc (StructuredFold.horner sl tr) 0).run
      { ev := ev, block := [], sites := [] } with
  | .ok (some ls, _) => some (qGenFlat ls)
  | .ok (none, _) => none
  | .error _ => none

def lookAst? : Option (Block EVM.Op) := qEmitNativeLookupA scratchSlot stateSlots false famEv

/-- ACCEPTANCE 1 OF 3 (THE DEPLOYMENT): 43 lines, 458 tokens, and the tree agrees with the parse. -/
def qemLookup_isTheParse_ok : Bool :=
  match lookAst? with
  | none => false
  | some b =>
      SyntaxEq.stmtsBeq (qGenFlat ctx.quotientNativeLookupComputation) b &&
        (yulTokens (String.intercalate "\n" ctx.quotientNativeLookupComputation)).length == 458 &&
        (yulTokens (EVM.print b)).length ==
          (yulTokens (EVM.print (qGenFlat ctx.quotientNativeLookupComputation))).length
#eval qemLookup_isTheParse_ok -- expect true

/-- ACCEPTANCE 2 OF 3 (THE DERIVED GENERATOR RUN). -/
def qemLookup_isTheProducerDerived_ok : Bool :=
  match lookAst?, producerLookup scratchSlot stateSlots false famEv with
  | some a, some pr =>
      SyntaxEq.stmtsBeq a pr &&
        (match genOut? with
         | none => false
         | some o =>
             SyntaxEq.stmtsBeq (qGenFlat o.qblocks.nativeLookupComputation) a &&
               o.qblocks.nativeLookupComputation.length ==
                 ctx.quotientNativeLookupComputation.length)
  | _, _ => false
#eval qemLookup_isTheProducerDerived_ok -- expect true

/-- ACCEPTANCE 3 OF 3 (THE ALL-ARMS CONTEXT), plus 'trace = true' as the third real context: the
    lookup family reads the fold, so the trace flag changes the program and the tie follows. -/
def qemLookup_allArms_ok : Bool :=
  qemFamiliesIgnoreTheFlags_ok &&
    (match lookAst?, qEmitNativeLookupA scratchSlot stateSlots true famEv,
            producerLookup scratchSlot stateSlots true famEv with
     | some a, some atr, some pt =>
         SyntaxEq.stmtsBeq (qGenFlat qvmAllArms.quotientNativeLookupComputation) a &&
           SyntaxEq.stmtsBeq atr pt && ! SyntaxEq.stmtsBeq atr a
     | _, _, _ => false)
#eval qemLookup_allArms_ok -- expect true

/-- TEETH (LOOKUP): six scaffolding tokens of the family text, mutated, each reddens the tie - the
    scratch bindings, the two challenge loads, the lsum fold operand, the k == 1 arm's 'sub(r, 1)',
    and the accumulator's 'q_lookup_core'. -/
def qemLookup_teethText_ok : Bool :=
  let t := String.intercalate "\n" ctx.quotientNativeLookupComputation
  match lookAst? with
  | none => false
  | some b =>
      let m1 := mutateFirst "let q_lookup_prefix := 0x6980" "let q_lookup_prefix := 0x6981" t
      let m2 := mutateFirst "let q_lookup_theta := mload(THETA_MPTR)"
                              "let q_lookup_theta := mload(BETA_MPTR)" t
      let m3 := mutateFirst "addmod(q_lookup_l0, q_lookup_llast, r)"
                            "addmod(q_lookup_l0, q_lookup_lblind, r)" t
      let m4 := mutateFirst "sub(r, 1)" "sub(r, 2)" t
      let m5 := mutateFirst "let q_lookup_core := addmod(mulmod(q_lookup_diff"
                            "let q_lookup_core := addmod(mulmod(q_lookup_t_beta" t
      let m6 := mutateFirst "let q_lookup_s_sum_h := mulmod(f_16" "let q_lookup_s_sum_h := mulmod(f_11" t
      SyntaxEq.stmtsBeq (reg t) b && ! SyntaxEq.stmtsBeq (reg m1) b &&
        ! SyntaxEq.stmtsBeq (reg m2) b && ! SyntaxEq.stmtsBeq (reg m3) b &&
        ! SyntaxEq.stmtsBeq (reg m4) b && ! SyntaxEq.stmtsBeq (reg m5) b &&
        ! SyntaxEq.stmtsBeq (reg m6) b &&
        t != m1 && t != m2 && t != m3 && t != m4 && t != m5 && t != m6
#eval qemLookup_teethText_ok -- expect true

/-- The lookup family's perturbed evaluators, same reason as the permutation ones. -/
def lookMList : List (Midfall.Generator.Word × List Midfall.Generator.Word × Midfall.Generator.Word × Midfall.Generator.Word) :=
  (famEv.data.lookupEvals.head?.map fun (_, hs, z, zn) => [(q2w 0x3100, hs, z, zn)]).getD [] ++
    famEv.data.lookupEvals.drop 1
def lookZList : List (Midfall.Generator.Word × List Midfall.Generator.Word × Midfall.Generator.Word × Midfall.Generator.Word) :=
  (famEv.data.lookupEvals.head?.map fun (mm, hs, _, zn) => [(mm, hs, q2w 0x3120, zn)]).getD [] ++
    famEv.data.lookupEvals.drop 1
def lookEvM : Evaluator (Fr Yul.blsR) :=
  { famEv with «data» := { famEv.data with lookupEvals := lookMList } }
def lookEvZ : Evaluator (Fr Yul.blsR) :=
  { famEv with «data» := { famEv.data with lookupEvals := lookZList } }
def lookEvOne : Evaluator (Fr Yul.blsR) :=
  { famEv with cs := { famEv.cs with lookups := famEv.cs.lookups.take 1 } }
/-- The other direction on the same field: an EMPTY lookup list still renders the ten header lines
    and no per-lookup block, so the list is read and not transcribed. 'take 1' would not show this -
    the deployment has exactly one lookup - which is why the gate perturbs the list to zero. -/
def lookEvNil : Evaluator (Fr Yul.blsR) :=
  { famEv with cs := { famEv.cs with lookups := #[] } }

/-- FIELD REACH (LOOKUP): scratch base, the two state slots, the trace flag, the lookup list, the
    lookup evals and the meta count - each perturbed alone, each still tying to the producer and
    each moving the tree. -/
def qemLookup_fieldsReach_ok : Bool :=
  let base := lookAst?.getD []
  let tieMoves (sc : Nat) (sl : QuotientStateSlots) (tr : Bool)
      (ev : Evaluator (Fr Yul.blsR)) : Bool :=
    match qEmitNativeLookupA sc sl tr ev, producerLookup sc sl tr ev with
    | some a, some pr => SyntaxEq.stmtsBeq a pr && ! SyntaxEq.stmtsBeq a base
    | _, _ => false
  tieMoves (scratchSlot + 0x20) stateSlots false famEv &&
    tieMoves scratchSlot { stateSlots with
      evalNumerMptr := stateSlots.evalNumerMptr + 0x20 } false famEv &&
    tieMoves scratchSlot { stateSlots with
      traceIdMptr := stateSlots.traceIdMptr + 0x20 } true famEv &&
    tieMoves scratchSlot stateSlots true famEv &&
    tieMoves scratchSlot stateSlots false lookEvM &&
    tieMoves scratchSlot stateSlots false lookEvZ &&
    tieMoves scratchSlot stateSlots false lookEvNil
#eval qemLookup_fieldsReach_ok -- expect true

/-- THE 'numLookups == 0' ARM IS COMPUTED, both sides. -/
def lookEvNone : Evaluator (Fr Yul.blsR) :=
  ({ famEv with meta_ := { famEv.meta_ with numLookups := 0 } })
def qemLookup_emptyArm_ok : Bool :=
  (qEmitNativeLookupA scratchSlot stateSlots false lookEvNone).isNone &&
    (producerLookup scratchSlot stateSlots false lookEvNone).isNone &&
    (match lookAst? with | some b => ! b.isEmpty | none => false)
#eval qemLookup_emptyArm_ok -- expect true

/-- THE k >= 2 ARM IS REACHED, NOT ASSUMED. The deployment's single lookup has ONE parallel input,
    so the staging loops, the prefix/suffix products and the shared-prefix attempt are all outside
    what the fixture exercises - exactly the shape of defect OBJ.15's teeth caught. The remedy is
    the same: a SYNTHETIC circuit. Replicating the deployment's parallel input five times makes the
    chunker emit a chunk of more than one input, and the twin ties to the producer there too. -/
def qemLookup_k2ArmReaches_ok : Bool :=
  match famEv.cs.lookups.toList with
  | [] => false
  | L :: _ =>
      let wideInputs : Array (Array (Expression (Fr Yul.blsR))) :=
        (List.replicate 5 (L.inputExpressions.getD 0 #[])).toArray
      let wideLookups : Array (LogupBatchedArgument (Fr Yul.blsR)) :=
        #[{ L with inputExpressions := wideInputs }]
      let wide : Evaluator (Fr Yul.blsR) :=
        ({ famEv with cs := { famEv.cs with lookups := wideLookups } })
      match qEmitNativeLookupA scratchSlot stateSlots false wide,
            producerLookup scratchSlot stateSlots false wide with
      | some a, some pr =>
          SyntaxEq.stmtsBeq a pr &&
            (EVM.print a).contains "q_lookup_product" &&
            (EVM.print a).contains "q_lookup_suf_prev" &&
            ! SyntaxEq.stmtsBeq a (lookAst?.getD [])
      | _, _ => false
#eval qemLookup_k2ArmReaches_ok -- expect true

/-- The deployment's own first parallel input, and its tail advice query: the shared-prefix
    synthetic is built from them so the prefix is a REAL expression the Evaluator can render. -/
def sharedCommon : List (Expression (Fr Yul.blsR)) :=
  ((famEv.cs.lookups.toList.head?.bind fun L =>
      (L.inputExpressions.toList.head?.map fun first => first.toList.dropLast))).getD []
def sharedTailQ : Option AdviceQuery :=
  famEv.cs.lookups.toList.head?.bind fun L =>
    (L.inputExpressions.toList.head?.bind fun first =>
      match first.toList.getLast? with
      | some (Expression.advice q) => some q
      | _ => none)
def sharedInputs : Array (Array (Expression (Fr Yul.blsR))) :=
  match sharedTailQ with
  | none => #[]
  | some q => ((List.range 4).map fun i =>
      (sharedCommon ++ [Expression.advice { q with columnIndex := 900 + i }]).toArray).toArray
def sharedEvals : List ((Nat × Int) × Midfall.Generator.Word) :=
  match sharedTailQ with
  | none => []
  | some q => (List.range 4).map fun i => ((900 + i, q.rotation.int), q2w (0x2000 + i * 0x20))
def sharedLookups : Array (LogupBatchedArgument (Fr Yul.blsR)) :=
  match famEv.cs.lookups.toList with
  | [] => #[]
  | L :: _ => #[{ L with inputExpressions := sharedInputs }]
def sharedAdvice : List ((Nat × Int) × Midfall.Generator.Word) :=
  sharedEvals ++ famEv.data.adviceEvals
def lookEvShared : Evaluator (Fr Yul.blsR) :=
  ({ famEv with cs := { famEv.cs with lookups := sharedLookups },
                «data» := { famEv.data with adviceEvals := sharedAdvice } })

def qemLookup_sharedPrefixArm_ok : Bool :=
  match qEmitNativeLookupA scratchSlot stateSlots false lookEvShared,
        producerLookup scratchSlot stateSlots false lookEvShared with
  | some a, some pr =>
      SyntaxEq.stmtsBeq a pr &&
        (EVM.print a).contains "q_lookup_shared_i" &&
        (EVM.print a).contains "q_lookup_prod_i" &&
        ! (EVM.print a).contains "mstore(add(q_lookup_f, 0x0), addmod(" &&
        ! SyntaxEq.stmtsBeq a (lookAst?.getD [])
  | _, _ => false
#eval qemLookup_sharedPrefixArm_ok -- expect true

/-- THE 'k == 0' ARM IS UNREACHABLE THROUGH THE CHUNKER, and that is a measured fact and not an
    assumption: 'rustChunks' never emits an empty chunk, so no 'inputExpressions' shape makes a
    chunk of length zero. The arm is twin'd because the producer has it and a total twin must
    totalise, and this gate says plainly that nothing at the deployment or in a synthetic circuit
    exercises it. -/
def qemLookup_k0ArmUnreachable_ok : Bool :=
  match famEv.cs.lookups.toList with
  | [] => false
  | L :: _ =>
      let widths := [0, 1, 2, 3, 4, 5, 6, 7, 8]
      widths.all fun n =>
        let ins : Array (Array (Expression (Fr Yul.blsR))) :=
          (List.replicate n (L.inputExpressions.getD 0 #[])).toArray
        let ev : Evaluator (Fr Yul.blsR) :=
          ({ famEv with cs := { famEv.cs with lookups := #[{ L with inputExpressions := ins }] } })
        match (LogupBatchedArgument.chunkByDegree { L with inputExpressions := ins }
                (match ConstraintSystem.degree famEv.cs with | .ok d => d | .error _ => 1)) with
        | .ok c => c.inputExpressionChunks.toList.all fun ch => ch.size > 0
        | .error _ => true
#eval qemLookup_k0ArmUnreachable_ok -- expect true

/-! ## The five families together, and the artifact -/

/-- THE FIVE FAMILIES ARE FIVE AND PAIRWISE DIFFERENT: a family whose emitter was a stub, or one
    landed five times, fails this. The sizes are the ones the two cards measured. -/
def qem2_fiveFamiliesAreDistinct_ok : Bool :=
  let a := qEmitInlineFamily inlineIds foldPlan scratchSlot stateSlots false
  let b := qEmitNativeIdentityFamily nativeIds foldPlan scratchSlot stateSlots false
  match qEmitPostVmFamily stateSlots false famEv, permAst?, lookAst? with
  | some c, some d, some e =>
      ! SyntaxEq.stmtsBeq a b && ! SyntaxEq.stmtsBeq a c && ! SyntaxEq.stmtsBeq a d &&
        ! SyntaxEq.stmtsBeq a e && ! SyntaxEq.stmtsBeq b c && ! SyntaxEq.stmtsBeq b d &&
        ! SyntaxEq.stmtsBeq b e && ! SyntaxEq.stmtsBeq c d && ! SyntaxEq.stmtsBeq c e &&
        ! SyntaxEq.stmtsBeq d e &&
        (yulTokens (String.intercalate "\n" ctx.quotientNativePermutationComputation)).length == 1038 &&
        (yulTokens (String.intercalate "\n" ctx.quotientNativeLookupComputation)).length == 458 &&
        (yulTokens (EVM.print d)).length ==
          (yulTokens (EVM.print (qGenFlat ctx.quotientNativePermutationComputation))).length &&
        (yulTokens (EVM.print e)).length ==
          (yulTokens (EVM.print (qGenFlat ctx.quotientNativeLookupComputation))).length
  | _, _, _ => false
#eval qem2_fiveFamiliesAreDistinct_ok -- expect true

/-- THE FINGERPRINT CANNOT HAVE MOVED. Nothing in this section is wired into 'emitPartialM' or
    'emitQuotientNumeratorA': the deployed program still reaches every one of the five families
    through OBJ.2's parse, the numerator tree still agrees with that parse, and the object the
    fingerprint pins is still 14,109 tokens at '0x3149ae4f...bef176'. The last clause is the
    positive half: the twin is NOT what the deployed numerator emits. -/
def qem2_fingerprintUntouched_ok : Bool :=
  numA_agreesWithParse_ok && numA_isTheParseFixture_ok && numA_isTheParseAllArms_ok &&
    Midfall.Instances.ObjectFingerprint.objectFingerprint_ok &&
    Midfall.Instances.ObjectFingerprint.objectTokens.length == 14109 &&
    ! (SyntaxEq.stmtsBeq (GenAst.emitQuotientNumerator ctx) (permAst?.getD [])) &&
    ! (SyntaxEq.stmtsBeq (GenAst.emitQuotientNumerator ctx) (lookAst?.getD []))
#eval qem2_fingerprintUntouched_ok -- expect true

end Midfall.Instances.QvmFamilyKats
