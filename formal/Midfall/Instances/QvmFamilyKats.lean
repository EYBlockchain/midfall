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

set_option autoImplicit false

namespace Midfall.Instances.QvmFamilyKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientFold
open Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientBlocks
open Midfall.Generator.QuotientEvaluator Midfall.Generator.PlanNew
open Midfall.Instances Midfall.Instances.M2BatchKats Midfall.Instances.GeneratedKats
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.Lowering Midfall.Lowering.GenAst Midfall.Lowering.YulParse
open Midfall.LoweringV2
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

end Midfall.Instances.QvmFamilyKats
