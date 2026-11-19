-- |
-- Midfall.Lowering.GenAstQvmFamilies
--
-- PG-Q-OBJECT / QEMIT (PLAN-V3.md:948, "one emitter card per line family (issued by ROW.Q)"):
-- AST TWINS OF THE BLOCK PRODUCERS for the generated line families that OBJ.15 splices through
-- 'parseLines' at 'GenAstQvm.lean:61-69'.
--
-- WHY THIS FILE EXISTS. OBJ.15 landed the interpreter TEMPLATE as a tree and deliberately left the
-- six generated line families parsed, because the card's fence excluded "AST twins of the block
-- producers". ROW.Q.5 needs exactly what that fence excluded: a list induction over a block
-- producer requires a Lean function the producer can be compared with, statement for statement, so
-- the induction can run over the identity list. This file is those emitters, one per family, and it
-- is the prerequisite ROW.Q reported as missing.
--
-- THE SPLIT, AND WHAT STAYS PARSED. Each producer is scaffolding plus the Evaluator's expression
-- lines. The SCAFFOLDING is what a block producer's twin has to be: the braces, the scratch store,
-- the y-fold advance, the accumulator add, the selector-bucket update, the trash challenge load and
-- the three trash fold lines. All of it is built here from the identity's own fields - 'lines',
-- 'var', 'target', the selector gap, the scratch slot and the three 'QuotientStateSlots' pointers -
-- and none of it is parsed. The expression lines the Evaluator writes inside the scaffolding stay
-- spliced by 'qGenFlat': their AST twins are 'GenAstQuotient' (OBJ.15's sibling package, which
-- already gates 'evaluateA' / 'compressExpressionsA' against the text Evaluator), and a second twin
-- of the Evaluator here would be the duplicate implementation the package exists to avoid.
--
-- THE FINGERPRINT DOES NOT MOVE, AND THAT IS A GATE. Nothing here is wired into 'emitPartialM' or
-- into 'emitQuotientNumeratorA': the deployed program still reaches its numerator through the OBJ.2
-- parse. Every claim is a 'Bool' gate in 'Midfall/Instances/QvmFamilyKats.lean' (D-P71:
-- 'native_decide' stays in Instances/, and nothing in the headline cone may rest on a concrete
-- model), and the gates tie each twin to the parse of the producer's OWN text at the deployment and
-- at the all-arms context, with teeth that redden if a scaffolding token is mutated.
--
-- OUT OF SCOPE, NAMED: the 'StructuredFold.weighted' arm (the compact path always passes 'horner',
-- QuotientBlocks.lean:866, and 'compactBlocksHornerRecordsNoSites_ok' gates it), the legacy/direct
-- family 'quotientEvalNumerComputations' (it renders in the template's 'when None' arm, which
-- OBJ.15's fence excludes), and the two native structured loop blocks (permutation and lookup),
-- whose scaffolding is three times the size and whose split is reported as the remainder.
--

import Midfall.Lowering.GenAstQvm
import Midfall.Lowering.GenAstQuotient
import Midfall.Generator.Quotient.FoldCompute
import Midfall.Generator.Quotient.QuotientBlocks

set_option autoImplicit false

namespace Midfall.Lowering.GenAst
open YulSemantics YulSemantics.EVM Midfall.Generator Midfall.Lowering.YulParse
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientEvaluator Midfall.Lowering.GenAstQuotient

/-! ### The fold scaffolding, as AST -/

/-- The AST twin of 'pushQuotientTrace' (FoldCompute.lean:336-342): the trace-id read with the
    value, then the trace-id bump. With 'trace = false' the producer appends NOTHING, and neither
    does this - the flag is not a formatting choice. -/
def qPushTraceA (slots : QuotientStateSlots) (value : Expr Op) (trace : Bool) : Block Op :=
  if !trace then []
  else [yexpr (ycall "trace_u256" [yop Op.mload [ylit slots.traceIdMptr], value]),
        yexpr (yop Op.mstore [ylit slots.traceIdMptr,
          yop Op.add [yop Op.mload [ylit slots.traceIdMptr], ylit 1]])]

/-- The AST twin of 'pushStructuredFoldAdvance' at 'count = 1' (FoldCompute.lean:360-368): the
    straight-line arm, 'mstore(EVAL, mulmod(mload(EVAL), y, r))'. The loop arm is not twin'd here
    because every caller in the compact path passes 1. -/
def qFoldAdvance1A (slots : QuotientStateSlots) : Block Op :=
  [yexpr (yop Op.mstore [ylit slots.evalNumerMptr,
      yop Op.mulmod [yop Op.mload [ylit slots.evalNumerMptr], yvar "y", yvar "r"]])]

/-- The AST twin of 'pushQuotientEvalNumerAdd' (FoldCompute.lean:347-350): the other half of the
    Horner fold, 'mstore(EVAL, addmod(mload(EVAL), value, r))'. -/
def qEvalNumerAddA (slots : QuotientStateSlots) (value : Expr Op) : Block Op :=
  [yexpr (yop Op.mstore [ylit slots.evalNumerMptr,
      yop Op.addmod [yop Op.mload [ylit slots.evalNumerMptr], value, yvar "r"]])]

/-- The Horner fold as one AST snippet: trace, advance, add. This is what 'pushFold' becomes once
    the 'StructuredFold' is destructured into the two fields its 'horner' arm carries. -/
def qHornerFoldA (slots : QuotientStateSlots) (trace : Bool) (value : Expr Op) : Block Op :=
  qPushTraceA slots value trace ++ qFoldAdvance1A slots ++ qEvalNumerAddA slots value

/-- The selector-bucket update 'direct_quotient_block' appends for a 'Selector(idx)' identity: its
    own block, with the gap power read only when the gap is non-zero. The 'none' gap is the
    producer's release panic (FoldCompute.lean:433-435, 'panicAt siteSelectorGap'); it emits
    nothing here, and 'qemGapPanicArmUnused_ok' gates that no identity the compact path reaches ever
    takes it - so the arm is a documented totalising fallback and not a silent divergence. -/
def qSelectorBucketA (slots : QuotientStateSlots) (idx : Nat) (gap : Option Nat)
    (value : Expr Op) : Block Op :=
  let gapStmts : Block Op :=
    match gap with
    | some g => if g != 0
      then [yset "q_selector_acc" (yop Op.mulmod [yvar "q_selector_acc",
              yop Op.mload [yop Op.add [ylit slots.selectorPowerMptr, ylit (g * wordBytes)]],
              yvar "r"])]
      else []
      | none => []
  [yblock ([ylet "q_selector_ptr" (yop Op.add [yvar "SELECTOR_ACC_MPTR", ylit (idx * 0x20)]),
            ylet "q_selector_acc" (yop Op.mload [yvar "q_selector_ptr"])] ++ gapStmts ++
           [yexpr (yop Op.mstore [yvar "q_selector_ptr",
              yop Op.addmod [yvar "q_selector_acc", value, yvar "r"]])])]

/-! ### The inline and native-identity families: the twin of 'direct_quotient_block' -/

/-- THE AST TWIN OF 'directQuotientBlock' (FoldCompute.lean:421-446) - the producer of BOTH the
    inline prefix and the native-identity family. Same seven inputs, same order of statements; the
    identity's own expression lines are the only part still spliced by parse, and everything the
    producer itself writes is built from the fields. -/
def qEmitDirectBlock (lines : List String) (var : String) (target : QuotientTarget)
    (selectorGap : Option Nat) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) : Block Op :=
  let inner := qGenFlat (specializeLimb7Chains lines)
  let scratch : Expr Op := yop Op.mload [ylit evalScratchSlot]
  let b0 := [yblock (inner ++ [yexpr (yop Op.mstore [ylit evalScratchSlot, yvar var])])]
  let b1 := b0 ++ qPushTraceA slots scratch trace
  let b2 := b1 ++ qFoldAdvance1A slots
  match target with
  | QuotientTarget.main => b2 ++ qEvalNumerAddA slots scratch
  | QuotientTarget.selector idx => b2 ++ qSelectorBucketA slots idx selectorGap scratch

/-- THE INLINE FAMILY AS AN AST: one block per inline identity, in plan order, each built by
    'qEmitDirectBlock'. This is the twin ROW.Q.5 inducts over: the producer maps the same function
    over the same list and returns lines instead of statements. -/
def qEmitInlineFamily (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) : Block Op :=
  ids.flatMap fun id =>
    qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot slots trace

/-- THE NATIVE-IDENTITY FAMILY AS AN AST, spelled as the CASE LIST the render consumes: one
    '(case index0 => ...)' per identity, in list order, with the same fail-closed default the
    template's switch carries. Distinct from 'qEmitInlineFamily' in exactly the way the render is
    distinct: the identity family is a switch body, the inline family is a statement run. -/
def qEmitNativeIdentityCases (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    List (Literal × Block Op) :=
  (ids.zipIdx).map fun (id, i) =>
    (Literal.number i,
      qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot slots trace)

/-- The native-identity family as the flat statement run 'qGenNested' builds today, so the two
    acceptance contexts compare against one spelling. -/
def qEmitNativeIdentityFamily (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) : Block Op :=
  ((qEmitNativeIdentityCases ids fold evalScratchSlot slots trace).map Prod.snd).flatten

/-- The switch the native-identity arm carries: the cases above over 'q_native_idx' with the
    template's fail-closed default. This is what 'qvmNativeArms' splices as a case list. -/
def qEmitNativeIdentitySwitch (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) : Stmt Op :=
  Stmt.switch (yvar "q_native_idx")
    (qEmitNativeIdentityCases ids fold evalScratchSlot slots trace)
    (some [yexpr (ycall "q_program_fail" [])])

/-! ### The post-VM family: the twin of 'structured_trash_loop_block' -/

/-- THE AST TWIN OF 'structuredTrashLoopBlock' (QuotientBlocks.lean:805-834). The producer runs in
    'FM F' and pushes strings; this runs in the Evaluator's own 'E F' and pushes statements, and it
    calls the Evaluator's AST twins ('compressExpressionsA', 'evaluateA') where the producer calls
    the text ones - which is what makes it a twin and not a re-parse. The 'q_trash_tau' load is
    emitted ONCE outside the loop here exactly as at Q:1955, the one place the structured path and
    the Evaluator's own trashcan path differ. The 'base' parameter of the producer is the fold-site
    position, which only the Weighted fold records; the compact path always passes Horner, so the
    twin takes the two fields the Horner arm carries instead. -/
def qEmitTrashBlock {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool) :
    E F (Option (Block Op)) := do
  let st0 ← get
  if st0.meta_.numTrashcans == 0 then pure none
  else do
    let tau : String := "q_trash_tau"
    let head : Block Op := [ylet tau (yop Op.mload [yvar "TRASH_CHALLENGE_MPTR"])]
    let blocks ← st0.cs.trashcans.toList.zipIdx.mapM fun (argument, idx) => do
      resetLocals
      let (compressedLines, compressedVar) ←
        compressExpressionsA argument.constraintExpressions.toList tau
      let (selectorLines, selectorVar) ← evaluateA argument.selector
      let st ← get
      let trashEval ← atIndex st.data.trashcanEvals idx 1974 "trashcan evals index"
      pure (yblock (compressedLines ++ selectorLines ++
        [ylet "q_trash_one_minus_selector" (yaddmod (ylit 1) (ysubR (yvar selectorVar))),
         ylet "q_trash_scaled" (ymulmod (yvar "q_trash_one_minus_selector") (wordExpr trashEval)),
         ylet "q_trash_eval" (yaddmod (yvar compressedVar) (ysubR (yvar "q_trash_scaled")))]
        ++ qHornerFoldA slots trace (yvar "q_trash_eval")))
    pure (some [yblock (head ++ blocks)])

/-- THE POST-VM FAMILY AS AN AST: the trash block, or nothing when the circuit has no trashcans -
    the producer returns 'none' there and the render emits an empty splice, which
    'qemPostVm_allArmsAndEmpty_ok' pins rather than leaves to the comment. -/
def qEmitPostVmFamily {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (ev : Evaluator F) : Option (Block Op) :=
  match (qEmitTrashBlock slots trace).run ev with
  | .ok (r, _) => r
  | .error _ => none

end Midfall.Lowering.GenAst
