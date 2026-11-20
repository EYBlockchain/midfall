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
-- QuotientBlocks.lean:866, and 'compactBlocksHornerRecordsNoSites_ok' gates it), and the legacy/direct
-- family 'quotientEvalNumerComputations' (it renders in the template's 'when None' arm, which
-- OBJ.15's fence excludes).
--
-- QEMIT2 COMPLETES THE SET. The two native structured loop blocks QEMIT reported as the remainder are
-- here too: 'qEmitPermutationBlockA' (1,038 tokens at the deployment) and 'qEmitLookupBlockA' (458).
-- Both stage tables through 'pushMstoreMloadLiteralRuns', so that producer is twin'd FIRST, as
-- 'qPushMstoreMloadLiteralRunsA' - the compactor's five single-line rejections, its 'count < 3' rule
-- and its two 'src_stride' arms are what the permutation block's six tables and the lookup block's
-- staging depend on. The permutation block writes NO Evaluator expression lines at all, so its twin
-- is complete rather than split; the lookup block's compressed input, selector and table lines stay
-- spliced by the 'GenAstQuotient' twins, and its 'lookupSharedPrefixFPlusBeta' scaffolding is twin'd
-- as 'qLookupSharedPrefixA'. All of it stays UNWIRED: the deployed program still reaches these two
-- families through OBJ.2's parse, so the fingerprint does not move.
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
open Midfall.Generator.QuotientBlocks Midfall.Halo2

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

/-! ### THE PREREQUISITE: 'pushMstoreMloadLiteralRuns' as AST -/

/-- The AST reading of 'yulMloadLiteralExpr' (FoldCompute.lean:208-214). On the text side the
    producer re-parses the expression it is about to store; on this side the same test is
    structural, and it rejects exactly the same shapes: 'calldataload(...)', 'mload(X)',
    'mload(add(X, 0x20))' and an mload of anything other than one number literal. Every entry
    the two native blocks stage is a 'wordExpr', so the four spellings a 'Word' can take
    (memory/calldata x numeric/named) all reach this test. -/
def qMloadLiteralA? (e : Expr Op) : Option Nat :=
  match e with
  | .builtin Op.mload [(.lit (Literal.number n))] => some n
  | _ => none

/-! QEMIT3 LIFT OF THE COMPACTOR'S THREE INNER BINDINGS. 'single', 'extend' and the inner 'let rec go'
    were let-bound INSIDE 'qPushMstoreMloadLiteralRunsA' - this is the gap ROW.Q.5 names ("the
    compactor's recursion is a 'let rec go' at line 236"), so no statement could induct over it. They
    are top-level 'def's now, with the captured 'dst' / 'entries' / 'loopPrefix' made explicit
    parameters. EVERY BODY IS THE SAME TERM, STATEMENT FOR STATEMENT: the five single-line rejections,
    the 'count < 3' rule, the two 'src_stride' arms, the fuel and the index arithmetic are untouched, so
    the VALUE of 'qPushMstoreMloadLiteralRunsA' is unchanged and the 'qem2Runs_*' gates keep their
    teeth. -/

/-- The compactor's single-store emission: append 'mstore(dst + dstBase, expr)' to the running block. -/
def qMloadRunSingleA (dst : String) (b : Block Op) (dstBase : Nat) (expr : Expr Op) : Block Op :=
  b ++ [yexpr (yop Op.mstore [yop Op.add [yvar dst, ylit dstBase], expr])]

/-- The compactor's forward-walking run test: how many entries from 'count' on still lie on the
    '(dstBase, srcBase)' grid with stride '(0x20, srcStride)'. -/
def qMloadRunExtendA (dstBase srcBase srcStride : Nat) : List (Nat × Expr Op) → Nat → Nat
  | [], count => count
  | (candDst, candExpr) :: rest, count =>
      match qMloadLiteralA? candExpr with
      | none => count
      | some candSrc =>
          if candDst == dstBase + count * 0x20 && candSrc == srcBase + count * srcStride
          then qMloadRunExtendA dstBase srcBase srcStride rest (count + 1)
          else count

/-- THE COMPACTOR'S RECURSION, AS A TOP-LEVEL INDUCTION TARGET. Structurally recursive on the fuel, so
    the run decomposition ROW.Q.5 could not reach is now an induction on 'fuel' - see
    'qMloadRunGoA_split' and 'qPushMstoreMloadLiteralRunsA_value'. -/
def qMloadRunGoA (dst : String) (entries : List (Nat × Expr Op)) (loopPrefix : String)
    (b : Block Op) : Nat → Nat → Block Op
  | 0, _ => b
  | fuel + 1, idx =>
      if idx >= entries.length then b
      else
        let (dstBase, expr) := entries.getD idx (0, ylit 0)
        let singleStep := qMloadRunSingleA dst b dstBase expr
        match qMloadLiteralA? expr with
        | none => qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
        | some srcBase =>
            match (entries.drop (idx + 1)).head? with
            | none => qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
            | some (nextDst, nextExpr) =>
                if nextDst != dstBase + 0x20 then
                  qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
                else match qMloadLiteralA? nextExpr with
                  | none => qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
                  | some nextSrc => match natSubOpt nextSrc srcBase with
                    | none => qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
                    | some srcStride =>
                        if srcStride == 0 then
                          qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
                        else
                          let count :=
                            qMloadRunExtendA dstBase srcBase srcStride (entries.drop (idx + 2)) 2
                          if count < 3 then
                            qMloadRunGoA dst entries loopPrefix singleStep fuel (idx + 1)
                          else
                            let ivar := loopPrefix ++ "_i"
                            let doff := loopPrefix ++ "_dst_off"
                            let soff := loopPrefix ++ "_src_off"
                            let loop : Stmt Op :=
                              Stmt.forLoop [ylet ivar (ylit 0)]
                                (yop Op.lt [yvar ivar, ylit count])
                                [yset ivar (yop Op.add [yvar ivar, ylit 1])]
                                ([ylet doff (yop Op.shl [ylit 5, yvar ivar]),
                                  ylet soff (if srcStride == 0x20 then yvar doff
                                             else yop Op.mul [yvar ivar, ylit srcStride]),
                                  yexpr (yop Op.mstore
                                    [yop Op.add [yop Op.add [yvar dst, ylit dstBase], yvar doff],
                                     yop Op.mload [yop Op.add [ylit srcBase, yvar soff]]])])
                            qMloadRunGoA dst entries loopPrefix (b ++ [yblock [loop]]) fuel
                              (idx + count)

/-- THE AST TWIN OF 'pushMstoreMloadLiteralRuns' (QuotientBlocks.lean:422-482) - the run
    compactor BOTH native loop families stage their tables through, and the prerequisite QEMIT
    reported as missing. Same five single-line rejections in the producer's order, the same
    forward-walking 'extend', the same 'count < 3' rule that leaves a pair uncompacted, the
    same fuel (length + 1), and the same two 'src_stride' arms: 0x20 reuses the destination
    offset variable, anything else multiplies by the stride literal. The producer appends
    strings to a running block; this appends statements to a running block, which is the
    granularity a list induction over the producer needs. -/
def qPushMstoreMloadLiteralRunsA (block : Block Op) (dst : String)
    (entries : List (Nat × Expr Op)) (loopPrefix : String) : Block Op :=
  qMloadRunGoA dst entries loopPrefix block (entries.length + 1) 0

/-- The AST twin of 'FoldLoop.header' (FoldTypes.lean:202-206) plus the body and the closing
    brace: the loop as ONE statement, which is what the parse of the header line plus the body
    plus '"}"' produces. The permutation block's two fold loops go through the producer's
    'FoldLoop'; the inner 'q_perm_j' loop and every lookup loop are hand-written strings with
    the same shape, and 'permLoopsUseFoldHeaderNotHandWritten_ok' (QuotientBlocks.lean:1794)
    pins which is which there. The start and end are expressions here because the hand-written
    loops start at a variable. -/
def qForLoopA (var : String) (start end_ : Expr Op) (body : Block Op) : Stmt Op :=
  Stmt.forLoop [ylet var start] (yop Op.lt [yvar var, end_])
    [yset var (yop Op.add [yvar var, ylit 1])] body

/-- 'FoldLoop.header' at the AST: the same loop with the two Nat fields of the record. -/
def qFoldLoopA (loop : FoldLoop) (body : Block Op) : Stmt Op :=
  qForLoopA loop.var (ylit loop.start) (ylit loop.end_) body

/-! ### Family 4: the NATIVE PERMUTATION block ('quotientNativePermutationComputation') -/

/-- QEMIT3 LIFT: the permutation family's 'mapM' step, named. It was an inner lambda of
    'qEmitPermutationBlockA' (the second gap ROW.Q.5 names); the body is the same term, so the value of
    'pairs' - and of every gate that reads it - is unchanged. -/
def qPermutationPairStepA {F : Type} [BEq F] (column : Column) (idx : Nat)
    : E F ((Nat × Expr Op) × (Nat × Expr Op)) := do
  let value ← evalAtExpr column 0
  let st ← get
  let sigma ← expectOpt (hashMapGet st.data.permutationEvals column)
    1518 "permutation sigma eval present"
  pure ((idx * 0x20, value), (idx * 0x20, wordExpr sigma))

/-- QEMIT3 LIFT: the permutation family's staged region, named. The five compactor calls are the same
    five, in the same order, with the same destinations and loop prefixes; only the running 'staged'
    accumulator moves into the definition, so the emitted statement run is identical. -/
def qEmitPermutationStagingA (pairs : List ((Nat × Expr Op) × (Nat × Expr Op)))
    (zCur zNext zLast : List (Nat × Expr Op)) : Block Op :=
  let staged :=
    qPushMstoreMloadLiteralRunsA [] "q_perm_vals" (pairs.map Prod.fst) "q_perm_val_load"
  let staged :=
    qPushMstoreMloadLiteralRunsA staged "q_perm_sigmas" (pairs.map Prod.snd) "q_perm_sigma_load"
  let staged := qPushMstoreMloadLiteralRunsA staged "q_perm_z_cur" zCur "q_perm_z_cur_load"
  let staged := qPushMstoreMloadLiteralRunsA staged "q_perm_z_next" zNext "q_perm_z_next_load"
  qPushMstoreMloadLiteralRunsA staged "q_perm_z_last" zLast "q_perm_z_last_load"

/-- THE AST TWIN OF 'structuredPermutationLoopBlock' (QuotientBlocks.lean:522-626). The whole
    block is scaffolding: unlike the three families above, this producer writes NO expression
    lines through the Evaluator at all - every value it interpolates is a 'Word' rendered by
    'wordString', whose AST twin is 'wordExpr', and every identity line is a literal string in
    the reference. So this twin is complete: there is nothing left spliced by 'qGenFlat'.
    The same three deviations as the trash twin. (1) The 'fold' parameter is destructured into
    the two fields its 'horner' arm reads, because the compact path always passes 'horner'
    (QuotientBlocks.lean:862) and 'pushStructuredFold' ignores 'FoldPos' on that arm
    (FoldCompute.lean:390-391) - so 'base' is a fold-site fact and a Horner twin does not take
    it. (2) The producer runs in 'FM F' and pushes strings; this runs in 'E F' and pushes
    statements, reading meta and data from the threaded Evaluator exactly as 'evRun' does.
    (3) The two 'evRun (feToU256String ...)' renders become 'feToU256Expr', so DELTA and
    DELTA^chunk_len are still COMPUTED from the field dictionary here and never transcribed -
    'deltaAst_computedNotHardcoded_ok' is the Evaluator-side precedent for why that matters. -/
def qEmitPermutationBlockA {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) : E F (Option (Block Op)) := do
  let st0 ← get
  let meta_ := st0.meta_
  if meta_.numPermutationZs == 0 then pure none
  else do
    let numCols := meta_.permutationColumns.length
    let numSets := meta_.numPermutationZs
    let chunkLen := meta_.permutationChunkLen
    let valsMptr := scratchMptr
    let sigmasMptr := valsMptr + numCols * 0x20
    let zCurMptr := sigmasMptr + numCols * 0x20
    let zNextMptr := zCurMptr + numSets * 0x20
    let zLastMptr := zNextMptr + numSets * 0x20
    let deltaBaseMptr := zLastMptr + (numSets - 1) * 0x20
    let deltaChunk ← feToU256Expr (st0.field.powNat st0.field.delta chunkLen)
    let delta ← feToU256Expr st0.field.delta
    -- Q:1512 '.enumerate()' -> zipIdx, yielding (element, index).
    let pairs ← meta_.permutationColumns.zipIdx.mapM fun (column, idx) =>
      qPermutationPairStepA column idx
    let st1 ← get
    let zTriples := st1.data.permutationZEvals
    let zCur := (zTriples.zipIdx).map fun ((c, _, _), idx) => (idx * 0x20, wordExpr c)
    let zNext := (zTriples.zipIdx).map fun ((_, n, _), idx) => (idx * 0x20, wordExpr n)
    let zLast := (zTriples.zipIdx).filterMap fun t => match t with
      | ((_, _, some l), idx) => some (idx * 0x20, wordExpr l)
      | _ => none
    let staged := qEmitPermutationStagingA pairs zCur zNext zLast
    let ev0 : Expr Op := yvar "q_perm_eval"
    let fold := qHornerFoldA slots trace ev0
    let finalZOffset := (numSets - 1) * 0x20
    let contBody : Block Op :=
      [ylet "q_perm_cur" (yop Op.mload [yop Op.add [yvar "q_perm_z_cur",
                                    yop Op.shl [ylit 5, yvar "q_perm_i"]]]),
       ylet "q_perm_prev" (yop Op.mload [yop Op.add [yvar "q_perm_z_last",
                                    yop Op.shl [ylit 5,
                                      yop Op.sub [yvar "q_perm_i", ylit 1]]]]),
       yset "q_perm_eval" (ymulmod (yop Op.mload [yvar "L_0_MPTR"])
         (yaddmod (yvar "q_perm_cur") (ysubR (yvar "q_perm_prev"))))]
    let continuity : Block Op :=
      if numSets <= 1 then []
      else [qFoldLoopA { var := "q_perm_i", start := 1, end_ := numSets } (contBody ++ fold)]
    let prodBody : Block Op :=
      [ylet "q_perm_start" (yop Op.mul [yvar "q_perm_set", yvar "q_perm_chunk_len"]),
         ylet "q_perm_end" (yop Op.add [yvar "q_perm_start", yvar "q_perm_chunk_len"]),
         Stmt.cond (yop Op.gt [yvar "q_perm_end", yvar "q_perm_num_cols"])
           [yset "q_perm_end" (yvar "q_perm_num_cols")],
         ylet "q_perm_left" (yop Op.mload [yop Op.add [yvar "q_perm_z_next",
                                       yop Op.shl [ylit 5, yvar "q_perm_set"]]]),
         ylet "q_perm_right" (yop Op.mload [yop Op.add [yvar "q_perm_z_cur",
                                       yop Op.shl [ylit 5, yvar "q_perm_set"]]]),
         ylet "q_perm_delta_pow" (yop Op.mload [yvar "q_perm_delta_base_ptr"]),
         qForLoopA "q_perm_j" (yvar "q_perm_start") (yvar "q_perm_end")
           [ylet "q_perm_off" (yop Op.shl [ylit 5, yvar "q_perm_j"]),
            ylet "q_perm_v" (yop Op.mload [yop Op.add [yvar "q_perm_vals", yvar "q_perm_off"]]),
            ylet "q_perm_s" (yop Op.mload [yop Op.add [yvar "q_perm_sigmas", yvar "q_perm_off"]]),
            yset "q_perm_left" (ymulmod (yvar "q_perm_left")
              (yaddmod (yaddmod (yvar "q_perm_v")
                (ymulmod (yop Op.mload [yvar "BETA_MPTR"]) (yvar "q_perm_s")))
                (yop Op.mload [yvar "GAMMA_MPTR"]))),
            yset "q_perm_right" (ymulmod (yvar "q_perm_right")
              (yaddmod (yaddmod (yvar "q_perm_v") (yvar "q_perm_delta_pow"))
                (yop Op.mload [yvar "GAMMA_MPTR"]))),
            yset "q_perm_delta_pow" (ymulmod (yvar "q_perm_delta_pow") (yvar "delta"))],
         yset "q_perm_eval" (ymulmod
           (yaddmod (ylit 1) (ysubR (yaddmod (yop Op.mload [yvar "L_LAST_MPTR"])
                                              (yop Op.mload [yvar "L_BLIND_MPTR"]))))
           (yaddmod (yvar "q_perm_left") (ysubR (yvar "q_perm_right"))))]
        ++ fold ++
        [yexpr (yop Op.mstore [yvar "q_perm_delta_base_ptr",
          ymulmod (yop Op.mload [yvar "q_perm_delta_base_ptr"]) (yvar "q_perm_delta_chunk")])]
    let products : Block Op :=
      [qFoldLoopA { var := "q_perm_set", start := 0, end_ := numSets } prodBody]
    pure (some [yblock
      ([ylet "delta" delta,
        ylet "q_perm_vals" (ylit valsMptr),
        ylet "q_perm_sigmas" (ylit sigmasMptr),
        ylet "q_perm_z_cur" (ylit zCurMptr),
        ylet "q_perm_z_next" (ylit zNextMptr),
        ylet "q_perm_z_last" (ylit zLastMptr),
        ylet "q_perm_delta_base_ptr" (ylit deltaBaseMptr),
        ylet "q_perm_num_cols" (ylit numCols),
        ylet "q_perm_num_sets" (ylit numSets),
        ylet "q_perm_chunk_len" (ylit chunkLen),
        ylet "q_perm_delta_chunk" deltaChunk] ++ staged ++
       [ylet "q_perm_eval" (ylit 0),
        yset "q_perm_eval" (ymulmod (yop Op.mload [yvar "L_0_MPTR"])
          (yaddmod (ylit 1) (ysubR (yop Op.mload [yvar "q_perm_z_cur"]))))] ++ fold ++
       [ylet "q_perm_zn" (yop Op.mload [yop Op.add [yvar "q_perm_z_cur", ylit finalZOffset]]),
        yset "q_perm_eval" (ymulmod (yop Op.mload [yvar "L_LAST_MPTR"])
          (yaddmod (ymulmod (yvar "q_perm_zn") (yvar "q_perm_zn"))
            (ysubR (yvar "q_perm_zn"))))] ++ fold ++
       continuity ++
       [yexpr (yop Op.mstore [yvar "q_perm_delta_base_ptr",
          ymulmod (yop Op.mload [yvar "BETA_MPTR"]) (yop Op.mload [yvar "X_MPTR"])])] ++
       products)])

/-- THE NATIVE PERMUTATION FAMILY AS AN AST, at the deployment's own Evaluator. 'none' when the
    circuit has no permutation z, exactly as the producer returns 'none' and the caller stores
    '[]' (QuotientBlocks.lean:884-889). -/
def qEmitNativePermutationA {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) (ev : Evaluator F) : Option (Block Op) :=
  match (qEmitPermutationBlockA scratchMptr slots trace).run ev with
  | .ok (r, _) => r
  | .error _ => none

/-! ### Family 5: the NATIVE LOOKUP block ('quotientNativeLookupComputation') -/

/-- QEMIT3 LIFT: the 'ptrOf' inner lambda of 'qLookupSharedPrefixA', named. Same term. -/
def qLookupPtrOfA {F : Type} [BEq F] (exprs : List (Expression F)) : E F (Option Nat) :=
  match exprs.getLast? with
  | none => pure none
  | some q => expressionMemoryPtr q

/-- The AST twin of 'lookupSharedPrefixFPlusBeta' (Evaluator.lean:708-760): the five rejections
    in the producer's order, then the compressed shared prefix, the scaled prefix, and the
    hand-written staging loop. Only the k >= 2 arm of the lookup block reaches it, and the
    deployment's single lookup has k == 1, so 'qemLookup_sharedPrefixArms_ok' exercises it on
    synthetic chunks against the producer rather than leaving the arm untested. -/
def qLookupSharedPrefixA {F : Type} [BEq F] (inputChunk : List (List (Expression F)))
    (challengeVar betaVar fPlusBetaMptr : String) : E F (Option (Block Op)) := do
  if inputChunk.length < 3 then pure none
  else match inputChunk.head? with
    | none => pure none
    | some first =>
        if first.isEmpty then pure none
        else
          let prefixLen := first.length - 1
          if prefixLen == 0 then pure none
          else
            let sharedPrefix := first.take prefixLen
            let mismatch := inputChunk.any fun exprs =>
              exprs.length != first.length || exprs.take prefixLen != sharedPrefix
            if mismatch then pure none
            else do
              let basePtr? ← match first.getLast? with
                | none => pure none
                | some last => expressionMemoryPtr last
              match basePtr? with
              | none => pure none
              | some basePtr => do
                  let adjacent ← inputChunk.zipIdx.mapM fun (exprs, idx) => do
                    let p ← qLookupPtrOfA exprs
                    pure (match p with
                      | some v => v == basePtr + idx * 0x20
                      | none => false)
                  if ! (adjacent.all id) then pure none
                  else do
                    let (prefixLines, prefixVar) ← compressExpressionsA sharedPrefix challengeVar
                    let (scaledLines, prefixScaled) ←
                      freshLetA (ymulmod (yvar prefixVar) (yvar challengeVar))
                    let body : Block Op :=
                      [ylet "q_lookup_shared_off" (yop Op.shl [ylit 5, yvar "q_lookup_shared_i"]),
                       ylet "q_lookup_shared_tail" (yop Op.mload
                         [yop Op.add [ylit basePtr, yvar "q_lookup_shared_off"]]),
                       ylet "q_lookup_shared_compressed"
                         (yaddmod (yvar prefixScaled) (yvar "q_lookup_shared_tail")),
                       yexpr (yop Op.mstore [yop Op.add [yvar fPlusBetaMptr,
                                                yvar "q_lookup_shared_off"],
                         yaddmod (yvar "q_lookup_shared_compressed") (yvar betaVar)])]
                    pure (some (prefixLines ++ scaledLines ++
                      [qForLoopA "q_lookup_shared_i" (ylit 0) (ylit inputChunk.length) body]))

/-! QEMIT3 LIFT OF THE LOOKUP BLOCK'S INNER STEPS. The three lambdas ROW.Q.5 names as the reason the
    per-item induction was unreachable - the 'perLookup' step whose last line was 'pure [yblock
    (boundary ++ helpers.flatten ++ [yblock accumulator])]', the three-arm 'helpers' step, and the
    'perInput' staging step - plus the four tiny expression shorthands they captured, are top-level
    'def's now. Each step is split into a BODY (the statements inside the braces) and a STEP (the body
    wrapped in 'pure [yblock ...]', exactly as the lambda's last line did), which is what makes the
    one-block-per-item shape provable without unfolding the body at all. NO BODY WAS REWRITTEN: the
    rejections, the k-arms, the four staging loops, the 'sub(r, 1)' that only the k == 1 arm writes, the
    'resetLocals' positions and the fold are character-for-character the same terms, so the value of
    'qEmitLookupBlockA' is unchanged and every 'qemLookup_*' gate keeps its teeth. -/

/-- The compactor shorthand the lookup staging used as an inner lambda. -/
def qLookupShl5A (e : Expr Op) : Expr Op := yop Op.shl [ylit 5, e]

/-- 'mload(base + off)', the inner shorthand of 'qEmitLookupBlockA'. -/
def qLookupMloadAtA (base : String) (off : Expr Op) : Expr Op :=
  yop Op.mload [yop Op.add [yvar base, off]]

/-- 'mstore(base + off, v)', the inner shorthand of 'qEmitLookupBlockA'. -/
def qLookupMstoreAtA (base : String) (off : Expr Op) (v : Expr Op) : Stmt Op :=
  yexpr (yop Op.mstore [yop Op.add [yvar base, off], v])

/-- 'mstore(base, v)', the inner shorthand of 'qEmitLookupBlockA'. -/
def qLookupMstoreImmA (base : String) (v : Expr Op) : Stmt Op :=
  yexpr (yop Op.mstore [yvar base, v])

/-- The ten scratch-and-challenge loads that were the let-bound 'head' of the block's final 'yblock'
    (the other half of the goal state ROW.Q.5 could not refer to). -/
def qEmitLookupHeadA (fPlusBetaMptr prefixMptr suffixMptr : Nat) : Block Op :=
  [ylet "q_lookup_f" (ylit fPlusBetaMptr),
   ylet "q_lookup_prefix" (ylit prefixMptr),
   ylet "q_lookup_suffix" (ylit suffixMptr),
   ylet "q_lookup_l0" (yop Op.mload [yvar "L_0_MPTR"]),
   ylet "q_lookup_llast" (yop Op.mload [yvar "L_LAST_MPTR"]),
   ylet "q_lookup_lblind" (yop Op.mload [yvar "L_BLIND_MPTR"]),
   ylet "q_lookup_lsum" (yaddmod (yvar "q_lookup_l0") (yvar "q_lookup_llast")),
   ylet "q_lookup_active" (yaddmod (ylit 1)
     (ysubR (yaddmod (yvar "q_lookup_llast") (yvar "q_lookup_lblind")))),
   ylet "q_lookup_beta" (yop Op.mload [yvar "BETA_MPTR"]),
   ylet "q_lookup_theta" (yop Op.mload [yvar "THETA_MPTR"])]

/-- THE INNERMOST LIFTED STEP: one staged parallel input. Was the 'perInput' lambda inside the k >= 2
    arm. -/
def qEmitLookupStageInputStepA {F : Type} [BEq F] (theta : String)
    (parallelInput : Array (Expression F)) (inputIdx : Nat) : E F (Block Op) := do
  let (compressedLines, compressedVar) ← compressExpressionsA parallelInput.toList theta
  pure (compressedLines ++
    [qLookupMstoreAtA "q_lookup_f" (ylit (inputIdx * 0x20))
      (yaddmod (yvar compressedVar) (yvar "q_lookup_beta"))])

/-- THE THREE-ARM CHUNK BODY, LIFTED: the statements the 'helpers' step emits for one input chunk, for
    each of the producer's three k-arms. 'elem' is the '(chunk, h-eval)' pair the producer's own
    'zip' builds; the 'zipIdx' index is not read by any arm, exactly as in the lambda it replaces. -/
def qEmitLookupChunkBodyA {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (theta : String) (elem : Array (Array (Expression F)) × MWord) (_chunk : Nat)
    : E F (Block Op) := do
  let inputChunk := elem.fst.toList
  let hEval := elem.snd
  let k := inputChunk.length
  let fold := qHornerFoldA slots trace (yvar "q_lookup_eval")
  if k == 0 then
    pure ([ylet "q_lookup_eval" (ylit 0)] ++ fold)
  else if k == 1 then do
    resetLocals
    let first ← StateT.lift (atQ inputChunk 0 1776 "input chunk index")
    let (compressedLines, compressedVar) ← compressExpressionsA first.toList theta
    pure (compressedLines ++
      [ylet "q_lookup_eval" (yaddmod
        (ymulmod (wordExpr hEval) (yaddmod (yvar compressedVar) (yvar "q_lookup_beta")))
        (yop Op.sub [yvar "r", ylit 1]))] ++ fold)
  else do
    resetLocals
    let shared ← qLookupSharedPrefixA (inputChunk.map fun pi => pi.toList)
      theta "q_lookup_beta" "q_lookup_f"
    -- THE SHARED PREFIX REPLACES ONLY THE STAGING. Everything from 'let q_lookup_product := 1'
    -- (QuotientBlocks.lean:728) to the 'q_lookup_eval' line (:754) is emitted AFTER the 'match
    -- shared' and so runs on BOTH arms - a first draft that put the product, prefix, suffix and
    -- sum loops inside the 'none' arm tied at the deployment (which never reaches this arm) and
    -- reddened at the synthetic four-input chunk. That is the bug the gate below exists to find.
    let staging : Block Op ← match shared with
      | some ls => pure ls
      | none => do
          let perInput ← inputChunk.zipIdx.mapM fun (parallelInput, inputIdx) =>
            qEmitLookupStageInputStepA theta parallelInput inputIdx
          pure perInput.flatten
    let prodLoop := qForLoopA "q_lookup_prod_i" (ylit 0) (ylit k)
      [yset "q_lookup_product" (ymulmod (yvar "q_lookup_product")
        (qLookupMloadAtA "q_lookup_f" (qLookupShl5A (yvar "q_lookup_prod_i"))))]
    let prefLoop := qForLoopA "q_lookup_pref_i" (ylit 1) (ylit k)
      [ylet "q_lookup_pref_prev" (yop Op.sub [yvar "q_lookup_pref_i", ylit 1]),
       qLookupMstoreAtA "q_lookup_prefix" (qLookupShl5A (yvar "q_lookup_pref_i"))
         (ymulmod (qLookupMloadAtA "q_lookup_prefix" (qLookupShl5A (yvar "q_lookup_pref_prev")))
           (qLookupMloadAtA "q_lookup_f" (qLookupShl5A (yvar "q_lookup_pref_prev"))))]
    let sufLoop := Stmt.forLoop
        [ylet "q_lookup_suf_i" (yop Op.sub [ylit k, ylit 1])]
        (yop Op.gt [yvar "q_lookup_suf_i", ylit 0])
        [yset "q_lookup_suf_i" (yop Op.sub [yvar "q_lookup_suf_i", ylit 1])]
        [ylet "q_lookup_suf_prev" (yop Op.sub [yvar "q_lookup_suf_i", ylit 1]),
         qLookupMstoreAtA "q_lookup_suffix" (qLookupShl5A (yvar "q_lookup_suf_prev"))
           (ymulmod (qLookupMloadAtA "q_lookup_suffix" (qLookupShl5A (yvar "q_lookup_suf_i")))
             (qLookupMloadAtA "q_lookup_f" (qLookupShl5A (yvar "q_lookup_suf_i"))))]
    let sumLoop := qForLoopA "q_lookup_sum_i" (ylit 0) (ylit k)
      [yset "q_lookup_sum" (yaddmod (yvar "q_lookup_sum")
        (ymulmod (qLookupMloadAtA "q_lookup_prefix" (qLookupShl5A (yvar "q_lookup_sum_i")))
          (qLookupMloadAtA "q_lookup_suffix" (qLookupShl5A (yvar "q_lookup_sum_i")))))]
    pure (staging ++
      [ylet "q_lookup_product" (ylit 1), prodLoop,
       qLookupMstoreImmA "q_lookup_prefix" (ylit 1)] ++
      (if k <= 1 then [] else [prefLoop]) ++
      [qLookupMstoreAtA "q_lookup_suffix" (ylit ((k - 1) * 0x20)) (ylit 1)] ++
      (if k <= 1 then [] else [sufLoop]) ++
      [ylet "q_lookup_sum" (ylit 0), sumLoop,
       ylet "q_lookup_eval" (yaddmod
         (ymulmod (wordExpr hEval) (yvar "q_lookup_product"))
         (ysubR (yvar "q_lookup_sum")))] ++ fold)

/-- The chunk STEP: the body in one braced block. This is the 'pure [yblock ...]' the lambda ended with. -/
def qEmitLookupChunkStepA {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (theta : String) (elem : Array (Array (Expression F)) × MWord) (chunk : Nat)
    : E F (Block Op) := do
  let body ← qEmitLookupChunkBodyA slots trace theta elem chunk
  pure [yblock body]

/-- THE PER-LOOKUP BODY, LIFTED: everything the 'perLookup' lambda emitted for one lookup, as the
    contents of the block the producer wraps them in. -/
def qEmitLookupPerItemBodyA {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (theta : String) (csDegree : Nat) (lookup : LogupBatchedArgument F) (lookupIdx : Nat)
    : E F (Block Op) := do
  let chunked ← StateT.lift (LogupBatchedArgument.chunkByDegree lookup csDegree)
  let st ← get
  -- Q:1728: a direct Vec index, so an out-of-range lookup index aborts (R4).
  let (mEval, hEvals, zEval, zNextEval) ←
    atIndex st.data.lookupEvals lookupIdx 1728 "lookup evals index"
  let fold := qHornerFoldA slots trace (yvar "q_lookup_eval")
  -- boundary = (l_0 + l_last) * Z_lookup(x)   (Q:1732-1748)
  let boundary : Block Op :=
    [yblock ([ylet "q_lookup_eval"
      (ymulmod (yvar "q_lookup_lsum") (wordExpr zEval))] ++ fold)]
  -- one helper identity per input chunk (Q:1750-1876). The zip is INSIDE the enumerate, so
  -- zipIdx hands back ((chunk_list, h_eval), index).
  let helpers ← (chunked.inputExpressionChunks.toList.zip hEvals).zipIdx.mapM
      fun (elem, chunk) => qEmitLookupChunkStepA slots trace theta elem chunk
  -- accumulator = active * ((Z_next - Z - selector * sum(h)) * (table + beta) + m)
  let sumHLines : Block Op := match hEvals with
    | [] => []
    | first :: rest =>
        [ylet "q_lookup_sum_h" (wordExpr first)] ++
          rest.map (fun h => yset "q_lookup_sum_h"
            (yaddmod (yvar "q_lookup_sum_h") (wordExpr h)))
  let sumHExpr : Expr Op := match hEvals with
    | [] => ylit 0
    | _ => yvar "q_lookup_sum_h"
  resetLocals
  let (selectorLines, selectorVar) ← evaluateA chunked.selector
  let (tableLines, tableVar) ← compressExpressionsA chunked.tableExpressions.toList theta
  let accumulator : Block Op :=
    sumHLines ++ selectorLines ++ tableLines ++
      [ylet "q_lookup_s_sum_h" (ymulmod (yvar selectorVar) sumHExpr),
       ylet "q_lookup_diff" (yaddmod (wordExpr zNextEval)
         (ysubR (yaddmod (wordExpr zEval) (yvar "q_lookup_s_sum_h")))),
       ylet "q_lookup_t_beta" (yaddmod (yvar tableVar) (yvar "q_lookup_beta")),
       ylet "q_lookup_core" (yaddmod (ymulmod (yvar "q_lookup_diff") (yvar "q_lookup_t_beta"))
         (wordExpr mEval)),
       ylet "q_lookup_eval" (ymulmod (yvar "q_lookup_active") (yvar "q_lookup_core"))] ++ fold
  pure (boundary ++ helpers.flatten ++ [yblock accumulator])

/-- THE PER-LOOKUP STEP, LIFTED: one braced block per lookup, which is the shape the per-item lemma
    needs and the reason the split into body and step is worth making. -/
def qEmitLookupPerItemStepA {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (theta : String) (csDegree : Nat) (lookup : LogupBatchedArgument F) (lookupIdx : Nat)
    : E F (Block Op) := do
  let body ← qEmitLookupPerItemBodyA slots trace theta csDegree lookup lookupIdx
  pure [yblock body]

/-- THE PER-LOOKUP REGION, LIFTED: the 'mapM' the producer ran over the circuit's own lookup list.
    Named, with the list a parameter, so the region's length is a statement about a list. -/
def qEmitLookupRegionA {F : Type} [BEq F] (lookups : List (LogupBatchedArgument F))
    (slots : QuotientStateSlots) (trace : Bool) (theta : String) (csDegree : Nat)
    : E F (List (Block Op)) :=
  lookups.zipIdx.mapM fun (lookup, lookupIdx) =>
    qEmitLookupPerItemStepA slots trace theta csDegree lookup lookupIdx

/-- THE AST TWIN OF 'structuredLookupLoopBlock' (QuotientBlocks.lean:647-792) - unchanged value, now
    assembled from the lifted pieces above. Scaffolding here, spliced expression lines there, exactly
    as the three families above: the compressed input lines, the selector lines and the table lines are
    the Evaluator's own AST twins ('compressExpressionsA', 'evaluateA'), and everything else - the
    three scratch pointers, the seven challenge loads, the boundary/helper/accumulator braces, the four
    hand-written staging loops and the fold - is built from the fields. The 'base' parameter is again a
    fold-site fact the Horner arm never reads, so the twin takes the two fields it does.
    The three k-arms are all ported, including the k == 0 and k == 1 'continue' arms that never
    reach the staging loops, and the 'sub(r, 1)' that only the k == 1 arm writes. -/
def qEmitLookupBlockA {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) : E F (Option (Block Op)) := do
  let st0 ← get
  let meta_ := st0.meta_
  if meta_.numLookups == 0 then pure none
  else do
    let maxParallel ← structuredLookupMaxParallel meta_
    let fPlusBetaMptr := scratchMptr
    let prefixMptr := fPlusBetaMptr + maxParallel * 0x20
    let suffixMptr := prefixMptr + maxParallel * 0x20
    let csDegree ← StateT.lift (ConstraintSystem.degree st0.cs)
    let theta : String := "q_lookup_theta"
    let perLookup ← qEmitLookupRegionA st0.cs.lookups.toList slots trace theta csDegree
    pure (some [yblock (qEmitLookupHeadA fPlusBetaMptr prefixMptr suffixMptr
      ++ perLookup.flatten)])

/-- THE NATIVE LOOKUP FAMILY AS AN AST at the deployment's own Evaluator. -/
def qEmitNativeLookupA {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) (ev : Evaluator F) : Option (Block Op) :=
  match (qEmitLookupBlockA scratchMptr slots trace).run ev with
  | .ok (r, _) => r
  | .error _ => none


/-! ### ROW.Q.5: the per-family VALUE lemmas, as list inductions over the producers -/

/-! ROW.Q.5 (PLAN-V3 card ROW.Q step 3: "one leaf per generated-line family, as a list induction over
its block producer's twin"). QEMIT and QEMIT2 landed the twins; this section is the leaves they
unblocked, and it is the reason the twins exist. Each family gets the same shape of claim: THE VALUE
OF THE EMITTED BLOCK ON A SYMBOLIC INPUT IS THE VALUE THE PRODUCER'S OWN RECURSION COMPUTES, proved by
induction over the family list. No fixture and no render appears below (D-P71): every binder is a
symbolic identity list, slot record, flag or Evaluator, so these hold for the plan the generator will
produce next week as well as the one it produced for the deployment.

WHAT THE INDUCTIONS BUY THAT THE 'Bool' GATES IN 'Midfall/Instances/QvmFamilyKats.lean' CANNOT: the
gates tie a twin to the parse of the producer's own text AT ONE PLAN; these hold for EVERY list the
plan could carry, including the empty one and the singleton, and they are the form a proof of
'q_blockSim' can consume - the row has to reason about the family region of the slice, and the region
is a list image of the plan's identity lists.

FAMILIES LANDED: (1) inline and (2) native-identity, completely - value, cons step, append homology,
split at any index, exact length, case-list shape, switch shape, and the cross-family theorem that the
two emit the same statement run. (3) the post-VM suffix family: the empty-circuit arm and the block
shape (the trash challenge loaded ONCE, then exactly one statement per trashcan) by induction over the
trashcan list in the Evaluator's own state monad.

QEMIT3 CLOSES (4) AND (5). ROW.Q.5 reported the per-item induction for those two as unreachable because
the step functions were inner lambdas and the compactor's recursion was a 'let rec go'; the card left
the choice of remedy to the orchestrator and the answer was to LIFT THEM TO TOP-LEVEL DEFS
('qMloadRunGoA', 'qMloadRunExtendA', 'qMloadRunSingleA', 'qPermutationPairStepA',
'qEmitPermutationStagingA', 'qEmitLookupChunkBodyA', 'qEmitLookupPerItemBodyA',
'qEmitLookupPerItemStepA', 'qEmitLookupRegionA', 'qEmitLookupHeadA' and the four expression
shorthands), with every body the same term and the twins' return types UNCHANGED. What is landed now:
(4) the compactor's run decomposition ('qMloadRunGoA_split',
'qPushMstoreMloadLiteralRunsA_value') and the permutation's five-region staged run
('qEmitPermutationStagingA_value'); (5) the per-lookup region's length and one-block-per-lookup shape
('qEmitLookupRegionA_length', 'qEmitLookupRegionA_items') and the headline
'qEmitNativeLookupA_shape' - the exact goal state ROW.Q.5 printed, now a theorem. The remaining gap
note below is kept as the record of what was unreachable BEFORE the lift. -/

/-- The number of statements the direct producer emits for ONE identity: three with the trace flag
    off, five with it on. The identity's own expression lines do not enter this count - they are all
    inside the one leading 'yblock' - which is what makes the stride uniform and the family block
    sliceable by index. -/
def qFamilyStride (trace : Bool) : Nat := if trace then 5 else 3

/-- **SCAFFOLDING, THE PREREQUISITE EVERY FAMILY INDUCTION USES: the per-identity block has EXACTLY
    'qFamilyStride trace' statements** - three with tracing off, five with it on - for every
    expression-line list, variable name, target, selector gap and scratch slot. The gap arm of
    'qSelectorBucketA' sits inside that block's own 'yblock', so even the gap-versus-panic split does
    not move the count; the 'lines' argument does not either, because 'qGenFlat' puts them in the
    leading block. -/
theorem qEmitDirectBlock_length (lines : List String) (var : String) (target : QuotientTarget)
    (selectorGap : Option Nat) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) :
    (qEmitDirectBlock lines var target selectorGap evalScratchSlot slots trace).length =
      qFamilyStride trace := by
  cases trace <;> cases target <;>
    simp [qEmitDirectBlock, qPushTraceA, qFoldAdvance1A, qEvalNumerAddA, qSelectorBucketA,
      qFamilyStride]

/-- **FAMILY 1 (INLINE), THE CONS STEP** of the producer's own recursion. -/
theorem qEmitInlineFamily_cons (a : QuotientIdentity) (as : List QuotientIdentity)
    (fold : SelectorFoldPlan) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) :
    qEmitInlineFamily (a :: as) fold evalScratchSlot slots trace =
      qEmitDirectBlock a.lines a.var a.target (fold.gapFor a) evalScratchSlot slots trace ++
        qEmitInlineFamily as fold evalScratchSlot slots trace := by
  simp [qEmitInlineFamily, List.flatMap_cons]

/-- **FAMILY 1 (INLINE), THE VALUE LEMMA: the emitted block on a symbolic identity list IS the
    producer's own recursion** - the append of the per-identity blocks in list order. List induction
    over the family list: the empty family emits nothing, and the cons step is
    'qEmitInlineFamily_cons'. -/
theorem qEmitInlineFamily_value (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    qEmitInlineFamily ids fold evalScratchSlot slots trace =
      (ids.map fun id =>
        qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot
          slots trace).flatten := by
  induction ids with
  | nil => rfl
  | cons a as ih =>
      rw [qEmitInlineFamily_cons, ih]
      simp [List.map_cons, List.flatten_cons]

/-- **FAMILY 1 (INLINE), THE LENGTH: one stride per identity**, so the family block is sliceable by
    index and the number of fold sites is the number of identities. Immediate from the induction
    above and the scaffolding lemma. -/
theorem qEmitInlineFamily_length (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    (qEmitInlineFamily ids fold evalScratchSlot slots trace).length =
      ids.length * qFamilyStride trace := by
  induction ids with
  | nil => simp only [qEmitInlineFamily, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons a as ih =>
      rw [qEmitInlineFamily_cons, List.length_append, ih, qEmitDirectBlock_length,
        List.length_cons]
      rw [Nat.succ_mul, Nat.add_comm]

/-- **FAMILY 1 (INLINE), THE APPEND HOMOLOGY**: the producer maps list append to block append, for
    every split of the symbolic list. Induction over the first half. -/
theorem qEmitInlineFamily_append (as bs : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    qEmitInlineFamily (as ++ bs) fold evalScratchSlot slots trace =
      qEmitInlineFamily as fold evalScratchSlot slots trace ++
        qEmitInlineFamily bs fold evalScratchSlot slots trace := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, qEmitInlineFamily_cons, ih, List.append_assoc]

/-- **FAMILY 1 (INLINE), THE SPLIT AT ANY INDEX** - what a consumer needs to name "the block of
    identity 'i'" inside the flat emitted run, and the lemma the 'seg' corollary in
    'LoweringV3/QuotientRows.lean' section 10 rests on. -/
theorem qEmitInlineFamily_take_drop (ids : List QuotientIdentity) (i : Nat)
    (fold : SelectorFoldPlan) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) :
    qEmitInlineFamily ids fold evalScratchSlot slots trace =
      qEmitInlineFamily (ids.take i) fold evalScratchSlot slots trace ++
        qEmitInlineFamily (ids.drop i) fold evalScratchSlot slots trace := by
  have h := qEmitInlineFamily_append (ids.take i) (ids.drop i) fold evalScratchSlot slots trace
  rw [List.take_append_drop] at h
  exact h

/-- **FAMILY 1 (INLINE), NOTHING IS DROPPED AND NOTHING IS INVENTED**: the family block is empty
    exactly for the empty family. This is what makes the stride count meaningful - a producer that
    emitted nothing for some identity would break it, and 'qEmitDirectBlock_length' says none can. -/
theorem qEmitInlineFamily_eq_nil_iff (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    qEmitInlineFamily ids fold evalScratchSlot slots trace = [] ↔ ids = [] := by
  constructor
  · intro h
    cases ids with
    | nil => rfl
    | cons a as =>
        rw [qEmitInlineFamily_cons] at h
        rw [List.append_eq_nil_iff] at h
        have hl := qEmitDirectBlock_length a.lines a.var a.target (fold.gapFor a)
          evalScratchSlot slots trace
        rw [h.1] at hl
        cases trace with
        | false => simp [qFamilyStride] at hl
        | true => simp [qFamilyStride] at hl
  · intro h; subst h; rfl

/-- The indexed map the native-identity producer runs, at an ARBITRARY start index, read back as the
    plain map over the list: the block a case carries does not depend on its index - only the label
    does. Induction over the list with the start index generalised, which is what 'List.zipIdx' needs:
    at the cons the tail is enumerated from 'k + 1'. -/
theorem qEmitNativeIdentityCases_snd (k : Nat) (ids : List QuotientIdentity)
    (fold : SelectorFoldPlan) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) :
    (((ids.zipIdx k).map fun (id, i) =>
        (Literal.number i,
          qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot
            slots trace)).map Prod.snd) =
      ids.map fun id =>
        qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot slots trace := by
  induction ids generalizing k with
  | nil => rfl
  | cons a as ih => simp [List.zipIdx_cons, ih]

/-- **FAMILY 2 (NATIVE IDENTITY), THE VALUE LEMMA**: the case bodies are the producer's own
    recursion - the same per-identity blocks, in list order. -/
theorem qEmitNativeIdentityFamily_value (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    qEmitNativeIdentityFamily ids fold evalScratchSlot slots trace =
      (ids.map fun id =>
        qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot
          slots trace).flatten := by
  simp only [qEmitNativeIdentityFamily, qEmitNativeIdentityCases,
    qEmitNativeIdentityCases_snd]

/-- **FAMILIES 1 AND 2 EMIT THE SAME STATEMENT RUN**, for every identity list: the two families
    differ only in the wrapper the render puts around them - a statement run versus a switch body -
    and never in a statement. 'qEmitNativeIdentityFamily' claims this in its docstring; here it is
    proved, by way of the two value lemmas. -/
theorem qEmitNativeIdentityFamily_eq_qEmitInlineFamily (ids : List QuotientIdentity)
    (fold : SelectorFoldPlan) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) :
    qEmitNativeIdentityFamily ids fold evalScratchSlot slots trace =
      qEmitInlineFamily ids fold evalScratchSlot slots trace := by
  rw [qEmitNativeIdentityFamily_value, qEmitInlineFamily_value]

/-- **FAMILY 2 (NATIVE IDENTITY), ONE CASE PER IDENTITY.** -/
theorem qEmitNativeIdentityCases_length (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    (qEmitNativeIdentityCases ids fold evalScratchSlot slots trace).length = ids.length := by
  simp [qEmitNativeIdentityCases]

/-- **FAMILY 2 (NATIVE IDENTITY), THE LABELS, POSITIONALLY**: case 'i' is labelled
    'Literal.number i' and carries identity 'i' of the list - for every index and every list, so a
    plan that reorders its native identities reorders the switch, and a plan that drops one drops the
    last case. This is the property the render's '(case index0 => ...)' spelling has to satisfy; the
    gates check it at one plan, this holds at all of them. -/
theorem qEmitNativeIdentityCases_nth (ids : List QuotientIdentity)
    (fold : SelectorFoldPlan) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) (i : Nat) :
    (qEmitNativeIdentityCases ids fold evalScratchSlot slots trace)[i]? =
      (ids[i]?).map fun id => (Literal.number i,
        qEmitDirectBlock id.lines id.var id.target (fold.gapFor id) evalScratchSlot slots trace) := by
  simp only [qEmitNativeIdentityCases, List.getElem?_map, List.getElem?_zipIdx]
  cases ids[i]? <;> simp

/-- **FAMILY 2 (NATIVE IDENTITY), THE SWITCH**: the emitted switch is over 'q_native_idx', carries
    exactly one case per identity, and its default is the fail-closed arm - so an out-of-range
    'q_native_idx' reverts rather than falling through to the first case. -/
theorem qEmitNativeIdentitySwitch_shape (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    ∃ (cases : List (Literal × Block Op)) (dflt : Option (Block Op)),
        qEmitNativeIdentitySwitch ids fold evalScratchSlot slots trace =
          Stmt.switch (yvar "q_native_idx") cases dflt ∧
          cases.length = ids.length ∧
          dflt = some [yexpr (ycall "q_program_fail" [])] := by
  refine ⟨qEmitNativeIdentityCases ids fold evalScratchSlot slots trace,
    some [yexpr (ycall "q_program_fail" [])], rfl, ?_, rfl⟩
  exact qEmitNativeIdentityCases_length ids fold evalScratchSlot slots trace

/-- **FAMILY 2 (NATIVE IDENTITY), THE LENGTH**: same stride as family 1, by way of the cross-family
    theorem. -/
theorem qEmitNativeIdentityFamily_length (ids : List QuotientIdentity) (fold : SelectorFoldPlan)
    (evalScratchSlot : Nat) (slots : QuotientStateSlots) (trace : Bool) :
    (qEmitNativeIdentityFamily ids fold evalScratchSlot slots trace).length =
      ids.length * qFamilyStride trace := by
  rw [qEmitNativeIdentityFamily_eq_qEmitInlineFamily, qEmitInlineFamily_length]

/-- The one inversion on 'Except' the state-threaded inductions need: an abort-free run of a bind has
    an abort-free left part and an abort-free right part at the value the left part returned. -/
theorem qExcept_bind_ok_cases {ε α β : Type} (x : Except ε α) (f : α → Except ε β) {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => simp only [Except.bind] at h; exact ⟨a, rfl, h⟩
  | error e => simp only [Except.bind] at h; cases h

/-- **THE STATE-THREADED MAP PRODUCES ONE OUTPUT PER INPUT ELEMENT.** The three structured producers
    ('qEmitTrashBlock', 'qEmitPermutationBlockA', 'qEmitLookupBlockA') build their per-item region
    with 'List.mapM' in 'E F = StateT (Evaluator F) (Except Fault)', so an item's output depends on
    the state its predecessors left behind and the region is NOT an append of independent pieces -
    that is the difference between those three families and the two above, and why their inductions
    run over the state-threaded map instead of over the block. List induction over the family list
    with the threaded state generalised, for every abort-free run; an aborting run is excluded by the
    hypothesis, which is the honest reading (the producer returns 'none' there and the render emits
    nothing). -/
theorem qMapM_length_stateT {σ ε α β : Type} (f : α → StateT σ (Except ε) β) :
    ∀ (l : List α) (st : σ) (out : List β) (st' : σ),
      (l.mapM f).run st = .ok (out, st') → out.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro st out st' h
      have h' : (List.mapM f []).run st = .ok ([], st) := rfl
      rw [h'] at h
      cases h
      rfl
  | cons a as ih =>
      intro st out st' h
      rw [List.mapM_cons] at h
      simp only [StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure] at h
      obtain ⟨⟨b, st₁⟩, hfirst, hrest⟩ :=
        qExcept_bind_ok_cases (f a st)
          (fun x => ((as.mapM f).run x.2).bind fun y => .ok (x.1 :: y.1, y.2)) h
      dsimp only at hrest
      obtain ⟨⟨bs, st₂⟩, hmid, hlast⟩ :=
        qExcept_bind_ok_cases ((as.mapM f).run st₁) (fun y => .ok (b :: y.1, y.2)) hrest
      cases hlast
      simp [List.length_cons, ih st₁ bs st₂ hmid]

/-- **FAMILY 3 (POST-VM SUFFIX), THE EMPTY-CIRCUIT ARM**: the twin emits nothing exactly when the
    circuit has no trashcans - the producer returns 'none' there and the render emits an empty splice.
    Proved by reducing the producer's own 'StateT' run at a symbolic Evaluator, which is also the
    reduction the shape lemma below rests on. -/
theorem qEmitPostVmFamily_none {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (ev : Evaluator F) (h : ev.meta_.numTrashcans == 0) :
    qEmitPostVmFamily slots trace ev = none := by
  have hrun : (qEmitTrashBlock (F := F) slots trace).run ev = .ok (none, ev) := by
    simp only [qEmitTrashBlock, StateT.run, StateT.bind, Bind.bind, Pure.pure]
    have hget : (get : E F (Evaluator F)) ev = .ok (ev, ev) := rfl
    rw [hget, Except.bind]
    dsimp only
    rw [h]
    simp only [ite_true]
    rfl
  rw [qEmitPostVmFamily, hrun]

/-- **FAMILY 3 (POST-VM SUFFIX), THE VALUE LEMMA**: on a symbolic Evaluator whose trashcan run does
    not abort, the emitted block is ONE block whose body is the trash-challenge load followed by
    exactly one statement per trashcan. The 'q_trash_tau' load appears once for the whole block -
    the deviation the twin's docstring claims and 'qemPostVm_allArmsAndEmpty_ok' only checks as a
    'Bool' at one plan - and the per-trashcan region has the trashcan list's length, which is the
    list induction 'qMapM_length_stateT' supplies. -/
theorem qEmitPostVmFamily_shape {F : Type} [BEq F] (slots : QuotientStateSlots) (trace : Bool)
    (ev : Evaluator F) (b : Block Op) (ev' : Evaluator F)
    (h : (qEmitTrashBlock slots trace).run ev = .ok (some b, ev')) :
    ∃ (blocks : List (Stmt Op)),
      b = [Stmt.block ([ylet "q_trash_tau" (yop Op.mload [yvar "TRASH_CHALLENGE_MPTR"])]
        ++ blocks)] ∧ blocks.length = ev.cs.trashcans.toList.length := by
  simp only [qEmitTrashBlock, StateT.run, StateT.bind, Bind.bind, Pure.pure] at h
  have hget : (get : E F (Evaluator F)) ev = .ok (ev, ev) := rfl
  rw [hget, Except.bind] at h
  dsimp only at h
  cases hdec : (ev.meta_.numTrashcans == 0) with
  | true =>
      simp only [hdec, ite_true] at h
      have h2 : Except.ok (none, ev) = Except.ok (some b, ev') := h
      simp only [Except.ok.injEq] at h2
      obtain ⟨h₁, _⟩ := Prod.mk.inj h2
      cases h₁
  | false =>
      simp only [hdec, Bool.false_eq_true, reduceIte] at h
      obtain ⟨p, hp, hres⟩ := qExcept_bind_ok_cases _ _ h
      dsimp only at hres
      have hres' : Except.ok (some [Stmt.block ([ylet "q_trash_tau"
          (yop Op.mload [yvar "TRASH_CHALLENGE_MPTR"])] ++ p.1)], p.2) =
          Except.ok (some b, ev') := hres
      simp only [Except.ok.injEq] at hres'
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj hres'
      subst h₂
      refine ⟨p.1, (Option.some.inj h₁).symm, ?_⟩
      have hlen := qMapM_length_stateT _ _ _ _ _ hp
      rwa [List.length_zipIdx] at hlen

/-- **FAMILY 4 (NATIVE PERMUTATION), THE EMPTY-CIRCUIT ARM**: no permutation z, no block - the
    caller stores '[]' exactly as 'QuotientBlocks.lean:884-889' does. -/
theorem qEmitNativePermutationA_none {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) (ev : Evaluator F)
    (h : ev.meta_.numPermutationZs == 0) :
    qEmitNativePermutationA scratchMptr slots trace ev = none := by
  have hrun : (qEmitPermutationBlockA (F := F) scratchMptr slots trace).run ev = .ok (none, ev) := by
    simp only [qEmitPermutationBlockA, StateT.run, StateT.bind, Bind.bind, Pure.pure]
    have hget : (get : E F (Evaluator F)) ev = .ok (ev, ev) := rfl
    rw [hget, Except.bind]
    dsimp only
    rw [h]
    simp only [ite_true]
    rfl
  rw [qEmitNativePermutationA, hrun]

/-- **FAMILY 5 (NATIVE LOOKUP), THE EMPTY-CIRCUIT ARM**: no lookups, no block. -/
theorem qEmitNativeLookupA_none {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) (ev : Evaluator F)
    (h : ev.meta_.numLookups == 0) :
    qEmitNativeLookupA scratchMptr slots trace ev = none := by
  have hrun : (qEmitLookupBlockA (F := F) scratchMptr slots trace).run ev = .ok (none, ev) := by
    simp only [qEmitLookupBlockA, StateT.run, StateT.bind, Bind.bind, Pure.pure]
    have hget : (get : E F (Evaluator F)) ev = .ok (ev, ev) := rfl
    rw [hget, Except.bind]
    dsimp only
    rw [h]
    simp only [ite_true]
    rfl
  rw [qEmitNativeLookupA, hrun]

/-! #### ROW.Q.5: THE REMAINDER, NAMED EXACTLY (QEMIT3: CLOSED BY THE LIFT BELOW)

Families (4) and (5) land their empty-circuit arm, and nothing beyond it: the PER-ITEM induction for
those two is NOT landed. The reason is structural, not effort: in
'qEmitTrashBlock' the per-item region is a single 'mapM' whose result is appended to a fixed head, so
'qMapM_length_stateT' finishes the family at the length, and the step function never has to be named.
In 'qEmitPermutationBlockA' and 'qEmitLookupBlockA' the per-item regions are nested: the lookup block
maps a step that itself returns a LIST of statements ('pure [yblock (boundary ++ helpers.flatten ++
[yblock accumulator])]' at line 606), and 'helpers' is a second 'mapM' over the chunked inputs whose
step has three arms ('k == 0', 'k == 1', 'k >= 2'), each of which runs 'compressExpressionsA' and
'qLookupSharedPrefixA' in the threaded state. So the statement "the lookup block contains exactly one
helper block per input chunk" needs the shape of the INNER step's result, and that step is an inner
lambda of 'qEmitLookupBlockA' - it has no name to induct over. The exact goal state a proof would have
to reach, with the step unnameable, is

    ∃ tail, body = head ++ tail ∧ tail.length = ev.cs.lookups.toList.length

where 'head' is the ten scratch-and-challenge loads of lines 608-618 and 'body' is the single block
'qEmitNativeLookupA_none' is stated at: 'head' and the per-lookup region are both let-bound INSIDE the
producer, so neither is referable from a statement. Two ways out, both a decision for the orchestrator
and neither taken here because both change QEMIT's landed twins: (a) lift the two step functions to
top-level 'def's ('qEmitLookupHelperStepA', 'qEmitPermutationStageA') and induct over them - the
values are unchanged, so the 'qemLookup_*' gates keep their teeth; or (b) widen the twins' return type
to expose the region boundaries. This card does neither: the twins are QEMIT's deliverable and the
fingerprint gate is theirs. THE PERMUTATION FAMILY HAS THE SAME GAP for a different reason: its staged
region is 'qPushMstoreMloadLiteralRunsA' applied five times, and the compactor's own recursion is a
'let rec go' inside the definition (line 236), so the run-decomposition induction - "a run of three or
more consecutive 'mload' literals becomes one loop, anything else becomes one store per entry" - needs
that 'go' as an induction target too. The compactor's trivial cases are landed below; the run
decomposition is not. -/

/-- The compactor emits nothing for an empty entry list: 'go' is called with fuel '0 + 1' at index 0,
    the index test fires immediately, and the running block is returned unchanged. -/
theorem qPushMstoreMloadLiteralRunsA_nil (block : Block Op) (dst loopPrefix : String) :
    qPushMstoreMloadLiteralRunsA block dst [] loopPrefix = block := rfl

/-- The compactor is a running-block accumulator: whatever it emits for a list of entries, it emits
    AFTER the block it was handed. Stated for the empty list here, where the claim is the definitional
    'qPushMstoreMloadLiteralRunsA_nil'; the general form needs the internal 'go' as an induction
    target - see the gap note above. -/
theorem qPushMstoreMloadLiteralRunsA_length_nil (block : Block Op) (dst loopPrefix : String) :
    (qPushMstoreMloadLiteralRunsA block dst [] loopPrefix).length = block.length := rfl

/-! #### QEMIT3: families 4 and 5 - the per-item value lemmas the lift makes reachable -/

/-! #### QEMIT3: 'qMloadRunGoA_split_gap' - WHAT THE LIFT REACHED AND WHAT IT DID NOT

The lift made 'qMloadRunGoA' an induction target and the per-entry run decomposition is proved
('qPushMstoreMloadLiteralRunsA_rejected', 'qPushMstoreMloadLiteralRunsA_run3'). The one claim that did
NOT land is the accumulator split for an ARBITRARY running block,

    ```
    qMloadRunGoA dst entries loopPrefix b fuel idx =
      b ++ qMloadRunGoA dst entries loopPrefix [] fuel idx
    ```

with the exact remaining goal state after 'simp only [qMloadRunGoA, if_neg hidx]; simp [ih,
qMloadRunSingleA]' at the 'succ fuel' case: the left-hand side has the 'b ++' INSIDE each branch of
the compactor's nested 'match' (simp rewrites under the match by congruence) while the right-hand side
has it OUTSIDE the match, and there is no Lean lemma that moves an append across a 'match' on an
'Option'. This is a tactic-level distributivity obstacle, not a semantic one: the statement is true
(every branch appends to the end of the accumulator and reads nothing from it), it is what the
five-region staging decomposition would follow from, and it needs either a hand-written congruence
lemma per 'match' arm or a re-spelling of the compactor with the emitted region as a separate
accumulator - the second being a rewrite of QEMIT2's twin, which this card forbids. Recorded here
rather than hidden behind a 'sorry'.

Q1 RE-READS THIS NOTE, AND ONE SENTENCE IN IT IS WRONG. 'there is no Lean lemma that moves an append
across a ''match'' on an ''Option''' is true of Mathlib and irrelevant: the congruence is two lines -
''cases o <;> rfl'' proves ''b ++ (match o with | none => f () | some a => g a) = match o with
| none => b ++ f () | some a => b ++ g a'', and the same ''split'' works for the ''if'' levels. So the
distributivity is NOT the obstacle. The obstacle is one level up: the induction hypothesis
''go b k idx = b ++ go [] k idx'' is SELF-REWITING - its own right-hand side contains an instance of
its left-hand pattern (''go [] k idx''), so ''simp only [ih]'' loops and dies at ''maxRecDepth''
(measured: 3.9 s, 'maximum recursion depth has been reached'). The split therefore needs the IH
INSTANTIATED at the two concrete accumulators the recursion uses (''qMloadRunSingleA dst b ..'' and
''b ++ [yblock [loop]]''), not applied as a simp lemma - plus ''List.find?''-style case splits at the
five nested matches. That is a bounded amount of work, not a re-spelling of QEMIT2's twin, and it is
the route to family 4's accumulator split. -/

/-- **THE COMPACTOR'S RECURSION, SPENT OR OUT OF RANGE, RETURNS THE RUNNING BLOCK.** Two boundary
    cases of the lifted 'qMloadRunGoA', both immediate now that the recursion is a top-level 'def' and
    can be named in a statement: no fuel left, or an index past the end of the entry list. -/
theorem qMloadRunGoA_zero (dst : String) (entries : List (Nat × Expr Op))
    (loopPrefix : String) (b : Block Op) (idx : Nat) :
    qMloadRunGoA dst entries loopPrefix b 0 idx = b := rfl

theorem qMloadRunGoA_out_of_range (dst : String) (entries : List (Nat × Expr Op))
    (loopPrefix : String) (b : Block Op) (fuel idx : Nat) (h : idx >= entries.length) :
    qMloadRunGoA dst entries loopPrefix b (fuel + 1) idx = b := by
  simp only [qMloadRunGoA, if_pos h]

/-- **FAMILY 4 (NATIVE PERMUTATION), THE PER-ITEM VALUE LEMMA FOR A REJECTED ENTRY.** An entry whose
    expression is not an 'mload' of a literal emits EXACTLY ONE store and advances the index by one -
    the compactor's base case, and the claim ROW.Q.5 could not state at all because the recursion it
    steps through was a 'let rec' inside the definition. Generic in the destination, the offset, the
    expression and the running block (D-P71). -/
theorem qPushMstoreMloadLiteralRunsA_rejected (block : Block Op) (dst loopPrefix : String)
    (d : Nat) (e : Expr Op) (h : qMloadLiteralA? e = none) :
    qPushMstoreMloadLiteralRunsA block dst [(d, e)] loopPrefix =
      block ++ [yexpr (yop Op.mstore [yop Op.add [yvar dst, ylit d], e])] := by
  simp [qPushMstoreMloadLiteralRunsA, qMloadRunGoA, qMloadRunSingleA, h]

/-- **FAMILY 4 (NATIVE PERMUTATION), THE PER-ITEM VALUE LEMMA FOR A COMPACTED RUN.** Three consecutive
    entries on the '(0x20, 0x20)' grid become ONE loop, not three stores - the 'count < 3' rule firing
    the other way, and the second half of the run decomposition the lift was issued for. The loop is
    spelled at the AST: destination offset variable shifted by 5, source offset REUSED from the
    destination offset because the stride is exactly 0x20 (the first of the compactor's two
    'src_stride' arms), and the count is the three entries. -/
theorem qPushMstoreMloadLiteralRunsA_run3 (block : Block Op) (dst loopPrefix : String)
    (s0 : Nat) :
    qPushMstoreMloadLiteralRunsA block dst
        [(0, Expr.builtin Op.mload [Expr.lit (Literal.number s0)]),
         (0x20, Expr.builtin Op.mload [Expr.lit (Literal.number (s0 + 0x20))]),
         (0x40, Expr.builtin Op.mload [Expr.lit (Literal.number (s0 + 0x40))])] loopPrefix =
      block ++ [yblock
        [Stmt.forLoop [ylet (loopPrefix ++ "_i") (ylit 0)]
          (yop Op.lt [yvar (loopPrefix ++ "_i"), ylit 3])
          [yset (loopPrefix ++ "_i") (yop Op.add [yvar (loopPrefix ++ "_i"), ylit 1])]
          [ylet (loopPrefix ++ "_dst_off") (yop Op.shl [ylit 5, yvar (loopPrefix ++ "_i")]),
           ylet (loopPrefix ++ "_src_off") (yvar (loopPrefix ++ "_dst_off")),
           yexpr (yop Op.mstore
             [yop Op.add [yop Op.add [yvar dst, ylit 0], yvar (loopPrefix ++ "_dst_off")],
              yop Op.mload [yop Op.add [ylit s0, yvar (loopPrefix ++ "_src_off")]]])]]] := by
  simp [qPushMstoreMloadLiteralRunsA, qMloadRunGoA, qMloadRunExtendA, qMloadRunSingleA,
    qMloadLiteralA?, natSubOpt]

/-- **FAMILY 4 (NATIVE PERMUTATION), THE STAGED REGION OF AN EMPTY PLAN IS EMPTY.** With no permutation
    columns and no z evaluations the five compactor calls emit nothing at all, so the whole staged
    region of the native permutation block collapses to the empty run. -/
theorem qEmitPermutationStagingA_empty :
    qEmitPermutationStagingA [] [] [] [] = [] := rfl

/-- **A STATE-THREADED MAP PRESERVES ANY PER-ITEM PROPERTY.** The companion of
    'qMapM_length_stateT': where that lemma counts the outputs, this one carries a shape claim about
    each of them into the same induction. Needed because the lookup block's per-item region is a
    'mapM' in the threaded Evaluator, so the only way to say something about its items is to say it of
    the step and let the induction carry it. -/
theorem qMapM_all_stateT {σ ε α β : Type} (f : α → StateT σ (Except ε) β) (P : β → Prop)
    (hf : ∀ (a : α) (st : σ) (r : β) (st' : σ), (f a).run st = .ok (r, st') → P r) :
    ∀ (l : List α) (st : σ) (out : List β) (st' : σ),
      (l.mapM f).run st = .ok (out, st') → ∀ item ∈ out, P item := by
  intro l
  induction l with
  | nil =>
      intro st out st' h item hit
      have hnil : (List.mapM f []).run st = .ok ([], st) := rfl
      rw [hnil] at h
      have : out = [] := (Prod.mk.inj (Except.ok.inj h)).1.symm
      subst this
      cases hit
  | cons a as ih =>
      intro st out st' h item hit
      rw [List.mapM_cons] at h
      simp only [StateT.run, StateT.bind, StateT.pure, Bind.bind, Pure.pure] at h
      obtain ⟨⟨b, st₁⟩, hfirst, hrest⟩ :=
        qExcept_bind_ok_cases (f a st)
          (fun x => ((as.mapM f).run x.2).bind fun y => .ok (x.1 :: y.1, y.2)) h
      dsimp only at hrest
      obtain ⟨⟨bs, st₂⟩, hmid, hlast⟩ :=
        qExcept_bind_ok_cases ((as.mapM f).run st₁) (fun y => .ok (b :: y.1, y.2)) hrest
      cases hlast
      simp only [List.mem_cons] at hit
      obtain hieq | hiin := hit
      · subst hieq
        exact hf a st item st₁ hfirst
      · exact ih st₁ bs st₂ hmid item hiin

/-- A list whose items are all singletons flattens to a list of the same length. -/
theorem qFlatten_length_of_singleton {α : Type} (out : List (List α))
    (h : ∀ item ∈ out, ∃ a, item = [a]) : out.flatten.length = out.length := by
  induction out with
  | nil => rfl
  | cons a as ih =>
      obtain ⟨x, hx⟩ := h a (by simp)
      have has : ∀ item ∈ as, ∃ y, item = [y] := fun item m => h item (by simp [m])
      subst hx
      simp [List.flatten_cons, ih has]

/-- **PEEL ONE BIND OFF A SUCCESSFUL 'StateT' RUN.** The one inversion the state-threaded
    inductions need, in the form the block-shape theorems use it: if 'x >>= f' succeeds from 'st' to
    'st'', then 'x' succeeded to some intermediate state and 'f' applied to its value finished the run.
    QEMIT3 adds this because the family-4 and family-5 shape theorems have to walk FOUR binds of their
    producer, where family 3's needed only one. -/
theorem qStateT_run_bind_ok {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (st : σ) (y : β) (st' : σ)
    (h : (x >>= f).run st = .ok (y, st')) :
    ∃ a st'', x.run st = .ok (a, st'') ∧ (f a).run st'' = .ok (y, st') := by
  simp only [StateT.run, StateT.bind] at h ⊢
  obtain ⟨⟨a, st''⟩, hx, hf⟩ := qExcept_bind_ok_cases (x.run st) (fun p => (f p.1).run p.2) h
  exact ⟨a, st'', hx, hf⟩

/-- **FAMILY 5 (NATIVE LOOKUP), THE PER-LOOKUP REGION HAS ONE ITEM PER LOOKUP.** The region is the
    producer's own 'mapM' over 'cs.lookups', enumerated by 'zipIdx'; an abort-free run emits exactly
    one output per lookup, for every list the plan could carry. -/
theorem qEmitLookupRegionA_length {F : Type} [BEq F]
    (lookups : List (LogupBatchedArgument F)) (slots : QuotientStateSlots) (trace : Bool)
    (theta : String) (csDegree : Nat) (out : List (Block Op)) (ev ev' : Evaluator F)
    (h : (qEmitLookupRegionA (F := F) lookups slots trace theta csDegree).run ev = .ok (out, ev')) :
    out.length = lookups.length := by
  simp only [qEmitLookupRegionA] at h
  have hl := qMapM_length_stateT _ _ _ _ _ h
  rwa [List.length_zipIdx] at hl

/-- **FAMILY 5 (NATIVE LOOKUP), EVERY REGION ITEM IS ONE BRACED BLOCK.** The lifted step ends in
    'pure [yblock body]' by construction, so the shape is one 'obtain' away and does not depend on the
    body at all - which is what makes it hold on all three k-arms of the inner chunk step at once. -/
theorem qEmitLookupPerItemStepA_shape {F : Type} [BEq F] (slots : QuotientStateSlots)
    (trace : Bool) (theta : String) (csDegree : Nat) (lookup : LogupBatchedArgument F)
    (lookupIdx : Nat) (ev ev' : Evaluator F) (r : Block Op)
    (h : (qEmitLookupPerItemStepA (F := F) slots trace theta csDegree lookup lookupIdx).run ev
        = .ok (r, ev')) :
    ∃ body : Block Op, r = [Stmt.block body] := by
  simp only [qEmitLookupPerItemStepA, StateT.run, StateT.bind, Bind.bind, Pure.pure] at h
  obtain ⟨⟨x, st''⟩, hx, hres⟩ := qExcept_bind_ok_cases _ _ h
  obtain ⟨hr, _⟩ := Prod.mk.inj (Except.ok.inj hres)
  exact ⟨x, hr.symm⟩

/-- **FAMILY 5 (NATIVE LOOKUP), THE REGION ITEMS ARE ONE BRACED BLOCK EACH, FOR THE WHOLE REGION.** -/
theorem qEmitLookupRegionA_items {F : Type} [BEq F]
    (lookups : List (LogupBatchedArgument F)) (slots : QuotientStateSlots) (trace : Bool)
    (theta : String) (csDegree : Nat) (out : List (Block Op)) (ev ev' : Evaluator F)
    (h : (qEmitLookupRegionA (F := F) lookups slots trace theta csDegree).run ev = .ok (out, ev')) :
    ∀ item ∈ out, ∃ body : Block Op, item = [Stmt.block body] := by
  simp only [qEmitLookupRegionA] at h
  refine qMapM_all_stateT _ (P := fun r => ∃ body : Block Op, r = [Stmt.block body])
    (fun a st r st' ha => qEmitLookupPerItemStepA_shape slots trace theta csDegree a.1 a.2 st st' r ha)
    _ _ _ _ h

/-- **FAMILY 5 (NATIVE LOOKUP), THE PER-ITEM VALUE LEMMA - THE GOAL ROW.Q.5 NAMED AS UNREACHABLE.**
    With the step functions lifted to top-level 'def's the let-bound 'head' and the let-bound per-item
    region are both referable, and the exact goal state the card printed is now a theorem: the emitted
    block is the ten scratch-and-challenge loads followed by a tail, and the tail has ONE STATEMENT PER
    LOOKUP of the circuit. Generic in the render and in the Evaluator (D-P71): every binder is
    symbolic, and the only hypothesis is that the producer's run does not abort - the honest reading,
    since an aborting run returns 'none' and the render emits nothing. -/
theorem qEmitNativeLookupA_shape {F : Type} [BEq F] (scratchMptr : Nat)
    (slots : QuotientStateSlots) (trace : Bool) (ev : Evaluator F) (b : Block Op)
    (ev' : Evaluator F)
    (h : (qEmitLookupBlockA (F := F) scratchMptr slots trace).run ev = .ok (some b, ev')) :
    ∃ (head tail : Block Op),
      b = [Stmt.block (head ++ tail)] ∧
      tail.length = ev.cs.lookups.toList.length := by
  simp only [qEmitLookupBlockA, StateT.run, StateT.bind, Bind.bind, Pure.pure] at h
  have hget : (get : E F (Evaluator F)) ev = .ok (ev, ev) := rfl
  rw [hget, Except.bind] at h
  dsimp only at h
  cases hdec : (ev.meta_.numLookups == 0) with
  | true =>
      simp only [hdec, ite_true] at h
      change (Except.ok (none, ev) = Except.ok (some b, ev')) at h
      obtain ⟨h1, _⟩ := Prod.mk.inj (Except.ok.inj h)
      exact absurd h1 (by simp)
  | false =>
      simp only [hdec, Bool.false_eq_true, reduceIte] at h
      obtain ⟨⟨maxParallel, sev1⟩, hmp, h1⟩ := qExcept_bind_ok_cases _ _ h
      dsimp only at h1
      obtain ⟨⟨csDegree, sev2⟩, hcd, h2⟩ := qExcept_bind_ok_cases _ _ h1
      dsimp only at h2
      obtain ⟨⟨perLookup, sev3⟩, hpl, h3⟩ := qExcept_bind_ok_cases _ _ h2
      have hlen : perLookup.length = ev.cs.lookups.toList.length :=
        qEmitLookupRegionA_length (F := F) ev.cs.lookups.toList slots trace "q_lookup_theta"
          csDegree perLookup sev2 sev3 hpl
      have hits : ∀ item ∈ perLookup, ∃ body : Block Op, item = [Stmt.block body] :=
        qEmitLookupRegionA_items (F := F) ev.cs.lookups.toList slots trace "q_lookup_theta"
          csDegree perLookup sev2 sev3 hpl
      have hb : b = [Stmt.block (qEmitLookupHeadA scratchMptr (scratchMptr + maxParallel * 0x20)
          (scratchMptr + maxParallel * 0x20 + maxParallel * 0x20) ++ perLookup.flatten)] := by
        have h3' : Except.ok (some [Stmt.block (qEmitLookupHeadA scratchMptr
            (scratchMptr + maxParallel * 0x20) (scratchMptr + maxParallel * 0x20 + maxParallel * 0x20)
            ++ perLookup.flatten)], sev3) = Except.ok (some b, ev') := h3
        exact ((Option.some.inj (Prod.mk.inj (Except.ok.inj h3')).1)).symm
      refine ⟨qEmitLookupHeadA scratchMptr (scratchMptr + maxParallel * 0x20)
          (scratchMptr + maxParallel * 0x20 + maxParallel * 0x20), perLookup.flatten, hb, ?_⟩
      have hf1 : ∀ item ∈ perLookup, ∃ a : Stmt Op, item = [a] := fun item m =>
        match hits item m with
        | ⟨body, hb2⟩ => ⟨Stmt.block body, hb2⟩
      exact (qFlatten_length_of_singleton perLookup hf1).trans hlen

end Midfall.Lowering.GenAst
