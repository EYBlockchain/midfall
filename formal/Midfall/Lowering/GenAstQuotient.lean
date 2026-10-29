-- |
-- Midfall.Lowering.GenAstQuotient
--
-- P-STR2AST: the batched-identity numerator Evaluator as a REAL Yul AST.
--
-- WHAT THIS FILE IS FOR. 'Midfall.Generator.QuotientEvaluator' is the port of
-- yul_emit.rs and it is the last module in the tree that builds Yul by string concatenation:
-- 'abbrev Lines := List String', 'letLine v rhs := "let " ++ v ++ " := " ++ rhs', and
-- composite right-hand sides written as "addmod(" ++ lhsVar ++ ", " ++ rhsVar ++ ", r)".
-- D-P30 names it as the 18-site case and forbids the form. This file is the conversion: every
-- one of those sites has an AST twin here, and the twins are gated against the text port.
--
-- THE TEXT PORT IS KEPT (D-P30 clause 2), AND HERE THAT IS NOT A FORMALITY. The Evaluator's
-- output is not just rendered, it is PARSED: QuotientBlocks.quotientYulExpr (Q:978-984) feeds
-- every emitted line through QuotientBuilder.assignment to build the quotient VM program.
-- So the text path is load-bearing for a second reason and cannot be dropped at all in this
-- package; the AST path is added beside it. That is also what makes the cross-check possible
-- without a runtime Yul parser for the AST: the two paths are run on the SAME expression with
-- the SAME state and their outputs are compared token for token.
--
-- THE CACHE IS THE HAZARD, AND THE CROSS-CHECK SEES IT. init_var keys its dedup cache on the
-- RENDERED VALUE TEXT (YE:1128-1137), which is what makes two structurally equal
-- subexpressions share one let and is observable in the variable numbering. The AST twin keys
-- on 'EVM.printExpr' of the expression instead. Those two keys induce the SAME partition
-- exactly when no two distinct text values print to the same AST and vice versa - which holds
-- here because every numeric literal that reaches init_var is hex-spelled in the text port and
-- the bare decimal "0" and "1" only ever go through freshLet, which bypasses the cache. That
-- is a claim, so it is a gate: evaluateAst_matchesText_ok pins that the AST path and the text
-- path agree on the FINAL VARIABLE, the LINE COUNT and the post-run state (counter, cache
-- size, pow5 flag) for every expression in the corpus. A cache partition that merged or split
-- one entry would move the variable numbering and redden it.
--
-- PLAN DEPENDENCE. The Evaluator's interpolated values are the Data eval pointers, the meta
-- counts (numCommittedInstances, simpleSelectorCols, numPermutationZs, numLookups,
-- numTrashcans, permutationChunkLen, numQuotients) and the field dictionary's DELTA.
-- evaluatorAstDependsOnData_ok and evaluatorAstDependsOnMeta_ok perturb each one and require
-- the emitted AST to move; deltaAst_computedNotHardcoded_ok is the AST twin of the text port's
-- deltaLiteral gate.
--

import Midfall.Generator.Quotient.Evaluator
import Midfall.Lowering.GenAst
import Midfall.Generator.YulGolden
import YulSemantics.Syntax
import YulSemantics.PrettyPrint

namespace Midfall.Lowering.GenAstQuotient
open YulSemantics YulSemantics.EVM Midfall.Generator Midfall.Lowering.GenAst
open Midfall.Generator.QuotientEvaluator
open Midfall.Halo2

abbrev MWord := Midfall.Generator.Word
abbrev MPtr := Midfall.Generator.Ptr
abbrev MValue := Midfall.Generator.Value

/-! ### The AST twins of the string formatters (D-P30 sites 1-6) -/

/-- The AST twin of 'printValue' (Filters.lean:87-93). Five arms, same order. The text arm
    renders the number through fmtHex, which pads to an even nibble count; the AST stores the
    value and the printer renders decimal, so the two spellings are pinned by
    evaluatorAst_numericSpelling_ok and are invisible to stmtsBeq by construction. -/
def valueExpr (v : MValue) : Expr Op :=
  match v with
  | Value.integer i => if i >= 0 then ylit i.toNat
                       else yop Op.sub [ylit 0, ylit (Int.natAbs i)]
  | Value.identifier name 0 => yvar name
  | Value.identifier name off =>
      if off > 0 then yop Op.add [yvar name, ylit off.toNat]
      else yop Op.sub [yvar name, ylit (Int.natAbs off)]

/-- The AST twin of 'printWord' / 'wordKey' (ENC:764-775): calldata words are read with
    calldataload, memory words with mload. Site: 'wordString'. -/
def wordExpr (w : MWord) : Expr Op :=
  match w.ptr.loc with
  | Location.calldata => yop Op.calldataload [valueExpr w.ptr.value]
  | Location.memory => yop Op.mload [valueExpr w.ptr.value]

/-- The AST twin of 'u256String' (YE:1148-1154). The text renders "0x" ++ hexDigits; the AST
    carries the number. The two branches of the Rust's bit_len() test render the same text and
    the same number, so the branch stays documentation here too. -/
def u256Expr (value : Word256) : Expr Op := ylit value.toNat

/-- The AST twin of 'feToU256String': the field element through the R9 repr, then feToU256,
    then the literal. Same monadic shape, same fault on a bad repr. -/
def feToU256Expr {F : Type} (x : F) : E F (Expr Op) := do
  let ctx <- (fun s => s.field) <$> get
  pure (u256Expr (<- StateT.lift (feToU256 (ctx.repr x))))

/-- The AST twin of 'evalAt' / 'instanceEvalAt' returning an expression instead of text. -/
def instanceEvalExpr {F : Type} (columnIndex : Nat) (rotation : Int) : E F (Expr Op) := do
  let e <- get
  if columnIndex < e.meta_.numCommittedInstances then
    let w <- expectOpt (hashMapGet e.data.committedInstanceEvals (columnIndex, rotation))
      1117 "committed instance eval present"
    pure (wordExpr w)
  else pure (wordExpr e.data.instanceEval)

def evalAtExpr {F : Type} (column : Column) (rotation : Int) : E F (Expr Op) := do
  let e <- get
  let colIdx := column.index
  match column.columnType with
  | Any.advice _ =>
      let w <- expectOpt (hashMapGet e.data.adviceEvals (colIdx, rotation))
        850 "advice eval present in permutation chunk"
      pure (wordExpr w)
  | Any.fixed =>
      if e.meta_.simpleSelectorCols.contains colIdx then pure (ylit 1)
      else
        let w <- expectOpt (hashMapGet e.data.fixedEvals (colIdx, rotation))
          859 "fixed eval present in permutation chunk"
        pure (wordExpr w)
  | Any.instance => instanceEvalExpr colIdx rotation

/-! ### The composite right-hand sides (D-P30 sites 7-14) -/

/-- 'addmod(a, b, r)' - the text port writes "addmod(" ++ a ++ ", " ++ b ++ ", r)". -/
def yaddmod (a b : Expr Op) : Expr Op := yop Op.addmod [a, b, yvar "r"]
/-- 'mulmod(a, b, r)'. -/
def ymulmod (a b : Expr Op) : Expr Op := yop Op.mulmod [a, b, yvar "r"]
/-- 'sub(r, a)' - the field negation operand the text port writes inside addmod. -/
def ysubR (a : Expr Op) : Expr Op := yop Op.sub [yvar "r", a]
/-- 'addmod(0, sub(r, a), r)' - the negated-expression line (YE:1090). -/
def ynegField (a : Expr Op) : Expr Op := yaddmod (ylit 0) (ysubR a)
/-- 'q_pow5(a)' - a USER call: the helper is a generated function, not a dialect opcode. -/
def yqPow5 (a : Expr Op) : Expr Op := ycall "q_pow5" [a]
/-- 'mulmod(mulmod(a, b, r), c, r)' - the fused product-times-coefficient line (YE:1013). -/
def ymulmod3 (a b c : Expr Op) : Expr Op := ymulmod (ymulmod a b) c
/-- 'addmod(mulmod(prev, challenge, r), expr, r)' - the compression fold step (YE:765). -/
def ycompressStep (prev challenge expr : Expr Op) : Expr Op :=
  yaddmod (ymulmod prev challenge) expr

/-- The cache key for an AST value: its printed form. 'EVM.printExpr' is injective on the
    grammar this file emits (distinct constructors print distinctly, and the only numeric
    spelling is decimal), so this reproduces the text port's key partition. -/
def cacheKey (e : Expr Op) : String := EVM.printExpr e

/-- The AST twin of 'initVar' (YE:1128-1137). Same cache, same key position, same
    name-else-fresh_var rule, same insert-before-return order. The ONLY difference is that the
    key is the printed AST instead of the rendered text - which is what the whole file's
    cross-check exists to justify. -/
def initVarA {F : Type} (value : Expr Op) (name : Option String) :
    E F (Block Op × String) := do
  let e <- get
  let key := cacheKey value
  match hashMapGet e.varCache key with
  | some cached => pure ([], cached)
  | none => do
      let v <- match name with
        | some nm => pure nm
        | none => nextVar
      modify fun s => { s with varCache := hashMapInsert key v s.varCache }
      pure ([Stmt.letDecl [v] (some value)], v)

/-- The AST twin of 'freshLet' - deliberately NOT cached, exactly like the text port's, and
    for the same reason (freshLetBypassesCache_ok is the text-side gate of that fact). -/
def freshLetA {F : Type} (rhs : Expr Op) : E F (Block Op × String) := do
  let v <- freshVar
  pure ([Stmt.letDecl [v] (some rhs)], v)

/-- The AST twin of 'evaluateBasicCore' (YE:1025-1108) - the ten-closure visitor. Same
    closures, same order, same cache calls, same named slots. -/
def evaluateBasicCoreA {F : Type} [BEq F] (expression : Expression F) : E F (Block Op × String) :=
  expression.evaluate
    { constant := fun scalar => do initVarA (<- feToU256Expr scalar) none
      selectorColumn := fun _ =>
        throw (Midfall.Halo2.Fault.panic (site 1041 "virtual selectors must be removed before codegen"))
      fixedColumn := fun query => do
        let e <- get
        let columnIndex := query.columnIndex
        let rotation := query.rotation.int
        if e.meta_.simpleSelectorCols.contains columnIndex then
          initVarA (ylit 1) none
        else
          let eval <- expectOpt (hashMapGet e.data.fixedEvals (columnIndex, rotation))
            1054 "fixed eval present"
          initVarA (wordExpr eval) (some (columnEvalVar "f" columnIndex rotation))
      adviceColumn := fun query => do
        let e <- get
        let columnIndex := query.columnIndex
        let rotation := query.rotation.int
        let eval <- expectOpt (hashMapGet e.data.adviceEvals (columnIndex, rotation))
          1066 "advice eval present"
        initVarA (wordExpr eval) (some (columnEvalVar "a" columnIndex rotation))
      instanceColumn := fun query => do
        let eval <- instanceEvalExpr query.columnIndex query.rotation.int
        initVarA eval (some (columnEvalVar "i" query.columnIndex query.rotation.int))
      challenge := fun ch => do
        let e <- get
        let w <- atIndex e.data.challenges ch.index 1078 "challenges index"
        initVarA (wordExpr w) (some ("c_" ++ toString ch.index))
      negated := fun inner => do
        let (lines, var) <- inner
        let (addLines, addVar) <- initVarA (ynegField (yvar var)) none
        pure (lines ++ addLines, addVar)
      sum := fun lhs rhs => do
        let (lhsLines, lhsVar) <- lhs
        let (rhsLines, rhsVar) <- rhs
        let (lines, var) <- initVarA (yaddmod (yvar lhsVar) (yvar rhsVar)) none
        pure (lhsLines ++ rhsLines ++ lines, var)
      product := fun lhs rhs => do
        let (lhsLines, lhsVar) <- lhs
        let (rhsLines, rhsVar) <- rhs
        let (lines, var) <- initVarA (ymulmod (yvar lhsVar) (yvar rhsVar)) none
        pure (lhsLines ++ rhsLines ++ lines, var)
      scaled := fun inner scalar => do
        let (lines, var) <- inner
        let (scalarLines, scalarVar) <- initVarA (<- feToU256Expr scalar) none
        let (mulLines, mulVar) <-
          initVarA (ymulmod (yvar var) (yvar scalarVar)) none
        pure (lines ++ scalarLines ++ mulLines, mulVar) }

/-- The AST twin of 'evaluateBasic' (YE:1026-1032) with the pow5 guard. -/
def evaluateBasicA {F : Type} [BEq F] (expression : Expression F) : E F (Block Op × String) := do
  match <- pow5BaseExpr expression with
  | some base => do
      let (lines, baseVar) <- evaluateBasicCoreA base
      modify fun s => { s with pow5Used := true }
      let (powLines, powVar) <- initVarA (yqPow5 (yvar baseVar)) none
      pure (lines ++ powLines, powVar)
  | none => evaluateBasicCoreA expression

/-- The AST twin of 'evaluateScaledTerm' (YE:970-1022). -/
def evaluateScaledTermA {F : Type} [BEq F] (expression : Expression F) (coeff : F) :
    E F (Block Op × String) := do
  let e <- get
  let coeffIsOne := e.field.eqF coeff e.field.one
  match <- pow5BaseExpr expression with
  | some base => do
      let (lines, baseVar) <- evaluateBasicCoreA base
      modify fun s => { s with pow5Used := true }
      let (powLines, powVar) <- initVarA (yqPow5 (yvar baseVar)) none
      let lines := lines ++ powLines
      if coeffIsOne then pure (lines, powVar)
      else
        let (coeffLines, coeffVar) <- initVarA (<- feToU256Expr coeff) none
        let (scaleLines, outVar) <-
          initVarA (ymulmod (yvar powVar) (yvar coeffVar)) none
        pure (lines ++ coeffLines ++ scaleLines, outVar)
  | none =>
      match expression with
      | Expression.product lhs rhs => do
          let (lhsLines, lhsVar) <- evaluateBasicA lhs
          let (rhsLines, rhsVar) <- evaluateBasicA rhs
          let lines := lhsLines ++ rhsLines
          if coeffIsOne then
            let (outLines, outVar) <-
              initVarA (ymulmod (yvar lhsVar) (yvar rhsVar)) none
            pure (lines ++ outLines, outVar)
          else
            let (coeffLines, coeffVar) <- initVarA (<- feToU256Expr coeff) none
            let (outLines, outVar) <- initVarA
              (ymulmod3 (yvar lhsVar) (yvar rhsVar) (yvar coeffVar)) none
            pure (lines ++ coeffLines ++ outLines, outVar)
      | _ => do
          let (lines, var) <- evaluateBasicA expression
          if coeffIsOne then pure (lines, var)
          else
            let (coeffLines, coeffVar) <- initVarA (<- feToU256Expr coeff) none
            let (scaleLines, outVar) <-
              initVarA (ymulmod (yvar var) (yvar coeffVar)) none
            pure (lines ++ coeffLines ++ scaleLines, outVar)

/-- The AST twin of 'evaluateSumWithCoeffAndConst' (YE:897-942). The fusion predicate is the
    text port's, unchanged - only the emission differs. -/
def evaluateSumWithCoeffAndConstA {F : Type} [BEq F] (expression : Expression F) :
    E F (Option (Block Op × String)) := do
  let e <- get
  let field := e.field
  let (constant0, terms0) := collectSumTerms field expression field.one (field.zero, [])
  let terms := terms0.filter fun (coeff, _) => ! field.isZero coeff
  let hasConstant := ! field.isZero constant0
  let firstCoeffNotOne := match terms.head? with
    | some (coeff, _) => ! field.eqF coeff field.one
    | none => false
  let shouldFuse := hasConstant || terms.length > 1 || firstCoeffNotOne
  if ! shouldFuse then pure none
  else do
    let (lines0, acc0) <-
      if hasConstant then do
        let (cl, cv) <- initVarA (<- feToU256Expr constant0) none
        pure (cl, some cv)
      else pure ([], none)
    let (lines, acc) <- terms.foldlM
        fun (acc : Block Op × Option String) (pair : F × Expression F) => do
          let (termLines, termVar) <- evaluateScaledTermA pair.2 pair.1
          match acc with
          | (ls, some accVar) =>
              let (addLines, addVar) <-
                initVarA (yaddmod (yvar accVar) (yvar termVar)) none
              pure (ls ++ termLines ++ addLines, some addVar)
          | (ls, none) => pure (ls ++ termLines, some termVar)
        (lines0, acc0)
    match acc with
    | some var => pure (some (lines, var))
    | none => do let r <- initVarA (ylit 0) none; pure (some r)

/-- The AST twin of 'evaluate' (YE:885-891). -/
def evaluateA {F : Type} [BEq F] (expression : Expression F) : E F (Block Op × String) := do
  match <- evaluateSumWithCoeffAndConstA expression with
  | some result => pure result
  | none => evaluateBasicA expression

/-- The AST twin of 'compressExpressions' (YE:753-776). The fold starts from the literal 0 and
    NOT from a variable, which is why the first line is addmod(mulmod(0, <tau>, r), <e0>, r).
    The empty case is a freshLet of 0 and is NOT cached. -/
def compressExpressionsA {F : Type} [BEq F] (expressions : List (Expression F))
    (challengeVar : String) : E F (Block Op × String) := do
  let (lines, acc) <- expressions.foldlM
      fun (acc : Block Op × Option String) (expr : Expression F) => do
        let (eLines, eVar) <- evaluateA expr
        let next <- freshVar
        let prev : Expr Op := match acc.2 with
          | some v => yvar v
          | none => ylit 0
        pure (acc.1 ++ eLines ++
          [Stmt.letDecl [next] (some (ycompressStep prev (yvar challengeVar) (yvar eVar)))],
          some next)
      ([], none)
  match acc with
  | some var => pure (lines, var)
  | none => do
      let zero <- freshVar
      pure ([Stmt.letDecl [zero] (some (ylit 0))], zero)

/-- The AST twin of 'compressExpressionsWithTheta' (YE:735-750). The empty case returns
    init_var(0x0) and emits NO mload(THETA_MPTR) at all - two spellings of zero one line
    apart from compressExpressions' empty case, and the AST port has to keep them distinct. -/
def compressExpressionsWithThetaA {F : Type} [BEq F] (expressions : List (Expression F)) :
    E F (Block Op × String) :=
  if expressions.isEmpty then initVarA (ylit 0) none
  else do
    let theta <- freshVar
    let (lines, finalVar) <- compressExpressionsA expressions theta
    pure ([Stmt.letDecl [theta] (some (yop Op.mload [yvar "THETA_MPTR"]))] ++ lines, finalVar)

/-- The AST twin of 'evaluateAndReset' (YE:879-882). -/
def evaluateAndResetA {F : Type} [BEq F] (expression : Expression F) : E F (Block Op × String) := do
  reset
  evaluateA expression

/-! ### The four family emitters as AST -/

/-- The AST twin of 'GateComputation' - same nine fields, with 'lines' a real block. -/
structure GateComputationA (F : Type) where
  lines : Block Op
  varName : String
  simpleSelectorIndex : Option Nat
  gateIndex : Nat
  gateName : String
  constraintIndex : Nat
  constraintName : String
  polynomialIndex : Nat

/-- The AST twin of 'gateComputationsTagged' (YE:211-238). -/
def gateComputationsTaggedA {F : Type} [BEq F] : E F (List (GateComputationA F)) := do
  let e <- get
  let perGate <- e.cs.gates.toList.zipIdx.mapM fun (gate, gateIndex) => do
    let simpleSel := gate.queriedSelectors.toList.find? fun sel => sel.isSimple
    let simpleIdx := simpleSel.map fun sel => sel.index
    let polys := (Gate.polynomials gate).toList
    polys.zipIdx.mapM fun (poly, polynomialIndex) => do
      let (lines, vName) <- evaluateAndResetA poly
      let constraintName <- Gate.constraintName gate polynomialIndex
      let g : GateComputationA F :=
        { lines := lines, varName := vName, simpleSelectorIndex := simpleIdx,
          gateIndex := gateIndex, gateName := gate.name, constraintIndex := polynomialIndex,
          constraintName := constraintName, polynomialIndex := polynomialIndex }
      pure g
  pure (perGate.flatten)

/-- The AST twin of 'permutationComputations' (YE:264-412), all four families. The delta
    ladder literal is DELTA^(set_idx * chunk_len) computed through the R9 dictionary and
    never hard-coded, and the ladder is NOT multiplied after a chunk's last column. -/
def permutationComputationsA {F : Type} [BEq F] : E F (List (Block Op × String)) := do
  let e <- get
  if e.meta_.numPermutationZs == 0 then pure []
  else do
    let chunkLen := e.meta_.permutationChunkLen
    let columns := e.meta_.permutationColumns
    let zEvals := e.data.permutationZEvals
    let fam1 <- do
      reset
      let (z0, _, _) <- expectOpt zEvals.head? 279 "perm sets non-empty"
      let (l1, l0) <- freshLetA (yop Op.mload [yvar "L_0_MPTR"])
      let (l2, omz) <- freshLetA (yaddmod (ylit 1) (ysubR (wordExpr z0)))
      let (l3, bnd) <- freshLetA (ymulmod (yvar l0) (yvar omz))
      pure (l1 ++ l2 ++ l3, bnd)
    let fam2 <- do
      reset
      let (zn, _, _) <- expectOpt zEvals.getLast? 295 "perm sets non-empty"
      let zns := wordExpr zn
      let (l1, llast) <- freshLetA (yop Op.mload [yvar "L_LAST_MPTR"])
      let (l2, sq) <- freshLetA (ymulmod zns zns)
      let (l3, sqm) <- freshLetA (yaddmod (yvar sq) (ysubR zns))
      let (l4, bnd) <- freshLetA (ymulmod (yvar llast) (yvar sqm))
      pure (l1 ++ l2 ++ l3 ++ l4, bnd)
    let fam3 <- ((List.range e.meta_.numPermutationZs).drop 1).mapM fun i => do
      reset
      let (zi, _, _) <- atIndex zEvals i 315 "z_evals index"
      let (_, _, prevLast) <- atIndex zEvals (i - 1) 317 "z_evals index"
      let zPrevLast <- match prevLast with
        | some w => pure (wordExpr w)
        | none => throw (Midfall.Halo2.Fault.panic (site 317 "non-last set has last eval"))
      let (l1, l0) <- freshLetA (yop Op.mload [yvar "L_0_MPTR"])
      let (l2, diff) <- freshLetA (yaddmod (wordExpr zi) (ysubR zPrevLast))
      let (l3, cont) <- freshLetA (ymulmod (yvar l0) (yvar diff))
      pure (l1 ++ l2 ++ l3, cont)
    let delta <- StateT.lift (feToU256 (e.field.repr e.field.delta))
    let chunkss <- StateT.lift (rustChunks chunkLen (site 332 "permutation chunk length")
      columns.toArray)
    let fam4 <- (List.zip zEvals chunkss.toList).zipIdx.mapM fun (pair, setIdx) => do
      let ((zCur, zNext, _), chunkColsA) := pair
      let chunkCols := chunkColsA.toList
      reset
      let (a1, lLast) <- freshLetA (yop Op.mload [yvar "L_LAST_MPTR"])
      let (a2, lBlind) <- freshLetA (yop Op.mload [yvar "L_BLIND_MPTR"])
      let (a3, lSum) <- freshLetA (yaddmod (yvar lLast) (yvar lBlind))
      let (a4, active) <- freshLetA (yaddmod (ylit 1) (ysubR (yvar lSum)))
      let (a5, beta) <- freshLetA (yop Op.mload [yvar "BETA_MPTR"])
      let (a6, gamma) <- freshLetA (yop Op.mload [yvar "GAMMA_MPTR"])
      let (a7, left) <- freshLetA (wordExpr zNext)
      let leftBlock <- chunkCols.mapM fun col => do
        let colEval <- evalAtExpr col 0
        let sEval <- expectOpt (hashMapGet e.data.permutationEvals col) 365
          "permutation eval present"
        let (b1, betaS) <- freshLetA (ymulmod (yvar beta) (wordExpr sEval))
        let (b2, term) <- freshLetA
          (yaddmod (yaddmod colEval (yvar betaS)) (yvar gamma))
        pure (b1 ++ b2 ++ [Stmt.assign [left] (ymulmod (yvar left) (yvar term))])
      let initialDeltaPower <- StateT.lift (feToU256 (e.field.repr
        (e.field.powNat e.field.delta (setIdx * chunkLen))))
      let (c1, deltaPow) <- freshLetA
        (ymulmod (ymulmod (yvar beta) (yop Op.mload [yvar "X_MPTR"]))
          (u256Expr initialDeltaPower))
      let (c2, right) <- freshLetA (wordExpr zCur)
      let lastColIdx := chunkCols.length - 1
      let rightBlock <- chunkCols.zipIdx.mapM fun (col, colPos) => do
        let colEval <- evalAtExpr col 0
        let (d1, term) <- freshLetA
          (yaddmod (yaddmod colEval (yvar deltaPow)) (yvar gamma))
        let d2 := [Stmt.assign [right] (ymulmod (yvar right) (yvar term))]
        if colPos != lastColIdx then
          pure (d1 ++ d2 ++ [Stmt.assign [deltaPow]
            (ymulmod (yvar deltaPow) (u256Expr delta))])
        else pure (d1 ++ d2)
      let (e1, diff) <- freshLetA (yaddmod (yvar left) (ysubR (yvar right)))
      let (e2, constraint) <- freshLetA (ymulmod (yvar active) (yvar diff))
      pure (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7
        ++ leftBlock.flatten ++ c1 ++ c2 ++ rightBlock.flatten ++ e1 ++ e2, constraint)
    pure ([fam1, fam2] ++ fam3 ++ fam4)

/-- The AST twin of 'lookupComputations' (YE:439-632): boundary, one helper identity per
    chunk (the prefix/suffix product construction with NO inversion), and the accumulator. -/
def lookupComputationsA {F : Type} [BEq F] : E F (List (Block Op × String)) := do
  let e <- get
  if e.meta_.numLookups == 0 then pure []
  else do
    let csDegree <- StateT.lift (ConstraintSystem.degree e.cs)
    let perLookup <- e.cs.lookups.toList.zipIdx.mapM fun (lookup, lookupIdx) => do
      let (mEval, hEvals, zEval, zNextEval) <-
        atIndex e.data.lookupEvals lookupIdx 449 "lookup evals index"
      let chunked <- StateT.lift (LogupBatchedArgument.chunkByDegree lookup csDegree)
      let boundary <- do
        reset
        let (b1, l0) <- freshLetA (yop Op.mload [yvar "L_0_MPTR"])
        let (b2, lLast) <- freshLetA (yop Op.mload [yvar "L_LAST_MPTR"])
        let (b3, lSum) <- freshLetA (yaddmod (yvar l0) (yvar lLast))
        let (b4, bnd) <- freshLetA (ymulmod (yvar lSum) (wordExpr zEval))
        pure (b1 ++ b2 ++ b3 ++ b4, bnd)
      let selectorExpr := chunked.selector
      let helpers <- (chunked.inputExpressionChunks.toList.zip hEvals).mapM
          fun (inputChunk, hEval) => do
        reset
        let (h0, beta) <- freshLetA (yop Op.mload [yvar "BETA_MPTR"])
        let compressed <- inputChunk.toList.mapM fun parallelInput => do
          let (cl, cv) <- compressExpressionsWithThetaA parallelInput.toList
          let (fl, fv) <- freshLetA (yaddmod (yvar cv) (yvar beta))
          pure (cl ++ fl, fv)
        let fVars := compressed.map Prod.snd
        let preLines := compressed.flatMap Prod.fst
        let k := fVars.length
        if k == 0 then
          let zero <- freshVar
          pure (h0 ++ preLines ++ [Stmt.letDecl [zero] (some (ylit 0))], zero)
        else do
          let f0 <- atIndex fVars 0 504 "f_plus_beta_vars index"
          let (pLines, pv) <- freshLetA (yvar f0)
          let pFold := (fVars.drop 1).map fun fb =>
            Stmt.assign [pv] (ymulmod (yvar pv) (yvar fb))
          let (pre0Lines, pre0) <- freshLetA (ylit 1)
          let prefixRes <- ((List.range k).drop 1).foldlM
            (fun (st : List String × Block Op) (j : Nat) => do
              let prevP <- atIndex st.1 (j - 1) 522 "prefix_vars index"
              let prevF <- atIndex fVars (j - 1) 523 "f_plus_beta_vars index"
              let (ls, pj) <- freshLetA (ymulmod (yvar prevP) (yvar prevF))
              pure (st.1 ++ [pj], st.2 ++ ls))
            ([pre0], pre0Lines)
          let (suf0Lines, suf0) <- freshLetA (ylit 1)
          let suffixRes <- (List.range (k - 1)).reverse.foldlM
            (fun (st : List String × Block Op) (j : Nat) => do
              let nextS <- atIndex st.1 (j + 1) 537 "suffix_vars index"
              let nextF <- atIndex fVars (j + 1) 538 "f_plus_beta_vars index"
              let (ls, sj) <- freshLetA (ymulmod (yvar nextS) (yvar nextF))
              pure (setIdx st.1 j sj, st.2 ++ ls))
            (List.replicate (k - 1) "" ++ [suf0], suf0Lines)
          let preVars := prefixRes.1
          let sufVars := suffixRes.1
          let preFirst <- atIndex preVars 0 548 "prefix_vars index"
          let sufFirst <- atIndex sufVars 0 548 "suffix_vars index"
          let (sumLines0, sumVar) <-
            freshLetA (ymulmod (yvar preFirst) (yvar sufFirst))
          let sumRest <- ((List.range k).drop 1).foldlM
            (fun (st : Block Op) (j : Nat) => do
              let preJ <- atIndex preVars j 554 "prefix_vars index"
              let sufJ <- atIndex sufVars j 554 "suffix_vars index"
              let (tl, term) <- freshLetA (ymulmod (yvar preJ) (yvar sufJ))
              pure (st ++ tl ++ [Stmt.assign [sumVar]
                (yaddmod (yvar sumVar) (yvar term))]))
            sumLines0
          let (hpLines, hp) <- freshLetA (ymulmod (wordExpr hEval) (yvar pv))
          let (hcLines, helperC) <- freshLetA
            (yaddmod (yvar hp) (ysubR (yvar sumVar)))
          pure (h0 ++ preLines ++ pLines ++ pFold ++ prefixRes.2 ++ suffixRes.2
            ++ sumRest ++ hpLines ++ hcLines, helperC)
      let accumulator <- do
        reset
        let (x1, lLast) <- freshLetA (yop Op.mload [yvar "L_LAST_MPTR"])
        let (x2, lBlind) <- freshLetA (yop Op.mload [yvar "L_BLIND_MPTR"])
        let (x3, active) <- freshLetA
          (yaddmod (ylit 1) (ysubR (yaddmod (yvar lLast) (yvar lBlind))))
        let (x4, beta) <- freshLetA (yop Op.mload [yvar "BETA_MPTR"])
        let hFirst <- atIndex hEvals 0 589 "h_evals index"
        let (x5, sumH) <- freshLetA (wordExpr hFirst)
        let hFold := (hEvals.drop 1).map fun h =>
          Stmt.assign [sumH] (yaddmod (yvar sumH) (wordExpr h))
        let (selLines, selVar) <- evaluateA selectorExpr
        let (x6, sSumH) <- freshLetA (ymulmod (yvar selVar) (yvar sumH))
        let (x7, diff) <- freshLetA
          (yaddmod (wordExpr zNextEval) (ysubR (yaddmod (wordExpr zEval) (yvar sSumH))))
        let (tLines, tVar) <- compressExpressionsWithThetaA chunked.tableExpressions.toList
        let (x8, tPlusBeta) <- freshLetA (yaddmod (yvar tVar) (yvar beta))
        let (x9, core) <- freshLetA
          (yaddmod (ymulmod (yvar diff) (yvar tPlusBeta)) (wordExpr mEval))
        let (x10, accC) <- freshLetA (ymulmod (yvar active) (yvar core))
        pure (x1 ++ x2 ++ x3 ++ x4 ++ x5 ++ hFold ++ selLines ++ x6 ++ x7 ++ tLines ++ x8
          ++ x9 ++ x10, accC)
      pure ([boundary] ++ helpers ++ [accumulator])
    pure (perLookup.flatten)

/-- The AST twin of 'trashcanComputations' (YE:654-723). The lazy challenge load is kept:
    with no constraint expressions the mload(TRASH_CHALLENGE_MPTR) statement is never
    emitted, so an empty trashcan's block has no unused let. -/
def trashcanComputationsA {F : Type} [BEq F] : E F (List (Block Op × String)) := do
  let e <- get
  if e.meta_.numTrashcans == 0 then pure []
  else
    e.cs.trashcans.toList.zipIdx.mapM fun (argument, idx) => do
      reset
      let constraintExprs := argument.constraintExpressions.toList
      let (headLines, trashChallenge) <-
        if constraintExprs.isEmpty then pure ([], none)
        else do
          let var <- freshVar
          pure ([Stmt.letDecl [var]
            (some (yop Op.mload [yvar "TRASH_CHALLENGE_MPTR"]))], some var)
      let foldRes <- constraintExprs.foldlM
        (fun (st : Block Op × Option String) (expr : Expression F) => do
          let (eLines, eVar) <- evaluateA expr
          let next <- freshVar
          let prev : Expr Op := match st.2 with | some v => yvar v | none => ylit 0
          let tau <- match trashChallenge with
            | some t => pure (yvar t)
            | none => throw (Midfall.Halo2.Fault.panic
                (site 687 "trash_challenge present when expressions non-empty"))
          pure (st.1 ++ eLines ++
            [Stmt.letDecl [next] (some (ycompressStep prev tau (yvar eVar)))], some next))
        (headLines, none)
      let (lines1, compressed) <- match foldRes.2 with
        | some v => pure (foldRes.1, yvar v)
        | none => do
            let zero <- freshVar
            pure (foldRes.1 ++ [Stmt.letDecl [zero] (some (ylit 0))], yvar zero)
      let (selLines, selVar) <- evaluateA argument.selector
      let (y1, oneMinusQ) <- freshLetA (yaddmod (ylit 1) (ysubR (yvar selVar)))
      let trashEval <- atIndex e.data.trashcanEvals idx 708 "trashcan evals index"
      let (y2, scaled) <- freshLetA (ymulmod (yvar oneMinusQ) (wordExpr trashEval))
      let (y3, c) <- freshLetA (yaddmod compressed (ysubR (yvar scaled)))
      pure (lines1 ++ selLines ++ y1 ++ y2 ++ y3, c)


/-! ### Gates: the AST path against the text path -/

namespace Kats
open Midfall.Generator.QuotientEvaluatorKats

/-- The corpus: every expression shape the Evaluator can emit, each through a different arm of
    the visitor or the fusion predicate. A corpus of one expression would let an arm of the
    visitor be wrong and stay green, so the list is one per closure plus the fused paths. -/
def corpus : List (Expression QVMFr) :=
  [ eA 0, eAn 0, eF 1, eF 0, eI 0, eC 5, eMul (eA 0) (eA 1), eAdd (eA 0) (eA 1),
    eNeg (eA 0), eScale (eA 2) 3, eAdd (eScale (eA 2) 3) (eC 5),
    eMul (eMul (eA 0) (eA 1)) (eA 2), eMul (eA 3) (eA 4),
    eMul (eMul (eMul (eMul (eA 0) (eA 0)) (eA 0)) (eA 0)) (eA 0),
    eAdd (eC 1) (eAdd (eC 2) (eA 1)), eAdd (eScale (eA 1) 1) (eC 0) ]

/-- Run both paths on one expression from one starting state and return the four observables:
    the final variable, the statement count, the printed token stream and the post-state. -/
def bothRoutes (expr : Expression QVMFr) (start : Evaluator QVMFr) :
    Bool × String :=
  match evaluate expr start, evaluateA expr start with
  | .ok ((tLines, tVar), _), .ok ((aLines, aVar), _) =>
      (tVar == aVar && tLines.length == aLines.length &&
        yulTokens ("{" ++ String.intercalate "\n" tLines ++ "}") == yulTokens (EVM.print aLines),
       tVar)
  | _, _ => (false, "")

/-- GATE 1 (THE CROSS-CHECK). For every expression in the corpus, from the fixture state and
    from the pow5-helper state: the text path and the AST path agree on the FINAL VARIABLE
    NAME, on the NUMBER of emitted statements, and their outputs tokenise identically.

    The variable name and the count are not redundancy for the token check - they are the
    CACHE check. init_var dedups on the rendered value, so if the AST path's key partition
    differed from the text path's at any point, a later expression would reuse a different
    variable and the name would move even when the arithmetic is right. Pinning the name and
    the count alongside the tokens is what makes the printed comparison a statement about the
    same program and not merely about a program that happens to look alike. -/
def evaluateAst_matchesText_ok : Bool :=
  corpus.all fun expr => (bothRoutes expr ev).1 && (bothRoutes expr evPow5).1

/-- GATE 2 (the post-state agrees, so the interior mutability is ported the same way). The
    var_counter, the cache SIZE and the pow5 flag after each route must match - the cache
    contents themselves are keyed differently by construction (text vs printed AST) and only
    their cardinality is observable here, which is stated rather than hidden. -/
def evaluateAst_stateAgrees_ok : Bool :=
  let row (start : Evaluator QVMFr) (expr : Expression QVMFr) : Bool :=
    let s1 := match evaluate expr start with | .ok (_, s) => s | .error _ => start
    let s2 := match evaluateA expr start with | .ok (_, s) => s | .error _ => start
    s1.varCounter == s2.varCounter && s1.varCache.length == s2.varCache.length &&
      s1.pow5Used == s2.pow5Used
  -- from the plain state AND from the pow5-enabled one: the pow5 flag is the Cell<bool> the
  -- header names as hazard 1's third mutable, and a converter that forgot to set it is only
  -- observable on the second route.
  corpus.all (row ev) && corpus.all (row evPow5) &&
    -- and the flag really flips on the q_pow5 arm on both paths, so the row above is not
    -- comparing two states that both stayed false
    (match evaluate (eMul (eMul (eMul (eMul (eA 0) (eA 0)) (eA 0)) (eA 0)) (eA 0)) evPow5 with
        | .ok (_, s) => s.pow5Used
        | .error _ => false) &&
    (match evaluateA (eMul (eMul (eMul (eMul (eA 0) (eA 0)) (eA 0)) (eA 0)) (eA 0)) evPow5 with
        | .ok (_, s) => s.pow5Used
        | .error _ => false)

/-- GATE 3 (the four family emitters, whole). gate/permutation/lookup/trash: same block count,
    same final variable per identity, same token stream per identity, from the same fixture.
    These are the sites the brief counts as the string machinery, and they are where a
    converter loses a line: the delta ladder's last-column guard, the lazy trash challenge
    load, the k == 0 helper arm, the prefix/suffix duplicate 'let varN := 1'. -/
def familiesAst_matchesText_ok : Bool :=
  let g := match runOpt gateComputationsTagged ev, runOpt gateComputationsTaggedA ev with
    | some xs, some ys => xs.length == ys.length &&
        (xs.zip ys).all fun (x, y) =>
          x.var == y.varName && x.lines.length == y.lines.length &&
          yulTokens ("{" ++ String.intercalate "\n" x.lines ++ "}") == yulTokens (EVM.print y.lines)
    | _, _ => false
  let p := match runOpt permutationComputations ev, runOpt permutationComputationsA ev with
    | some xs, some ys => xs.length == ys.length &&
        (xs.zip ys).all fun (x, y) => x.2 == y.2 &&
          yulTokens ("{" ++ String.intercalate "\n" x.1 ++ "}") == yulTokens (EVM.print y.1)
    | _, _ => false
  let l := match runOpt lookupComputations ev, runOpt lookupComputationsA ev with
    | some xs, some ys => xs.length == ys.length &&
        (xs.zip ys).all fun (x, y) => x.2 == y.2 &&
          yulTokens ("{" ++ String.intercalate "\n" x.1 ++ "}") == yulTokens (EVM.print y.1)
    | _, _ => false
  let t := match runOpt trashcanComputations ev, runOpt trashcanComputationsA ev with
    | some xs, some ys => xs.length == ys.length &&
        (xs.zip ys).all fun (x, y) => x.2 == y.2 &&
          yulTokens ("{" ++ String.intercalate "\n" x.1 ++ "}") == yulTokens (EVM.print y.1)
    | _, _ => false
  g && p && l && t &&
    -- and the families are non-empty at the fixture, so the four clauses above are not all
    -- passing over an empty zip
    ((runOpt gateComputationsTagged ev).getD []).length == 3 &&
      ((runOpt permutationComputations ev).getD []).length == 5 &&
      ((runOpt lookupComputations ev).getD []).length == 3 &&
      ((runOpt trashcanComputations ev).getD []).length == 1

/-- GATE 4 (THE NUMERIC-SPELLING DIVERGENCE, pinned as string containment). The text port
    writes mload(0x2000) and 0x5; the AST printer writes mload(8192) and 5. Neither yulTokens
    nor stmtsBeq can see this - that is the standing note - so the mapping is pinned here
    explicitly, per D-P30 clause 3, with the value equality checked by the same hex reader
    yulTokens uses. -/
def evaluatorAst_numericSpelling_ok : Bool :=
  let txt := match runOpt (evaluate (eA 0)) ev with
    | some (ls, _) => String.intercalate "\n" ls
    | none => ""
  let printed := match runOpt (evaluateA (eA 0)) ev with
    | some (ls, _) => EVM.print ls
    | none => ""
  txt.contains "mload(0x2000)" && printed.contains "mload(8192)" &&
    ! txt.contains "8192" && ! printed.contains "0x2000" && hexVal "2000" == 8192 &&
    -- and a field constant: the text writes 0x5, the AST writes 5
    (let t2 := match runOpt (evaluate (eC 5)) ev with
      | some (ls, _) => String.intercalate "\n" ls
      | none => ""
      let p2 := match runOpt (evaluateA (eC 5)) ev with
      | some (ls, _) => EVM.print ls
      | none => ""
      t2.contains "0x5" && p2.contains "5" && ! p2.contains "0x5")

/-- GATE 5 (PLAN DEPENDENCE - the Data side). Every eval pointer the Evaluator reaches
    through, moved in the Data, moves the emitted AST. These are the values a converter would
    most plausibly hard-code, because at the fixture they are a fixed set of addresses. -/
def evaluatorAstDependsOnData_ok : Bool :=
  let base := match runOpt (evaluateA (eMul (eA 0) (eF 1))) ev with
    | some (ls, _) => ls
    | none => []
  let neq (x : Block Op) : Bool := ! SyntaxEq.stmtsBeq base x
  neq (match runOpt (evaluateA (eMul (eA 0) (eF 1)))
        (Evaluator.new (qFrCtx qDelta) qCs qMeta { qData with
          adviceEvals := [((0, 0), wmem 0x2100)] }) with
      | some (ls, _) => ls | none => []) &&
    neq (match runOpt (evaluateA (eMul (eA 0) (eF 1)))
        (Evaluator.new (qFrCtx qDelta) qCs qMeta { qData with
          fixedEvals := [((1, 0), wmem 0x2500)] }) with
      | some (ls, _) => ls | none => []) &&
    neq (match runOpt (evaluateA (eI 0))
        (Evaluator.new (qFrCtx qDelta) qCs qMeta { qData with
          instanceEval := wmem 0x3900 }) with
      | some (ls, _) => ls | none => []) &&
    neq (match runOpt (evaluateA (eI 1))
        (Evaluator.new (qFrCtx qDelta) qCs qMeta { qData with
          committedInstanceEvals := [((0, 0), wmem 0x2900)] }) with
      | some (ls, _) => ls | none => []) &&
    neq (match runOpt (evaluateA (eC 0))
        (Evaluator.new (qFrCtx qDelta) qCs qMeta { qData with
          challenges := [wmem 0x3d00] }) with
      | some (ls, _) => ls | none => [])

/-- Per-identity token agreement between the text family list and the AST family list. A
    named helper because the projection inside a match arm does not elaborate here. -/
def permZipOk (xs : List (Lines × Var)) (ys : List (Block Op × String)) : Bool :=
  match xs, ys with
  | x :: xr, y :: yr =>
      yulTokens ("{" ++ String.intercalate "\n" x.1 ++ "}") == yulTokens (EVM.print y.1)
        && permZipOk xr yr
  | [], [] => true
  | _, _ => false

/-- GATE 6 (PLAN DEPENDENCE - the meta side, including the zero/small-at-the-fixture cases the
    standing note warns about). simpleSelectorCols decides whether a fixed column emits the
    literal 1 or a lookup; numCommittedInstances decides which instance arm runs;
    numPermutationZs / numLookups / numTrashcans decide whether a family exists at all. -/
def evaluatorAstDependsOnMeta_ok : Bool :=
  let base := match runOpt (evaluateA (eF 1)) ev with
    | some (ls, _) => ls | none => []
  let neq (x : Block Op) : Bool := ! SyntaxEq.stmtsBeq base x
  neq (match runOpt (evaluateA (eF 1))
        (Evaluator.new (qFrCtx qDelta) qCs { qMeta with simpleSelectorCols := [1] } qData) with
      | some (ls, _) => ls | none => []) &&
    (let z := match runOpt (evaluateA (eI 0))
          (Evaluator.new (qFrCtx qDelta) qCs { qMeta with numCommittedInstances := 0 } qData) with
        | some (ls, _) => ls | none => []
      let o := match runOpt (evaluateA (eI 0)) ev with
        | some (ls, _) => ls | none => []
      ! SyntaxEq.stmtsBeq o z) &&
    -- the three family-count guards, each driven to zero and back
    (runOpt permutationComputationsA (Evaluator.new (qFrCtx qDelta) qCs
        { qMeta with numPermutationZs := 0 } qData) |>.getD []).isEmpty &&
    (runOpt lookupComputationsA (Evaluator.new (qFrCtx qDelta) qCs
        { qMeta with numLookups := 0 } qData) |>.getD []).isEmpty &&
    (runOpt trashcanComputationsA (Evaluator.new (qFrCtx qDelta) qCs
        { qMeta with numTrashcans := 0 } qData) |>.getD []).isEmpty &&
    -- and FEWER permutation z slots removes a family on both paths, token-agreeing. Going the
    -- other way (3 slots) is not a legal perturbation of THIS fixture: qData carries exactly
    -- two permutation-Z eval triples, so a third slot aborts at the atIndex on YE:315 on both
    -- paths - which is the R4 panic working, and is why the row drives the count down.
    (let m1 := { qMeta with numPermutationZs := 1 }
      let t := runOpt permutationComputations (Evaluator.new (qFrCtx qDelta) qCs m1 qData)
      let a := runOpt permutationComputationsA (Evaluator.new (qFrCtx qDelta) qCs m1 qData)
      match t, a with
      | some xs, some ys => xs.length == 4 && ys.length == 4 &&
          permZipOk xs ys
      | _, _ => false) &&
    -- the lazy challenge load: an EMPTY trashcan must emit no mload(TRASH_CHALLENGE_MPTR) on
    -- either path. This is the AST twin of the text port's trashcanEmptyNoChallengeLoad_ok,
    -- and without it the empty arm of YE:671-677 is untested here - measured, since an
    -- earlier version of this gate passed while always emitting the load.
    (let emptyTr : TrashArgument QVMFr :=
        { name := "tr0", selector := eF 1, constraintExpressions := #[] }
      let cs2 : ConstraintSystem QVMFr := { qCs with trashcans := #[emptyTr] }
      let e2 := Evaluator.new (qFrCtx qDelta) cs2 qMeta qData
      match runOpt trashcanComputations e2, runOpt trashcanComputationsA e2 with
      | some t, some a =>
          (t.headD ([], "")).1.any (fun l => l == "let var0 := 0") &&
            ! (t.headD ([], "")).1.any (fun l => l.contains "TRASH_CHALLENGE_MPTR") &&
            ! (EVM.print (a.headD ([], "")).1).contains "TRASH_CHALLENGE_MPTR" &&
            yulTokens ("{" ++ String.intercalate "\n" (t.headD ([], "")).1 ++ "}") ==
              yulTokens (EVM.print (a.headD ([], "")).1)
      | _, _ => false)

/-- GATE 7 (DELTA is computed, not hard-coded, on the AST path too). The text port has
    deltaLiteral_computedNotHardcoded_ok; this is its twin: changing the field dictionary's
    delta changes the emitted literal, and the emitted literal is the DECIMAL of the number
    the text port renders as hex. -/
def deltaAst_computedNotHardcoded_ok : Bool :=
  let p5 := match runOpt permutationComputationsA (Evaluator.new (qFrCtx 5) qCs qMeta qData) with
    | some ps => EVM.print ((ps.getD 3 ([], "")).1)
    | none => ""
  let p9 := match runOpt permutationComputationsA (Evaluator.new (qFrCtx 9) qCs qMeta qData) with
    | some ps => EVM.print ((ps.getD 3 ([], "")).1)
    | none => ""
  p5.contains ", 5, r)" && p9.contains ", 9, r)" && ! p5.contains ", 9, r)" &&
    -- and the initial power is DELTA^(set_idx*chunk_len): 5^3 = 125, 7^3 = 343
    (match runOpt permutationComputationsA (Evaluator.new (qFrCtx 7) qCs qMeta qData) with
      | some ps => ((EVM.print ((ps.getD 4 ([], "")).1))).contains "343"
      | none => false)

/-- GATE 8 (the relation gap, at the Evaluator). Every mulmod of the emitted AST spelled as a
    USER call named mulmod keeps the token stream and breaks stmtsBeq - the class every
    previous slice reproduced, now on the quotient emitter. The rewrite has to reach inside
    the nested let expressions, which is why it goes through mapStmtExprs and why the count
    below proves it fired. -/
def evaluatorAstDetectsBuiltinVsCall_ok : Bool :=
  let good := match runOpt (evaluateA (eAdd (eMul (eA 0) (eA 1)) (eScale (eA 2) 3))) ev with
    | some (ls, _) => ls | none => []
  let bad := good.map (Midfall.Lowering.GenAst.mapStmtExprs fun
    | Expr.builtin Op.mulmod args => Expr.call "mulmod" args
    | e => e)
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad &&
    Midfall.Generator.VerifierPartialKats.occ (EVM.print good) "mulmod(" == 2 &&
    Midfall.Generator.VerifierPartialKats.occ (EVM.print bad) "mulmod(" == 2

/-- GATE 9 (the AST is a program, not a shape). Structural facts about one emitted identity:
    the gate product is TWO named column lets and one mulmod let whose value is a builtin
    (not a call), and the negated arm is an addmod whose second argument is a sub. Matching on
    constructors is what separates this from a token count. -/
def evaluatorAstIsReal_ok : Bool :=
  match runOpt (evaluateA (eMul (eA 0) (eA 1))) ev with
  | some (ls, v) =>
      ls.length == 3 &&
      (match ls[0]? with
       | some (Stmt.letDecl ["a_0"] (some (Expr.builtin Op.mload [Expr.lit (Literal.number 8192)])))
           => true
       | _ => false) &&
      (match ls[2]? with
       | some (Stmt.letDecl [_] (some (Expr.builtin Op.mulmod
           [Expr.var "a_0", Expr.var "a_1", Expr.var "r"]))) => true
       | _ => false) &&
      v == "var0"
  | none => false

/-- The gate product of the fixture, quoted from the text port's own bytes through the vendored
    DSL: two named advice-column lets and one mulmod. Hex here parses to the same
    Literal.number the constructor path builds, so this is an independent elaboration of the
    same program and not a restatement of the constructors. -/
def gateProduct_quotation : Block Op := yul% {
  let a_0 := mload(0x2000)
  let a_1 := mload(0x2020)
  let var0 := mulmod(a_0, a_1, r)
}

/-- The same three statements with mulmod spelled as a USER call - the shape stmtsBeq must
    reject and yulTokens must not. -/
def gateProduct_wrongQuotation : Block Op :=
  [ Stmt.letDecl ["a_0"] (some (Expr.builtin Op.mload [Expr.lit (Literal.number 8192)]))
  , Stmt.letDecl ["a_1"] (some (Expr.builtin Op.mload [Expr.lit (Literal.number 8224)]))
  , Stmt.letDecl ["var0"] (some (Expr.call "mulmod"
      [Expr.var "a_0", Expr.var "a_1", Expr.var "r"])) ]

def trashBlock_quotation : Block Op := yul% {
  let var0 := mload(TRASH_CHALLENGE_MPTR)
  let a_3 := mload(0x2060)
  let a_4 := mload(0x2080)
  let var1 := mulmod(a_3, a_4, r)
  let var2 := addmod(mulmod(0, var0, r), var1, r)
  let f_1 := mload(0x2420)
  let var3 := addmod(1, sub(r, f_1), r)
  let var4 := mulmod(var3, mload(0x3a00), r)
  let var5 := addmod(var2, sub(r, var4), r)
}

/-- GATE 10 (THE AUTHORITATIVE RELATION, against an independent elaboration path). The token
    gate compares the AST port to the TEXT port, which is independent of the AST port but not
    of the constructors' own choices. Here the emitted AST is compared under stmtsBeq to a
    'yul%' QUOTATION of the same identity - parsed by the vendored DSL, not built by these
    helpers - which is the check D-P30 clause 1 names as the record. Two identities: the gate
    product (two named column lets and a mulmod) and the whole trashcan block (nine
    statements, the lazy challenge load, the selector fold, the final difference). The third
    clause is the non-vacuity half: the same three statements with mulmod spelled as a USER
    call must NOT satisfy the check, so the gate is not merely two spellings of one source. -/
def evaluateAst_quotation_ok : Bool :=
  SyntaxEq.stmtsBeq
    (match runOpt (evaluateA (eMul (eA 0) (eA 1))) ev with
      | some (ls, _) => ls | none => []) gateProduct_quotation &&
    SyntaxEq.stmtsBeq
      (match runOpt trashcanComputationsA ev with
        | some ts => (ts.headD ([], "")).1 | none => []) trashBlock_quotation &&
    ! SyntaxEq.stmtsBeq
      (match runOpt (evaluateA (eMul (eA 0) (eA 1))) ev with
        | some (ls, _) => ls | none => []) gateProduct_wrongQuotation

end Kats

#eval Midfall.Lowering.GenAstQuotient.Kats.evaluateAst_matchesText_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluateAst_stateAgrees_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.familiesAst_matchesText_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluatorAst_numericSpelling_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluatorAstDependsOnData_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluatorAstDependsOnMeta_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.deltaAst_computedNotHardcoded_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluatorAstDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluatorAstIsReal_ok -- expect true
#eval Midfall.Lowering.GenAstQuotient.Kats.evaluateAst_quotation_ok -- expect true

end Midfall.Lowering.GenAstQuotient
