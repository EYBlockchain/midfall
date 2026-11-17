import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Program
set_option autoImplicit false

/-!
  PROPOSED: `formal/Midfall/Lowering/YulParse.lean` (new, INFRA). A TOTAL, fuel-structural parser
  from the `yulTokens` stream of generator text to the vendored AST, resolving built-in versus
  user call with the vendored `EVM.mkCall` (the rule the `yul%` DSL uses, and solc's rule: a name
  that is a built-in is the built-in). `none` on any token it does not understand.
-/

namespace Midfall.Lowering.YulParse

open YulSemantics YulSemantics.EVM

abbrev Toks := List String

def isNumTok (t : String) : Bool := !t.isEmpty && t.all Char.isDigit

def isIdentTok (t : String) : Bool :=
  !t.isEmpty && !(t.front.isDigit) &&
    t.all (fun c => c.isAlphanum || c == '_' || c == '$' || c == '.') &&
    !(["let", "if", "for", "switch", "case", "default", "function", "break", "continue", "leave",
      "true", "false"].contains t)

def litOf (t : String) : Option Literal :=
  if t == "true" then some (.bool true)
  else if t == "false" then some (.bool false)
  else if isNumTok t then some (.number t.toNat!)
  else none

/-- comma-separated identifiers up to (not including) a stop token -/
def identList : Nat → Toks → Option (List String × Toks)
  | 0, _ => none
  | fuel + 1, t :: rest =>
      if isIdentTok t then
        match rest with
        | "," :: rest' => (identList fuel rest').map fun (xs, r) => (t :: xs, r)
        | _ => some ([t], rest)
      else none
  | _ + 1, [] => none

mutual
def parseExpr : Nat → Toks → Option (Expr Op × Toks)
  | 0, _ => none
  | fuel + 1, t :: rest =>
      match litOf t with
      | some l => some (.lit l, rest)
      | none =>
          if isIdentTok t then
            match rest with
            | "(" :: ")" :: rest' => some (mkCall t [], rest')
            | "(" :: rest' =>
                (parseArgs fuel rest').map fun (args, r) => (mkCall t args, r)
            | _ => some (.var t, rest)
          else none
  | _ + 1, [] => none

/-- arguments after the opening parenthesis, consuming the closing one -/
def parseArgs : Nat → Toks → Option (List (Expr Op) × Toks)
  | 0, _ => none
  | fuel + 1, toks =>
      match parseExpr fuel toks with
      | some (e, "," :: rest) => (parseArgs fuel rest).map fun (es, r) => (e :: es, r)
      | some (e, ")" :: rest) => some ([e], rest)
      | _ => none
end

mutual
/-- statements up to and including the closing brace of the enclosing block -/
def parseStmts : Nat → Toks → Option (List (Stmt Op) × Toks)
  | 0, _ => none
  | _ + 1, "}" :: rest => some ([], rest)
  | fuel + 1, toks =>
      match parseStmt fuel toks with
      | some (s, rest) => (parseStmts fuel rest).map fun (ss, r) => (s :: ss, r)
      | none => none

def parseBlock : Nat → Toks → Option (List (Stmt Op) × Toks)
  | 0, _ => none
  | fuel + 1, "{" :: rest => parseStmts fuel rest
  | _ + 1, _ => none

def parseCases : Nat → Toks →
    Option (List (Literal × List (Stmt Op)) × Option (List (Stmt Op)) × Toks)
  | 0, _ => none
  | fuel + 1, "case" :: l :: rest =>
      match litOf l, parseBlock fuel rest with
      | some lit, some (body, r) =>
          (parseCases fuel r).map fun (cs, d, r') => ((lit, body) :: cs, d, r')
      | _, _ => none
  | fuel + 1, "default" :: rest =>
      (parseBlock fuel rest).map fun (body, r) => ([], some body, r)
  | _ + 1, toks => some ([], none, toks)

def parseStmt : Nat → Toks → Option (Stmt Op × Toks)
  | 0, _ => none
  | fuel + 1, "{" :: rest => (parseStmts fuel rest).map fun (b, r) => (.block b, r)
  | fuel + 1, "function" :: name :: "(" :: rest =>
      let ps? : Option (List String × Toks) :=
        match rest with
        | ")" :: r => some ([], r)
        | _ => match identList fuel rest with
               | some (ps, ")" :: r) => some (ps, r)
               | _ => none
      match ps? with
      | none => none
      | some (ps, r) =>
          let rs? : Option (List String × Toks) :=
            match r with
            | "-" :: ">" :: r' => identList fuel r'
            | _ => some ([], r)
          match rs? with
          | none => none
          | some (rs, r2) => (parseBlock fuel r2).map fun (b, r3) => (.funDef name ps rs b, r3)
  | fuel + 1, "let" :: rest =>
      match identList fuel rest with
      | some (xs, ":" :: "=" :: r) => (parseExpr fuel r).map fun (e, r') => (.letDecl xs (some e), r')
      | some (xs, r) => some (.letDecl xs none, r)
      | none => none
  | fuel + 1, "if" :: rest =>
      match parseExpr fuel rest with
      | some (c, r) => (parseBlock fuel r).map fun (b, r') => (.cond c b, r')
      | none => none
  | fuel + 1, "switch" :: rest =>
      match parseExpr fuel rest with
      | some (c, r) => (parseCases fuel r).map fun (cs, d, r') => (.switch c cs d, r')
      | none => none
  | fuel + 1, "for" :: rest =>
      match parseBlock fuel rest with
      | some (init, r1) =>
          match parseExpr fuel r1 with
          | some (c, r2) =>
              match parseBlock fuel r2 with
              | some (post, r3) =>
                  (parseBlock fuel r3).map fun (body, r4) => (.forLoop init c post body, r4)
              | none => none
          | none => none
      | none => none
  | _ + 1, "break" :: rest => some (.break, rest)
  | _ + 1, "continue" :: rest => some (.continue, rest)
  | _ + 1, "leave" :: rest => some (.leave, rest)
  | fuel + 1, toks =>
      -- assignment `a, b := e` or an expression statement
      match identList fuel toks with
      | some (xs, ":" :: "=" :: r) => (parseExpr fuel r).map fun (e, r') => (.assign xs e, r')
      | _ => (parseExpr fuel toks).map fun (e, r) => (.exprStmt e, r)
end

/-- A whole block given as a token stream WITH its braces. All tokens must be consumed. -/
def parseTokens (toks : Toks) : Option (Block Op) :=
  match parseBlock (toks.length + 1) toks with
  | some (b, []) => some b
  | _ => none

/-- Generated lines (no enclosing braces). -/
def parseLines (ls : List String) : Option (Block Op) :=
  parseTokens ("{" :: Midfall.Generator.yulTokens (String.intercalate "\n" ls) ++ ["}"])

end Midfall.Lowering.YulParse

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs
open Midfall.LoweringV2 Midfall.Lowering Midfall.Lowering.YulParse YulSemantics YulSemantics.EVM

def b : PartialCtx := partialCtxOfVerifier poseidonM

def rt (toks : List String) : String :=
  match parseTokens toks with
  | none => "PARSE FAILED"
  | some blk => s!"parsed stmts={blk.length} roundTrip={yulTokens (EVM.print blk) == toks} tokens={toks.length}"

-- 1. the WHOLE main assembly block of the generator text (14054 tokens): parse, print, compare
#eval rt (mainAssemblyTokens poseidonM)
-- 2. the ABI guard block
#eval rt (abiGuardTokens poseidonM)
-- 3. the emitter's AST against the parse, STRUCTURALLY, region by region (stmtsBeq, not tokens)
def reg (text : String) (ast : Block EVM.Op) : String :=
  match parseLines [text] with
  | none => "PARSE FAILED"
  | some blk => s!"stmts={blk.length}/{ast.length} stmtsBeq={SyntaxEq.stmtsBeq blk ast}"
#eval reg (partsOf poseidonM).assemblyHelpers (GenAst.emitHelpers poseidonPv)
#eval reg (partsOf poseidonM).vkLoading (GenAst.emitPartial poseidonPv .vkLoading)
#eval reg (partsOf poseidonM).transcriptProofParser (GenAst.emitPartial poseidonPv .transcriptParser)
#eval reg (partsOf poseidonM).lagrange (GenAst.emitPartial poseidonPv .lagrange)
#eval reg (renderQuotientAndLinearization b "" "") (GenAst.emitPartial poseidonPv .quotientLin)
#eval reg (partsOf poseidonM).pcs (GenAst.emitPartial poseidonPv .pcs)
#eval reg (partsOf poseidonM).finalPairing (GenAst.emitPartial poseidonPv .finalPairing)
#eval reg (partsOf poseidonM).traceReturn (GenAst.emitPartial poseidonPv .traceReturn)
-- 4. the regions the emitter does not produce: parse them
#eval rt ("{" :: yulTokens (partsOf poseidonM).accumulatorHelpers ++ ["}"])
#eval rt ("{" :: yulTokens (renderQuotientHelpers b) ++ ["}"])
#eval rt ("{" :: yulTokens (renderQuotientNumeratorBlock b) ++ ["}"])
-- 5. the parsed program: closedness and writer scan on the FULL text (what Valid.closed / noWriters
--    would say about the real program)
def parsedMain : Block EVM.Op := (parseTokens (mainAssemblyTokens poseidonM)).getD []
def parsedGuard : Block EVM.Op := (parseTokens (abiGuardTokens poseidonM)).getD []
def parsedProg : Block EVM.Op :=
  Inline.inlineContractConstants (constTableOf poseidonM)
    (parsedGuard ++ wrapperLocals poseidonM 0 0 ++ parsedMain)
#eval (parsedMain.length, parsedGuard.length)
#eval (freeNames (Inline.inlineContractConstants (constTableOf poseidonM) parsedMain))
#eval (Midfall.Yul.Bridge.noWritersFuel 20000 parsedProg)
-- 6. user calls of the full program all resolve to a defined function with the right arity?
def funSigs (blk : Block EVM.Op) : List (String × Nat) :=
  blk.filterMap fun s => match s with | .funDef n ps _ _ => some (n, ps.length) | _ => none
#eval funSigs parsedMain

/-! ## The V3 main block, constructively: today's emitters + the four missing regions -/

namespace V3
open Midfall.Lowering.YulParse

/-- PCS with the template's scopes: one wrapper block holding the 8 `computationsAst` blocks. -/
def emitPcsScoped (pv : PlanView) : Block EVM.Op :=
  match Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
      pv.truncatedChallenges false with
  | .ok blocks => [Stmt.block (blocks.map Stmt.block)]
  | .error _ => []

/-- INTERIM stand-ins for the three un-emitted regions: the parse of the model's own text. -/
def accHelpersP (m : Model) : Block EVM.Op :=
  (parseLines [renderAccumulatorHelpers (partialCtxOfVerifier m)]).getD []
def quotientHelpersP (m : Model) : Block EVM.Op :=
  (parseLines [renderQuotientHelpers (partialCtxOfVerifier m)]).getD []
def quotientNumeratorP (m : Model) : Block EVM.Op :=
  (parseLines [renderQuotientNumeratorBlock (partialCtxOfVerifier m)]).getD []

def emitPartialV3 (pv : PlanView) (m : Model) : Partial → Block EVM.Op
  | .quotientLin => quotientHelpersP m ++ quotientNumeratorP m ++ GenAst.emitQuotientLin pv
  | .pcs => emitPcsScoped pv
  | q => GenAst.emitPartial pv q

def emitSlicesV3 (pv : PlanView) (m : Model) : Block EVM.Op :=
  Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++ emitPartialV3 pv m q

def mainAsmRawV3 (pv : PlanView) (m : Model) : YulBlock :=
  mainGuardBlock ++ GenAst.emitHelpers pv ++ accHelpersP m ++ mainLocals ++ emitSlicesV3 pv m

end V3
open V3

-- 7. pcs with scopes: structural equality with the parse of the pcs text
#eval reg (partsOf poseidonM).pcs (emitPcsScoped poseidonPv)
-- 8. THE WHOLE BLOCK: token agreement (today's clause) and structural agreement (proposed clause)
#eval (yulTokens (EVM.print (mainAsmRawV3 poseidonPv poseidonM)) == mainAssemblyTokens poseidonM,
       SyntaxEq.stmtsBeq (mainAsmRawV3 poseidonPv poseidonM) parsedMain,
       (mainAsmRawV3 poseidonPv poseidonM).length)
-- 9. slice lengths (statements) in the complete program
#eval Midfall.Lowering.partials.map (fun q => (emitPartialV3 poseidonPv poseidonM q).length)
-- 10. functions: what `helpersOf` hoists today (8) vs what the complete program defines (15)
#eval ((funSigs (GenAst.emitHelpers poseidonPv)).map (·.1)).length
#eval (funSigs (mainAsmRawV3 poseidonPv poseidonM)).length
-- 11. user-function calls per region of the complete program (callee inventory)
mutual
def callsE : Expr EVM.Op → List String
  | .call f args => f :: callsEs args
  | .builtin _ args => callsEs args
  | _ => []
def callsEs : List (Expr EVM.Op) → List String
  | [] => []
  | e :: es => callsE e ++ callsEs es
end
def tokCalls (blk : Block EVM.Op) : List (String × Nat) :=
  let toks := yulTokens (EVM.print blk)
  let names := (funSigs parsedMain).map (·.1)
  names.filterMap fun n =>
    -- occurrences of `n (` that are not preceded by `function`
    let rec go (prev : String) : List String → Nat
      | a :: b :: rest => (if a == n && b == "(" && prev != "function" then 1 else 0) + go a (b :: rest)
      | _ => 0
    let c := go "" toks
    if c == 0 then none else some (n, c)
#eval Midfall.Lowering.partials.map (fun q => (repr q, tokCalls (emitPartialV3 poseidonPv poseidonM q)))
#eval ("helpers", tokCalls (GenAst.emitHelpers poseidonPv))
#eval ("accHelpers", tokCalls (accHelpersP poseidonM))
-- 12. the function definitions that sit INSIDE a slice (fact 8)
#eval Midfall.Lowering.partials.map (fun q => (repr q, (funSigs (emitPartialV3 poseidonPv poseidonM q)).map (·.1)))
-- 13. closedness and no-writers of the complete inlined program
def progV3 : Block EVM.Op :=
  Inline.inlineContractConstants (constTableOf poseidonM)
    (abiGuardBlock poseidonM ++ wrapperLocals poseidonM 0 0 ++ mainAsmRawV3 poseidonPv poseidonM)
#eval (freeNames (Inline.inlineContractConstants (constTableOf poseidonM) (mainAsmRawV3 poseidonPv poseidonM)),
       Midfall.Yul.Bridge.noWritersFuel 20000 progV3)
-- 14. ONE-LITERAL MUTATION FALSIFIERS for the new regions: flip one number in each region's text
def mutateFirst (needle repl : String) (s : String) : String :=
  match s.splitOn needle with
  | a :: b :: rest => a ++ repl ++ String.intercalate needle (b :: rest)
  | _ => s
def agreesWith (accText qhText qnbText : String) : Bool :=
  let acc := (parseLines [accText]).getD []
  let qh := (parseLines [qhText]).getD []
  let qnb := (parseLines [qnbText]).getD []
  let main := mainGuardBlock ++ GenAst.emitHelpers poseidonPv ++ acc ++ mainLocals ++
    (Midfall.Lowering.partials.foldl (init := []) fun a q => a ++
      (match q with
       | .quotientLin => qh ++ qnb ++ GenAst.emitQuotientLin poseidonPv
       | .pcs => emitPcsScoped poseidonPv
       | q => GenAst.emitPartial poseidonPv q))
  SyntaxEq.stmtsBeq main parsedMain
def accT : String := renderAccumulatorHelpers b
def qhT : String := renderQuotientHelpers b
def qnbT : String := renderQuotientNumeratorBlock b
#eval agreesWith accT qhT qnbT                                             -- expect true
#eval agreesWith (mutateFirst "0x20" "0x21" accT) qhT qnbT                 -- expect false
#eval agreesWith accT (mutateFirst "0x3cc81b89" "0x3cc81b8a" qhT) qnbT     -- TRUE: first hit is inside a COMMENT (not observable)
#eval agreesWith accT (mutateFirst "shl(224, 0x3cc81b89)" "shl(224, 0x3cc81b8a)" qhT) qnbT  -- expect false
#eval agreesWith accT (mutateFirst "mulmod(x2, x2, q_r)" "mulmod(x2, x, q_r)" qhT) qnbT     -- expect false (q_pow5 body)
#eval agreesWith accT qhT (mutateFirst "0x20" "0x21" qnbT)                 -- expect false
#eval (accT != mutateFirst "0x20" "0x21" accT, qhT != mutateFirst "0x3cc81b89" "0x3cc81b8a" qhT,
       qnbT != mutateFirst "0x20" "0x21" qnbT)                             -- the mutations are real
