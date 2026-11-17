-- |
-- Midfall.Lowering.YulParse
--
-- OBJ.1 (PLAN-V3 V3 row 31, the M2 entry). A TOTAL parser from the `yulTokens` stream of generator
-- text to the vendored AST, usable in statements and by `native_decide`.
--
-- WHAT THIS FILE IS FOR. Every emitter in `Midfall/Lowering/GenAst*.lean` builds the vendored AST
-- directly, and the text port in `Midfall/Generator/*` prints the tokens the generator writes. The
-- two sides have only ever been compared by `yulTokens` - a relation that is strictly weaker than
-- structural equality (YulGolden.lean says so in its own header). Nothing in the tree could turn a
-- token stream back into an `AST`, so no statement could say "the parse of the emitted text is the
-- emitted AST". This file is that function: `parseTokens` reads a token stream produced by
-- `Midfall.Generator.yulTokens` and returns the vendored `Block EVM.Op`, resolving a call name to a
-- built-in or a user function with the vendored `EVM.mkCall` - the rule the `yul%` DSL uses, and
-- solc's rule: a name that is a built-in is the built-in. It answers `none` on any token it does not
-- understand: there is no partial result, no error recovery, and no silent drop of a suffix.
--
-- TOTALITY. The parser is structured over a fuel `Nat`, not over the token list: `parseStmts` and
-- `parseArgs` consume a variable number of tokens per step, so the list is not a decreasing argument
-- and `termination_by` would not close it. The fuel IS decreasing, and `parseTokens` supplies
-- `toks.length + 1` - one unit of fuel per token, which is an upper bound on what any well-formed
-- stream of that length can cost. So the file compiles with no `partial`, no `unsafe` and no
-- `decreasing_by`, and it is usable under `native_decide` from `Midfall/Instances/`. The cost of
-- that shape is that a stream longer than its own fuel budget reads as `none` rather than as a
-- success; `parseTokens` sizes the budget from the input, so the only way to hit it is a stream that
-- does not parse anyway.
--
-- PORTANCE. `docs/plans/V3-evidence/lean/object/Parse1.lean`, lines 16-158, verbatim; only the
-- header and the imports were adapted. The measurement harness of that scratch file is NOT ported
-- here: the gates live in `Midfall/Instances/YulParseKats.lean`.
--
import YulSemantics.Syntax
import Midfall.Generator.YulGolden

set_option autoImplicit false

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
