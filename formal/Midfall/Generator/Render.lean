-- |
-- Midfall.Generator.Render
--
-- STATUS UNDER D-P13 (docs/design.md, docs/ecosystem.md 12.3): the generator's
-- identity criterion is STRUCTURAL on the vendored AST, and neither formatting nor
-- comments are part of it. The golden test therefore lives in
-- Midfall/Generator/YulGolden.lean, not here. This module stays because a canonical
-- renderer is still needed - solc takes text, and Midfall.Lowering.Lowered holds
-- blocks that must eventually become a compilable file - but the byte gates at the
-- bottom of this file are RENDERER NOTES: they pin what this renderer emits, so a
-- formatting change is a deliberate edit rather than drift. They are not the
-- correctness obligation. The divergence gates among them document formatting the
-- vendored AST cannot record (hex spelling, brace style, spread calls): irrelevant
-- to correctness under D-P13, kept visible on purpose.
--
-- A renderer for the Rust generator's output, written OVER THE
-- VENDORED YulSemantics AST ('Expr EVM.Op', 'Stmt EVM.Op', 'Block EVM.Op',
-- 'Object EVM.Op' from vendor/yul-semantics). This module defines NO Yul node
-- types of its own: the dialect has exactly one AST in this repository, per plan
-- Section 7 ('ImportSolcIR imports solc IR into the yul-semantics AST') and
-- design decision D-P2. 'Line' below is an output-stream element and 'Target' a
-- rendering dispatch, not syntax.
--
-- WHY A SECOND PRINTER AT ALL. 'YulSemantics.PrettyPrint' exists, and it does not
-- produce these bytes. It is a debugging dump for optimizer output - its own
-- module header says so ("Untrusted utility... numbers print in decimal"). The
-- committed artifacts come from Askama templates plus Rust emitters, and their
-- bytes are determined by things the AST does not record. The gap is measured and
-- gated at the bottom of this file; docs/ecosystem.md section 11 carries the
-- construct-by-construct table.
--
-- THE TWO LOSS CLASSES, and how each is handled.
--
--   1. COMMENT AND LAYOUT TEXT. 'Stmt Op' has no comment constructor, and the
--      committed assembly is interleaved with comment lines (971 of them in
--      Halo2Verifier.sol), blank lines, trailing comments, and indentation a
--      template author typed by hand. No AST of any shape recovers those bytes,
--      so they are NOT modelled as statements: they travel beside the AST as
--      'Line.text', and 'Line.code' carries the Yul. This is the finding the plan
--      has to absorb: byte-identity of generated Solidity is not a property of
--      the Yul AST alone, so 'render g o = (lower g o).map print' can only hold
--      if 'lower' produces an AST PLUS a text stream. Alpha-equivalence over the
--      comment-free AST is the right relation for Phase 5's irCheck and must not
--      be confused with byte-identity.
--   2. LITERAL SPELLING. 'Literal.number (n : Nat)' stores a value, not the text
--      that wrote it. The committed file spells the same value several ways -
--      '0x00' (Halo2Verifier.sol:329) and '0x0' (:1584) are both zero; '0x0100'
--      (:219) and '0x100' (:540) are both 256 - and the Rust's 'hex()' filter,
--      'hex_padded(pad)' and '{:#x}' are three different formatters (ported in
--      Filters.lean). Therefore NO function from the vendored AST can be
--      byte-exact on the corpus: two committed texts share one AST. This renderer
--      prints decimal, which is exact wherever the generator emitted decimal and
--      diverges wherever it emitted hex. 'hexCollision_ok' below proves the
--      collision rather than hiding it. Closing the gap needs a spelling channel
--      on 'Literal' (an upstream change) or a text-annotated literal.
--
-- FORMAT RULES THIS RENDERER IMPLEMENTS, each pinned to committed bytes by a gate
-- at the bottom of the file:
--
--   * 4 spaces per level, no tabs (Halo2Verifier.sol:3112, level 5).
--   * 'let a := e' / 'let a, b := e' / 'a := e' / 'a, b := e', one space either
--     side of ':=' (:3112, :3116, :673).
--   * calls 'f(a, b)': comma plus space, nothing inside the parens, no space
--     before '()' when empty (:219 'gas()').
--   * brace policy: 0 statements '{}', 1 statement '{ s }', 2 or more one per
--     line with the closing brace back at the opening level (:2016 vs :448-451).
--     'function' bodies and 'for' bodies are always multiline (:322, :1320).
--   * 'for { init } cond { post } {' + body + '}' (:1320).
--   * 'switch e' then 'case L {' / 'default {' at the SWITCH's own level (:2245).
--   * 'leave' / 'break' / 'continue' bare on their line (:495).
--   * blank lines are empty, not indented (no trailing whitespace anywhere in
--     either artifact).
--
-- WHY THE FUEL PARAMETER. Lean 4.35's structural estimator cannot drive
-- recursion through 'Stmt.switch', whose case list is a 'List (Literal ×
-- Block Op)': the goal 'sizeOf b ≤ sizeOf cs' for 'b ∈ Prod.snd '' cs' is out of
-- its reach, and the mutual variants all fail the same way. Rather than a
-- 'partial' def (rule R10) or a parallel AST, the renderer is well-founded on an
-- explicit fuel that the public entry point sets to 'sizeOf s + 1'. Every
-- recursive call goes to a strict subterm, whose 'sizeOf' is smaller, so the fuel
-- is never exhausted and the '0' case is unreachable; it is kept total rather than
-- 'partial'.

import YulSemantics.Syntax
import YulSemantics.PrettyPrint

namespace Midfall.Generator
open YulSemantics

/-- LF. The artifacts contain no CR. -/
def nl : String := "\n"

/-- Spaces per indentation level: 4, matching the corpus and 'YulSemantics.pad'. -/
def indentWidth : Nat := 4

/-- Leading whitespace of level 'lvl'. -/
def indentAt (lvl : Nat) : String := "".pushn ' ' (indentWidth * lvl)

/-- A literal, in the only spelling the vendored AST can express: decimal. See
    loss class 2. rust: the absence of a spelling field at
    vendor/yul-semantics/YulSemantics/Ast.lean:38-42, against
    proofs/solidity-verifier/src/lowering/render/models.rs:1019-1038. -/
def renderLit : Literal → String
  | .number n => toString n
  | .bool true => "true"
  | .bool false => "false"
  | .string s => "\"" ++ s ++ "\""

/-- rust: proofs/solidity-verifier/src/lowering/render/models.rs (template text
    around '{{ ... }}' interpolations); call shape pinned by
    Halo2Verifier.sol:207 'mcopy(add(scratch, 0x20), scratch, 0x20)'. -/
def renderExpr : Expr EVM.Op → String
  | .lit l => renderLit l
  | .var x => x
  | .builtin op args =>
    EVM.opName op ++ "(" ++ String.intercalate ", " (args.map renderExpr) ++ ")"
  | .call fn args =>
    fn ++ "(" ++ String.intercalate ", " (args.map renderExpr) ++ ")"

/-- One line of rendered output. 'code' is Yul from the vendored AST, placed at a
    level; 'text' is a template literal line carried verbatim - comments, blank
    lines, trailing-comment continuations, ragged indentation. See loss class 1. -/
inductive Line where
  | code (lvl : Nat) (s : Stmt EVM.Op)
  | text (raw : String)
  /-- Template text appended to the PREVIOUS line: a trailing comment
      ('mstore(..)        // base len', Halo2Verifier.sol:329) or a comment that
      shares a line with a closing brace ('}            // ===', :1413). -/
  | tail (raw : String)

/-- '{' then one statement per line at 'lvl + 1' then '}' at 'lvl'. Non-recursive:
    the statement renderer is passed in as 'one', which is what keeps the fuel
    recursion inside a single definition. -/
def multilineBody (one : Nat → Stmt EVM.Op → String) (lvl : Nat) (b : Block EVM.Op) : String :=
  "{" ++ nl ++ String.intercalate nl (b.map fun s => indentAt (lvl + 1) ++ one (lvl + 1) s)
    ++ nl ++ indentAt lvl ++ "}"

/-- The brace policy: 0 statements '{}', 1 statement '{ s }' unless the site is
    one the corpus always writes multiline, 2 or more one per line. -/
def bracesAt (one : Nat → Stmt EVM.Op → String) (alwaysMultiline : Bool) (lvl : Nat)
    (b : Block EVM.Op) : String :=
  match b with
  | [] => "{}"
  | [s] => if alwaysMultiline then multilineBody one lvl b else "{ " ++ one lvl s ++ " }"
  | _ => multilineBody one lvl b

/-- How much fuel the public entry points start with. Every recursive call
    descends to a strict subterm, so the fuel only has to exceed the deepest
    nesting in the corpus; the committed verifier nests six levels at most
    (Halo2Verifier.sol:1868-1874), and 'renderFuel_exhausted_ok' below proves the
    budget is not being consumed silently. -/
def renderFuel : Nat := 512

/-- The fuel-parameterised statement renderer. Running out of fuel emits a loud
    marker rather than an empty string, so a too-small 'renderFuel' turns the
    golden gates red instead of truncating output. -/
def renderStmtFuel : Nat → Nat → Stmt EVM.Op → String
  | 0, _, _ => "<fuel-exhausted>"
  | fuel + 1, lvl, s => match s with
    | .exprStmt e => renderExpr e
    | .leave => "leave"
    | .«break» => "break"
    | .«continue» => "continue"
    | .letDecl vars none => "let " ++ String.intercalate ", " vars
    | .letDecl vars (some e) =>
      "let " ++ String.intercalate ", " vars ++ " := " ++ renderExpr e
    | .assign vars e => String.intercalate ", " vars ++ " := " ++ renderExpr e
    | .block b => bracesAt (renderStmtFuel fuel) true lvl b
    | .cond c b => "if " ++ renderExpr c ++ " " ++ bracesAt (renderStmtFuel fuel) false lvl b
    | .funDef n ps rs b =>
      "function " ++ n ++ "(" ++ String.intercalate ", " ps ++ ")"
        ++ (if rs.isEmpty then "" else " -> " ++ String.intercalate ", " rs)
        ++ " " ++ multilineBody (renderStmtFuel fuel) lvl b
    | .forLoop init c post b =>
      "for " ++ bracesAt (renderStmtFuel fuel) false lvl init ++ " " ++ renderExpr c ++ " "
        ++ bracesAt (renderStmtFuel fuel) false lvl post ++ " "
        ++ multilineBody (renderStmtFuel fuel) lvl b
    | .switch c cs dflt =>
      "switch " ++ renderExpr c
        ++ String.intercalate nl (cs.map fun cb =>
          nl ++ indentAt lvl ++ "case " ++ renderLit cb.fst ++ " "
            ++ bracesAt (renderStmtFuel fuel) false lvl cb.snd)
        ++ match dflt with
          | none => ""
          | some d => nl ++ indentAt lvl ++ "default " ++ bracesAt (renderStmtFuel fuel) false lvl d

/-- A vendored statement at level 'lvl', WITH its leading indent. -/
def renderStmt (lvl : Nat) (s : Stmt EVM.Op) : String :=
  indentAt lvl ++ renderStmtFuel renderFuel lvl s

/-- A block placed at level 'lvl', braces excluded - what a template partial
    produces: the body of an assembly block. -/
def renderBlock (lvl : Nat) (b : Block EVM.Op) : String :=
  String.intercalate nl (b.map fun s => renderStmt lvl s)

/-- A block's braces at level 'lvl'. -/
def renderBlockBraces (lvl : Nat) (b : Block EVM.Op) : String :=
  bracesAt (fun l s => renderStmtFuel renderFuel l s) false lvl b

/-- One output line: 'code' takes the printer's indent, 'text' is verbatim, and
    'tail' is appended to the previous line rather than starting one. -/
def renderLine : Line → String
  | .code lvl s => renderStmt lvl s
  | .text raw => raw
  | .tail raw => raw

/-- Accumulate the stream: 'text' and 'code' start a new line, 'tail' extends the
    current one with no separator at all - that is what a trailing comment is. -/
def renderLinesFrom (acc : String) : List Line → String
  | [] => acc
  | .tail raw :: rest => renderLinesFrom (acc ++ raw) rest
  | l :: rest => renderLinesFrom (acc ++ nl ++ renderLine l) rest

/-- The output stream, one line per element, no trailing newline. -/
def renderLines : List Line → String
  | [] => ""
  | x :: xs => renderLinesFrom (renderLine x) xs

/-- A Yul object: 'object "N" { code { ... } object "S" { ... } data "d" "..." }'.
    As in the vendored printer, the generator's real objects are Solidity
    contracts, so the contract shell is template text; this is the Yul-object
    rendering of the same tree. -/
def renderObject : Nat → Object EVM.Op → String
  | lvl, .mk name code subs segs =>
    indentAt lvl ++ "object \"" ++ name ++ "\" {" ++ nl
      ++ indentAt (lvl + 1) ++ "code {" ++ nl
      ++ String.intercalate nl (code.map fun s => indentAt (lvl + 2) ++ renderStmt (lvl + 2) s)
      ++ nl ++ indentAt (lvl + 1) ++ "}"
      ++ String.intercalate "" (subs.map fun o =>
        nl ++ indentAt (lvl + 1) ++ renderObject (lvl + 1) o)
      ++ String.intercalate "" (segs.map fun seg =>
        nl ++ indentAt (lvl + 1) ++ "data \"" ++ seg.fst ++ "\" " ++ ppData seg.snd)
      ++ nl ++ indentAt lvl ++ "}"

/-! # Renderer notes

These are NOT the golden test. Under D-P13 the obligation is structural and lives
in Midfall/Generator/YulGolden.lean, anchored on output from the CURRENT
generator. What follows pins what this renderer emits for small inputs, so that a
formatting change here is a deliberate edit rather than silent drift - a drift
detector whose expected side is this renderer's own definition, labelled as such
precisely because docs/REVIEW.md R-20/R-30/R-34 is what happens when that kind of
check is mistaken for evidence.

The corpus slices that used to live here were transcribed from
deployments/sepolia/moonlight-wrap/, which is the DEPLOYED artifact but was
generated on 2026-05-19 (4bab29c) by templates superseded five months later: no
typed-error taxonomy, '^0.8.24' instead of the pinned 0.8.30, and a "q_acc"
quotient-direct emitter that no longer exists anywhere in src. Pinning a renderer
to those bytes would certify the wrong generator, so they are dropped rather than
kept green. The two structural facts they established are restated below without
the stale anchor. -/

namespace Midfall.Generator.Notes
open Midfall.Generator YulSemantics

/-- Four spaces per level, one statement per line. -/
def note_indent_ok : Bool :=
  renderBlock 3 (yul% { let a := 1 }) == "            let a := 1"

/-- The brace policy: one statement inline, two multiline with the closing brace
    back at the opening level. -/
def note_braces_ok : Bool :=
  renderBlockBraces 2 (yul% { revert(0, 0) }) == "{ revert(0, 0) }"
    && renderBlockBraces 2 (yul% { revert(0, 0) mstore(0, 1) })
      == "{\n            revert(0, 0)\n            mstore(0, 1)\n        }"

/-- Calls: comma plus space, nothing inside the parens, zero-arg calls bare. -/
def note_calls_ok : Bool :=
  renderExpr (yulE% mulmod(add(a, 1), mload(b), r)) == "mulmod(add(a, 1), mload(b), r)"
    && renderExpr (yulE% gas()) == "gas()"

/-- The text channel: a comment line is verbatim, a tail extends the previous line
    with no separator, and a blank line stays empty rather than taking the indent.
    'renderBlockBraces' and 'renderStmt' deliberately do NOT add the leading indent -
    the caller places the target. -/
def note_lines_ok : Bool :=
  renderLines [Line.text "  // hi",
               Line.code 2 (yul% { let a := 1 }).head!,
               Line.tail "  // tail",
               Line.text ""] == "  // hi\n        let a := 1  // tail\n"

/-- STRUCTURAL FACT 1, restated without a stale anchor: the vendored AST cannot
    record a literal's spelling, so two committed spellings of one value collapse.
    This is why byte-identity was never achievable over the AST alone. -/
def hexCollision_ok : Bool :=
  SyntaxEq.exprBeq (yulE% add(p, 0x00)) (yulE% add(p, 0x0))
    && renderExpr (yulE% add(p, 0x00)) == "add(p, 0)"

/-- STRUCTURAL FACT 2: the AST cannot record which brace spelling a template
    used, so a one-statement body is always rendered inline here even though the
    corpus writes it both ways. -/
def bracePolicy_note_ok : Bool :=
  renderStmt 2 (yul% { if c { revert(0, 0) } }).head! == "        if c { revert(0, 0) }"

end Midfall.Generator.Notes

#eval Midfall.Generator.Notes.note_indent_ok -- expect true
#eval Midfall.Generator.Notes.note_braces_ok -- expect true
#eval Midfall.Generator.Notes.note_calls_ok -- expect true
#eval Midfall.Generator.Notes.note_lines_ok -- expect true
#eval Midfall.Generator.Notes.hexCollision_ok -- expect true
#eval Midfall.Generator.Notes.bracePolicy_note_ok -- expect true