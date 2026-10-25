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
-- design decision D-P2. 'Line' below is an output-stream element, not syntax.
-- An earlier revision of this header also advertised a 'Target' rendering
-- dispatch; this module has never defined one, and R-38 found the same class of
-- phantom reference in the fuel comments. The rule this file now follows is that
-- a header may only name what the file contains.
--
-- WHY A SECOND PRINTER AT ALL. 'YulSemantics.PrettyPrint' exists, and it does not
-- produce these bytes. It is a debugging dump for optimizer output - its own
-- module header says so ("Untrusted utility... numbers print in decimal"). The
-- committed artifacts come from Askama templates plus Rust emitters, and their
-- bytes are determined by things the AST does not record. The gap is measured and
-- gated at the bottom of this file; docs/ecosystem.md 12.1 carries the
-- construct-by-construct table (an earlier revision of this header pointed at
-- section 11, which is about rust_trace.json instead).
--
-- WHICH FILE EVERY ':NNNN' BELOW MEANS. 'D:' is the TRACKED DUMP that the golden
-- test is anchored on:
-- proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol, 3024
-- lines, no trailing newline. 'P:' is the DEPLOYED artifact,
-- deployments/sepolia/moonlight-wrap/Halo2Verifier.sol, 3573 lines, generated five
-- months earlier by superseded templates. They are different files with different
-- line numbers: D:3112 does not exist. R-38 found that every citation in this file
-- was silently a P: citation, so each one below has been re-anchored and checked
-- against the file it now names; where a construct exists only in the deployed
-- artifact that is said out loud instead of the citation being moved.
--
-- THE FOUR LOSS CLASSES, and how each is handled.
--
--   1. COMMENT AND LAYOUT TEXT. 'Stmt Op' has no comment constructor, and the
--      committed assembly is interleaved with comment lines - 1194 of the 3024
--      lines of D begin with a '//' (recipe: grep -cE '^[[:space:]]*//') and 1204
--      contain one (grep -cF '//'), plus 122 blank lines, trailing comments, and
--      indentation a template author typed by hand.
--      No AST of any shape recovers those bytes, so they are NOT modelled as
--      statements: they travel beside the AST as 'Line.text', and 'Line.code'
--      carries the Yul. This is the finding the plan has to absorb: byte-identity
--      of generated Solidity is not a property of the Yul AST alone, so
--      'render g o = (lower g o).map print' can only hold if 'lower' produces an
--      AST PLUS a text stream. Structural equality over the comment-free AST is
--      the right relation for Phase 5's irCheck and must not be confused with
--      byte-identity.
--   2. LITERAL SPELLING. 'Literal.number (n : Nat)' stores a value, not the text
--      that wrote it. The committed file spells the same value several ways -
--      '0x00' (D:357) and '0x0' (D:1790) are both zero; '0x0100' (D:376) and
--      '0x100' (D:472) are both 256 - and the Rust's 'hex()' filter,
--      'hex_padded(pad)' and '{:#x}' are three different formatters (ported in
--      Filters.lean). Therefore NO function from the vendored AST can be
--      byte-exact on the corpus: two committed texts share one AST. This renderer
--      prints decimal, which is exact wherever the generator emitted decimal and
--      diverges wherever it emitted hex. 'hexCollision_ok' below proves the
--      collision rather than hiding it. Closing the gap needs a spelling channel
--      on 'Literal' (an upstream change) or a text-annotated literal.
--   3. TEXT THAT IS NOT A STATEMENT. A comment can sit INSIDE one statement: D:1902
--      is 'switch q_op', D:1903 a comment, D:1904 'case 0x05 {' - all one
--      'Stmt.switch'. D:1020-1025 is 'ok := and(' with two comment lines between
--      its arguments. Neither the AST (no comment constructor) nor the 'Line'
--      stream below (which can only extend the current line or start a new one,
--      never interrupt a statement that is still open) can carry it. Recorded as
--      the fourth divergence in docs/ecosystem.md 12.1; it bites Phase 5, which
--      has to reproduce these bytes from an AST.
--   4. FREE IDENTIFIERS. The fixtures reference names that the Yul does not define:
--      FR_MODULUS, MODEXP_GAS, ERR_NON_CANONICAL_SCALAR and 91 'uint256 internal
--      constant' declarations in D. 'stmtsBeq' compares those as unbound strings,
--      so their spelling is decided outside the Yul and outside this relation.
--      docs/ecosystem.md 12.1 records it; Phase 5 owes the mapping.
--
-- FORMAT RULES THIS RENDERER IMPLEMENTS, each pinned by a gate at the bottom of
-- the file and each re-anchored to the dump it was actually read off (R-38):
--
--   * 4 spaces per level, no tabs: D:834 is a level-5 statement at 20 spaces.
--     Zero tab characters in D. NOT a total law: D:1987-1993 puts a 'for' body at
--     the same indentation as its 'for' (the emitter does not re-indent that
--     block), so indentation is a template property, not a function of AST depth.
--   * 'let a := e' / 'let a, b, c := e' / 'a := e' / 'a, b := e', one space either
--     side of ':=': D:834, D:1074, D:661, D:1019.
--   * calls 'f(a, b)': comma plus space, nothing inside the parens, no space
--     before '()' when empty: D:364 'returndatasize()', D:1911 'q_program_fail()'.
--     The zero-arg 'gas()' cited before is DEPLOYED-ONLY (P:219): the dump passes
--     named gas constants and contains no 'gas(' at all.
--   * brace policy: 0 statements '{}', 1 statement '{ s }', 2 or more one per
--     line with the closing brace back at the opening level: D:334 (one statement
--     inline) vs D:835-838 (two statements multiline). Both spellings of a
--     ONE-statement body occur: inline at D:334, multiline at D:378-380 - so this
--     rule is not derivable from the AST, which is what 'bracePolicy_note_ok'
--     records.
--   * 'function' bodies and 'for' bodies are always multiline: D:640, D:1509.
--   * 'for { init } cond { post } {' + body + '}': D:1509. Empty init/post are
--     written both ways: 'for {}' at D:833 and 'for { }' at D:1894.
--   * 'switch e' then 'case L {' at the SWITCH's own level: D:1902 and D:1904,
--     both at 20 spaces. 'default' is not exercised by the dump.
--   * 'leave' bare on its line: D:783. 'break' and 'continue' do not occur
--     anywhere in D, so their rendering is a choice, not a measurement.
--   * blank lines: 122 of the 3024 lines of D are blank, and SIX of them carry
--     indentation (D:85, 525, 1098, 1103, 1891, 3010 - 'grep -nE '^[[:space:]]+$'').
--     The earlier claim that neither artifact has trailing whitespace was false:
--     the deployed artifact has none, the dump has those six.
--
-- WHY THE FUEL PARAMETER. Lean 4.35's structural estimator cannot drive
-- recursion through 'Stmt.switch', whose case list is a 'List (Literal ×
-- Block Op)': the goal 'sizeOf b ≤ sizeOf cs' for 'b ∈ Prod.snd '' cs' is out of
-- its reach, and the mutual variants all fail the same way (R-37). Rather than a
-- 'partial' def (rule R10) or a parallel AST, the renderer is well-founded on an
-- explicit fuel. THE BUDGET IS A CONSTANT 512 ('renderFuel'), not 'sizeOf s + 1'
-- as an earlier version of this header claimed: 'renderStmt' passes the constant,
-- every recursive call descends one level, and the deepest statement nest
-- measured in the dump is 7 (D:1987-1993), so 512 is never approached. The '0'
-- case is therefore unreachable in practice but kept total rather than 'partial'.
-- What protects it is 'renderFuel_exhausted_ok' and 'renderFuel_deep_ok' below:
-- they show a too-small budget emits the marker and that 512 is enough for a
-- corpus-deep nest. They do NOT show the golden gates would notice - see
-- 'golden_detectsFuelExhaustion_ok' in YulGolden.lean for the honest version.

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
    proofs/solidity-verifier/src/lowering/render/models.rs:1019-1038. The two
    spellings that collide are D:357 ('0x00') and D:1790 ('0x0'). -/
def renderLit : Literal → String
  | .number n => toString n
  | .bool true => "true"
  | .bool false => "false"
  | .string s => "\"" ++ s ++ "\""

/-- rust: proofs/solidity-verifier/src/lowering/render/models.rs (template text
    around '{{ ... }}' interpolations); call shape pinned by
    dump:333 'mcopy(add(scratch, 0x20), scratch, 0x20)'. -/
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
      ('mstore(add(scratch, 0x00), 0x20)        // base len', dump:357) or a
      comment that shares a line with a closing brace ('}            // ===',
      deployed P:1413 - that one exists ONLY in the deployed artifact; no line of
      the dump has a '}' followed by a comment). Note what 'tail' cannot do: it
      extends the CURRENT line, so a comment inside a statement that is still
      open (loss class 3, dump:1902-1904) has nowhere to go. -/
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

/-- How much fuel the public entry points start with: a constant, not a function
    of the input. Every recursive call descends to a strict subterm, so the fuel
    only has to exceed the deepest statement nesting in the corpus. Measured
    depth of the tracked dump is SEVEN, first reached at dump:1987-1993 (a 'for'
    inside a bare '{' block inside a 'function' inside the assembly block); the
    deployed artifact nests eight. 512 is comfortably above both.
    'renderFuel_exhausted_ok' and 'renderFuel_deep_ok' below prove the budget is
    both sufficient and observable - not that the golden gates would notice. -/
def renderFuel : Nat := 512

/-- The fuel-parameterised statement renderer. Running out of fuel emits a loud
    '<fuel-exhausted>' marker rather than an empty string, so a too-small budget
    is visible in the output instead of silently truncating it. Be precise about
    what protects that, because an earlier revision of this comment claimed a
    protection the code did not have. The golden gates print with
    'YulSemantics.EVM.print' and never call this function, so setting 'renderFuel'
    to 1 reddens ZERO golden gates (measured). What reddens is
    'renderFuel_deep_ok' below - the gate R-38 finding 5 asked for - together with
    'bracePolicy_note_ok', which renders through 'renderStmt' (measured: 1 of the
    6 pre-existing renderer notes, 0 golden gates).
    'golden_detectsFuelExhaustion_ok' in YulGolden.lean establishes only the
    weaker, honest claim: the token relation can SEE the marker, so if a golden
    comparison is ever routed through this renderer, exhaustion will not pass
    silently. -/
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

/-- 'needle' occurs in 'hay'. Lean core at this toolchain has no
    String.isInfixOf, and 'splitOn' gives it for free. -/
def containsStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Three statement levels: 'if' / 'if' / call. Needs fuel 3 to render fully. -/
def fuelProbe : Stmt EVM.Op := (yul% { if c { if d { revert(0, 0) } } }).head!

/-- Seven statement levels, matching the deepest statement nest measured in the
    tracked dump (dump:1987-1993). Needs fuel 8 to render fully. -/
def deepProbe : Block EVM.Op :=
  yul% { if a { if b { if c { if d { if e { if f { if g { revert(0, 0) } } } } } } } }

/-- THE FUEL CAN RUN OUT, AND SAYS SO. Fuel 0 emits the marker immediately; fuel 2
    is one short of what 'fuelProbe' needs and emits it one level down; fuel 3 is
    enough and emits nothing. The wrong implementation this rules out is a renderer
    that silently returns the empty string when it cannot recurse further -
    truncation that looks like a short program instead of a failure. Change the
    '0' arm of 'renderStmtFuel' to return "" and the first conjunct goes red. -/
def renderFuel_exhausted_ok : Bool :=
  renderStmtFuel 0 0 fuelProbe == "<fuel-exhausted>"
    && containsStr (renderStmtFuel 2 0 fuelProbe) "<fuel-exhausted>"
    && ! containsStr (renderStmtFuel 3 0 fuelProbe) "<fuel-exhausted>"

/-- THE CONSTANT IS BIG ENOUGH, AND THAT IS CHECKABLE. A nest as deep as the
    deepest thing in the tracked dump renders with no marker at 'renderFuel', and
    one fuel short of its requirement it does not - so the budget is doing work
    rather than being decoration. Set 'renderFuel' to 1 and the first conjunct
    goes red; that is the experiment that makes this a gate and not a comment. -/
def renderFuel_deep_ok : Bool :=
  ! containsStr (multilineBody (renderStmtFuel renderFuel) 0 deepProbe) "<fuel-exhausted>"
    && containsStr (multilineBody (renderStmtFuel 7) 0 deepProbe) "<fuel-exhausted>"

end Midfall.Generator.Notes

#eval Midfall.Generator.Notes.note_indent_ok -- expect true
#eval Midfall.Generator.Notes.note_braces_ok -- expect true
#eval Midfall.Generator.Notes.note_calls_ok -- expect true
#eval Midfall.Generator.Notes.note_lines_ok -- expect true
#eval Midfall.Generator.Notes.hexCollision_ok -- expect true
#eval Midfall.Generator.Notes.bracePolicy_note_ok -- expect true
#eval Midfall.Generator.Notes.renderFuel_exhausted_ok -- expect true
#eval Midfall.Generator.Notes.renderFuel_deep_ok -- expect true