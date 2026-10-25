-- |
-- Midfall.Generator.Templates
--
-- The template layer: which Askama templates exist, what fixed text they carry,
-- and the one template this package can render end to end. Together with
-- Midfall/Generator/Models.lean (the records) and Midfall/Generator/Render.lean
-- (the printer) this is the port of
-- proofs/solidity-verifier/src/lowering/render/mod.rs, whose whole content is
-- `pub(crate) mod models; pub(crate) mod yul; pub(crate) use models::*;` -
-- the re-export surface is what this module provides, since `yul.rs` is a
-- five-line reserved placeholder that defines nothing (recorded, not invented
-- around).
--
-- CITATION NOTATION, same as Models.lean: M: is
-- src/lowering/render/models.rs, MR: is src/lowering/render/mod.rs, T: is
-- proofs/solidity-verifier/templates/, D: is the tracked dump
-- target/poseidon-fixture-dump/Halo2Verifier.sol (3024 lines) and DVK: is
-- target/poseidon-fixture-dump/Halo2VerifyingKey.sol (271 lines). No cite here
-- points at deployments/sepolia/moonlight-wrap/ - R-36 shows that artifact is
-- five months stale.
--
-- WHY THERE IS NO WALL OF TEMPLATE TEXT IN THIS FILE. The templates are 4324
-- lines of Askama. Copying them into Lean string literals would be a
-- transcription with nothing checking it, which is exactly R-38 finding 1: a
-- golden gate that compares a pasted string against a pasted string cannot fail
-- when the artifact changes. The only drift protection in this tree for
-- committed bytes is scripts/check_golden_provenance.py, and it checks the nine
-- pinned slices in YulGolden.lean. So the discipline here is: port as DATA only
-- what can be checked against something this file does not control, and let the
-- rest arrive with the renderers that consume it (plan Section 8: one Lean fn
-- per template/partial producing a `Yul.Block`, packages 3-4).
--
-- What that leaves, and what checks it:
--
--   * The template paths, the include graph, and the include ORDER of every
--     partial in both registries. Two channels pin that order and neither is a
--     paste: scripts/check_golden_provenance.py re-reads the include lines of
--     the two contract templates and requires `verifierIncludes` and
--     `evaluatorIncludes` to be exactly those paths, in that order, at the line
--     numbers the two doc comments state; and, separately, the five
--     provenance-pinned fixture slices must start in the dump in the same
--     relative order as the partials that own them, which is what
--     `includeOrder_matchesFixtureAnchors_ok` checks. The second channel sees
--     five of the thirteen verifier partials and none of the evaluator side;
--     the first sees all fifteen. R-40 F7 was this bullet claiming more than
--     the gate alone covers. Measured: swapping two unanchored entries of
--     `verifierIncludes`, or the two of `evaluatorIncludes`, reddens the script
--     and not the gate.
--   * The fixed literals the templates contribute (typed-error selectors,
--     FR_MODULUS, the BLS_P words). Each is checked against a computation -
--     keccak of the error name via `Midfall.abiSelector`, or the base-field
--     modulus from Midfall/Yul/Externals.lean - so a mistyped nibble reddens a
--     gate.
--   * The verifying-key constructor template, rendered as a vendored AST plus a
--     `Line` stream, and compared to the pinned DVK:62-72 fixture under
--     `stmtsBeq` (authoritative, D-P13) and under the token relation
--     (secondary). That is the first place in the tree where a model is rendered
--     and the result is checked against committed bytes.
--
-- The pragma line and the NatSpec blocks are ported as text but NOT gated: the
-- only thing that could check them is the artifact, and no pinned slice covers
-- them. That is said out loud rather than papered over with a gate that compares
-- the string to itself.

import YulSemantics.Syntax
import YulSemantics.PrettyPrint
import Midfall.Common.Bytes
import Midfall.Common.Keccak
import Midfall.Generator.Filters
import Midfall.Generator.Models
import Midfall.Generator.Render
import Midfall.Generator.YulGolden

namespace Midfall.Generator
open Midfall YulSemantics

/-! ## The template registry

The three `#[template(path = ...)]` attributes on the model structs, and the
include graph each contract expands. rust: M:286-287, M:495-496, M:684-685
(the Askama attributes) and MR:8-11 (the module surface) @formal-baseline. -/

/-- rust: M:287 (`#[template(path = "contracts/Halo2VerifyingKey.sol")]`). -/
def templatePathHalo2VerifyingKey : String := "contracts/Halo2VerifyingKey.sol"

/-- rust: M:496 (`#[template(path = "contracts/Halo2Verifier.sol")]`). -/
def templatePathHalo2Verifier : String := "contracts/Halo2Verifier.sol"

/-- rust: M:685 (`#[template(path = "contracts/Halo2QuotientEvaluator.sol")]`). -/
def templatePathHalo2QuotientEvaluator : String := "contracts/Halo2QuotientEvaluator.sol"

/-- The `{% include %}` list of T:contracts/Halo2Verifier.sol, in template
    order: lines 85, 87, 89, 201, 203, 205, 217, 219, 221, 223, 225, 227, 229.
    The three `.sol` partials expand at contract level and the ten
    `.yul` partials inside the main assembly block; the interleaved
    `{%- if -%}` / `{%- match -%}` control flow between them belongs to the
    renderers, not to this list. The order and these line numbers are not taken
    on trust: scripts/check_golden_provenance.py re-reads the include lines of
    the template and fails unless this list is those paths, in that order, at
    those lines. -/
def verifierIncludes : List String :=
  [ "partials/verifier/Constants.sol",
    "partials/verifier/PrecompileSmoke.sol",
    "partials/verifier/Constructors.sol",
    "partials/verifier/AssemblyHelpers.yul",
    "partials/verifier/AccumulatorHelpers.yul",
    "partials/verifier/TraceAndGasHelpers.yul",
    "partials/verifier/VkLoading.yul",
    "partials/verifier/TranscriptProofParser.yul",
    "partials/verifier/Lagrange.yul",
    "partials/verifier/QuotientAndLinearization.yul",
    "partials/verifier/Pcs.yul",
    "partials/verifier/FinalPairing.yul",
    "partials/verifier/TraceReturn.yul" ]

/-- The `{% include %}` list of T:contracts/Halo2QuotientEvaluator.sol, in
    template order: lines 152, 153. Same deal as `verifierIncludes`: the
    provenance script re-reads the paths and these line numbers from the
    template, so this order is checked and not merely asserted. -/
def evaluatorIncludes : List String :=
  [ "partials/quotient_numerator/QuotientHelpers.yul",
    "partials/quotient_numerator/QuotientNumeratorBlock.yul" ]

/-- Which artifact region each pinned golden fixture came from, as
    (partial, first line of the slice). R-40 F2: these five line numbers used to
    be hand-typed and compared to nothing, while the comment below claimed the
    provenance script re-read them. It now does - scripts/check_golden_provenance.py
    parses this list and asserts, per entry, that the partial appears in
    `verifierIncludes`, that the partial file exists under
    proofs/solidity-verifier/templates/, and that the line number is the START of
    a real pinned fixture slice in the dump that the partial's directory expands
    into. What that script still cannot check, and does not claim to: that the
    named partial is the file that generated that region. The dump is rendered
    Askama output, so a partial's own source lines mostly do not appear in it
    verbatim (measured: 2 of these 5 slices begin with a line found in the named
    partial), and nothing in this tree expands the templates. So the LINE half of
    each pair is machine-checked against the artifact and the PARTIAL half is a
    human attribution that only the include registry constrains. -/
def fixtureAnchors : List (String × Nat) :=
  [ ("partials/verifier/PrecompileSmoke.sol", 357),
    ("partials/verifier/AssemblyHelpers.yul", 640),
    ("partials/verifier/Lagrange.yul", 1509),
    ("partials/verifier/QuotientAndLinearization.yul", 1902),
    ("partials/verifier/Pcs.yul", 2744) ]

/-- The pragma every template pins. T:contracts/Halo2Verifier.sol:13,
    Halo2VerifyingKey.sol:6, Halo2QuotientEvaluator.sol:5 all say 0.8.30, and
    the header comment at T:contracts/Halo2Verifier.sol:2-12 explains why it is
    pinned rather than floated. NOT gated: nothing in this package can observe
    the compiler version, and comparing the string to itself would be decoration.
    The deployed artifact says `^0.8.24`, which is R-36 evidence, not a
    counterexample to this constant. -/
def pragmaLine : String := "pragma solidity 0.8.30;"

/-! ## Fixed text the templates contribute

These are literals written in the template source, not interpolated from a model,
so they belong to the template layer rather than to Models.lean. Every one is
gated against a computation this file does not control. -/

/-- The eight typed errors declared on the contract, in declaration order.
    rust: T:contracts/Halo2Verifier.sol:60-83 (`error BadCalldataShape();` and
    the seven after it) @formal-baseline. -/
def typedErrorNames : List String :=
  [ "BadCalldataShape", "VkMismatch", "NonCanonicalScalar", "BadPointEncoding",
    "PrecompileFailed", "ProofRejected", "QuotientProgramInvalid",
    "MemoryLayoutViolated" ]

/-- The Yul-readable selector constants: (constant name, error name, selector).
    rust: T:partials/verifier/Constants.sol:225-232 @formal-baseline, rendered
    identically at D:284-291. The Rust generator computes these with the sha3
    crate and pins them with `p4_error_selectors_match_declared_errors` in
    src/lowering/tests.rs; `errorSelectors_matchKeccak_ok` below is the Lean
    side of that pin, using the VCVio Keccak port. -/
def errorSelectors : List (String × String × BitVec 32) :=
  [ ("ERR_BAD_CALLDATA_SHAPE", "BadCalldataShape", 0x1b99e37c),
    ("ERR_VK_MISMATCH", "VkMismatch", 0xa447d73e),
    ("ERR_NON_CANONICAL_SCALAR", "NonCanonicalScalar", 0x77530042),
    ("ERR_BAD_POINT_ENCODING", "BadPointEncoding", 0xf27905ec),
    ("ERR_PRECOMPILE_FAILED", "PrecompileFailed", 0x84e81692),
    ("ERR_PROOF_REJECTED", "ProofRejected", 0xc3b0d8cd),
    ("ERR_QUOTIENT_PROGRAM_INVALID", "QuotientProgramInvalid", 0x3cc81b89),
    ("ERR_MEMORY_LAYOUT_VIOLATED", "MemoryLayoutViolated", 0xc9888d23) ]

/-- FR_MODULUS as the template writes it: T:partials/verifier/Constants.sol:236,
    rendered at D:295. -/
def frModulusConstant : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- BLS_P_HI: T:partials/verifier/Constants.sol:241, rendered at D:300. The
    template comment says it is "Fp modulus minus one, split like an EIP-2537
    coordinate", i.e. the top 16 bytes of p-1 right-aligned - which is what
    `blsPWords_recombine_ok` checks. -/
def blsPHi : Nat := 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7

/-- BLS_P_MINUS_ONE_LO: Constants.sol:242, rendered at D:301. -/
def blsPMinusOneLo : Nat := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa

/-- BLS_P_MINUS_ONE_PACKED_0: Constants.sol:245, rendered at D:304. The packed
    public-accumulator sentinel for the shifted coordinate codec: the low 224
    bits of p-1, i.e. four radix-2^56 limbs. -/
def blsPMinusOnePacked0 : Nat := 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa

/-- BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG: Constants.sol:246, rendered at D:305.
    Used only for the first x-coordinate word; the flag is bit 56, the low bit of
    limb 1, which `blsPackedSentinels_ok` pins. -/
def blsPMinusOnePacked0WithIdFlag : Nat :=
  0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa

/-- BLS_P_MINUS_ONE_PACKED_1: Constants.sol:247, rendered at D:306: the remaining
    157 bits of p-1, shifted down. -/
def blsPMinusOnePacked1 : Nat := 0x0000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84


/-! ## The verifying-key constructor template

The one template this package can render end to end:
T:contracts/Halo2VerifyingKey.sol:54-96, whose body is fully determined by the
`Halo2VerifyingKey` record. rust: that template plus M:820-825
(`Halo2VerifyingKey::render`, the Askama `render_into` wrapper), whose
Lean counterpart is `constructorStmts` / `constructorBodyLines` below.

Two channels, both derived from the same record: the vendored AST (what D-P13
compares) and the text stream (what solc reads). The text channel is where the
hex spelling lives, so it goes through `hexFilter` and
`hexPaddedFilter` from Filters.lean rather than through the decimal
renderer - which is what makes the token gate below an independent check of the
filters against committed bytes. -/

/-- Statements inside `assembly {` ... }` sit at 12 spaces, level 3
    (DVK:62). -/
def vkAssemblyLevel : Nat := 3

/-- One `mstore(add(payload, 0xNNNN), 0x...64 nibbles...)` as AST. The word
    index is multiplied by 32 exactly as the template does
    (T:contracts/Halo2VerifyingKey.sol:72); the AST records the VALUE, so the
    hex_padded(4) / hex_padded(64) spellings appear only on the text channel -
    loss class 2 of Render.lean. -/
def vkPayloadWordStmt (wordIdx : Nat) (val : Word256) : Stmt EVM.Op :=
  .exprStmt (.builtin EVM.Op.mstore
    [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number (32 * wordIdx))]
    , .lit (Literal.number val.toNat) ])

/-- The same word as one output line, with the trailing comment the template
    writes after it. -/
def vkPayloadWordLine (wordIdx : Nat) (val : Word256) (comment : String) : Line :=
  .text (indentAt vkAssemblyLevel ++ "mstore(add(payload, "
    ++ hexPaddedFilter 4 (32 * wordIdx) ++ "), "
    ++ hexPaddedFilter 64 val.toNat ++ ") // " ++ comment)

/-- The three setup statements: the runtime base, the payload pointer one byte
    past the INVALID prefix, and the INVALID byte itself.
    rust: T:contracts/Halo2VerifyingKey.sol:62-64. Note the template hard-codes
    `0x01` and `0xfe` where models.rs has `VK_RUNTIME_PREFIX_LEN` and
    `VK_RUNTIME_PREFIX`; the gate `vkConstructor_prefixConstants_ok` is what
    keeps the two readings of the same fact from drifting apart. -/
def vkSetupStmts (self : Halo2VerifyingKey) : Block EVM.Op :=
  [ .letDecl ["runtime"] (some (.lit (Literal.number self.constructorPayloadMptr)))
  , .letDecl ["payload"]
      (some (.builtin EVM.Op.add [.var "runtime", .lit (Literal.number vkRuntimePrefixLen)]))
  , .exprStmt (.builtin EVM.Op.mstore8 [.var "runtime", .lit (Literal.number vkRuntimePrefix)]) ]

/-- The setup statements as text. -/
def vkSetupLines (self : Halo2VerifyingKey) : List Line :=
  [ .text (indentAt vkAssemblyLevel ++ "let runtime := "
      ++ hexFilter self.constructorPayloadMptr),
    .text (indentAt vkAssemblyLevel ++ "let payload := add(runtime, "
      ++ hexFilter vkRuntimePrefixLen ++ ")"),
    .text (indentAt vkAssemblyLevel ++ "mstore8(runtime, " ++ hexFilter vkRuntimePrefix ++ ")") ]

/-- The constant words at word indices 0..n-1: the `for (name, chunk) in
    constants` loop at T:contracts/Halo2VerifyingKey.sol:68-73, including the
    coefficient-run header lines `word_headers` produces. -/
def vkConstantStmts (self : Halo2VerifyingKey) : Block EVM.Op :=
  ((List.range self.constants.length).zip self.constants).map
    fun (i, (_, v)) => vkPayloadWordStmt i v

/-- The same loop as text, with `word_comment` as the trailing comment. -/
def vkConstantLines (self : Halo2VerifyingKey) : List Line :=
  ((List.range self.constants.length).zip self.constants).flatMap fun (i, (_, v)) =>
    (self.wordHeaders i).map (fun h => .text (indentAt vkAssemblyLevel ++ "// " ++ h))
      ++ [vkPayloadWordLine i v (self.wordComment i)]

/-- Four words of one commitment, starting at word `base`: the two loops at
    T:contracts/Halo2VerifyingKey.sol:74-82 (fixed) and 83-91 (permutation). -/
def vkCommStmts (base : Nat) (comms : List G1Words) : Block EVM.Op :=
  ((List.range comms.length).zip comms).flatMap fun (j, w) =>
    [ vkPayloadWordStmt (base + 4 * j) w.xHi, vkPayloadWordStmt (base + 4 * j + 1) w.xLo,
      vkPayloadWordStmt (base + 4 * j + 2) w.yHi, vkPayloadWordStmt (base + 4 * j + 3) w.yLo ]

/-- The same, as text: the two-line section comment then the four labelled words.
    The two Rust loops differ only in the comment wording and the label prefix,
    which is what the arguments carry. -/
def vkCommLines (header : List String) (label : String) (base : Nat)
    (comms : List G1Words) : List Line :=
  ((List.range comms.length).zip comms).flatMap fun (j, w) =>
    (header.map fun h =>
      .text (indentAt vkAssemblyLevel ++ "// " ++ h.replace "IDX" (toString j)))
    ++ [ vkPayloadWordLine (base + 4 * j) w.xHi (label ++ "[" ++ toString j ++ "].x_hi"),
         vkPayloadWordLine (base + 4 * j + 1) w.xLo (label ++ "[" ++ toString j ++ "].x_lo"),
         vkPayloadWordLine (base + 4 * j + 2) w.yHi (label ++ "[" ++ toString j ++ "].y_hi"),
         vkPayloadWordLine (base + 4 * j + 3) w.yLo (label ++ "[" ++ toString j ++ "].y_lo") ]

/-- The `return` statement, spelled the way the template spells it: the
    length is recomputed from the three list lengths
    (`1 + 32 * (constants.len() + 4*fixed + 4*perm)`,
    T:contracts/Halo2VerifyingKey.sol:95) and NOT taken from
    `runtime_len()` (M:409-411). Two formulas for one number;
    `vkConstructor_returnFormula_ok` is what keeps them equal. -/
def Halo2VerifyingKey.constructorReturnStmt (self : Halo2VerifyingKey) : Stmt EVM.Op :=
  .exprStmt (.builtin EVM.Op.ret
    [ .var "runtime",
      .lit (Literal.number (1 + 32 * (self.constants.length
        + 4 * self.fixedComms.length + 4 * self.permutationComms.length))) ])

/-- The whole constructor body as a vendored block, braces excluded: what the
    template emits between `assembly {` and its closing brace. The final
    `return` is the dialect built-in `EVM.Op.ret`, whose source name is
    "return" (vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean:169). -/
def Halo2VerifyingKey.constructorStmts (self : Halo2VerifyingKey) : Block EVM.Op :=
  vkSetupStmts self ++ vkConstantStmts self
    ++ vkCommStmts self.constants.length self.fixedComms
    ++ vkCommStmts (self.constants.length + 4 * self.fixedComms.length) self.permutationComms
    ++ [(constructorReturnStmt self)]

/-- The comment block the template writes before the setup statements
    (T:contracts/Halo2VerifyingKey.sol:56-61, DVK:56-61). -/
def vkLeadingCommentLines : List Line :=
  [ .text (indentAt vkAssemblyLevel ++ "// Runtime layout:"),
    .text (indentAt vkAssemblyLevel ++ "//   byte 0      : INVALID, so the payload cannot be executed"),
    .text (indentAt vkAssemblyLevel ++ "//   byte 1..end : generated VK payload copied by Halo2Verifier"),
    .text (indentAt vkAssemblyLevel ++ "//"),
    .text (indentAt vkAssemblyLevel ++ "// `runtime` includes the INVALID prefix; `payload` points to word"),
    .text (indentAt vkAssemblyLevel ++ "// zero of the verifier-key data described in the contract NatSpec.") ]

/-- The constructor body as an output stream: comments verbatim, statements in
    the templates own hex spelling. -/
def Halo2VerifyingKey.constructorBodyLines (self : Halo2VerifyingKey) : List Line :=
  vkLeadingCommentLines ++ (vkSetupLines self) ++
    [ .text (indentAt vkAssemblyLevel ++ "// Header, base-point, and quotient-program words generated from"),
      .text (indentAt vkAssemblyLevel ++ "// VkPayloadLayout. The inline names on each mstore identify the"),
      .text (indentAt vkAssemblyLevel ++ "// exact slot in the rendered source.") ] ++
    (vkConstantLines self) ++
    vkCommLines [ "Fixed-column commitment IDX, stored as one",
                  "EIP-2537 padded uncompressed G1 slot." ]
      "fixed_comms" self.constants.length self.fixedComms ++
    vkCommLines [ "Permutation commitment IDX, also a 4-word",
                  "EIP-2537 padded uncompressed G1 slot." ]
      "permutation_comms" (self.constants.length + 4 * self.fixedComms.length)
      self.permutationComms

/-- The trailing blank line, the two-line comment and the `return`
    (T:contracts/Halo2VerifyingKey.sol:92-95, DVK:265-268). -/
def Halo2VerifyingKey.constructorReturnLines (self : Halo2VerifyingKey) : List Line :=
  [ .text "",
    .text (indentAt vkAssemblyLevel ++ "// Return exactly the INVALID prefix plus the generated payload. The"),
    .text (indentAt vkAssemblyLevel ++ "// linked verifier pins this byte length and the resulting codehash."),
    .text (indentAt vkAssemblyLevel ++ "return(runtime, "
      ++ hexFilter (1 + 32 * (self.constants.length + 4 * self.fixedComms.length
        + 4 * self.permutationComms.length)) ++ ")") ]

/-- The whole constructor body: the AST channel and the text channel are the same
    template expansion seen twice. -/
def Halo2VerifyingKey.constructorLines (self : Halo2VerifyingKey) : List Line :=
  self.constructorBodyLines ++ self.constructorReturnLines

end Midfall.Generator

/-! ## Known-answer tests for the template layer

Same rule as Models.lean: each gate names the wrong implementation it rules out.
The expected sides here come from three sources this file does not control:
`Midfall.abiSelector` (a Keccak port), `Midfall.Yul.blsP` /
`blsR` (an EIP-cited port), and the pinned golden fixtures in
YulGolden.lean, which scripts/check_golden_provenance.py re-derives from the
committed `.sol` bytes. A gate that only compared two literals in this file
would be decoration and is not written. -/

namespace Midfall.Generator.TemplateKats

open Midfall Midfall.Generator Midfall.Generator.Golden YulSemantics

/-- The argument lists of every `if iszero(staticcall(...))` guard in a
    block, in order. -/
def staticcallGuards (b : Block EVM.Op) : List (List (Expr EVM.Op)) :=
  b.filterMap fun
    | .cond (.builtin EVM.Op.iszero [ .builtin EVM.Op.staticcall args ]) _ => some args
    | _ => none

/-- A numeric literal at position `i` of an argument list. -/
def argNat (args : List (Expr EVM.Op)) (i : Nat) : Option Nat :=
  match listNth args i with
  | some (.lit (Literal.number n)) => some n
  | _ => none

/-- The bound of the single `for ... lt(i, N) ...` loop in a block. -/
def forLoopBound (b : Block EVM.Op) : Option Nat :=
  match b.filterMap fun
    | Stmt.forLoop _ (.builtin EVM.Op.lt [ _, .lit (Literal.number n) ]) _ _ => some n
    | _ => none with
  | [n] => some n
  | _ => none

/-- The `(offset, value)` pairs of every `mstore(add(base, off), lit)`
    in a block, in order. -/
def mstoreAddLits (b : Block EVM.Op) : List (Nat × Expr EVM.Op) :=
  b.filterMap fun
    | .exprStmt (.builtin EVM.Op.mstore
        [ .builtin EVM.Op.add [ _, .lit (Literal.number off) ], v ]) => some (off, v)
    | _ => none

/-- A plain numeric word value. -/
def litVal (e : Expr EVM.Op) : Option Nat :=
  match e with
  | .lit (Literal.number n) => some n
  | _ => none

/-- The `sub(FR_MODULUS, k)` shape: the exponent the scalar-inversion frame
    writes is the modulus minus two, not a literal. -/
def frMinus (e : Expr EVM.Op) : Option Nat :=
  match e with
  | .builtin EVM.Op.sub [ .var nm, .lit (Literal.number k) ] =>
      if nm == "FR_MODULUS" then some k else none
  | _ => none

/-- Is this expression a bare identifier with this name? -/
def isVarNamed (nm : String) (e : Expr EVM.Op) : Bool :=
  match e with
  | .var s => s == nm
  | _ => false

/-- Is this expression the bare `FR_MODULUS` identifier? -/
def isFrModulus (e : Expr EVM.Op) : Bool := isVarNamed "FR_MODULUS" e

/-- The label of the first case of the single switch in a block. -/
def firstSwitchCaseLabel (b : Block EVM.Op) : Option Nat :=
  match b.filterMap fun
    | Stmt.switch _ ((.number n, _) :: _) _ => some n
    | _ => none with
  | [n] => some n
  | _ => none

/-- The four 2G words inside the `spread` fixture, destructured from the
    known shape rather than collected, so a change to the fixture shape shows up
    as `none` rather than as a silently shorter list. -/
def spreadTwoGWords : List Nat :=
  match Golden.spread_ast with
  | [ Stmt.cond (.builtin EVM.Op.iszero [ .builtin EVM.Op.and [
        .builtin EVM.Op.and [ .builtin EVM.Op.eq [ _, .lit (Literal.number a) ],
                              .builtin EVM.Op.eq [ _, .lit (Literal.number b) ] ],
        .builtin EVM.Op.and [ .builtin EVM.Op.eq [ _, .lit (Literal.number c1) ],
                              .builtin EVM.Op.eq [ _, .lit (Literal.number d) ] ] ] ]) _ ] =>
      [a, b, c1, d]
  | _ => []

/-- The body of the `scalar_inv` helper fixture. -/
def scalarInvBody : Block EVM.Op :=
  match Golden.scalarInv_ast with
  | [ Stmt.funDef _ _ _ body ] => body
  | _ => []

/-- The word stride the batch-inversion fixture advances by. -/
def batchInvStride : Option Nat :=
  match Golden.batchInv_ast with
  | [ Stmt.forLoop _ _ _ body ] =>
      match body.filterMap fun
        | Stmt.assign [_] (.builtin EVM.Op.add [ _, .lit (Literal.number n) ]) => some n
        | _ => none with
      | n :: more => if more.all (· == n) then some n else none
      | [] => none
  | _ => none

/-- THE SELECTORS ARE THE KECCAKS OF THE DECLARED NAMES. Rules out a mistyped
    selector nibble in the ported table: the expected side is computed by the
    VCVio Keccak port over the error name ported from the same template, so a
    wrong hex value cannot be fixed by editing the other side of this file. This
    is the Lean mirror of the Rust pin the template comment names
    (`p4_error_selectors_match_declared_errors`). -/
def errorSelectors_matchKeccak_ok : Bool :=
  errorSelectors.length == 8
    && errorSelectors.all fun (_, err, sel) => abiSelector (err ++ "()") == sel

/-- THE SELECTOR TABLE COVERS THE DECLARED ERRORS, in the same order and with the
    same count. That is exactly what the Rust test asserts, and it is the check
    that a seventh error added to the contract without a Yul constant (or the
    reverse) fails. Rules out a dropped or duplicated row in the ported table. -/
def errorSelectors_coverDeclaredErrors_ok : Bool :=
  errorSelectors.map (·.2.1) == typedErrorNames
    && (errorSelectors.map (·.1)).all (fun n => n.startsWith "ERR_")
    && (errorSelectors.map (·.1)).Nodup

/-- FR_MODULUS as the template writes it is the same number the EIP-cited port
    in Midfall/Yul/Externals.lean:120 carries. Rules out this file having copied
    a modulus from a stale artifact, and rules out the two ports disagreeing -
    the free-identifier hazard loss class 4 of Render.lean records. -/
def frModulus_matchesBlsR_ok : Bool := frModulusConstant == Midfall.Yul.blsR

/-- The two BLS_P words recombine to p-1, which is what the template comment at
    T:partials/verifier/Constants.sol:238-240 claims and what the artifact
    comparisons at D:725-728 rely on. Rules out a nibble being mistyped in
    either word, and rules out the pair being p rather than p-1: the low word
    ends in `aaaa`, not `aaab`. -/
def blsPWords_recombine_ok : Bool :=
  blsPHi * 2 ^ 256 + blsPMinusOneLo == Midfall.Yul.blsP - 1
    && blsPHi == (Midfall.Yul.blsP - 1) / 2 ^ 256
    && blsPMinusOneLo == (Midfall.Yul.blsP - 1) % 2 ^ 256

/-- The packed accumulator sentinels are the same p-1 split at 224 bits instead
    of 256 - four radix-2^56 limbs in the low word - and the id-flag variant
    differs from the plain one by exactly bit 56, the low bit of limb 1. Rules
    out the flag being applied to the wrong limb, which would make the shifted
    coordinate codec read a non-identity point as the identity, and rules out
    the two packings disagreeing about p-1. -/
def blsPackedSentinels_ok : Bool :=
  blsPMinusOnePacked1 * 2 ^ 224 + blsPMinusOnePacked0 == Midfall.Yul.blsP - 1
    && blsPMinusOnePacked0 == (Midfall.Yul.blsP - 1) % 2 ^ 224
    && blsPMinusOnePacked1 == (Midfall.Yul.blsP - 1) / 2 ^ 224
    && blsPMinusOnePacked0WithIdFlag - blsPMinusOnePacked0 == 2 ^ 56

/-- THE INCLUDE ORDER MATCHES THE ANCHORS - and this gate alone sees only the
    SHAPE of the anchor list. Every pinned fixture slice is annotated with the
    artifact lines it came from, and each belongs to one partial; the order those
    line numbers appear in must be the order the contract template includes its
    partials in. What reddens THIS gate: swapping two entries of
    `fixtureAnchors`, re-anchoring one fixture to a line that breaks the
    increasing order, naming a partial that is not in `verifierIncludes`, or
    changing the number of anchors away from five. What does NOT redden it, and
    is the reason R-40 F2 was filed: an anchor line number that is not the real
    start of any fixture slice - 1,2,3,4,5 satisfies every clause here. That
    half of the claim is checked by scripts/check_golden_provenance.py, which
    parses `fixtureAnchors` out of this file and matches each line against the
    slice starts it re-reads from the committed dump. Together the gate and the
    script make the cross-check real; on its own this gate is an ordering check on
    five numbers, nothing more.

    COVERAGE, stated because the module header used to claim more than this
    (R-40 F7): the five anchors are five of the thirteen verifier partials and
    none of the two evaluator partials, so the relative order of the other eight
    is invisible here. Swapping `AccumulatorHelpers.yul` and
    `TraceAndGasHelpers.yul` in `verifierIncludes`, or the two entries of
    `evaluatorIncludes`, reddens nothing in this file - it reddens
    scripts/check_golden_provenance.py, which now compares both registries, in
    order, against the include lines of the two contract templates. -/
def includeOrder_matchesFixtureAnchors_ok : Bool :=
  fixtureAnchors.length == 5
    && fixtureAnchors.all (fun (p, _) => verifierIncludes.contains p)
    && (fixtureAnchors.map (·.2)).Pairwise (· < ·)
    && (fixtureAnchors.map fun (p, _) =>
          (verifierIncludes.takeWhile (· != p)).length).Pairwise (· < ·)

/-- The two contracts that are not the verifier each include something the other
    does not, and no partial is included twice by one contract. Rules out the
    registry lists being copy-pasted onto each other. -/
def includeGraph_disjoint_ok : Bool :=
  verifierIncludes.Nodup && evaluatorIncludes.Nodup
    && verifierIncludes.all (fun x => ! evaluatorIncludes.contains x)
    && verifierIncludes.length == 13 && evaluatorIncludes.length == 2


/-- The first five header words of the poseidon fixture VK - exactly the region
    DVK:62-72 covers, with the values that slice carries. The DATA here is the
    same data the fixture pins, so this model is not a check of the numbers; it
    is the input to a check of the template: the offsets, the padding widths, the
    INVALID prefix, the order of the three setup statements, and the label
    comments. -/
def poseidonVkHead : Halo2VerifyingKey := {
  constructorPayloadMptr := 0x80
  constants :=
    [ ("vk_digest", 0x4cc2e5ac0d3a524691c3723a18e826d6ed01cbf767fdec83fcf3a8f9e7640494),
      ("num_instances", 1),
      ("k", 6),
      ("n_inv", 0x721df0b5dcf70753126cf0a7e97b50a53e6ead72f3fe628f03ffffff04000001),
      ("omega", 0x45af6345ec055e4d14a1e27164d8fdbd2d967f4be2f951558140d032f0a9ee53) ]
  fixedComms := []
  permutationComms := []
  quotientConstOffsetWords := none
  quotientConstWords := 0
  quotientProgramOffsetWords := none
  quotientProgramWords := 0
  quotientConstLabels := []
  quotientConstHeaders := []
}

/-- The Rust test VK (M:1064-1146) with the constructor payload base the Rust
    reads from `VkConstructorMemoryLayout` (LM:59, 0x80) instead of the 0 the
    Models.lean fixture uses, because the render assertions at M:1470-1473 name
    that address. -/
def vkWithPayloadBase (base : Nat) (vk : Halo2VerifyingKey) : Halo2VerifyingKey :=
  { vk with constructorPayloadMptr := base }

def vkForRender : Halo2VerifyingKey :=
  vkWithPayloadBase 0x80 (Midfall.Generator.ModelKats.syntheticVk 2 3)

/-- `needle` occurs in `hay`. -/
def containsStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- THE RENDERED VK CONSTRUCTOR HEAD IS THE COMMITTED CONSTRUCTOR HEAD, under the
    authoritative relation. The expected side is `Golden.vkHead_ast`, the
    `yul%` quotation of DVK:62-72 that scripts/check_golden_provenance.py
    re-derives from the committed bytes, so this is a model-to-artifact check and
    not a paste-to-paste one. It is the first place in the tree where a ported
    template is rendered and compared to the generator output under `stmtsBeq`.

    SCOPE - eight statements, and the name oversells it if that is not said.
    `poseidonVkHead` has `fixedComms := []` and `permutationComms := []`, and
    the comparison is `List.take 8`, so what is compared is exactly the three
    setup statements and the five constant words. Concretely it rules out: the
    payload offset being `32*i` vs `32*(i+1)` in `vkPayloadWordStmt`; the
    INVALID byte being stored after the payload pointer is taken; the `mstore8`
    and the two `let`s being emitted in a different order; and a wrong VALUE in
    one of the five header words.

    WHAT IT CANNOT SEE, measured rather than asserted (R-40 F1). (i) The
    commitment loops at T:contracts/Halo2VerifyingKey.sol:74-91 - 18 of the
    template's 43 body lines. With both commitment lists empty the template
    emits no commitment statement, and `.take 8` would drop one even if it did:
    perturbing the stride in `vkCommStmts` (`4 * j` -> `5 * j`) and swapping
    `xLo`/`yHi` there reddened nothing in this tree until
    `vkConstructor_commitments_matchesExpectedAst_ok` was added, which is the
    gate that covers them, and the fixed loop is now tied to the committed bytes
    as well by `vkConstructor_fixedComms_matchesArtifact_ok`. (ii) The hex filters: the AST channel records the
    numeric value only, so a filter that spells a word differently but elaborates
    to the same number passes here - loss class 2 of Render.lean. Spelling is
    checked on the text channel by `vkConstructor_tokens_matchPinnedStream_ok`
    and `vkRender_matchesRustTestAssertions_ok`. The `.take 8` is because the
    fixture is a slice: the ninth statement, the `return`, is checked by
    `vkRender_matchesRustTestAssertions_ok` instead. -/
def vkConstructor_matchesGolden_ok : Bool :=
  YulSemantics.SyntaxEq.stmtsBeq (List.take 8 poseidonVkHead.constructorStmts) Golden.vkHead_ast

/-- Two fixed and one permutation commitment with pairwise distinct coordinate
    words, so a word-order error inside a G1 slot changes the payload instead of
    silently re-writing the same value into the next slot. The values are
    placeholders chosen for distinguishability; they are NOT the poseidon VK's
    commitments (DVK:103 carries those) and nothing here claims they are. -/
def vkTestComms : List G1Words :=
  [ { xHi := 0x0100, xLo := 0x0101, yHi := 0x0102, yLo := 0x0103 },
    { xHi := 0x0104, xLo := 0x0105, yHi := 0x0106, yLo := 0x0107 } ]

/-- See `vkTestComms`; one commitment, based at word 13 because two fixed
    commitments occupy words 5..12. -/
def vkTestPermComms : List G1Words :=
  [ { xHi := 0x0200, xLo := 0x0201, yHi := 0x0202, yLo := 0x0203 } ]

/-- `poseidonVkHead` with non-empty commitment lists: the same five header words
    at words 0..4, two fixed commitments at words 5..12 and one permutation
    commitment at words 13..16, so the two loops at
    T:contracts/Halo2VerifyingKey.sol:74-91 emit something. -/
def poseidonVkWithComms : Halo2VerifyingKey :=
  { poseidonVkHead with
    fixedComms := vkTestComms,
    permutationComms := vkTestPermComms }

/-- The commitment region of `poseidonVkWithComms.constructorStmts`: the twelve
    `mstore`s between the five constant words and the `return`. The length
    guard is what makes the slice honest - without it a perturbation that changed
    the NUMBER of statements would misalign the slice rather than redden it, and
    a misaligned slice compared against a twelve-statement expectation is exactly
    the kind of gate that cannot fail. -/
def vkCommsRegion : Block EVM.Op :=
  let s := poseidonVkWithComms.constructorStmts
  if s.length == 21 then (s.drop 8).take 12 else []

/-- THE EXPECTED COMMITMENT WORDS, written out by hand from the template: two G1
    slots of four words each starting at word 5 (`fixedComms`,
    T:contracts/Halo2VerifyingKey.sol:74-82) then one slot at word 13
    (`permutationComms`, :83-91), each slot in x_hi, x_lo, y_hi, y_lo order at
    byte offset `32 * word`, with the permutation base being
    `constants.len() + 4 * fixed.len()` rather than `4 * fixed.len()`.
    HAND-WRITTEN, NOT ARTIFACT-DERIVED, and the distinction is stated because it
    matters. The tracked artifact DVK does contain a VK with non-empty
    commitments (fixed_comms from DVK:103, permutation_comms later in the same
    file) and the fixed half of that region is now pinned: Golden.vkComms_ast is
    DVK:103-132, the first five fixed commitments, and
    vkConstructor_fixedComms_matchesArtifact_ok compares the rendered fixed loop
    against it. The permutation section is still unreachable from a contiguous
    slice - the artifact emits all 19 fixed commitments before the first
    permutation one - so THIS expectation stays hand-written, and it is a
    hand-written specification of the template:
    its value is that the specification and the code disagree when the code is
    wrong, which is what the perturbations recorded in the gate below document,
    and not that either side is tied to committed bytes. -/
def vkCommsExpectedAst : Block EVM.Op :=
  [ .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x00a0)]
      , .lit (Literal.number 0x0100) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x00c0)]
      , .lit (Literal.number 0x0101) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x00e0)]
      , .lit (Literal.number 0x0102) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x0100)]
      , .lit (Literal.number 0x0103) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x0120)]
      , .lit (Literal.number 0x0104) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x0140)]
      , .lit (Literal.number 0x0105) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x0160)]
      , .lit (Literal.number 0x0106) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x0180)]
      , .lit (Literal.number 0x0107) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x01a0)]
      , .lit (Literal.number 0x0200) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x01c0)]
      , .lit (Literal.number 0x0201) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x01e0)]
      , .lit (Literal.number 0x0202) ]),
    .exprStmt (.builtin EVM.Op.mstore
      [ .builtin EVM.Op.add [.var "payload", .lit (Literal.number 0x0200)]
      , .lit (Literal.number 0x0203) ]) ]

/-- THE COMMITMENT LOOPS ARE GATED. Renders a VK whose fixed and permutation
    commitment lists are non-empty and compares the twelve commitment statements
    to `vkCommsExpectedAst` under `stmtsBeq`. This is the gate R-40 F1 asked
    for: before it, the two loops at T:contracts/Halo2VerifyingKey.sol:74-91 were
    entirely ungated, because every other VK model in this package has empty
    commitment lists or compares only the head slice.
    Concretely it rules out, and was measured reddening on each of: the stride
    inside a slot being `4 * j` -> `5 * j`; the permutation section base being
    `4 * fixed.len()` instead of `constants.len() + 4 * fixed.len()`; the
    permutation loop being emitted at the fixed base so the two sections
    collide; `xLo` and `yHi` swapped within a slot; the slot order being
    x_hi, y_hi, x_lo, y_lo; and a commitment list being dropped so the region is
    no longer twelve statements. What it CANNOT see: the trailing comment text
    and the two-line section headers - those are `vkCommLines` on the text
    channel, and the AST carries no comments - the hex spelling of a word, and
    whether the VALUES are the real poseidon commitments, since the expected
    side is hand-written (`vkCommsExpectedAst`). -/
def vkConstructor_commitments_matchesExpectedAst_ok : Bool :=
  YulSemantics.SyntaxEq.stmtsBeq vkCommsRegion vkCommsExpectedAst

/-- The poseidon fixture VK's WHOLE constant table: the 35 words at DVK:68-102,
    names taken from the artifact's own trailing comments. `poseidonVkHead` is
    the first five of these; this is all of them, because the commitment offsets
    in the artifact are `32 * (constants.len() + 4*j + k)` with constants.len()
    equal to 35, and a model with five constants puts the same commitment at
    0x00a0 instead of 0x0460. -/
def poseidonVkFullConstants : List (String × Word256) :=
  [ ("vk_digest", 0x4cc2e5ac0d3a524691c3723a18e826d6ed01cbf767fdec83fcf3a8f9e7640494),
    ("num_instances", 0x0000000000000000000000000000000000000000000000000000000000000001),
    ("k", 0x0000000000000000000000000000000000000000000000000000000000000006),
    ("n_inv", 0x721df0b5dcf70753126cf0a7e97b50a53e6ead72f3fe628f03ffffff04000001),
    ("omega", 0x45af6345ec055e4d14a1e27164d8fdbd2d967f4be2f951558140d032f0a9ee53),
    ("omega_inv", 0x640d097461a2eeaf4e84b3cd7dc75b61db872ef3dce28e788d28c143168bba2c),
    ("omega_inv_to_l", 0x68f0ba2461933c32412d801131c542d24eb73f5d9958580573ea3fa3e6fe310f),
    ("has_accumulator", 0x0000000000000000000000000000000000000000000000000000000000000000),
    ("acc_offset", 0x0000000000000000000000000000000000000000000000000000000000000000),
    ("num_acc_limbs", 0x0000000000000000000000000000000000000000000000000000000000000000),
    ("num_acc_limb_bits", 0x0000000000000000000000000000000000000000000000000000000000000000),
    ("g1_x_hi", 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f),
    ("g1_x_lo", 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb),
    ("g1_y_hi", 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4),
    ("g1_y_lo", 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1),
    ("g2_x_c0_hi", 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051),
    ("g2_x_c0_lo", 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8),
    ("g2_x_c1_hi", 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65),
    ("g2_x_c1_lo", 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e),
    ("g2_y_c0_hi", 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a),
    ("g2_y_c0_lo", 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801),
    ("g2_y_c1_hi", 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99),
    ("g2_y_c1_lo", 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be),
    ("neg_s_g2_x_c0_hi", 0x00000000000000000000000000000000050ac27c3527072b81af0fa9a683e226),
    ("neg_s_g2_x_c0_lo", 0xda79275f2985c9e89a0db969b76e0b6be94fee874c48586737ad5588cf1e1041),
    ("neg_s_g2_x_c1_hi", 0x00000000000000000000000000000000116010f1b3d33aa5f3f608c385400979),
    ("neg_s_g2_x_c1_lo", 0xed36dc3fab53d3626f519c74d7e1ebef62c9ad35796404ce2fc3ebb42167b5a1),
    ("neg_s_g2_y_c0_hi", 0x0000000000000000000000000000000015b237e8c830b11d92578cb44ab0a93f),
    ("neg_s_g2_y_c0_lo", 0x5176b4898e3a759bb6fba9e6c9375340a8a87557a3943686097db68d914e268e),
    ("neg_s_g2_y_c1_hi", 0x00000000000000000000000000000000006d57f79a18220d1e5ef04bd519e995),
    ("neg_s_g2_y_c1_lo", 0x9a9cc71553bb761b5422a6b6971b75c8d3695bfa07b861c4b1c958da426efc45),
    ("quotient_const", 0x0000000000000000000000000000000000000000000000000000000000000001),
    ("quotient_program", 0x0556c010584005576008060d000b0200010556801156801156800556e008060d),
    ("quotient_program", 0x000b0300000556a01156a01156a005570008060d000b0300010556c01156c011),
    ("quotient_program", 0x56c005578008060d000b0300011b00001b00011b0002191f0000000000000000) ]

/-- The first five fixed commitments of the same VK, DVK:105-132, i.e. the
    `fixed_comms` the pinned `Golden.vkComms_ast` slice carries. Values are the
    artifact's, not placeholders: that is the point of the gate below. -/
def poseidonVkFullComms : List G1Words :=
  [ { xHi := 0x0000000000000000000000000000000016742a8c4f331d1be5bc8622ba92b271, xLo := 0xc798f706f7ed359adb5f2ac650537c84623ab7834d56f8e1d36c8442aea29c13,
      yHi := 0x0000000000000000000000000000000013ca2f8530986bc11083da96e5763226, yLo := 0x07cd6bdb82f308cb42878beaa2f5a0f3d5c62c6c7701d58ee27020e08e9cb8b7 },
    { xHi := 0x0000000000000000000000000000000013c538f85ca3091a013ab6a943c394cf, xLo := 0xdb4a55805d283af633abd3c03f5a700ee60f921c63dfd268120f7a13cd3bc355,
      yHi := 0x00000000000000000000000000000000049ef841da32566f73dc39ba90d1386d, yLo := 0x95c92b7204a5400036f4c40eebdbe4ba0642fa2654789f20340038a10835648a },
    { xHi := 0x000000000000000000000000000000000d084585756dbb5703f9c5f156a63cf4, xLo := 0xbec7b8323b6470c1cd0410237136761a3d52ebccab70f8a5cc8c0f78548953ba,
      yHi := 0x0000000000000000000000000000000008edfd70c65c5d312c37dc754a862cf1, yLo := 0x069893b6151b30977eebb406338f37bf47a30e510912b183020a88ea275e9355 },
    { xHi := 0x000000000000000000000000000000000a3146faad4b6dfd10526e417494857f, xLo := 0x555d39dd09f58f44b4a94034477f00169abf04dc7a1abb92cb06c9fb2abe2e2f,
      yHi := 0x00000000000000000000000000000000107769de5e57b32ad1bc2f5ed22aa2ee, yLo := 0x0eeba5d4e7c2105b7d872d80d7bcbd0ac018f2ae0aa25084cc205ecb36d584f6 },
    { xHi := 0x00000000000000000000000000000000199220c5e9f1f7f71c66c6abebf6b6eb, xLo := 0xa4f8a76ac55dbc2c9b6321a883612aeeee9c6100a0947235b90d4a128b0581ed,
      yHi := 0x000000000000000000000000000000000a88a4f6e4302c60014fe494699e83ee, yLo := 0x36f38f5739eb100abaedf297069e9678848ca55ff0f7e03c9c875f6a41ddb1d9 } ]

/-- The poseidon fixture VK as the artifact actually renders it. The permutation
    list is empty, and that is a limit of the pin rather than of the model: the
    artifact emits all 19 fixed commitments before the first permutation one,
    so no contiguous slice of DVK contains fixed-then-permutation unless every
    fixed commitment is transcribed too. The permutation loop stays gated by
    `vkConstructor_commitments_matchesExpectedAst_ok`, against the hand-written
    expectation. -/
def poseidonVkFull : Halo2VerifyingKey :=
  { poseidonVkHead with
    constants := poseidonVkFullConstants,
    fixedComms := poseidonVkFullComms }

/-- The twenty commitment statements of `poseidonVkFull.constructorStmts`: three
    setup, then the 35 constants, then the twenty, then the return, so the
    length guard is what makes the drop/take honest - without it a perturbation
    that changed the statement count would misalign the slice instead of
    reddening it. -/
def vkCommsArtifactRegion : Block EVM.Op :=
  let s := poseidonVkFull.constructorStmts
  if s.length == 59 then (s.drop 38).take 20 else []

/-- THE FIXED COMMITMENT LOOP AGAINST THE COMMITTED BYTES. This is the artifact-
    backed upgrade R-40 F1 asked for, scoped to what the artifact can actually
    back: the rendered fixed-commitment statements are compared under `stmtsBeq`
    to `Golden.vkComms_ast`, the DVK:103-132 slice that
    scripts/check_golden_provenance.py re-derives from the tracked file, so
    unlike `vkCommsExpectedAst` neither side is typed by hand. Concretely it
    rules out, and was measured reddening on: the stride inside a slot being
    `4 * j` -> `5 * j`; `xLo` and `yHi` exchanged within a slot; the fixed
    section base being anything other than `constants.len()`; and a commitment
    value differing from the one the generator wrote into the artifact. What it
    CANNOT see: the permutation loop, whose artifact offsets are unreachable
    without transcribing all 19 fixed commitments (see `poseidonVkFull`), and
    the section header comments, which are text-channel only. -/
def vkConstructor_fixedComms_matchesArtifact_ok : Bool :=
  YulSemantics.SyntaxEq.stmtsBeq vkCommsArtifactRegion Golden.vkComms_ast

/-- THE SAME SLICE ON THE TEXT CHANNEL, against the pinned token stream: the
    text is built from `hexFilter` and `hexPaddedFilter` over the
    model, and the expected side is the artifact token stream that
    scripts/check_golden_provenance.py re-derives from DVK:62-72. What it
    rules out, concretely: a wrong VALUE in a rendered word, a missing
    `mstore8` line, `add(runtime, 0x01)` spelled with another number, a
    mis-named identifier, and a dropped or duplicated statement. What it
    CANNOT rule out, measured rather than assumed: a padding-width change.
    The token relation reduces every literal to its value, so perturbing
    `hexPaddedFilter 64` to `hexPaddedFilter 63` reddened nothing - that is loss
    class 2 of Render.lean showing up inside a gate of this package, not a
    bug in the gate. The pad-4 spelling IS caught, but by
    `vkRender_matchesRustTestAssertions_ok`, which greps literal text. Comments are
    stripped by the token relation, so the comment TEXT is unchecked here;
    the statement text is not. -/
def vkConstructor_tokens_matchPinnedStream_ok : Bool :=
  yulTokens ("{" ++ renderLines (poseidonVkHead.constructorBodyLines) ++ "\n}")
    == yulTokens Golden.vkHead_committed

/-- THE TEMPLATE HARD-CODES WHAT models.rs DECLARES. The template writes
    `0x01` and `0xfe` literally (T:contracts/Halo2VerifyingKey.sol:63-64)
    while M:314-316 declares `VK_RUNTIME_PREFIX` and
    `VK_RUNTIME_PREFIX_LEN`; nothing in Rust connects them, so nothing in the
    port would either if this gate were absent. The expected strings are the
    artifact bytes at DVK:63-64 and the assertions at M:1475-1480. Rules out
    changing the model constant without the template, or vice versa - which would
    silently shift every payload word by one byte. -/
def vkConstructor_prefixConstants_ok : Bool :=
  let text := renderLines (poseidonVkHead.constructorBodyLines)
  containsStr text "let payload := add(runtime, 0x01)"
    && containsStr text "mstore8(runtime, 0xfe)"
    && vkRuntimePrefix == 0xfe && vkRuntimePrefixLen == 1

/-- THE RENDERED VK SATISFIES THE RUST TEST'S OWN ASSERTIONS. M:1446-1493 renders
    the synthetic VK and asserts six substrings of the output; they are ported
    here verbatim as the expected side, so this gate checks the Lean renderer
    against a Rust assertion rather than against a transcription. The
    `return(runtime, 0x0661)` case is the one that matters most: the comment
    at M:1452-1453 explains that 1633 has an odd nibble count and so the
    `hex` filter must pad it to `0x0661`, and `0x04e0` pins the
    permutation-commitment base at word 39. Rules out the length formula, the
    padding rule, and the section ordering all at once - and it is the only
    gate in this package that can see a hex padding width at all, because it
    greps literal text where the token relation cannot. -/
def vkRender_matchesRustTestAssertions_ok : Bool :=
  let text := renderLines (vkForRender.constructorLines)
  containsStr text "return(runtime, 0x0661)"
    && containsStr text "let runtime := 0x80"
    && containsStr text "let payload := add(runtime, 0x01)"
    && containsStr text "mstore8(runtime, 0xfe)"
    && containsStr text "mstore(add(payload, 0x0000),"
    && containsStr text "mstore(add(payload, 0x04e0),"
    && vkForRender.runtimeLen == 1633

/-- TWO FORMULAS FOR ONE LENGTH. The template recomputes the returned length as
    `1 + 32 * (constants.len() + 4*fixed + 4*perm)`
    (T:contracts/Halo2VerifyingKey.sol:95) instead of calling
    `runtime_len()` (M:409-411). They agree today; if a later package changes
    one - say by counting a G1 as 3 words - the artifact would return a runtime
    that is not the payload. Rules out exactly that divergence, on a model that
    has commitments, unlike the head slice. -/
def vkConstructor_returnFormula_ok : Bool :=
  YulSemantics.SyntaxEq.stmtsBeq [vkForRender.constructorReturnStmt]
    [ .exprStmt (.builtin EVM.Op.ret
        [ .var "runtime", .lit (Literal.number vkForRender.runtimeLen) ]) ]
    && vkForRender.runtimeLen == vkForRender.len + 1

/-- THE MODULUS AND THE WIDTHS THE SMOKE PROBE USES ARE THE MODEL CONSTANTS.
    `Golden.smoke_ast` is the provenance-pinned D:357-380 slice; its two
    staticcall frames carry the modexp address, the modexp frame size, the
    modexp output size, the G1ADD address, the G1ADD input size and the G1
    padded size as literals, and its loop bound is the smoke scratch size. Rules
    out `TemplateConstants` being re-derived from a different layout than the
    one the artifact was generated with - the failure R-36 describes for the
    deployed bytes, caught on the current ones. -/
def templateConstants_matchSmokeFixture_ok : Bool :=
  let c := templateConstantsDefault
  match staticcallGuards Golden.smoke_ast with
  | [me, ga] =>
      argNat me 1 == some c.modexp.address
        && argNat me 3 == some c.modexp.frameBytes
        && argNat me 5 == some c.modexp.outputBytes
        && argNat ga 1 == some c.eip2537.g1addAddress
        && argNat ga 3 == some c.g1addInputBytes
        && argNat ga 5 == some c.g1Bytes
        && forLoopBound Golden.smoke_ast == some c.eip2537.smokeScratchBytes
        && c.eip2537.smokeScratchBytes == c.pairingTwoPairBytes
  | _ => false

/-- THE MODEXP FRAME OFFSETS ARE THE ONES THE HELPER USES. The pinned
    `scalar_inv` helper (D:640-662) writes six words at offsets
    0x00, 0x20, 0x40, 0x60, 0x80, 0xa0 with lengths 32, 32, 32 then base,
    p-2, p. That is `ModexpTemplateConstants` field by field, and the
    exponent and modulus are `frModulusConstant`, so one fixture checks the
    frame layout and the field modulus together. Rules out the frame offsets
    being the header order rather than the EIP-198 order, and rules out the
    inversion exponent drifting from the modulus. -/
def templateConstants_matchScalarInvFixture_ok : Bool :=
  let c := templateConstantsDefault
  let rows := mstoreAddLits scalarInvBody
  rows.map (·.1)
      == [c.modexp.baseLenOffset, c.modexp.expLenOffset, c.modexp.modLenOffset,
          c.modexp.baseOffset, c.modexp.expOffset, c.modexp.modOffset]
    && litVal (rows.getD 0 (0, .lit (Literal.number 0))).2 == some c.wordBytes
    && litVal (rows.getD 1 (0, .lit (Literal.number 0))).2 == some c.wordBytes
    && litVal (rows.getD 2 (0, .lit (Literal.number 0))).2 == some c.wordBytes
    && isVarNamed "x" (rows.getD 3 (0, .var "")).2
    && frMinus (rows.getD 4 (0, .lit (Literal.number 0))).2 == some 2
    && isFrModulus (rows.getD 5 (0, .var "x")).2
    && (match staticcallGuards scalarInvBody with
        | [one] => argNat one 1 == some c.modexp.address
                     && argNat one 3 == some c.modexp.frameBytes
        | _ => false)

/-- THE OPCODE BYTE IS THE SWITCH LABEL. The pinned VM slice (D:1902-1917) opens
    with `switch q_op` / `case 0x05` and the arm pushes
    `mload` of a two-byte operand read from the program counter - which is
    `Q_OP_PUSH_MEM_U16` (QVM:571), value 0x05. Rules out the opcode table
    being read off a different build than the artifact, the exact drift R-36
    records for the deployed contract. -/
def qvmOp_matchesVmSwitchFixture_ok : Bool :=
  firstSwitchCaseLabel Golden.vmSwitch_ast
    == some templateConstantsDefault.quotientVm.op.pushMemU16

/-- THE DOUBLE GENERATOR IS THE PINNED ONE. The four literals inside the pinned
    `spread` slice (D:399-408) are the expected output of the
    `G1ADD(G, G)` smoke probe, i.e. exactly
    `templateConstants.eip2537.g1_double_generator` (M:200-203). Rules out
    the generator constants in this package disagreeing with the artifact that
    was generated from them - and unlike `g1Generator_doubles_ok` in
    Models.lean, this side is tied to committed bytes rather than to the group
    law, so the two gates fail for different reasons. -/
def g1Double_matchesSpreadFixture_ok : Bool :=
  let g := templateConstantsDefault.eip2537.g1DoubleGenerator
  spreadTwoGWords == [g.xHi.toNat, g.xLo.toNat, g.yHi.toNat, g.yLo.toNat]
    && spreadTwoGWords.length == 4

/-- THE WORD WIDTH IS THE STRIDE THE ARTIFACT USES. The pinned batch-inversion
    slice (D:833-843) advances `mptr` by 0x20 per word and bounds the loop
    at `sub(mptr_end, 0x20)`. Rules out `word_bytes` being read as 16 or
    64 while every derived width still looks self-consistent. -/
def wordBytes_matchesBatchInvFixture_ok : Bool :=
  batchInvStride == some templateConstantsDefault.wordBytes

end Midfall.Generator.TemplateKats

#eval Midfall.Generator.TemplateKats.errorSelectors_matchKeccak_ok -- expect true
#eval Midfall.Generator.TemplateKats.errorSelectors_coverDeclaredErrors_ok -- expect true
#eval Midfall.Generator.TemplateKats.frModulus_matchesBlsR_ok -- expect true
#eval Midfall.Generator.TemplateKats.blsPWords_recombine_ok -- expect true
#eval Midfall.Generator.TemplateKats.blsPackedSentinels_ok -- expect true
#eval Midfall.Generator.TemplateKats.includeOrder_matchesFixtureAnchors_ok -- expect true
#eval Midfall.Generator.TemplateKats.includeGraph_disjoint_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkConstructor_matchesGolden_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkConstructor_commitments_matchesExpectedAst_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkConstructor_fixedComms_matchesArtifact_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkConstructor_tokens_matchPinnedStream_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkConstructor_prefixConstants_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkRender_matchesRustTestAssertions_ok -- expect true
#eval Midfall.Generator.TemplateKats.vkConstructor_returnFormula_ok -- expect true
#eval Midfall.Generator.TemplateKats.templateConstants_matchSmokeFixture_ok -- expect true
#eval Midfall.Generator.TemplateKats.templateConstants_matchScalarInvFixture_ok -- expect true
#eval Midfall.Generator.TemplateKats.qvmOp_matchesVmSwitchFixture_ok -- expect true
#eval Midfall.Generator.TemplateKats.g1Double_matchesSpreadFixture_ok -- expect true
#eval Midfall.Generator.TemplateKats.wordBytes_matchesBatchInvFixture_ok -- expect true
