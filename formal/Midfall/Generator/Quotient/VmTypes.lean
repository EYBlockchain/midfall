-- |
-- Midfall.Generator.Quotient.VmTypes
--
-- The QUOTIENT VM VOCABULARY: types and constants, and nothing else. Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs (4336 lines
-- at git HEAD) - QVM:79-552 (the record types and the table-level constants),
-- QVM:554-616 (the 31 opcode constants and the 9 memory-token constants),
-- QVM:618-932 (the opcode / memory-token ABI tables and their two lookups) and
-- QVM:946-1069 (QuotientExpr, QuotientLimbShape, QuotientModarith7Shape,
-- QuotientMem, QuotientLeaf, QuotientProductAdd).
--
-- CITATION NOTATION. Nine prefixes, each named with its file and its line count
-- at HEAD, because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites
-- that silently pointed at the wrong file or at a declaration that does not exist.
-- Every range below was re-derived from `git show HEAD:<path>`, never from wc -l
-- on a dirty checkout (docs/plans/README.md standing note 2).
--
-- * QVM:  proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs
--   (4336 lines at HEAD) - the file this module ports. Working copy and HEAD agree
--   here (git status shows only proofs/solidity-verifier/src/api.rs modified).
-- * QVR:  proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs
--   (549 lines) - the reference interpreter, i.e. PLAN 9.5's QVM.run. It is the
--   reason this file exists; see WHY A VOCABULARY SPLIT below.
-- * DIS:  proofs/solidity-verifier/src/lowering/quotient_numerator/vm/disasm.rs
--   (a fourth consumer of the same numbers; findings F-1 and F-2 below).
-- * LT:   proofs/solidity-verifier/src/lowering/tests.rs (5156 lines) - where the
--   opcode and memory-token table conformance tests actually live (hazard 1).
-- * QL:   proofs/solidity-verifier/src/lowering/quotient_listing/tests.rs
--   (1069 lines) - the "31 opcodes" coverage assertion, QL:852-859.
-- * LM:   proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines) -
--   layout::quotient_limb (LM:351-362) and layout::accumulator (LM:291-304), the
--   right-hand sides of the limb constants, and their own pin test at LM:900-919.
-- * M:    proofs/solidity-verifier/src/lowering/render/models.rs (1494 lines) -
--   the Askama data model, i.e. the Yul-emitter leg of the ABI (M:117-175,
--   M:232-280). Its Lean port is Midfall/Generator/Models.lean.
-- * AP:   proofs/solidity-verifier/src/lowering/abi/proof.rs (537 lines) -
--   ProofCalldataLayout, the argument of RepackedProofLayoutPlan::from_proof_layout.
-- * TPL:  proofs/solidity-verifier/templates/partials/quotient_numerator/
--   QuotientNumeratorBlock.yul (1442 lines) - the Yul interpreter, the third
--   consumer of the opcode numbers. Read from disk by the hazard-1 gates; see
--   GATES AND THE ARTIFACT below.
--
-- WHY A VOCABULARY SPLIT, AND WHERE THE BOUNDARY IS (plan P-09a hazards 4 and 6).
--
-- `reference.rs` - the independent interpreter the certifier runs, and the anchor
-- of all of M6 - imports exactly this vocabulary and nothing else: QVR:36-48 names
-- `QuotientExpr`, `QuotientMem`, `QUOTIENT_VM_LIMBS`, `QUOTIENT_VM_PAIRWISE_COEFFS`,
-- the two `Q_MODARITH7_FLAG_*` constants and all 31 `Q_OP_*` constants. It does not
-- touch the builder. Porting vm/mod.rs whole would make the interpreter wait for
-- 4,336 lines; porting the vocabulary makes it reachable now. That is the whole
-- point of the split, so the boundary here is deliberate and is NOT soft:
--
-- * QVM:1071-4276 (QuotientProgramBuilder, the emit_* and u8/u16/u24 writers, the
--   limb recognizers, the run-compaction pass, the safety validator, the operand
--   walker and the Yul-line reader) is the compiler. Not ported here (hazard 6).
-- * QVM:228-297 (QuotientIdentityParts and its `all_identities` / `manifest`) and
--   QVM:367-489 (QuotientExecutionManifestEntry, `execution_manifest`,
--   `validate_execution_manifest`, `quotient_execution_entry`) are the plan-to-
--   manifest bridge: logic over the plan records, not vocabulary. The records are
--   ported; the bridge is not. `QuotientExecutionKind` is ported because the plan
--   names it, even though nothing in this file consumes it.
-- * QVM:934-944 (`scalar_le_to_be_word`) is a proof-repacking byte helper that
--   sits between the tables and the expression types. Not vocabulary; it belongs
--   with the repacker.
-- * QVM:4277-4336, the `#[cfg(test)] mod tests` of vm/mod.rs itself. Worth saying
--   plainly because plan hazard 1 points at "the opcode and memory-token table
--   conformance tests" and they are NOT here: these two tests
--   (`byte_compaction_groups_mixed_affine_sum_terms`,
--   `byte_validator_rejects_empty_affine_sum_sides`) exercise the run-compaction
--   pass and the byte validator, i.e. the compiler. The conformance tests are in
--   lowering/tests.rs; see HAZARD 1 below.
--
-- HAZARD 1: WHERE THE CONFORMANCE TESTS ARE, AND WHAT IS PORTED FROM THEM.
--
-- `reference.rs`'s own header (QVR:20-26) says the emitter-to-interpreter leg is
-- certified by running the bytecode, and that the INTERPRETER-TO-YUL leg is
-- "covered separately by the opcode and memory-token table conformance tests".
-- Those tests are:
--   * LT:2265-2323 `quotient_vm_opcode_and_token_tables_match_template_cases` -
--     every opcode name in the table must appear in TPL as
--     `case {{ template_constants.quotient_vm.op.<name>|hex() }}`; `case 0x1a`
--     must NOT appear; every memory token must appear as
--     `case {{ template_constants.quotient_vm.mem.<field>|hex() }} { q_ptr := <NAME> }`
--     through the name-to-field map at LT:2290-2301; and the limb counts must
--     equal layout::quotient_limb. Ported as six gates:
--     opcodeTable_matchesYulTemplateCases_ok, opcodeTable_caseCoverageIsExact_ok,
--     opcodeTable_noStaleNativeTrashCase_ok, memTokenTable_matchesYulTemplateCases_ok,
--     memTokenTable_caseCoverageIsExact_ok and limbCounts_crossCheckAccumulatorLimbs_ok.
--   * LT:2325-2339 `quotient_vm_lengths_are_derived_from_opcode_spec` - the
--     instruction walker must return each spec's byte_len. The walker is compiler
--     (QVM:3008-3024), so the walker leg is NOT ported; what IS ported is the
--     table-internal half, which the walker leg depends on:
--     opcodeTable_lengthsAreDerivedFromEncoding_ok and
--     opcodeTable_pinnedByteLengths_ok. The finding that the walker leg is not
--     reachable from a types-only package is recorded in the report, not hidden.
--   * QL:852-859 - a hand-assembled program that must exercise every table entry,
--     asserting `used.len() == QUOTIENT_OPCODE_TABLE.len(), "31 opcodes"`. The
--     program and the decoder are compiler; the COUNT and the DISTINCTNESS that
--     assertion is really about are ported as opcodeTable_is31DistinctOpcodes_ok
--     and opcodeSpec_lookup_ok.
--
-- GATES AND THE ARTIFACT (docs/REVIEW.md R-38 finding 1).
--
-- The four template gates above open TPL from disk at #eval time; nothing in them
-- is a pasted copy of the template. That is a deliberate departure from the
-- transcription-plus-provenance-script pattern Phase 6 had to fall back to, and it
-- is worth stating what it does and does not buy:
--
-- * It DOES buy drift protection in CI. `scripts/kat_gate.py` re-elaborates this
--   file with `lake env lean` on every `scripts/checks.sh` run, so editing or
--   regenerating the template without editing the table reddens the gates. `lake
--   build` alone does NOT re-run them once cached - lake tracks Lean sources, not
--   arbitrary files read by an #eval - so the checks.sh half is load-bearing here.
-- * It fails LOUDLY, not silently, when the artifact is unreachable: every
--   template gate returns false (not true) if the read yields an empty string, and
--   `templateArtifactReachable_ok` is a dedicated gate for exactly that condition,
--   so a wrong path shows up as a named red rather than as a vacuous green.
-- * The path is relative to `formal/`, which is the directory `scripts/checks.sh`
--   cd's into before running kat_gate.py and the directory lake runs in. Two
--   candidates are tried so a build invoked from the repo root also resolves.
--
-- PORT RULES AS THEY APPLY HERE (PLAN section 4, R1-R11).
--
-- * R1 provenance: one Lean def per Rust item, source order except for the moves
--   listed under WHAT MOVED below. No improvements.
-- * R2 names: snake_case to lowerCamelCase; type names kept. Two deviations, both
--   recorded at their sites: `QuotientIdentity::meta` becomes `meta_` (the Lean
--   reserved-word convention the plans README sets and Vk.lean follows), and
--   `QuotientTarget::Selector`'s payload is named `selectorIndex` rather than left
--   anonymous, because the Rust's own doc text calls it `selector_index`
--   (QVM:94-97, and QVM:292 in the manifest helper).
-- * R4 panics: the ported subset contains NO panic site. There is no indexing, no
--   division, no unwrap, no expect and no assert in any def here - the two
--   `Option`-returning lookups use `find?`, which is total. So R4 does not bite
--   this package, and that is a property of the subset, not an oversight: the panics
--   in vm/mod.rs (QVM:1146-1151, 1218, 1477, 1819-1848, 2904-2979) are all in the
--   builder and the validator.
-- * R5 integers: `usize`, `u64`, `u32`, `u16` and `u8` all become `Nat`, and `Nat`
--   does not truncate. Hazard 2 asks for a decision AT EACH SITE and they are not
--   all the same decision, so each width-bearing field carries its own note; the
--   summary is under INTEGER WIDTHS below.
-- * R6 collections: `Vec` becomes `List` (the Generator row, per the plans README).
--   `Vec<u8>` becomes `Midfall.Bytes` - ByteArray - because that is how Vk.lean
--   already models this very record's `bytes` field (QVM:120), and one record must
--   not have two byte representations in one tree. `&'static [T]` table slices also
--   become `List`. `HashMap`/`HashSet` appear only in the unported compiler.
-- * R7/R8/R9: nothing here inverts a field, reads a curve point, is feature-gated
--   except as noted at RepackedProofScalarLayout, or is generic over a trait.
-- * R10: every function over the recursive `QuotientExpr` is structural with an
--   explicit `termination_by`; there is no `partial` in this file.
-- * R11: the line-range table is in the package report.
--
-- WHAT MOVED, AND WHY (Lean is order-sensitive; the reference is not).
--
-- 1. The expression vocabulary (QVM:946-1069) is declared FIRST, before the record
--    types at QVM:79-156 that embed it: `QuotientIdentity.expr` (QVM:155) needs
--    `QuotientExpr`, and `QuotientExpr::Mem` (QVM:957) needs `QuotientMem`, which
--    in the Rust is declared 85 lines LATER at QVM:1038. Within that block the
--    order is QuotientMem, QuotientExpr, QuotientLimbShape, QuotientModarith7Shape,
--    QuotientLeaf, QuotientProductAdd - only QuotientMem moves ahead of
--    QuotientExpr; the rest is source order.
-- 2. `SelectorFoldPlan` (QVM:497-513) moves ahead of `QuotientProgramPlan`
--    (QVM:324), which has a `selector_fold` field (QVM:344).
-- 3. The 31 opcode constants (QVM:567-597), the two MODARITH7 flags (QVM:600-602)
--    and the 9 memory-token constants (QVM:608-616) stay where the Rust puts them -
--    before the tables that name them - but the table-level constants
--    (QVM:515-552) are hoisted to the top of the file, because the tables'
--    `byte_len` expressions and the hazard-5 gate both need the widths and the limb
--    count, and because `QuotientLimbShape`'s arity predicate is stated over
--    `QUOTIENT_VM_LIMBS`.
--
-- INTEGER WIDTHS (hazard 2). The reference profile is release (docs/BASELINE.md
-- "reference profile for the port: release"), so `+` and `*` wrap rather than panic
-- and `debug_assert!` is compiled out, but indexing and division by zero still
-- panic. `as` casts truncate silently in BOTH profiles. Per-site decisions:
--
-- * `QuotientMem::Literal(u32)` (QVM:1040): modelled as unbounded `Nat`. The only
--   producer is QVM:2974, `QuotientMem::Literal(offset as u32)`, where `offset` is
--   a `Value::Integer(isize)` (ENC:588) already guarded by
--   `assert!(offset >= 0)` (QVM:2973). The negative case is a REACHABLE panic in
--   principle and is not modelled here because the conversion function itself is
--   compiler (QVM:2965); the finding is recorded in the report. The >= 2^32 case is
--   a SILENT TRUNCATION, not a panic, and the build-time operand validator does not
--   catch it because it validates the already-truncated value (QVM:2240-2268). It is
--   unreachable in practice: every literal pointer comes from the memory planner,
--   whose bases are word-offsets into a verifier frame measured in kilobytes
--   (LayoutMemory.lean), and `quotientMem_widthsAndFixture_ok` pins the fixture's
--   pointers below 2^32 rather than assuming it. `quotientMem_noTruncation_ok`
--   states the divergence: the Lean model keeps 2^32 and 0 distinct where the Rust
--   would not.
-- * `QuotientMem::Token(u8)` / `TokenOffset(u8, u32)` (QVM:1042, 1044): token is
--   modelled as `Nat` and gated `< 256`. Out-of-width is UNREACHABLE at the token
--   position: the only producer is `quotient_mem_token_from_name` (QVM:2978), which
--   returns one of the nine `Q_MEM_*` constants (QVM:608-616) or panics, and
--   `validate_quotient_mem_token` (QVM:2758-2767) rejects any byte not in the token
--   table before a program is accepted. The offset of `TokenOffset` is the same
--   `isize`-to-`u32` `as` cast as the literal (QVM:2983) with the same reasoning.
-- * `QuotientLimbShape`'s `u16` pointers (QVM:986-995): modelled as `Nat`, and here
--   out-of-width IS reachable and the Rust does NOT truncate - it FALLS BACK.
--   Every producer goes through `u16::try_from(*ptr).ok()?` (QVM:3445, QVM:3506,
--   QVM:4024), so a pointer above 0xffff makes the recognizer return None and the
--   builder emits ordinary Fr opcodes. That is the same mechanism hazard 4 asks
--   about, and `limbPointerU16Boundary_ok` pins the boundary at exactly 0x10000.
-- * `QuotientOpcodeSpec::opcode` and `QuotientMemTokenSpec::token` (QVM:648, 660):
--   `Nat`, gated `< 256` by opcodeTable_is31DistinctOpcodes_ok and
--   quotientMem_widthsAndFixture_ok. Unreachable by construction: every value is one
--   of the named constants, all of which are written as hex literals <= 0x22.
-- * `usize` fields (globalIndex, maxStack, byteLen, numEvals, g1Groups, gaps,
--   tailExponents, maxPower, selectorIndex): `Nat`. None of them is produced by
--   arithmetic that can reach 2^64 in the reference - they are counts of identities,
--   bytes, columns and exponents in a circuit that has to fit a transcript - so R5's
--   "emulate wrapping only where it can actually occur" says do not emulate. Said
--   once here and again at the two sites where a reader might think otherwise
--   (`RepackedProofLayoutPlan.compressedLen` and `SelectorFoldPlan.maxPower`).
-- * `U256` becomes `Midfall.Word256` (BitVec 256), the Generator row's model
--   (Api.lean:67-80, Encoding.lean:87). This is the one place the port is NARROWER
--   than `Nat` would be, and deliberately so: `Word256` cannot hold an out-of-width
--   constant, so hazard 2's "do not silently widen" is satisfied structurally for
--   every coefficient field rather than by a gate.
--
-- DERIVATIONS ADDED ON THE LEAN SIDE, RECORDED NOT SILENT.
--
-- * `BEq` is derived on `QuotientLimbShape`, `QuotientModarith7Shape`,
--   `QuotientLeaf`, `QuotientProductAdd`, `QuotientIdentity`, `QuotientProgramItem`
--   and `QuotientProgramPlan`, where the Rust derives only `Clone, Debug`
--   (QVM:144, 167, 305, 323, 972, 1021, 1047, 1061). The Rust never compares those
--   types; the gates here must. Where the Rust DOES derive `PartialEq, Eq`
--   (QVM:84, 102, 159, 348, 623, 643, 655, 663, 952, 1037) the derivation matches.
-- * `QuotientLimbShape.wellFormed`, `QuotientLimbShapeEmit` and
--   `quotientLimbShapeEmit` have no single Rust counterpart: they are the
--   recognizers' length guards (QVM:3667, QVM:3714, QVM:3753, QVM:3776) and the
--   builder's two-arm dispatch (QVM:3165-3172, QVM:3199-3207) extracted as
--   vocabulary-level predicates, so hazard 4 can be gated without importing the
--   compiler. Each says so at its site.
-- * `renderedOpcodeConstants` / `renderedMemTokenConstants` are the field list of
--   M:233-276 addressed by name, i.e. the Yul-emitter leg expressed as data so it
--   can be compared with the table.

import Midfall.Common.Bytes
import Midfall.Generator.Abi
import Midfall.Generator.Api
import Midfall.Generator.Layout
import Midfall.Generator.Models

namespace Midfall.Generator

/-! ## Table-level constants (rust: QVM:515-552) - MOVED to the top; see WHAT MOVED 3 -/

/-- rust: QVM:515-516 (`QUOTIENT_EXTERNAL_MAGIC: u64 = 0x5155_4556_414c_0001`)
    @formal-baseline. The "magic/version word returned by a split quotient
    evaluator". `u64` is `Nat` (R5): nothing here adds to or shifts it, so the two
    readings cannot differ. -/
def quotientExternalMagic : Nat := 0x5155_4556_414c_0001

/-- rust: QVM:548 (`QUOTIENT_VM_LIMBS: usize = layout::quotient_limb::LIMBS`)
    @formal-baseline. The right-hand side is LM:355, whose own doc says it
    "Matches the accumulator/public-input BLS12-381 base-field limb packing" -
    i.e. this 7 is the SAME 7 as `layout::accumulator::LIMBS` (LM:297), which is
    what makes plan hazard 5's cross-check meaningful rather than decorative.
    `quotientVmLimbs_agreesWithAccumulatorLimbs_ok` is that cross-check.

    LANDING NOTE: LM:351-362 is the Layout row's content and Layout.lean does not
    port it. Landing the four numbers here through the QVM re-export is the same
    call Api.lean:142-143 (finding F-2) made for the LM accumulator constants. -/
def quotientVmLimbs : Nat := 7

/-- rust: QVM:550 (`QUOTIENT_VM_PAIRWISE_TERMS: usize =
    layout::quotient_limb::PAIRWISE_TERMS`) @formal-baseline. LM:359 defines it as
    `LIMBS * LIMBS`; the literal is what LM:917 pins. -/
def quotientVmPairwiseTerms : Nat := 49

/-- rust: QVM:552 (`QUOTIENT_VM_PAIRWISE_COEFFS: usize =
    layout::quotient_limb::PAIRWISE_COEFFS`) @formal-baseline. LM:361 defines it as
    `2 * LIMBS - 1`; LM:918 pins 13. -/
def quotientVmPairwiseCoeffs : Nat := 13

/-- rust: LM:357 (`layout::quotient_limb::LIN_COEFFS: usize = LIMBS - 1`)
    @formal-baseline. Not a QVM item: it is the array length of the two coefficient
    lists below (QVM:521, QVM:530), so it has to be nameable here. Landing it in
    this file rather than Layout.lean follows the QVM:548 note above. -/
def quotientLimbLinCoeffs : Nat := 6

/-- rust: QVM:539-540 (`QUOTIENT_VM_RUN_COMPACTION_MIN_LEN: usize = 4`)
    @formal-baseline. "Minimum adjacent fused-op run worth replacing with a run
    opcode." Consumed by the unported compaction pass at QVM:1917 and QVM:1932. -/
def quotientVmRunCompactionMinLen : Nat := 4

/-- rust: QVM:541-542 (`QUOTIENT_VM_BYTE_U16_BYTES: usize = 2`) @formal-baseline.
    "Encoded byte width of a `u16` operand." -/
def quotientVmByteU16Bytes : Nat := 2

/-- rust: QVM:543-544 (`QUOTIENT_VM_BYTE_U24_BYTES: usize = 3`) @formal-baseline.
    "Encoded byte width of the selector-fold `(selector_index, gap)` operand." -/
def quotientVmByteU24Bytes : Nat := 3

/-- rust: QVM:545-546 (`QUOTIENT_VM_BYTE_U32_BYTES: usize = 4`) @formal-baseline.
    "Encoded byte width of absolute memory pointers and token offsets." This is the
    width hazard 2 is about: 4 bytes is 2^32 pointers, and the producer truncates
    into it with `as u32` (QVM:2974). See INTEGER WIDTHS in the header. -/
def quotientVmByteU32Bytes : Nat := 4

/-- rust: QVM:517-528 (`LIMB7_YUL_COEFFS: [&str; layout::quotient_limb::LIN_COEFFS]`)
    @formal-baseline. The header comment (QVM:517-520) is the important part for
    this package: these coefficients belong to the DIRECT and NATIVE Yul paths, not
    to the VM - "The VM limb opcodes do not hard-code these values; they load the
    corresponding Fr constants from the VK payload". So they are ported as data and
    nothing here evaluates them. `&str` becomes `String`; the array length is
    `quotientLimbLinCoeffs`. -/
def limb7YulCoeffs : List String :=
  ["0x100000000000000", "0x10000000000000000000000000000", "0x400000000",
   "0x40000000000000000000000", "0x1000", "0x100000000000000000"]

/-- rust: QVM:529-537 (`WIDE_LIMB7_YUL_COEFFS: [&str;
    layout::quotient_limb::LIN_COEFFS]`) @formal-baseline. "Coefficients for
    seven-term windows in the wide pairwise-product limb basis." Same status as
    `limb7YulCoeffs`: rendered data, not VM operands. -/
def wideLimb7YulCoeffs : List String :=
  ["0x100000000000000", "0x10000000000000000000000000000",
   "0x1000000000000000000000000000000000000000000",
   "0x10000000000000000000000000000000000000000000000000000000",
   "0x6bc66e553973f396854f5626172ba135587d41e37a68209402355093fdcaaf6c",
   "0x63f31e3f446953960c9d6964474300df43ab29179970f642a28e39d6c883c74b"]

/-! ## The expression vocabulary (rust: QVM:946-1069) - MOVED ahead of the records;
see WHAT MOVED 1 -/

/-- rust: QVM:1032-1045 (`enum QuotientMem`) @formal-baseline. Moved ahead of
    `QuotientExpr` (QVM:953), which embeds it at QVM:957.

    "Compact reference to a verifier memory word. Literal pointers are encoded
    directly when they fit. Tokens represent generated Yul symbols whose concrete
    address can change with the memory layout; token offsets support structured
    regions rooted at those symbols."

    Hazard 2, per constructor: `literal` is the Rust's `u32` (QVM:1040) and is
    modelled unbounded - see INTEGER WIDTHS, and `quotientMem_noTruncation_ok` for
    the divergence this admits. `token` is `u8` (QVM:1042) and out-of-width is
    unreachable there (the producer panics instead, QVM:2978-2979).
    `tokenOffset`'s second field is `u32` (QVM:1044), same reasoning as `literal`.

    The Rust derives `Clone, Copy, Debug, PartialEq, Eq, Hash` (QVM:1037); `BEq`
    covers the equality half and Lean has no `Hash` obligation to mirror. -/
inductive QuotientMem
  /-- rust: QVM:1039-1040 (`Literal(u32)`) - "Absolute memory pointer." -/
  | literal (ptr : Nat)
  /-- rust: QVM:1041-1042 (`Token(u8)`) - "Generated memory symbol token." -/
  | token (token : Nat)
  /-- rust: QVM:1043-1044 (`TokenOffset(u8, u32)`) - "Generated memory symbol token
      plus byte offset." -/
  | tokenOffset (token : Nat) (offset : Nat)
  deriving BEq

/-- rust: QVM:946-964 (`enum QuotientExpr`) @formal-baseline.

    "Field-expression AST accepted by the quotient VM builder. This is a
    deliberately tiny subset of Halo2 expressions and generated Yul: constants,
    verifier-memory loads, and Fr addition/multiplication/negation. Keeping the
    tree this small makes bytecode lowering auditable and lets the structural limb
    recognizers operate without depending on gate names."

    Hazard 3: the Rust recurses through `Box` (QVM:959-963) for stack-size reasons
    only; Lean needs no box and the constructors take the subtrees directly. Every
    function over this type in this file is structural with an explicit
    `termination_by` (R10) - there is no `partial` anywhere in this file - and the
    gate fixtures stay shallow, with the depth that is NOT being tested named at the
    gate. -/
inductive QuotientExpr
  /-- rust: QVM:954-955 (`Const(U256)`) - "Native Fr constant encoded as a `U256`." -/
  | const (value : Word256)
  /-- rust: QVM:956-957 (`Mem(QuotientMem)`) - "Memory-backed verifier value." -/
  | mem (mem : QuotientMem)
  /-- rust: QVM:958-959 (`Add(Box<QuotientExpr>, Box<QuotientExpr>)`) - "Fr addition
      modulo the scalar field." -/
  | add (lhs rhs : QuotientExpr)
  /-- rust: QVM:960-961 (`Mul(Box<QuotientExpr>, Box<QuotientExpr>)`) - "Fr
      multiplication modulo the scalar field." -/
  | mul (lhs rhs : QuotientExpr)
  /-- rust: QVM:962-963 (`Neg(Box<QuotientExpr>)`) - "Fr negation modulo the scalar
      field." -/
  | neg (inner : QuotientExpr)
  deriving BEq

/-- rust: QVM:966-997 (`enum QuotientLimbShape`) @formal-baseline.

    The doc comment is the safety property plan hazard 4 names, and it is quoted in
    full because the gates below are written against it:

    ```text
    Structural foreign-field limb shapes compressed by dedicated opcodes.

    These are recognized from the expression tree alone. That constraint is
    important: adding a limb opcode must never make correctness depend on a
    gate label or on a hand-maintained list of circuit gadgets. If a shape is
    not recognized exactly, the builder falls back to ordinary Fr VM opcodes.
    ```

    Two things follow, and both are gated. (a) No variant carries a name, a gate
    label or a circuit identifier: every payload is a coefficient (`U256`) or a
    memory pointer (`u16`), which `limbShapeCarriesNoGateLabel_ok` pins by
    destructuring each variant field-by-field so a future label-typed field stops
    compilation instead of slipping past a sample. (b) The arity is NOT part of the
    type: `terms` is a `Vec`, so a 6-term or 8-term `Lin7` is representable here
    and in Rust alike. `limbShapeArityNotEnforcedByType_ok` demonstrates that on
    purpose, and `limbShapeMisRecognition_fallsBack_ok` gates the fallback arm.
    Whether that is a guarantee or an intention is hazard 4's report, and the answer
    is: the recognizers enforce it (QVM:3667, 3714, 3753), the type does not, and
    `emit_limb_shape` (QVM:1466-1516) does not re-check it either. -/
inductive QuotientLimbShape
  /-- rust: QVM:985-987 (`Lin7 { terms: Vec<(U256, u16)> }`). One term per limb:
      a constant-table coefficient and the `u16` pointer holding that limb. -/
  | lin7 (terms : List (Word256 × Nat))
  /-- rust: QVM:988-991 (`Bilin7Row { lhs: u16, terms: Vec<(U256, u16)> }`) - one
      repeated limb times a seven-limb row. -/
  | bilin7Row (lhs : Nat) (terms : List (Word256 × Nat))
  /-- rust: QVM:992-996 (`Bilin7Pairwise { lhs_base: u16, rhs_base: u16,
      coeffs: Vec<U256> }`) - the full 7x7 grid folded onto its 13 `i + j`
      diagonals. -/
  | bilin7Pairwise (lhsBase rhsBase : Nat) (coeffs : List Word256)
  deriving BEq

/-- rust: QVM:999-1030 (`struct QuotientModarith7Shape`) @formal-baseline. The
    bundled form of the same structural blocks, "plus scalar memory terms and an
    optional outer condition", and - per its own doc - it "deliberately remains
    expression-shaped rather than gate-name-shaped".

    R2 note: these seven fields are PRIVATE in Rust (no `pub(crate)`, unlike every
    other record in this file), because only the unported builder reads them
    (QVM:1520-1596). Lean has no module-private field, so they are public here and
    that is a widening of visibility, not of content. -/
structure QuotientModarith7Shape where
  /-- rust: QVM:1023 (`cond: Option<u16>`) - the outer condition's memory pointer. -/
  cond : Option Nat
  /-- rust: QVM:1024 (`constant: U256`) -/
  constant : Word256
  /-- rust: QVM:1025 (`lin: Vec<Vec<(U256, u16)>>`) - nested linear blocks. -/
  lin : List (List (Word256 × Nat))
  /-- rust: QVM:1026 (`rows: Vec<(u16, Vec<(U256, u16)>)>`) -/
  rows : List (Nat × List (Word256 × Nat))
  /-- rust: QVM:1027 (`pairwise: Vec<(u16, u16, Vec<U256>)>`) -/
  pairwise : List (Nat × Nat × List Word256)
  /-- rust: QVM:1028 (`mem_terms: Vec<(U256, u16)>`) -/
  memTerms : List (Word256 × Nat)
  /-- rust: QVM:1029 (`product_terms: Vec<(U256, u16, u16)>`) -/
  productTerms : List (Word256 × Nat × Nat)
  deriving BEq

/-- rust: QVM:1047-1053 (`enum QuotientLeaf`) @formal-baseline. The two
    non-recursive shapes of the expression grammar, used by the unported accumulator
    emitters (QVM:1767-1800). Rust derives `Clone, Copy, Debug` only; `BEq` is
    added for the gates (see DERIVATIONS ADDED). -/
inductive QuotientLeaf
  /-- rust: QVM:1049-1050 (`Const(U256)`) - "Constant leaf." -/
  | const (value : Word256)
  /-- rust: QVM:1051-1052 (`Mem(QuotientMem)`) - "Memory leaf." -/
  | mem (mem : QuotientMem)
  deriving BEq

/-- rust: QVM:1055-1069 (`enum QuotientProductAdd`) @formal-baseline. "Fused
    `top += product` forms recognized during expression emission ... Encoding them
    as accumulator operations avoids push/load/mul/add sequences and is still easy to
    reason about because the VM stack effect is exactly zero."

    The three variants are the same three shapes the opcode table names
    `AddMulMemMemConstU8`, `AddMulConstU8MemU16` and `AddMulMemMem` (QVM:631-633),
    which `productAdd_matchesFusedOpcodeEncodings_ok` pins: the two lists are a
    hand-maintained pair, and a rename on one side is invisible to the compiler. -/
inductive QuotientProductAdd
  /-- rust: QVM:1063 (`MemMemConstU8 { lhs: u16, rhs: u16, scalar: U256 }`) -
      `top += mload(lhs) * mload(rhs) * const`. -/
  | memMemConstU8 (lhs rhs : Nat) (scalar : Word256)
  /-- rust: QVM:1065-1066 (`ConstU8Mem { scalar: U256, ptr: u16 }`) -
      `top += const * mload(ptr)`. -/
  | constU8Mem (scalar : Word256) (ptr : Nat)
  /-- rust: QVM:1067-1068 (`MemMem { lhs: u16, rhs: u16 }`) -
      `top += mload(lhs) * mload(rhs)`. -/
  | memMem (lhs rhs : Nat)
  deriving BEq

/-- Memory leaves of a tree, left to right. A modelling helper rather than a Rust
    item (see DERIVATIONS ADDED): the recognizers reach the same leaves through
    `quotient_mem_term` (QVM:4004-4026) while collecting Fr coefficients, which is
    compiler work this package does not do. Total by structure (R10), which is the
    hazard-3 claim made concrete. -/
def QuotientExpr.memLeaves (e : QuotientExpr) : List QuotientMem :=
  match e with
  | .const _ => []
  | .mem m => [m]
  | .add lhs rhs => lhs.memLeaves ++ rhs.memLeaves
  | .mul lhs rhs => lhs.memLeaves ++ rhs.memLeaves
  | .neg inner => inner.memLeaves

/-- Node count of a tree: it recurses through exactly the `Box` positions the Rust
    allocates (QVM:959-963), so it is the shape a structural fold has to survive.
    Modelling helper, same status as `QuotientExpr.memLeaves`. -/
def QuotientExpr.nodeCount (e : QuotientExpr) : Nat :=
  match e with
  | .const _ => 1
  | .mem _ => 1
  | .add lhs rhs => 1 + lhs.nodeCount + rhs.nodeCount
  | .mul lhs rhs => 1 + lhs.nodeCount + rhs.nodeCount
  | .neg inner => 1 + inner.nodeCount

/-- rust: the arity guards inside the recognizers - QVM:3667
    (`grouped.len() != QUOTIENT_VM_LIMBS`), QVM:3714 (`grouped.len() ==
    QUOTIENT_VM_LIMBS`), QVM:3753 (`pairs.len() != QUOTIENT_VM_PAIRWISE_TERMS`) and
    the diagonal count implied by QVM:3780 (`vec![None; QUOTIENT_VM_PAIRWISE_COEFFS]`).

    NOT a Rust item: it is those guards lifted out of the recognizers so the
    invariant they enforce can be stated against the type. The recognizers
    themselves (QVM:3156-3227, 3649-3813) are compiler and are not ported (hazard 6). -/
def QuotientLimbShape.wellFormed (shape : QuotientLimbShape) : Bool :=
  match shape with
  | .lin7 terms => terms.length == quotientVmLimbs
  | .bilin7Row _ terms => terms.length == quotientVmLimbs
  | .bilin7Pairwise _ _ coeffs => coeffs.length == quotientVmPairwiseCoeffs

/-- The two arms the builder chooses between, as data: the fused limb opcode for a
    recognized shape, or the ordinary Fr VM opcodes. Rust: the `Option` returns of
    `quotient_limb_shape` (QVM:3157-3173) and `quotient_limb_subshape`
    (QVM:3190-3227), whose `None` arms are the fallback the doc at QVM:970-971
    promises. Not a Rust item; see `QuotientLimbShape.wellFormed`. -/
inductive QuotientLimbShapeEmit
  /-- The fused limb opcode is emitted for this shape. -/
  | fused (shape : QuotientLimbShape)
  /-- Ordinary Fr VM opcodes: the fallback, which is always available because ADD,
      MUL, NEG, PUSH_* and the constant loads do not depend on the limb count. -/
  | generic
  deriving BEq

/-- The dispatch: a shape that is not recognized exactly - which includes a shape
    recognized with the wrong arity - must fall back, and must never be emitted as a
    fused opcode. This is hazard 4's safety property in the only form a types-only
    package can state it. -/
def quotientLimbShapeEmit (shape : Option QuotientLimbShape) : QuotientLimbShapeEmit :=
  match shape with
  | none => .generic
  | some s => if s.wellFormed then .fused s else .generic

/-- The memory pointers a limb shape addresses, so the "recognized from the
    expression tree alone" claim can be destructured field by field instead of
    sampled. Modelling helper. -/
def QuotientLimbShape.pointerOperands (shape : QuotientLimbShape) : List Nat :=
  match shape with
  | .lin7 terms => terms.map (fun (_, ptr) => ptr)
  | .bilin7Row lhs terms => lhs :: terms.map (fun (_, ptr) => ptr)
  | .bilin7Pairwise lhsBase rhsBase _ => [lhsBase, rhsBase]

/-- The coefficients a limb shape addresses (the `U256` half of each term). -/
def QuotientLimbShape.coefficientOperands (shape : QuotientLimbShape) : List Word256 :=
  match shape with
  | .lin7 terms => terms.map (fun (coeff, _) => coeff)
  | .bilin7Row _ terms => terms.map (fun (coeff, _) => coeff)
  | .bilin7Pairwise _ _ coeffs => coeffs

/-- rust: QVM:1055-1069 read against QVM:631-633. Modelling helper: it exists so
    `productAdd_matchesFusedOpcodeEncodings_ok` can compare the two hand-maintained
    lists of the same three fused shapes. -/
def QuotientProductAdd.encoding (product : QuotientProductAdd) : String :=
  match product with
  | .memMemConstU8 _ _ _ => "add_mul_mem_mem_const_u8"
  | .constU8Mem _ _ => "add_mul_const_u8_mem_u16"
  | .memMem _ _ => "add_mul_mem_mem"

/-- The pointers a MODARITH7 shape addresses, i.e. the payload the unported
    `emit_modarith7_shape` (QVM:1520-1596) writes. Modelled here so the "no gate
    label" claim covers MODARITH7 too and not only the three `QuotientLimbShape`
    variants. Modelling helper. -/
def QuotientModarith7Shape.pointerOperands (shape : QuotientModarith7Shape) : List Nat :=
  shape.cond.toList
    ++ (shape.lin.flatMap fun block => block.map (fun (_, ptr) => ptr))
    ++ (shape.rows.flatMap fun (lhs, terms) => lhs :: terms.map (fun (_, ptr) => ptr))
    ++ (shape.pairwise.flatMap fun (lhs, rhs, _) => [lhs, rhs])
    ++ (shape.memTerms.map (fun (_, ptr) => ptr))
    ++ (shape.productTerms.map (fun (_, lhs, _) => lhs) ++
        shape.productTerms.map (fun (_, _, rhs) => rhs))

/-- The constant-table values a MODARITH7 shape references: what QVM:3533-3552
    (`modarith7_coeffs`) collects. Modelling helper. -/
def QuotientModarith7Shape.coefficientOperands
    (shape : QuotientModarith7Shape) : List Word256 :=
  shape.constant
    :: (shape.lin.flatMap fun block => block.map (fun (coeff, _) => coeff))
    ++ (shape.rows.flatMap fun (_, terms) => terms.map (fun (coeff, _) => coeff))
    ++ (shape.pairwise.flatMap fun (_, _, coeffs) => coeffs)
    ++ (shape.memTerms.map (fun (coeff, _) => coeff))
    ++ (shape.productTerms.map (fun (coeff, _, _) => coeff))


/-! ## Identity and plan records (rust: QVM:79-552) -/

/-- rust: QVM:79-99 (`enum QuotientTarget`) @formal-baseline. "Destination of one
    evaluated quotient identity. Each identity occupies exactly one position in the
    global `y` batch. The target only decides where the evaluated scalar is
    accumulated after that position has been consumed." -/
inductive QuotientTarget
  /-- rust: QVM:86-91 (`Main`) - "Fully evaluated identity. The value contributes
      to the reconstructed numerator scalar. After the whole stream has been
      consumed, the Yul runtime stores the negation in `QUOTIENT_EVAL_MPTR`." -/
  | main
  /-- rust: QVM:92-98 (`Selector(usize)`) - "Simple-selector identity. The `usize`
      is an index into the sorted simple-selector column list, not the fixed-column
      index itself." Payload named `selectorIndex` per the R2 note in the header;
      `usize` is `Nat` and is an index, so out-of-width is unreachable. -/
  | selector (selectorIndex : Nat)
  deriving BEq

/-- rust: QVM:101-108 (`struct QuotientIdentityMetadata`) @formal-baseline.
    "Source metadata for one internal quotient identity." `source` is the api.rs
    enum, already ported at Api.lean:693-706; this file reuses it rather than
    re-declaring it, which is one of the two reasons this package imports
    `Midfall.Generator.Api` (the other is `AccumulatorEncoding.supportedNumLimbs`
    for the hazard-5 cross-check). -/
structure QuotientIdentityMetadata where
  /-- rust: QVM:104-105 (`global_index: usize`) - "Position in the global
      `y`-batch." -/
  globalIndex : Nat
  /-- rust: QVM:106-107 (`source: QuotientIdentitySource`) - "Source family and
      source-local metadata." -/
  source : QuotientIdentitySource
  deriving BEq

/-- rust: QVM:110-137 (`struct QuotientProgramBuild`) @formal-baseline. "Complete
    VM artifact emitted into the generated verifying-key payload."

    `bytes` is `Vec<u8>` modelled as `Bytes` (ByteArray), matching the projection
    Vk.lean:385-387 already lands for this same record; Vk.lean's `VkQuotientBuild`
    is the two-field view vk.rs reads and its doc says it "should become an alias of
    [the full record] when it lands". It has landed; making it one is a Vk.lean edit,
    which this package does not own (plans README: "Do not edit a file another package
    owns"). Finding F-4 in the report. -/
structure QuotientProgramBuild where
  /-- rust: QVM:119-120 (`bytes: Vec<u8>`) - "Encoded byte-oriented bytecode." -/
  bytes : Bytes
  /-- rust: QVM:121-122 (`consts: Vec<U256>`) - "Deduplicated Fr constants
      addressed by `PUSH_CONST` and fused opcodes." -/
  consts : List Word256
  /-- rust: QVM:123-128 (`max_stack: usize`) - "Maximum operand-stack depth of the
      pure interpreted bytecode. Native callbacks may reuse the same stack base as
      structured scratch, so the generator folds their scratch requirement into the
      final allocation separately." Produced by the unported builder (QVM:1085). -/
  maxStack : Nat
  /-- rust: QVM:129-133 (`used_ops: Vec<u8>`) - "Opcode bytes actually present in
      the finalized physical program. The template uses this to render only the
      interpreter cases reachable by this VK-specialized quotient program." -/
  usedOps : Bytes
  /-- rust: QVM:134-136 (`used_mem_tokens: Vec<u8>`) - "Memory-token operands
      actually present in the finalized physical program." -/
  usedMemTokens : Bytes
  deriving BEq

/-- rust: QVM:139-156 (`struct QuotientIdentity`) @formal-baseline. "One Halo2
    quotient identity in both native-Yul and VM-ready forms. The normal evaluator
    still emits assignment lines because direct inline paths and native callbacks
    reuse them. `expr` is built once during quotient planning and is the single
    source for compact VM bytecode emission."

    R2 reserved word: `meta` becomes `meta_`, the convention Vk.lean:945 and
    LayoutMemory.lean:29-30 set (the plans README: `meta` cannot even be a `let`
    binder in Lean 4.35). -/
structure QuotientIdentity where
  /-- rust: QVM:146-147 (`meta: QuotientIdentityMetadata`) - "Host-side diagnostic
      metadata for this identity." -/
  meta_ : QuotientIdentityMetadata
  /-- rust: QVM:148-149 (`lines: Vec<String>`) - "Yul assignment lines emitted by
      the existing evaluator." -/
  lines : List String
  /-- rust: QVM:150-151 (`var: String`) - "Name of the Yul variable holding the
      final identity evaluation." -/
  var : String
  /-- rust: QVM:152-153 (`target: QuotientTarget`) - "Accumulator target for this
      identity." -/
  target : QuotientTarget
  /-- rust: QVM:154-155 (`expr: QuotientExpr`) - "Typed expression form used by the
      VM." -/
  expr : QuotientExpr
  deriving BEq

/-- rust: QVM:158-165 (`struct RepackedProofScalarLayout`) @formal-baseline.

    R8: this one is `#[cfg(all(test, feature = "evm"))]` (QVM:158). `evm` is ON in
    the recorded profile (BASELINE.md), but `test` is not a build feature this port
    models, so the rule adopted is the one Api.lean:104-108 applies to its own
    cfg-gated item: port it, say it is test-only, and note that its only Rust caller
    is `scalar_layout` (QVM:212-225), which is itself gated the same way. The plan
    names this record, so it is here. -/
structure RepackedProofScalarLayout where
  /-- rust: QVM:161 (`eval_offset: usize`) -/
  evalOffset : Nat
  /-- rust: QVM:162 (`num_evals: usize`) -/
  numEvals : Nat
  /-- rust: QVM:163 (`q_eval_offset: usize`) -/
  qEvalOffset : Nat
  /-- rust: QVM:164 (`num_point_sets: usize`) -/
  numPointSets : Nat
  deriving BEq

/-- rust: QVM:167-175 (`struct RepackedProofLayoutPlan`) @formal-baseline. -/
structure RepackedProofLayoutPlan where
  /-- rust: QVM:169-170 (`g1_groups: Vec<usize>`) - "Counts of compressed G1
      commitments read before scalar evaluations." -/
  g1Groups : List Nat
  /-- rust: QVM:171-172 (`num_evals: usize`) - "Number of ordinary evaluation
      scalars." -/
  numEvals : Nat
  /-- rust: QVM:173-174 (`num_point_sets: usize`) - "Number of quotient-opening
      point-set scalars." -/
  numPointSets : Nat
  deriving BEq

/-- rust: QVM:177-187 (`RepackedProofLayoutPlan::from_proof_layout`)
    @formal-baseline. "Build a proof repacking plan from the typed Solidity
    calldata layout." `ProofCalldataLayout` is Abi.lean:209-235 and
    `commitment_read_groups` is Abi.lean:472-480, so this is the one place this
    package reaches another row's port for a constructor argument. -/
def RepackedProofLayoutPlan.fromProofLayout (layout : ProofCalldataLayout) :
    RepackedProofLayoutPlan :=
  { g1Groups := layout.commitmentReadGroups
    numEvals := layout.evals.itemCount
    numPointSets := layout.qEvals.itemCount }

/-- rust: QVM:188-192 (`prefix_g1_count`) @formal-baseline. "Number of compressed
    G1 points before the scalar eval block." `iter().sum()` over a `Vec<usize>` is
    an order-independent fold, so `List.foldl` is exact (R6). -/
def RepackedProofLayoutPlan.prefixG1Count (self : RepackedProofLayoutPlan) : Nat :=
  self.g1Groups.foldl (fun acc n => acc + n) 0

/-- rust: QVM:193-201 (`compressed_len`) @formal-baseline. "Native compressed proof
    byte length expected by the repacker." The five-term shape - prefix G1s, the eval
    block, one trailing G1, the point-set block, one more trailing G1 - is what
    `repackedProofLayout_arithmetic_ok` pins with pairwise DISTINCT counts, so a
    dropped term or a swapped stride cannot hide behind equal numbers. R5: `usize`
    addition, which wraps in the release profile and does not here; 2^64 proof bytes
    are not reachable in a calldata-shaped structure, so no wrapping is emulated. -/
def RepackedProofLayoutPlan.compressedLen (self : RepackedProofLayoutPlan) : Nat :=
  self.prefixG1Count * g1CompressedBytes + self.numEvals * wordBytes
    + g1CompressedBytes + self.numPointSets * wordBytes + g1CompressedBytes

/-- rust: QVM:203-210 (`repacked_len`) @formal-baseline. "Solidity-facing
    EIP-2537-padded proof byte length after repacking." The only difference from
    `compressedLen` is the G1 width: `G1_BYTES` (128, the EIP-2537 padded form)
    against `G1_COMPRESSED_BYTES` (48). Swapping those two is the mistake this pair
    of defs exists to make testable - see `repackedProofLayout_widthsDiffer_ok`. -/
def RepackedProofLayoutPlan.repackedLen (self : RepackedProofLayoutPlan) : Nat :=
  self.prefixG1Count * g1Bytes + self.numEvals * wordBytes
    + g1Bytes + self.numPointSets * wordBytes + g1Bytes

/-- rust: QVM:212-225 (`scalar_layout`) @formal-baseline. "Return scalar offsets
    within the repacked proof for tests." Test-only in the same sense as
    `RepackedProofScalarLayout`. The two offsets are the first two partial sums of
    `repackedLen`, which `repackedProofLayout_scalarOffsetsConsistent_ok` asserts
    rather than assumes: if the two defs ever disagree about the frame shape, the
    offsets and the length cannot both be right. -/
def RepackedProofLayoutPlan.scalarLayout (self : RepackedProofLayoutPlan) :
    RepackedProofScalarLayout :=
  let evalOffset := self.prefixG1Count * g1Bytes
  let qEvalOffset := evalOffset + self.numEvals * wordBytes + g1Bytes
  { evalOffset := evalOffset
    numEvals := self.numEvals
    qEvalOffset := qEvalOffset
    numPointSets := self.numPointSets }

/-- rust: QVM:299-315 (`enum QuotientProgramItem`) @formal-baseline. "Logical
    stream item before final bytecode lowering. Native items are not arithmetic
    opcodes in the Rust builder. They are identity-position markers; the Yul template
    replaces them with generated callback blocks that perform their own evaluation
    and fold at exactly the same point in the global `y` batch." -/
inductive QuotientProgramItem
  /-- rust: QVM:307-308 (`Identity(QuotientIdentity)`) - "Identity interpreted by
      the compact VM." -/
  | identity (identity : QuotientIdentity)
  /-- rust: QVM:309-310 (`NativePermutation`) - "Generated callback for the whole
      permutation identity block." -/
  | nativePermutation
  /-- rust: QVM:311-312 (`NativeLookup`) - "Generated callback for the whole lookup
      identity block." -/
  | nativeLookup
  /-- rust: QVM:313-314 (`NativeIdentity(usize)`) - "Generated callback for a
      selected heavy gate identity." -/
  | nativeIdentity (nativeIndex : Nat)
  deriving BEq

/-- rust: QVM:347-365 (`enum QuotientExecutionKind`) @formal-baseline. "Execution
    surface used to fold an identity."

    This is the THIRD copy of this shape in the reference: `QuotientIdentityExecution`
    (API:286-303, ported at Api.lean:665-686) has the same six variants in the same
    order with the same payload, and nothing in the Rust ties them - the manifest
    conversion at QVM:478-489 copies the value through a parameter, so a divergence
    between the two enums is invisible to `cargo check`.
    `executionKind_agreesWithQuotientIdentityExecution_ok` is that tie, and finding
    F-3 in the report names it as a duplicate-ABI hazard of the same family as F-1. -/
inductive QuotientExecutionKind
  /-- rust: QVM:350-351 (`Inline`) - "Direct Yul emitted before the VM loop." -/
  | inline
  /-- rust: QVM:352-353 (`Interpreted`) - "Compact VM bytecode expression followed
      by a fold opcode." -/
  | interpreted
  /-- rust: QVM:354-355 (`NativePermutation`) - "Native callback replacing the full
      permutation identity range." -/
  | nativePermutation
  /-- rust: QVM:356-357 (`NativeLookup`) - "Native callback replacing the full
      lookup identity range." -/
  | nativeLookup
  /-- rust: QVM:358-362 (`NativeIdentity { native_index }`) - "Native callback
      replacing one selected heavy gate identity." -/
  | nativeIdentity (nativeIndex : Nat)
  /-- rust: QVM:363-364 (`StructuredTail`) - "Structured Yul emitted after the VM
      loop." -/
  | structuredTail
  deriving BEq

/-- rust: QVM:491-513 (`struct SelectorFoldPlan` and its `gap_for`)
    @formal-baseline. Moved ahead of `QuotientProgramPlan` (QVM:324), which has a
    field of this type at QVM:343-344; see WHAT MOVED 2.

    "Codegen-time selector-bucket schedule for gap-based forward folding. Fully
    evaluated identities still use the ordinary Horner scan. Selector identities are
    sparse in that global stream, so each selector bucket only needs to be advanced
    across the gap since the previous identity for the same selector and then across
    the final tail after the stream ends." -/
structure SelectorFoldPlan where
  /-- rust: QVM:499-500 (`gaps_by_identity: Vec<Option<usize>>`) - "`Some(gap)` for
      selector identities by global identity index." -/
  gapsByIdentity : List (Option Nat)
  /-- rust: QVM:501-502 (`tail_exponents: Vec<usize>`) - "Final y-power tail for
      each selector bucket." -/
  tailExponents : List Nat
  /-- rust: QVM:503-504 (`max_power: usize`) - "Largest exponent referenced by
      either gaps or tails." R5: an exponent count in a circuit that fits a
      transcript, so no wrapping is emulated; it is also the runtime guard the Yul
      checks against (LT:2446, `program.selector_max_power`). -/
  maxPower : Nat
  deriving BEq

/-- The `#[derive(Default)]` of QVM:497: two empty vectors and a zero. Named
    explicitly because Lean has no `Default` coercion in play here; the house
    precedent is `proofReadPlanDefault` and `quotientIdentityPlanDefault` in
    Protocol.lean:324 and :341. -/
def selectorFoldPlanDefault : SelectorFoldPlan :=
  { gapsByIdentity := [], tailExponents := [], maxPower := 0 }

/-- rust: QVM:507-513 (`SelectorFoldPlan::gap_for`) @formal-baseline. "Gap from
    this selector identity to the previous identity in the same selector bucket."

    R3/R4: `Vec::get(i)` is bounds-checked and yields `None` out of range - it is
    NOT an index panic - and `.copied().flatten()` collapses both "no entry" and
    "entry is `None`" to `None`. `List.getD .. none` reproduces exactly that, and
    `selectorFoldPlan_gapFor_ok` separates the three cases (in-range `some`,
    in-range `none`, out-of-range) so the collapse is pinned rather than assumed. -/
def SelectorFoldPlan.gapFor (self : SelectorFoldPlan) (identity : QuotientIdentity) :
    Option Nat :=
  self.gapsByIdentity.getD identity.meta_.globalIndex none

/-- rust: QVM:317-345 (`struct QuotientProgramPlan`) @formal-baseline. "Hybrid
    execution plan for quotient numerator reconstruction. A small prefix may stay
    inline, most identities become VM bytecode, and selected expensive shapes can
    become native callbacks. The plan is a representation choice only: it must
    preserve the original identity order and the target of every identity."

    The two methods of its impl block (QVM:382-474, `execution_manifest` and
    `validate_execution_manifest`) are the plan-to-manifest bridge and are NOT
    ported; see the header. -/
structure QuotientProgramPlan where
  /-- rust: QVM:325-326 (`inline_identities: Vec<QuotientIdentity>`) - "Gate prefix
      emitted directly before the VM loop." -/
  inlineIdentities : List QuotientIdentity
  /-- rust: QVM:327-328 (`items: Vec<QuotientProgramItem>`) - "VM/native stream
      after the inline prefix." -/
  items : List QuotientProgramItem
  /-- rust: QVM:329-330 (`native_identities: Vec<QuotientIdentity>`) - "Bodies for
      `NativeIdentity` markers, addressed by marker index." -/
  nativeIdentities : List QuotientIdentity
  /-- rust: QVM:331-332 (`native_permutation_identities: Vec<QuotientIdentity>`) -
      "Identity range expanded by a `NativePermutation` marker, if present." -/
  nativePermutationIdentities : List QuotientIdentity
  /-- rust: QVM:333-334 (`native_lookup_identities: Vec<QuotientIdentity>`) -
      "Identity range expanded by a `NativeLookup` marker, if present." -/
  nativeLookupIdentities : List QuotientIdentity
  /-- rust: QVM:335-336 (`structured_tail_identities: Vec<QuotientIdentity>`) -
      "Structured post-VM identity range, currently the optional trash suffix." -/
  structuredTailIdentities : List QuotientIdentity
  /-- rust: QVM:337-338 (`sorted_simple: Vec<usize>`) - "Shared selector-column
      ordering." Sorted by the producer and NOT re-sorted here (the same note
      Api.lean:741-743 records for `simple_selector_cols`). -/
  sortedSimple : List Nat
  /-- rust: QVM:339-340 (`has_native_permutation: bool`) - "Whether the stream
      contains a native permutation callback marker." -/
  hasNativePermutation : Bool
  /-- rust: QVM:341-342 (`has_native_lookup: bool`) - "Whether the stream contains
      a native lookup callback marker." -/
  hasNativeLookup : Bool
  /-- rust: QVM:343-344 (`selector_fold: SelectorFoldPlan`) - "Gap exponents for
      simple-selector buckets in the global y-batch." -/
  selectorFold : SelectorFoldPlan
  deriving BEq

/-- rust: QVM:618-641 (`enum QuotientOpcodeEncoding`) @formal-baseline. "Operand
    decoder classes shared by tests and docs. The Yul template is the runtime
    decoder; this enum is the compile-time/spec view of the same ABI. Encodings with
    zero fixed byte length are dynamic byte-only forms."

    R2 note: the Rust's `None` variant is spelled `.none` here, which is what the
    "no operand" reading wants anyway; Lean disambiguates it from `Option.none` by
    expected type. No other variant needed a change. -/
inductive QuotientOpcodeEncoding
  /-- rust: QVM:625 (`None`) - no operand: the opcode is one byte. -/
  | none
  /-- rust: QVM:626 (`U8`) - one inline byte operand. -/
  | u8
  /-- rust: QVM:627 (`U16`) - a two-byte big-endian operand. -/
  | u16
  /-- rust: QVM:628 (`U24`) - a three-byte big-endian operand. -/
  | u24
  /-- rust: QVM:629 (`U32`) - a four-byte big-endian operand. -/
  | u32
  /-- rust: QVM:630 (`TokenOffset`) - token byte plus four-byte offset. -/
  | tokenOffset
  /-- rust: QVM:631 (`AddMulMemMemConstU8`) -/
  | addMulMemMemConstU8
  /-- rust: QVM:632 (`AddMulConstU8MemU16`) -/
  | addMulConstU8MemU16
  /-- rust: QVM:633 (`AddMulMemMem`) -/
  | addMulMemMem
  /-- rust: QVM:634 (`RunAddMulMemMemConstU8`) - dynamic: run count then operands. -/
  | runAddMulMemMemConstU8
  /-- rust: QVM:635 (`RunAddMulConstU8MemU16`) - dynamic. -/
  | runAddMulConstU8MemU16
  /-- rust: QVM:636 (`LimbLin`) - `QUOTIENT_VM_LIMBS` (slot, ptr) pairs. -/
  | limbLin
  /-- rust: QVM:637 (`LimbBilinRow`) - one ptr then `QUOTIENT_VM_LIMBS` pairs. -/
  | limbBilinRow
  /-- rust: QVM:638 (`LimbBilinPairwise`) - two ptrs then `PAIRWISE_COEFFS` slots. -/
  | limbBilinPairwise
  /-- rust: QVM:639 (`LimbModarith7`) - dynamic: flags then counted blocks. -/
  | limbModarith7
  /-- rust: QVM:640 (`AffineSum`) - dynamic: two counts then counted blocks. -/
  | affineSum
  deriving BEq

/-- rust: QVM:643-653 (`struct QuotientOpcodeSpec`) @formal-baseline. -/
structure QuotientOpcodeSpec where
  /-- rust: QVM:645-646 (`name: &'static str`) - "Stable snake-case name rendered
      into template constants." This is the string the hazard-1 conformance test
      matches against the Yul template, so it is ABI, not a comment. -/
  name : String
  /-- rust: QVM:647-648 (`opcode: u8`) - "Stable opcode byte." Hazard 2: `Nat`
      here, and every value is a `Q_OP_*` literal <= 0x22;
      opcodeTable_is31DistinctOpcodes_ok gates `< 256` for all 31. -/
  opcode : Nat
  /-- rust: QVM:649-650 (`byte_len: usize`) - "Byte length in byte-oriented
      encoding, or zero for dynamic run forms." -/
  byteLen : Nat
  /-- rust: QVM:651-652 (`encoding: QuotientOpcodeEncoding`) - "Operand decoding
      class." -/
  encoding : QuotientOpcodeEncoding
  deriving BEq

/-- rust: QVM:655-661 (`struct QuotientMemTokenSpec`) @formal-baseline. -/
structure QuotientMemTokenSpec where
  /-- rust: QVM:657-658 (`name: &'static str`) - "Generated Yul memory symbol." -/
  name : String
  /-- rust: QVM:659-660 (`token: u8`) - "Stable compact token used by VM bytecode."
      Hazard 2: `Nat`, gated `< 256`; out-of-width is unreachable because the only
      producer returns one of the nine `Q_MEM_*` constants or panics (QVM:2978). -/
  token : Nat
  deriving BEq

/-- rust: QVM:663-677 (`struct QuotientVmSpec`) @formal-baseline. "Complete compact
    VM ABI description used by docs/tests/template rendering." -/
structure QuotientVmSpec where
  /-- rust: QVM:665-666 (`opcodes: &'static [QuotientOpcodeSpec]`) - "Complete
      opcode table, used by template constants and ABI tests." -/
  opcodes : List QuotientOpcodeSpec
  /-- rust: QVM:667-668 (`mem_tokens: &'static [QuotientMemTokenSpec]`) - "Complete
      memory-token table, used by template constants and ABI tests." -/
  memTokens : List QuotientMemTokenSpec
  /-- rust: QVM:669-670 (`run_compaction_min_len: usize`) - "Minimum adjacent
      fused-op run length worth compacting." -/
  runCompactionMinLen : Nat
  /-- rust: QVM:671-672 (`limb_count: usize`) - "Number of foreign-field limbs
      recognized by limb opcodes." -/
  limbCount : Nat
  /-- rust: QVM:673-674 (`limb_pairwise_terms: usize`) - "Number of products in a
      7-by-7 pairwise convolution." -/
  limbPairwiseTerms : Nat
  /-- rust: QVM:675-676 (`limb_pairwise_coeffs: usize`) - "Number of distinct
      `i + j` coefficients in that convolution." -/
  limbPairwiseCoeffs : Nat
  deriving BEq


/-! ## The opcode ABI (rust: QVM:554-616) -/

-- rust: QVM:554-566. The comment is part of the ABI and is reproduced because the
-- gates below enforce what it states:
--
--   Opcode assignments are part of the verifier/VK ABI.
--
--   Stack convention:
--     * push opcodes place a value in q_top, spilling the previous top to the
--       memory stack when needed;
--     * generic ADD/MUL consume one spilled operand and q_top, leaving q_top;
--     * accumulator opcodes mutate q_top in place and have zero stack effect;
--     * FOLD_* consumes q_top and advances the quotient y-batch;
--     * native callback markers require an empty stack at identity boundaries.
--
--   The numeric assignments are intentionally sparse. Keep 0x1a reserved:
--   historical builds used it for an experimental native trash callback, but the
--   current VM intentionally has no operation at that value.
--
-- R2: the Rust names are already SCREAMING_SNAKE with a `Q_OP_` prefix; lowerCamelCase
-- gives `qOpPushConst` and so on. Hazard 2: every one is `u8` in Rust and `Nat`
-- here; opcodeTable_is31DistinctOpcodes_ok gates `< 256` and
-- opcodeConstants_matchTableOpcodes_ok gates that the table uses these and nothing else.

/-- rust: QVM:567 (`Q_OP_PUSH_CONST: u8 = 0x01`) - push VK constant-table value. -/
def qOpPushConst : Nat := 0x01
/-- rust: QVM:568 (`Q_OP_PUSH_MEM_LITERAL: u8 = 0x02`) - push mload(absolute_ptr). -/
def qOpPushMemLiteral : Nat := 0x02
/-- rust: QVM:569 (`Q_OP_PUSH_MEM_TOKEN: u8 = 0x03`) - push mload(symbolic_token). -/
def qOpPushMemToken : Nat := 0x03
/-- rust: QVM:570 (`Q_OP_PUSH_MEM_TOKEN_OFFSET: u8 = 0x04`) - push mload(token +
    offset). -/
def qOpPushMemTokenOffset : Nat := 0x04
/-- rust: QVM:571 (`Q_OP_PUSH_MEM_U16: u8 = 0x05`) - push mload(short absolute ptr).
    This is the byte Templates.lean:949-957 pins against the committed artifact. -/
def qOpPushMemU16 : Nat := 0x05
/-- rust: QVM:572 (`Q_OP_ADD: u8 = 0x06`) - binary Fr addition. -/
def qOpAdd : Nat := 0x06
/-- rust: QVM:573 (`Q_OP_MUL: u8 = 0x07`) - binary Fr multiplication. -/
def qOpMul : Nat := 0x07
/-- rust: QVM:574 (`Q_OP_NEG: u8 = 0x08`) - unary Fr negation. -/
def qOpNeg : Nat := 0x08
/-- rust: QVM:575 (`Q_OP_PUSH_CONST_U8: u8 = 0x09`) - push short constant-table slot. -/
def qOpPushConstU8 : Nat := 0x09
/-- rust: QVM:576 (`Q_OP_FOLD_MAIN: u8 = 0x0a`) - consume top into main y-fold. -/
def qOpFoldMain : Nat := 0x0a
/-- rust: QVM:577 (`Q_OP_FOLD_SELECTOR: u8 = 0x0b`) - consume top into selector
    bucket. -/
def qOpFoldSelector : Nat := 0x0b
/-- rust: QVM:578 (`Q_OP_ADD_CONST_U8: u8 = 0x0c`) - top += short constant. -/
def qOpAddConstU8 : Nat := 0x0c
/-- rust: QVM:579 (`Q_OP_MUL_CONST_U8: u8 = 0x0d`) - top *= short constant. -/
def qOpMulConstU8 : Nat := 0x0d
/-- rust: QVM:580 (`Q_OP_ADD_CONST: u8 = 0x0e`) - top += constant-table value. -/
def qOpAddConst : Nat := 0x0e
/-- rust: QVM:581 (`Q_OP_MUL_CONST: u8 = 0x0f`) - top *= constant-table value. -/
def qOpMulConst : Nat := 0x0f
/-- rust: QVM:582 (`Q_OP_ADD_MEM_U16: u8 = 0x10`) - top += mload(ptr). -/
def qOpAddMemU16 : Nat := 0x10
/-- rust: QVM:583 (`Q_OP_MUL_MEM_U16: u8 = 0x11`) - top *= mload(ptr). -/
def qOpMulMemU16 : Nat := 0x11
/-- rust: QVM:584 (`Q_OP_ADD_MUL_MEM_MEM_CONST_U8: u8 = 0x12`) -
    top += lhs * rhs * const. -/
def qOpAddMulMemMemConstU8 : Nat := 0x12
/-- rust: QVM:585 (`Q_OP_ADD_MUL_CONST_U8_MEM_U16: u8 = 0x13`) -
    top += const * mload(ptr). -/
def qOpAddMulConstU8MemU16 : Nat := 0x13
/-- rust: QVM:586 (`Q_OP_ADD_MUL_MEM_MEM: u8 = 0x14`) - top += lhs * rhs. -/
def qOpAddMulMemMem : Nat := 0x14
/-- rust: QVM:587 (`Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8: u8 = 0x15`) - compact run of
    op 0x12. -/
def qOpRunAddMulMemMemConstU8 : Nat := 0x15
/-- rust: QVM:588 (`Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16: u8 = 0x16`) - compact run of
    op 0x13. -/
def qOpRunAddMulConstU8MemU16 : Nat := 0x16
/-- rust: QVM:589 (`Q_OP_NATIVE_PERMUTATION: u8 = 0x19`) - delegate permutation
    family. Note the gap: 0x17 and 0x18 are unassigned, and 0x1a is deliberately
    reserved (QVM:564-565). -/
def qOpNativePermutation : Nat := 0x19
/-- rust: QVM:590 (`Q_OP_NATIVE_IDENTITY: u8 = 0x1b`) - delegate one selected gate
    identity. -/
def qOpNativeIdentity : Nat := 0x1b
/-- rust: QVM:591 (`Q_OP_LIN7: u8 = 0x1c`) - evaluate seven-limb linear form. -/
def qOpLin7 : Nat := 0x1c
/-- rust: QVM:592 (`Q_OP_BILIN7_ROW: u8 = 0x1d`) - evaluate one limb times a
    seven-limb row. -/
def qOpBilin7Row : Nat := 0x1d
/-- rust: QVM:593 (`Q_OP_BILIN7_PAIRWISE: u8 = 0x1e`) - evaluate a 7x7 pairwise
    product. -/
def qOpBilin7Pairwise : Nat := 0x1e
/-- rust: QVM:594 (`Q_OP_NATIVE_LOOKUP: u8 = 0x1f`) - delegate lookup family. -/
def qOpNativeLookup : Nat := 0x1f
/-- rust: QVM:595 (`Q_OP_POW5: u8 = 0x20`) - raise top to the fifth power. -/
def qOpPow5 : Nat := 0x20
/-- rust: QVM:596 (`Q_OP_MODARITH7: u8 = 0x21`) - dynamic mixed seven-limb affine
    form. -/
def qOpModarith7 : Nat := 0x21
/-- rust: QVM:597 (`Q_OP_AFFINE_SUM: u8 = 0x22`) - dynamic affine sum over
    mem/products. -/
def qOpAffineSum : Nat := 0x22

/-- rust: QVM:599-600 (`Q_MODARITH7_FLAG_COND: u8 = 0x01`) - "MODARITH7 operand
    flag: first operand is a conditional memory factor." Private in Rust (no
    `pub(crate)`) but imported by the reference interpreter at QVR:39, so it is
    vocabulary and is ported. -/
def qModarith7FlagCond : Nat := 0x01
/-- rust: QVM:601-602 (`Q_MODARITH7_FLAG_CONST: u8 = 0x02`) - "MODARITH7 operand
    flag: a nonzero constant term is encoded first." Also imported by QVR:39. -/
def qModarith7FlagConst : Nat := 0x02

-- rust: QVM:604-616 (`Q_MEM_*: u8`) @formal-baseline. "Memory tokens compress
-- generated Yul symbols whose concrete addresses depend on the memory planner.
-- Literal pointers are used for most proof/VK evals; tokens cover shared
-- challenge/common-polynomial locations that are easier and safer to address
-- symbolically in generated code."
/-- rust: QVM:608 (`Q_MEM_L0: u8 = 0x01`) - L_0(x). -/
def qMemL0 : Nat := 0x01
/-- rust: QVM:609 (`Q_MEM_L_LAST: u8 = 0x02`) - L_last(x). -/
def qMemLLast : Nat := 0x02
/-- rust: QVM:610 (`Q_MEM_L_BLIND: u8 = 0x03`) - L_blind(x). -/
def qMemLBlind : Nat := 0x03
/-- rust: QVM:611 (`Q_MEM_BETA: u8 = 0x04`) - permutation/lookup beta. -/
def qMemBeta : Nat := 0x04
/-- rust: QVM:612 (`Q_MEM_GAMMA: u8 = 0x05`) - permutation/lookup gamma. -/
def qMemGamma : Nat := 0x05
/-- rust: QVM:613 (`Q_MEM_X: u8 = 0x06`) - evaluation challenge x. -/
def qMemX : Nat := 0x06
/-- rust: QVM:614 (`Q_MEM_THETA: u8 = 0x07`) - lookup compression theta. -/
def qMemTheta : Nat := 0x07
/-- rust: QVM:615 (`Q_MEM_TRASH_CHALLENGE: u8 = 0x08`) - trash argument challenge. -/
def qMemTrashChallenge : Nat := 0x08
/-- rust: QVM:616 (`Q_MEM_INSTANCE_EVAL: u8 = 0x09`) - locally interpolated public
    input. -/
def qMemInstanceEval : Nat := 0x09

/-- rust: QVM:679-869 (`QUOTIENT_OPCODE_TABLE: &[QuotientOpcodeSpec]`)
    @formal-baseline. "Canonical opcode table shared by Rust tests and rendered
    template constants."

    Hazard 2, the `byteLen` column: the Rust writes each length as an expression
    over the width constants (QVM:684, 690, 696, ...), and this port keeps the
    expressions rather than the evaluated numbers, so a width change propagates the
    way the reference intends. `opcodeTable_lengthsAreDerivedFromEncoding_ok`
    re-derives every length from the encoding class alone - which is a real check,
    because the derivation is written independently of the table - and
    `opcodeTable_pinnedByteLengths_ok` pins the 31 evaluated numbers, so a wrong
    expression cannot slide in unnoticed. The four `byteLen = 0` entries are the
    dynamic forms the Rust says are "byte-only": the two RUN opcodes, MODARITH7 and
    AFFINE_SUM. -/
def quotientOpcodeTable : List QuotientOpcodeSpec :=
  [ { name := "push_const", opcode := qOpPushConst,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "push_mem_literal", opcode := qOpPushMemLiteral,
        byteLen := 1 + quotientVmByteU32Bytes, encoding := .u32 }
  , { name := "push_mem_token", opcode := qOpPushMemToken,
        byteLen := 1 + 1, encoding := .u8 }
  , { name := "push_mem_token_offset", opcode := qOpPushMemTokenOffset,
        byteLen := 1 + 1 + quotientVmByteU32Bytes, encoding := .tokenOffset }
  , { name := "push_mem_u16", opcode := qOpPushMemU16,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "add", opcode := qOpAdd,
        byteLen := 1, encoding := .none }
  , { name := "mul", opcode := qOpMul,
        byteLen := 1, encoding := .none }
  , { name := "neg", opcode := qOpNeg,
        byteLen := 1, encoding := .none }
  , { name := "push_const_u8", opcode := qOpPushConstU8,
        byteLen := 1 + 1, encoding := .u8 }
  , { name := "fold_main", opcode := qOpFoldMain,
        byteLen := 1, encoding := .none }
  , { name := "fold_selector", opcode := qOpFoldSelector,
        byteLen := 1 + quotientVmByteU24Bytes, encoding := .u24 }
  , { name := "add_const_u8", opcode := qOpAddConstU8,
        byteLen := 1 + 1, encoding := .u8 }
  , { name := "mul_const_u8", opcode := qOpMulConstU8,
        byteLen := 1 + 1, encoding := .u8 }
  , { name := "add_const", opcode := qOpAddConst,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "mul_const", opcode := qOpMulConst,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "add_mem_u16", opcode := qOpAddMemU16,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "mul_mem_u16", opcode := qOpMulMemU16,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "add_mul_mem_mem_const_u8", opcode := qOpAddMulMemMemConstU8,
        byteLen := 1 + 2 * quotientVmByteU16Bytes + 1, encoding := .addMulMemMemConstU8 }
  , { name := "add_mul_const_u8_mem_u16", opcode := qOpAddMulConstU8MemU16,
        byteLen := 1 + quotientVmByteU16Bytes + 1, encoding := .addMulConstU8MemU16 }
  , { name := "add_mul_mem_mem", opcode := qOpAddMulMemMem,
        byteLen := 1 + 2 * quotientVmByteU16Bytes, encoding := .addMulMemMem }
  , { name := "run_add_mul_mem_mem_const_u8", opcode := qOpRunAddMulMemMemConstU8,
        byteLen := 0, encoding := .runAddMulMemMemConstU8 }
  , { name := "run_add_mul_const_u8_mem_u16", opcode := qOpRunAddMulConstU8MemU16,
        byteLen := 0, encoding := .runAddMulConstU8MemU16 }
  , { name := "native_permutation", opcode := qOpNativePermutation,
        byteLen := 1, encoding := .none }
  , { name := "native_lookup", opcode := qOpNativeLookup,
        byteLen := 1, encoding := .none }
  , { name := "native_identity", opcode := qOpNativeIdentity,
        byteLen := 1 + quotientVmByteU16Bytes, encoding := .u16 }
  , { name := "lin7", opcode := qOpLin7,
        byteLen := 1 + quotientVmLimbs * (1 + quotientVmByteU16Bytes),
        encoding := .limbLin }
  , { name := "bilin7_row", opcode := qOpBilin7Row,
        byteLen := 1 + quotientVmByteU16Bytes
          + quotientVmLimbs * (1 + quotientVmByteU16Bytes),
        encoding := .limbBilinRow }
  , { name := "bilin7_pairwise", opcode := qOpBilin7Pairwise,
        byteLen := 1 + 2 * quotientVmByteU16Bytes + quotientVmPairwiseCoeffs,
        encoding := .limbBilinPairwise }
  , { name := "modarith7", opcode := qOpModarith7,
        byteLen := 0, encoding := .limbModarith7 }
  , { name := "pow5", opcode := qOpPow5,
        byteLen := 1, encoding := .none }
  , { name := "affine_sum", opcode := qOpAffineSum,
        byteLen := 0, encoding := .affineSum }
  ]

/-- rust: QVM:871-909 (`QUOTIENT_MEM_TOKEN_TABLE: &[QuotientMemTokenSpec]`)
    @formal-baseline. "Canonical symbolic-memory-token table shared with the Yul VM." -/
def quotientMemTokenTable : List QuotientMemTokenSpec :=
  [ { name := "L_0_MPTR", token := qMemL0 }
  , { name := "L_LAST_MPTR", token := qMemLLast }
  , { name := "L_BLIND_MPTR", token := qMemLBlind }
  , { name := "BETA_MPTR", token := qMemBeta }
  , { name := "GAMMA_MPTR", token := qMemGamma }
  , { name := "X_MPTR", token := qMemX }
  , { name := "THETA_MPTR", token := qMemTheta }
  , { name := "TRASH_CHALLENGE_MPTR", token := qMemTrashChallenge }
  , { name := "INSTANCE_EVAL_MPTR", token := qMemInstanceEval }
  ]

/-- rust: QVM:911-919 (`QUOTIENT_VM_SPEC: QuotientVmSpec`) @formal-baseline.
    "Complete compact VM ABI description used by docs/tests/template rendering."
    This is the value the hazard-1 conformance test iterates (LT:2270, LT:2288,
    LT:2314-2322), so the four scalar fields must be the same constants the table
    entries are built from - which
    `quotientVmSpec_fieldsMatchTheConstants_ok` checks rather than assumes. -/
def quotientVmSpec : QuotientVmSpec :=
  { opcodes := quotientOpcodeTable
    memTokens := quotientMemTokenTable
    runCompactionMinLen := quotientVmRunCompactionMinLen
    limbCount := quotientVmLimbs
    limbPairwiseTerms := quotientVmPairwiseTerms
    limbPairwiseCoeffs := quotientVmPairwiseCoeffs }

/-- rust: QVM:921-924 (`quotient_opcode_spec`) @formal-baseline. "Return the VM
    opcode spec for a stable opcode byte." `iter().find()` becomes `find?`: total,
    first match in table order, no panic (R4 note in the header). -/
def quotientOpcodeSpec (opcode : Nat) : Option QuotientOpcodeSpec :=
  quotientVmSpec.opcodes.find? fun spec => spec.opcode == opcode

/-- rust: QVM:926-932 (`quotient_opcode_byte_len`) @formal-baseline. "Return the
    fixed byte length of an opcode in byte-oriented encoding. Dynamic run opcodes
    intentionally return `None`; callers that need to walk bytecode containing those
    forms must decode the run count and operand width." -/
def quotientOpcodeByteLen (opcode : Nat) : Option Nat :=
  (quotientOpcodeSpec opcode) >>= fun spec =>
    if spec.byteLen != 0 then some spec.byteLen else none


end Midfall.Generator

/-! ## Gates (plan P-09a acceptance: at least 10, including hazard 1 and hazard 4)

    Every gate below is a Bool or an `IO Bool` with a matching
    `#eval ... -- expect true` line at the end of the file, so
    `scripts/kat_gate.py` turns each one into a CI obligation. Each doc names the
    concrete wrong implementation it rules out (docs/REVIEW.md R-38's rule), and the
    package report carries the perturbation actually run inside each stated scope
    (R-41). -/

namespace Midfall.Generator.QuotientVmKats

/-- Hazard 1's artifact. Two candidates so the gate resolves from `formal/` (where
    `scripts/checks.sh` and lake run) and from the repo root. -/
def templatePathCandidates : List String :=
  ["../proofs/solidity-verifier/templates/partials/quotient_numerator/QuotientNumeratorBlock.yul",
   "proofs/solidity-verifier/templates/partials/quotient_numerator/QuotientNumeratorBlock.yul"]

/-- A missing artifact is a RED, never a silent true: the read yields the empty
    string and every consumer checks it with `templateReadOk`. -/
def readFileOrEmpty (path : String) : IO String := do
  try
    let contents ← IO.FS.readFile path
    pure contents
  catch _e =>
    pure ""

/-- Read the first candidate that exists. -/
def readQuotientVmTemplate : IO String :=
  templatePathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

/-- TPL is 1442 lines / 55,000-odd bytes at HEAD. Anything much smaller is a wrong
    path or a truncated artifact, and must not be allowed to satisfy a needle check
    by accident. -/
def templateReadOk (tmpl : String) : Bool := tmpl.length > 20000

/-- The needle LT:2272-2277 builds for opcodes. -/
def opCasePrefix : String := "case {{ template_constants.quotient_vm.op."

/-- The needle prefix LT:2302-2308 builds for memory tokens. -/
def memCasePrefix : String := "case {{ template_constants.quotient_vm.mem."

/-- The lower-case identifier immediately after each occurrence of `pfx`. Used to
    read the template's switch arms back out of the artifact, which is what makes the
    coverage gates bidirectional instead of one-way like the Rust's. -/
def identAfter (pfx : String) (s : String) : List String :=
  ((s.splitOn pfx).tail?.getD []).map fun tail =>
    String.ofList (tail.toList.takeWhile fun c =>
      (('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_'))

/-- The template's opcode switch-arm names, in file order. TPL:494-1303. -/
def templateOpcodeCaseNames (tmpl : String) : List String :=
  let hits := (tmpl.splitOn "\n").filter fun line => line.contains opCasePrefix
  hits.flatMap (identAfter opCasePrefix)

/-- The template's memory-token switch-arm names. Each token appears twice:
    TPL:542-566 (the `PUSH_MEM_TOKEN` arm) and TPL:595-619 (the
    `PUSH_MEM_TOKEN_OFFSET` arm). -/
def templateMemTokenCaseNames (tmpl : String) : List String :=
  let hits := (tmpl.splitOn "\n").filter fun line => line.contains memCasePrefix
  hits.flatMap (identAfter memCasePrefix)

/-- rust: LT:2290-2301, the test-local `match name { "L_0_MPTR" => "l0", ... }` map
    from a Yul symbol to the Askama field that renders it. Ported as a total function
    returning `Option` rather than the Rust's `panic!`, so an unmapped token makes
    the gate false instead of aborting the build - and
    `memTokenTable_matchesYulTemplateCases_ok` still reddens, because the Rust's
    panic arm is exactly the "a token was added to the table but not to the map" case
    the gate is for. -/
def memTokenTemplateField (name : String) : Option String :=
  match name with
  | "L_0_MPTR" => some "l0"
  | "L_LAST_MPTR" => some "l_last"
  | "L_BLIND_MPTR" => some "l_blind"
  | "BETA_MPTR" => some "beta"
  | "GAMMA_MPTR" => some "gamma"
  | "X_MPTR" => some "x"
  | "THETA_MPTR" => some "theta"
  | "TRASH_CHALLENGE_MPTR" => some "trash_challenge"
  | "INSTANCE_EVAL_MPTR" => some "instance_eval"
  | _ => none

/-- The 31 (name, constant) pairs in QVM:567-597 order. Written out by hand from the
    constant block so that `opcodeConstants_matchTableOpcodes_ok` is a comparison
    between two independent transcriptions of the same ABI, not a tautology. -/
def opcodeConstantsByName : List (String × Nat) :=
  [("push_const", qOpPushConst), ("push_mem_literal", qOpPushMemLiteral),
   ("push_mem_token", qOpPushMemToken), ("push_mem_token_offset", qOpPushMemTokenOffset),
   ("push_mem_u16", qOpPushMemU16), ("add", qOpAdd), ("mul", qOpMul), ("neg", qOpNeg),
   ("push_const_u8", qOpPushConstU8), ("fold_main", qOpFoldMain),
   ("fold_selector", qOpFoldSelector), ("add_const_u8", qOpAddConstU8),
   ("mul_const_u8", qOpMulConstU8), ("add_const", qOpAddConst),
   ("mul_const", qOpMulConst), ("add_mem_u16", qOpAddMemU16),
   ("mul_mem_u16", qOpMulMemU16), ("add_mul_mem_mem_const_u8", qOpAddMulMemMemConstU8),
   ("add_mul_const_u8_mem_u16", qOpAddMulConstU8MemU16), ("add_mul_mem_mem", qOpAddMulMemMem),
   ("run_add_mul_mem_mem_const_u8", qOpRunAddMulMemMemConstU8),
   ("run_add_mul_const_u8_mem_u16", qOpRunAddMulConstU8MemU16),
   ("native_permutation", qOpNativePermutation), ("native_lookup", qOpNativeLookup),
   ("native_identity", qOpNativeIdentity), ("lin7", qOpLin7),
   ("bilin7_row", qOpBilin7Row), ("bilin7_pairwise", qOpBilin7Pairwise),
   ("modarith7", qOpModarith7), ("pow5", qOpPow5), ("affine_sum", qOpAffineSum)]

/-- rust: M:233-265, the Askama field list of the Yul-emitter leg, addressed by the
    same snake-case names the template interpolates. Field order is the Rust's, which
    is NOT the table's (affine_sum sits after the two run opcodes here and last in the
    table) - the ordering difference is itself the reason a set comparison is needed. -/
def renderedOpcodeConstants : List (String × Nat) :=
  let op := templateConstantsDefault.quotientVm.op
  [("push_const", op.pushConst), ("push_mem_literal", op.pushMemLiteral),
   ("push_mem_token", op.pushMemToken), ("push_mem_token_offset", op.pushMemTokenOffset),
   ("push_mem_u16", op.pushMemU16), ("add", op.add), ("mul", op.mul), ("neg", op.neg),
   ("push_const_u8", op.pushConstU8), ("fold_main", op.foldMain),
   ("fold_selector", op.foldSelector), ("add_const_u8", op.addConstU8),
   ("mul_const_u8", op.mulConstU8), ("add_const", op.addConst),
   ("mul_const", op.mulConst), ("add_mem_u16", op.addMemU16),
   ("mul_mem_u16", op.mulMemU16), ("add_mul_mem_mem_const_u8", op.addMulMemMemConstU8),
   ("add_mul_const_u8_mem_u16", op.addMulConstU8MemU16), ("add_mul_mem_mem", op.addMulMemMem),
   ("run_add_mul_mem_mem_const_u8", op.runAddMulMemMemConstU8),
   ("run_add_mul_const_u8_mem_u16", op.runAddMulConstU8MemU16),
   ("affine_sum", op.affineSum), ("native_permutation", op.nativePermutation),
   ("native_lookup", op.nativeLookup), ("native_identity", op.nativeIdentity),
   ("lin7", op.lin7), ("bilin7_row", op.bilin7Row),
   ("bilin7_pairwise", op.bilin7Pairwise), ("modarith7", op.modarith7),
   ("pow5", op.pow5)]

/-- rust: M:266-276, the memory-token half of the same rendering. -/
def renderedMemTokenConstants : List (String × Nat) :=
  let mem := templateConstantsDefault.quotientVm.mem
  [("L_0_MPTR", mem.l0), ("L_LAST_MPTR", mem.lLast), ("L_BLIND_MPTR", mem.lBlind),
   ("BETA_MPTR", mem.beta), ("GAMMA_MPTR", mem.gamma), ("X_MPTR", mem.x),
   ("THETA_MPTR", mem.theta), ("TRASH_CHALLENGE_MPTR", mem.trashChallenge),
   ("INSTANCE_EVAL_MPTR", mem.instanceEval)]

/-- Duplicate detection for the opcode bytes: a repeated byte is the single most
    damaging ABI error available here, because the Yul switch would silently merge two
    opcodes into one arm and the table lookup would return the first. -/
def hasDuplicateNat (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | x :: rest => (rest.any fun y => y == x) || hasDuplicateNat rest

/-- The byte length each encoding class occupies, written INDEPENDENTLY of the table
    (the table builds its own `byteLen` field per entry). This is what makes
    `opcodeTable_lengthsAreDerivedFromEncoding_ok` a check rather than a restatement:
    the two agree only if the transcription is faithful. -/
def derivedByteLenWith (limbs : Nat) (pairwiseCoeffs : Nat)
    (encoding : QuotientOpcodeEncoding) : Nat :=
  match encoding with
  | .none => 1
  | .u8 => 1 + 1
  | .u16 => 1 + quotientVmByteU16Bytes
  | .u24 => 1 + quotientVmByteU24Bytes
  | .u32 => 1 + quotientVmByteU32Bytes
  | .tokenOffset => 1 + 1 + quotientVmByteU32Bytes
  | .addMulMemMemConstU8 => 1 + 2 * quotientVmByteU16Bytes + 1
  | .addMulConstU8MemU16 => 1 + quotientVmByteU16Bytes + 1
  | .addMulMemMem => 1 + 2 * quotientVmByteU16Bytes
  | .runAddMulMemMemConstU8 => 0
  | .runAddMulConstU8MemU16 => 0
  | .limbLin => 1 + limbs * (1 + quotientVmByteU16Bytes)
  | .limbBilinRow => 1 + quotientVmByteU16Bytes + limbs * (1 + quotientVmByteU16Bytes)
  | .limbBilinPairwise => 1 + 2 * quotientVmByteU16Bytes + pairwiseCoeffs
  | .limbModarith7 => 0
  | .affineSum => 0

/-- The same derivation at the recorded widths. -/
def derivedByteLen (encoding : QuotientOpcodeEncoding) : Nat :=
  derivedByteLenWith quotientVmLimbs quotientVmPairwiseCoeffs encoding

/-- The 31 evaluated byte lengths the Rust table's expressions produce at HEAD,
    pinned as literals so a wrong expression in the table cannot agree with a wrong
    derivation. Order is the table's. -/
def pinnedByteLengths : List Nat :=
  [3, 5, 2, 6, 3, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3, 3, 6, 4, 5, 0, 0, 1, 1, 3, 22, 24,
   18, 0, 1, 0]

/-- The 31 opcode bytes the table must contain, as literals, in table order. -/
def pinnedOpcodeBytes : List Nat :=
  [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
   0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x19, 0x1f, 0x1b, 0x1c, 0x1d, 0x1e,
   0x21, 0x20, 0x22]

/-- R-48: a LOCAL memory fixture with pairwise-distinct pointers, because the shared
    `LayoutKats.verifierLayoutFixture` has all-zero PCS bases and any pointer
    comparison made on it is vacuous. Every gate below that compares pointers uses
    this one, and `quotientMem_widthsAndFixture_ok` asserts the distinctness before
    relying on it. -/
def memFixture : List QuotientMem :=
  [ .literal 0x100, .literal 0x120, .literal 0x140, .literal 0x160, .literal 0x180,
    .literal 0x1a0, .literal 0x1c0, .literal 0x1e0,
    .token qMemL0, .token qMemBeta, .token qMemX,
    .tokenOffset qMemL0 0x20, .tokenOffset qMemBeta 0x40, .tokenOffset qMemX 0x60 ]

/-- The literal pointers of the fixture, for the distinctness assertion. -/
def memFixtureLiterals : List Nat :=
  let asNats := memFixture.map fun m =>
    match m with
    | .literal ptr => some ptr
    | _ => none
  asNats.filterMap id

/-- The fixture's limb pointers, all distinct and all inside u16 - the shape the
    recognizers can actually produce (QVM:3445, QVM:4024). -/
def limbPointerFixture : List Nat := [0x100, 0x120, 0x140, 0x160, 0x180, 0x1a0, 0x1c0]

/-- The terms of the Lin7 fixture, reused by the row shape. -/
def lin7FixtureTerms : List (Word256 × Nat) :=
  List.zip (limbPointerFixture.map fun i => BitVec.ofNat 256 (i + 1)) limbPointerFixture

/-- A well-formed Lin7: seven (coefficient, pointer) pairs. -/
def lin7Fixture : QuotientLimbShape :=
  QuotientLimbShape.lin7
    (List.zip (limbPointerFixture.map fun i => BitVec.ofNat 256 (i + 1)) limbPointerFixture)

/-- The same shape with one term dropped and with one term added: both representable,
    both must fall back. -/
def lin7Short : QuotientLimbShape :=
  match lin7Fixture with
  | .lin7 terms => .lin7 terms.dropLast
  | _ => .lin7 []

def lin7Long : QuotientLimbShape :=
  match lin7Fixture with
  | .lin7 terms => .lin7 (terms ++ [(BitVec.ofNat 256 0xff, 0x1e0)])
  | _ => .lin7 []

def bilin7RowFixture : QuotientLimbShape :=
  QuotientLimbShape.bilin7Row 0x200 (lin7FixtureTerms)

def bilin7RowShort : QuotientLimbShape :=
  QuotientLimbShape.bilin7Row 0x200 (lin7FixtureTerms.dropLast)

def bilin7PairwiseFixture : QuotientLimbShape :=
  QuotientLimbShape.bilin7Pairwise 0x100 0x200
    ((List.range quotientVmPairwiseCoeffs).map fun k => BitVec.ofNat 256 (k + 1))

def bilin7PairwiseShort : QuotientLimbShape :=
  QuotientLimbShape.bilin7Pairwise 0x100 0x200
    ((List.range (quotientVmPairwiseCoeffs - 1)).map fun k => BitVec.ofNat 256 (k + 1))

def bilin7PairwiseLong : QuotientLimbShape :=
  QuotientLimbShape.bilin7Pairwise 0x100 0x200
    ((List.range (quotientVmPairwiseCoeffs + 1)).map fun k => BitVec.ofNat 256 (k + 1))

/-- A shallow expression tree, hazard 3. The depth is NOT what is being tested - the
    gate is about structural termination and about every constructor position being
    reachable by the folds - so the tree stays at depth 3 and says so. -/
def exprFixture : QuotientExpr :=
  .add (.mul (.mem (.literal 0x100)) (.const (BitVec.ofNat 256 3)))
       (.neg (.mul (.mem (.token qMemBeta)) (.mem (.tokenOffset qMemX 0x20))))

/-- The same tree with one leaf replaced, for the non-vacuity of the BEq gates. -/
def exprFixtureAlt : QuotientExpr :=
  .add (.mul (.mem (.literal 0x120)) (.const (BitVec.ofNat 256 3)))
       (.neg (.mul (.mem (.token qMemBeta)) (.mem (.tokenOffset qMemX 0x20))))

/-- A source identity for the metadata and selector-fold gates. -/
def identityFixture (globalIndex : Nat) (target : QuotientTarget) : QuotientIdentity :=
  { meta_ := { globalIndex := globalIndex,
               source := QuotientIdentitySource.gate globalIndex "g" 0 "c" 0 }
    lines := ["t := add(1, 2)"]
    var := "t"
    target := target
    expr := exprFixture }


/-- Shape equality is decided by coefficients and pointers and by nothing else, which
    is the type-level content of "recognized from the expression tree alone": there is
    no place in a shape for a gate label, a constraint index or a circuit-gadget name.
    Rules out the failure the QVM:968-971 doc forbids - a shape that compares equal for
    two different gates, or unequal because of a name. -/
def shapeOperandsDetermineShape (s1 s2 : QuotientLimbShape) : Bool :=
  (s1 == s2) == (s1.pointerOperands == s2.pointerOperands
    && s1.coefficientOperands == s2.coefficientOperands)

/-- A MODARITH7 fixture with one operand in every block, so the operand counts below
    are a field census rather than a sample. -/
def modarith7Fixture : QuotientModarith7Shape :=
  { cond := some 0x200
    constant := BitVec.ofNat 256 1
    lin := [[(BitVec.ofNat 256 2, 0x100)]]
    rows := [(0x200, [(BitVec.ofNat 256 3, 0x120)])]
    pairwise := [(0x100, 0x200, [BitVec.ofNat 256 4])]
    memTerms := [(BitVec.ofNat 256 5, 0x140)]
    productTerms := [(BitVec.ofNat 256 6, 0x160, 0x180)] }

/-- The map from `QuotientExecutionKind` to the api.rs enum it duplicates. Modelling
    helper: it exists so the duplicate-ABI claim can be gated (see F-3). -/
def executionOfKind (kind : QuotientExecutionKind) : QuotientIdentityExecution :=
  match kind with
  | .inline => .inline
  | .interpreted => .interpreted
  | .nativePermutation => .nativePermutation
  | .nativeLookup => .nativeLookup
  | .nativeIdentity nativeIndex => .nativeIdentity nativeIndex
  | .structuredTail => .structuredTail

/-- A proof calldata layout with pairwise distinct counts in every section the repacked
    plan reads, so a dropped or duplicated term cannot hide behind equal numbers. -/
def proofLayoutFixture : ProofCalldataLayout :=
  { proofCalldataLayoutDefault with
    trash := ProofSection.new 0 1 wordBytes
    quotientLimbs := ProofSection.new 0 3 wordBytes
    evals := ProofSection.new 0 5 wordBytes
    qEvals := ProofSection.new 0 2 wordBytes }

/-! ### Hazard 1: the opcode and memory-token table conformance gates -/

/-- THE ARTIFACT IS REALLY OPENED. The precondition every other template gate relies on:
    TPL is on disk, is big enough to be the real 1442-line template, and contains the
    interpreter's switch. Rules out the R-38 finding-1 failure mode - a "conformance"
    gate that passes because the file it claims to check was never read. Perturbing the
    path list reddens this gate and every one after it. -/
def templateArtifactReachable_ok : IO Bool := do
  let tmpl ← readQuotientVmTemplate
  pure (templateReadOk tmpl && tmpl.contains "switch q_op")

/-- LT:2270-2282, ported. Every opcode name in the table must have a switch arm in the
    Yul interpreter, addressed by the same snake-case template constant. Rules out the
    compiler emitting an opcode the generated contract has no case for - which is a
    silent revert at run time, not a type error. -/
def opcodeTable_matchesYulTemplateCases_ok : IO Bool := do
  let tmpl ← readQuotientVmTemplate
  if !templateReadOk tmpl then pure false else
    pure (quotientVmSpec.opcodes.all fun spec =>
      tmpl.contains (opCasePrefix ++ spec.name ++ "|hex() }}"))

/-- THE STRONGER HALF OF THE SAME CHECK, and a finding: the Rust test only iterates the
    table, so a switch arm added to the template for an opcode the table does not know
    passes LT:2270-2282. This gate reads the arms back out of TPL and compares both
    ways, so a stale arm, a renamed arm or a duplicated arm reddens here. Also pins the
    count at 31, which is what QL:859 asserts about the decoder. -/
def opcodeTable_caseCoverageIsExact_ok : IO Bool := do
  let tmpl ← readQuotientVmTemplate
  if !templateReadOk tmpl then pure false else
    let caseNames := templateOpcodeCaseNames tmpl
    let tableNames := quotientVmSpec.opcodes.map fun s => s.name
    pure (caseNames.length == 31 && tableNames.length == 31
      && caseNames.all fun n => tableNames.contains n
      && tableNames.all fun n => (caseNames.filter fun m => m == n).length == 1)

/-- LT:2283-2286 plus the reservation note at QVM:564-565: the retired native-trash
    opcode must not survive in the template, and must not be reachable through the
    table either. Rules out a half-removal - the constant deleted from the table but
    its case still rendered, or vice versa. -/
def opcodeTable_noStaleNativeTrashCase_ok : IO Bool := do
  let tmpl ← readQuotientVmTemplate
  if !templateReadOk tmpl then pure false else
    pure (!tmpl.contains "case 0x1a"
      && quotientVmSpec.opcodes.all fun s => s.opcode != 0x1a
      && quotientOpcodeSpec 0x1a == none
      && quotientOpcodeByteLen 0x1a == none)

/-- LT:2288-2313, ported, including the name-to-field map at LT:2290-2301. Every memory
    token must reach a switch arm that binds `q_ptr` to the named Yul symbol. Rules
    out a token added to the table with no arm, and - through the `none` arm of
    `memTokenTemplateField` - a token added to the table with no entry in the map,
    which in Rust is a `panic!` inside the test. -/
def memTokenTable_matchesYulTemplateCases_ok : IO Bool := do
  let tmpl ← readQuotientVmTemplate
  if !templateReadOk tmpl then pure false else
    pure (quotientVmSpec.memTokens.all fun spec =>
      match memTokenTemplateField spec.name with
      | none => false
      | some field =>
          tmpl.contains ("case {{ template_constants.quotient_vm.mem." ++ field
            ++ "|hex() }} { q_ptr := " ++ spec.name ++ " }"))

/-- The bidirectional memory-token check the Rust does not make: TPL has exactly 18
    token arms (9 tokens x the `PUSH_MEM_TOKEN` and `PUSH_MEM_TOKEN_OFFSET` arms),
    every one of them a mapped token, and every mapped token appearing exactly twice.
    Rules out an arm bound to the wrong symbol - the needle in the gate above already
    ties symbol to field, and this ties the count. -/
def memTokenTable_caseCoverageIsExact_ok : IO Bool := do
  let tmpl ← readQuotientVmTemplate
  if !templateReadOk tmpl then pure false else
    let fields := templateMemTokenCaseNames tmpl
    let tableFields := quotientVmSpec.memTokens.filterMap fun s => memTokenTemplateField s.name
    pure (fields.length == 18 && tableFields.length == 9
      && fields.all fun f => tableFields.contains f
      && tableFields.all fun f => (fields.filter fun g => g == f).length == 2)

/-- LT:2325-2339, the table-internal half (see the header for why the walker half is
    out of scope). Each entry's declared length must be the length its encoding class
    has, re-derived here independently of the table. Rules out a transcription error in
    one `byteLen` expression - a wrong operand width in the ABI, which the interpreter
    would read as a misaligned instruction stream. -/
def opcodeTable_lengthsAreDerivedFromEncoding_ok : Bool :=
  quotientVmSpec.opcodes.all fun s =>
      s.byteLen == derivedByteLen s.encoding
    && (s.byteLen == 0)
      == (s.encoding == .runAddMulMemMemConstU8 || s.encoding == .runAddMulConstU8MemU16
        || s.encoding == .limbModarith7 || s.encoding == .affineSum)

/-- The same 31 lengths pinned as LITERALS, so the derivation above cannot drift with
    the table: both must agree with the numbers the Rust expressions evaluate to at
    HEAD. Rules out a width constant being edited to make a wrong table look right. -/
def opcodeTable_pinnedByteLengths_ok : Bool :=
  pinnedByteLengths.length == 31
    && (quotientVmSpec.opcodes.map fun s => s.byteLen) == pinnedByteLengths

/-- QL:852-859's count claim, ported at the vocabulary level: 31 entries, 31 distinct
    bytes, every byte a `u8`, no zero, no reserved 0x1a, and the byte sequence equal
    to the pinned literal list. A duplicated opcode byte is the worst available failure
    here: the Yul switch merges two opcodes into one arm and the table lookup silently
    returns the first. -/
def opcodeTable_is31DistinctOpcodes_ok : Bool :=
  quotientVmSpec.opcodes.length == 31
    && (quotientVmSpec.opcodes.all fun s => s.opcode < 256)
    && !hasDuplicateNat (quotientVmSpec.opcodes.map fun s => s.opcode)
    && (quotientVmSpec.opcodes.map fun s => s.opcode) == pinnedOpcodeBytes
    && !hasDuplicateNat pinnedOpcodeBytes
    && (quotientVmSpec.opcodes.all fun s => s.opcode != 0 && s.opcode != 0x1a)
    && (quotientVmSpec.opcodes.map fun s => s.name) == (opcodeConstantsByName.map Prod.fst)

/-- The two independent transcriptions of the ABI - the constant block QVM:567-597 and
    the table QVM:680-869 - must agree name by name. Rules out the table being built
    from a literal instead of the constant, which is the drift the QVM:554 header warns
    about ("Opcode assignments are part of the verifier/VK ABI"). -/
def opcodeConstants_matchTableOpcodes_ok : Bool :=
  opcodeConstantsByName.length == 31
    && (opcodeConstantsByName.all fun (name, value) =>
          ((quotientOpcodeTable.filter fun s => s.name == name).map fun s => s.opcode)
            == [value])

/-- QVM:921-932 and the four dynamic forms. The lookup must find every table byte, must
    miss the reserved and unassigned ones, and `quotient_opcode_byte_len` must return
    `none` for exactly the four byte-only opcodes - the contract the walker depends on
    (QVM:2563-2564). -/
def opcodeSpec_lookup_ok : Bool :=
  (quotientVmSpec.opcodes.all fun s =>
      ((quotientOpcodeSpec s.opcode).map fun t => t.name) == some s.name)
    && quotientOpcodeSpec 0x00 == none
    && quotientOpcodeSpec 0x17 == none
    && quotientOpcodeSpec 0x18 == none
    && quotientOpcodeSpec 0x23 == none
    && quotientOpcodeByteLen qOpLin7 == some 22
    && quotientOpcodeByteLen qOpBilin7Row == some 24
    && quotientOpcodeByteLen qOpBilin7Pairwise == some 18
    && quotientOpcodeByteLen qOpPushMemLiteral == some 5
    && quotientOpcodeByteLen qOpFoldSelector == some 4
    && (quotientVmSpec.opcodes.filter fun s =>
          quotientOpcodeByteLen s.opcode == none).length == 4

/-- THE YUL-EMITTER LEG. M:233-265 assigns each Askama field from a `Q_OP_*` constant
    by hand, and the template interpolates the field. Nothing compares that hand-built
    list with the table, so a field wired to the wrong constant is invisible to
    `cargo check`. This gate compares the two as data, in both directions, and it is
    the only thing in the tree that does. -/
def opcodeTable_matchesRenderedTemplateConstants_ok : Bool :=
  renderedOpcodeConstants.length == 31
    && (renderedOpcodeConstants.all fun (name, value) =>
          quotientOpcodeTable.any fun s => s.name == name && s.opcode == value)
    && (quotientOpcodeTable.all fun s =>
          renderedOpcodeConstants.any fun (name, value) =>
            name == s.name && value == s.opcode)

/-- The same for the nine memory tokens (M:266-276), plus the dense-run claim
    Models.lean:1136 makes in prose: the tokens are exactly 1..9. -/
def memTokenTable_matchesRenderedTemplateConstants_ok : Bool :=
  renderedMemTokenConstants.length == 9
    && (renderedMemTokenConstants.all fun (name, value) =>
          quotientMemTokenTable.any fun s => s.name == name && s.token == value)
    && (quotientMemTokenTable.all fun s =>
          renderedMemTokenConstants.any fun (name, value) =>
            name == s.name && value == s.token)
    && (quotientMemTokenTable.map fun s => s.token) == [1, 2, 3, 4, 5, 6, 7, 8, 9]
    && (quotientMemTokenTable.all fun s => s.token < 256)
    && !hasDuplicateNat (quotientMemTokenTable.map fun s => s.token)

/-- QVM:911-919: the spec record must carry the same constants the table entries were
    built from. Rules out the spec being hand-filled with a copy that has since drifted,
    which is exactly the shape of the LT:2314-2322 assertions. -/
def quotientVmSpec_fieldsMatchTheConstants_ok : Bool :=
  quotientVmSpec.opcodes == quotientOpcodeTable
    && quotientVmSpec.memTokens == quotientMemTokenTable
    && quotientVmSpec.runCompactionMinLen == quotientVmRunCompactionMinLen
    && quotientVmSpec.limbCount == quotientVmLimbs
    && quotientVmSpec.limbPairwiseTerms == quotientVmPairwiseTerms
    && quotientVmSpec.limbPairwiseCoeffs == quotientVmPairwiseCoeffs
    && quotientVmRunCompactionMinLen == 4

/-! ### Hazard 5: the limb-count cross-check -/

/-- HAZARD 5, and the stop condition the plan set. `QUOTIENT_VM_LIMBS =
    layout::quotient_limb::LIMBS = 7` (QVM:548, LM:355) against
    `AccumulatorEncoding.supportedNumLimbs = accumulatorLimbs = 7`
    (Api.lean:427, :172), which is itself `layout::accumulator::LIMBS` (LM:297).
    They AGREE, so the package does not stop. The Rust pins both at LM:902 and LM:916
    inside its own layout test, and the derived relations (49 = 7*7, 13 = 2*7-1,
    6 = 7-1) are re-checked here rather than trusted.

    PLAN 9.5's `Supported.hLimbs` (docs/PLAN.md:420, landed as
    Lowering/Types.lean:52-61) is the relational statement
    `numQuotientLimbs = csDegree - 1`, not a number, so it cannot disagree with 7 and
    is not treated as a numeric cross-check - see the report. -/
def limbCounts_crossCheckAccumulatorLimbs_ok : Bool :=
  quotientVmLimbs == 7
    && quotientVmLimbs == accumulatorLimbs
    && quotientVmLimbs == AccumulatorEncoding.supportedNumLimbs
    && quotientVmPairwiseTerms == quotientVmLimbs * quotientVmLimbs
    && quotientVmPairwiseCoeffs == 2 * quotientVmLimbs - 1
    && quotientLimbLinCoeffs == quotientVmLimbs - 1
    && quotientVmPairwiseTerms == 49
    && quotientVmPairwiseCoeffs == 13
    && limb7YulCoeffs.length == quotientLimbLinCoeffs
    && wideLimb7YulCoeffs.length == quotientLimbLinCoeffs
    && templateConstantsDefault.quotientVm.limbCount == quotientVmLimbs
    && templateConstantsDefault.quotientVm.limbPairwiseCoeffs == quotientVmPairwiseCoeffs
    && templateConstantsDefault.quotientVm.byteU32Bytes == quotientVmByteU32Bytes

/-- The three limb opcodes' declared lengths must be the lengths the limb count implies,
    and no other opcode's length may depend on it. This is the coupling that makes a
    mis-sized shape detectable rather than silently mis-decoded: LIN7 carries exactly
    `LIMBS` (slot, ptr) pairs and the decoder reads exactly that many (QVR:386). -/
def limbOpcodeWidthsTrackTheLimbCount_ok : Bool :=
  (quotientOpcodeTable.filter fun s =>
      s.encoding == .limbLin || s.encoding == .limbBilinRow
        || s.encoding == .limbBilinPairwise).length == 3
    && (quotientOpcodeTable.find? fun s => s.name == "lin7").map (fun s => s.byteLen)
        == some (1 + quotientVmLimbs * (1 + quotientVmByteU16Bytes))
    && (quotientOpcodeTable.find? fun s => s.name == "bilin7_row").map (fun s => s.byteLen)
        == some (1 + quotientVmByteU16Bytes
                  + quotientVmLimbs * (1 + quotientVmByteU16Bytes))
    && (quotientOpcodeTable.find? fun s => s.name == "bilin7_pairwise").map (fun s => s.byteLen)
        == some (1 + 2 * quotientVmByteU16Bytes + quotientVmPairwiseCoeffs)

/-! ### Hazard 2: integer widths -/

/-- HAZARD 2 at `QuotientMem`, and R-48's distinctness precondition: the fixture's
    eight literal pointers are asserted pairwise distinct BEFORE anything compares them,
    because the shared `LayoutKats.verifierLayoutFixture` has all-zero bases and a
    pointer comparison made on it is vacuous. Also pins that every token the fixture
    uses is a table token, and that the table's tokens fit `u8`. -/
def quotientMem_widthsAndFixture_ok : Bool :=
  memFixtureLiterals.length == 8
    && !hasDuplicateNat memFixtureLiterals
    && (memFixtureLiterals.all fun p => p < 2^32)
    && (quotientMemTokenTable.all fun s => s.token < 256)
    && (memFixture.all fun m =>
          match m with
          | .literal _ => true
          | .token t => quotientMemTokenTable.any fun s => s.token == t
          | .tokenOffset t _ => quotientMemTokenTable.any fun s => s.token == t)

/-- HAZARD 2, stated as a divergence rather than hidden: the Rust truncates
    `offset as u32` (QVM:2974, QVM:2983) in the release profile, and a Lean `Nat`
    does not. So the Lean model distinguishes pointers the Rust would collapse. The
    claim being gated is that the port does NOT silently widen - the boundary is named
    and pinned, and the reachability argument is in the header. Rules out a port that
    emulated the truncation and thereby hid a pointer bug that the Rust would also hide,
    and rules out a reader assuming the two models agree above 2^32. -/
def quotientMem_noTruncation_ok : Bool :=
  QuotientMem.literal (2^32) != QuotientMem.literal 0
    && QuotientMem.literal (2^32 + 0x100) != QuotientMem.literal 0x100
    && QuotientMem.tokenOffset qMemL0 (2^32) != QuotientMem.tokenOffset qMemL0 0
    && quotientVmByteU32Bytes == 4
    && 2^32 == (2^8)^4

/-- HAZARD 2 at the `u16` positions, where the reference does NOT truncate: every
    producer of a limb pointer goes through `u16::try_from(ptr).ok()?` (QVM:3445,
    QVM:3506, QVM:4024), so an out-of-width pointer makes the recognizer return `None`
    and the builder falls back. The boundary is 0x10000, and the two encodings the
    boundary selects between differ by exactly the width difference in the table. -/
def limbPointerU16Boundary_ok : Bool :=
  (limbPointerFixture.all fun p => p < 0x10000)
    && 0xffff < 0x10000
    && !((0x10000 : Nat) < 0x10000)
    && (quotientOpcodeByteLen qOpPushMemU16 == some 3)
    && (quotientOpcodeByteLen qOpPushMemLiteral == some 5)
    && quotientVmByteU32Bytes - quotientVmByteU16Bytes == 2

/-! ### Hazard 4: the shape-recognition invariant -/

/-- HAZARD 4, part (a): a shape carries coefficients and pointers and nothing else, so
    correctness cannot depend on a gate label. Checked as an equivalence over six pairs
    of shapes (equal shapes iff equal operand censuses), plus a field census of the
    MODARITH7 bundle: 9 pointers and 6 coefficients for the seven blocks of
    `modarith7Fixture`, so a new field changes a count and reddens this gate. -/
def limbShapeCarriesNoGateLabel_ok : Bool :=
  shapeOperandsDetermineShape lin7Fixture lin7Fixture
    && shapeOperandsDetermineShape lin7Fixture lin7Short
    && shapeOperandsDetermineShape lin7Fixture lin7Long
    && shapeOperandsDetermineShape bilin7RowFixture bilin7RowShort
    && shapeOperandsDetermineShape bilin7PairwiseFixture bilin7PairwiseShort
    && shapeOperandsDetermineShape lin7Fixture bilin7RowFixture
    && lin7Fixture.pointerOperands.length == 7
    && lin7Fixture.coefficientOperands.length == 7
    && bilin7RowFixture.pointerOperands.length == 8
    && bilin7PairwiseFixture.pointerOperands.length == 2
    && bilin7PairwiseFixture.coefficientOperands.length == 13
    && modarith7Fixture.pointerOperands.length == 9
    && modarith7Fixture.coefficientOperands.length == 6
    && (modarith7Fixture.pointerOperands.all fun p => p < 0x10000)

/-- HAZARD 4, part (b), and the honest half: the arity is NOT enforced by the type. A
    6-term and an 8-term `Lin7` are well-typed values here and in Rust, and both are
    distinct from the 7-term one, so nothing in the representation stops a mis-sized
    shape from existing. What stops it is the recognizer's length guard, which is
    compiler and is not ported in this package. -/
def limbShapeArityNotEnforcedByType_ok : Bool :=
  lin7Fixture.pointerOperands.length == 7
    && lin7Short.pointerOperands.length == 6
    && lin7Long.pointerOperands.length == 8
    && lin7Fixture != lin7Short
    && lin7Fixture != lin7Long
    && lin7Short != lin7Long
    && bilin7RowShort.pointerOperands.length == 7
    && bilin7PairwiseFixture.coefficientOperands.length == 13
    && bilin7PairwiseShort.coefficientOperands.length == 12
    && bilin7PairwiseLong.coefficientOperands.length == 14

/-- HAZARD 4, part (c): THE FALLBACK-NOT-MISEVALUATION GATE. A shape that is not
    recognized exactly - including one recognized with the wrong arity - must fall back
    to the ordinary Fr VM opcodes and must never be emitted as a fused opcode. The two
    arms are pinned apart, so a dispatch that defaulted a mis-sized shape to the fused
    arm (the mis-evaluation the doc forbids) reddens this gate, and so does a dispatch
    that ignored its argument and always fell back. -/
def limbShapeMisRecognition_fallsBack_ok : Bool :=
  quotientLimbShapeEmit none == .generic
    && quotientLimbShapeEmit (some lin7Fixture) == .fused lin7Fixture
    && quotientLimbShapeEmit (some bilin7RowFixture) == .fused bilin7RowFixture
    && quotientLimbShapeEmit (some bilin7PairwiseFixture) == .fused bilin7PairwiseFixture
    && quotientLimbShapeEmit (some lin7Short) == .generic
    && quotientLimbShapeEmit (some lin7Long) == .generic
    && quotientLimbShapeEmit (some bilin7RowShort) == .generic
    && quotientLimbShapeEmit (some bilin7PairwiseShort) == .generic
    && quotientLimbShapeEmit (some bilin7PairwiseLong) == .generic
    && (quotientLimbShapeEmit (some lin7Fixture)) != (quotientLimbShapeEmit (some lin7Short))
    && (quotientLimbShapeEmit (some bilin7PairwiseFixture))
        != (quotientLimbShapeEmit (some bilin7PairwiseShort))

/-- HAZARD 4, part (d): the fallback is always AVAILABLE, which is what makes "falls
    back, never mis-evaluates" a real option rather than a promise. Changing the limb
    count moves exactly three opcode lengths - the three limb classes - and leaves the
    other 28 fixed, so the generic Fr path (push, add, mul, neg, fold, the fused
    product forms) does not depend on the limb algebra at all. -/
def limbWidthSensitivity_onlyLimbEncodings_ok : Bool :=
  let limbClasses : List QuotientOpcodeEncoding :=
    [.limbLin, .limbBilinRow, .limbBilinPairwise]
  let allEncodings : List QuotientOpcodeEncoding :=
    [.none, .u8, .u16, .u24, .u32, .tokenOffset, .addMulMemMemConstU8,
     .addMulConstU8MemU16, .addMulMemMem, .runAddMulMemMemConstU8,
     .runAddMulConstU8MemU16, .limbLin, .limbBilinRow, .limbBilinPairwise,
     .limbModarith7, .affineSum]
  allEncodings.length == 16
    && (allEncodings.all fun e =>
          (derivedByteLenWith 7 13 e == derivedByteLenWith 8 15 e) == (!limbClasses.contains e))
    && (quotientVmSpec.opcodes.filter fun s => !limbClasses.contains s.encoding).length == 28
    && derivedByteLenWith 7 13 .limbLin == 22
    && derivedByteLenWith 8 15 .limbLin == 25

/-- rust: QVM:1055-1069 against QVM:631-633. The three fused product shapes exist twice
    - as enum variants and as operand-encoding classes - and nothing ties the two names.
    Rules out a rename on one side, which would leave the recognizer emitting an opcode
    the table describes under a different class. -/
def productAdd_matchesFusedOpcodeEncodings_ok : Bool :=
  let products : List QuotientProductAdd :=
    [ .memMemConstU8 0x140 0x160 (BitVec.ofNat 256 7),
      .constU8Mem (BitVec.ofNat 256 1) 0x180,
      .memMem 0x1a0 0x1c0 ]
  products.length == 3
    && (products.all fun p =>
          (quotientOpcodeTable.filter fun s => s.name == p.encoding).length == 1)
    && (products.map fun p =>
          (quotientOpcodeTable.find? fun s => s.name == p.encoding).map fun s => s.encoding)
        == [some .addMulMemMemConstU8, some .addMulConstU8MemU16, some .addMulMemMem]
    && (quotientVmSpec.opcodes.filter fun s =>
          s.encoding == .addMulMemMemConstU8 || s.encoding == .addMulConstU8MemU16
            || s.encoding == .addMulMemMem).length == 3

/-! ### Hazards 2 and 3 at the expression type, and the record field censuses -/

/-- HAZARD 3: the recursive type folds structurally. The tree is depth 3 on purpose -
    the DEPTH is not what is being tested, per the plan's instruction to keep gate trees
    shallow - what is tested is that every constructor position is reachable by a
    structural fold and that the fold agrees with the tree's shape. Rules out a fold
    that drops a constructor (a `Neg` arm that returns `[]`, say) and a fold that
    reverses the operand order of `Add`. -/
def quotientExpr_structuralRecursion_ok : Bool :=
  exprFixture.memLeaves == [.literal 0x100, .token qMemBeta, .tokenOffset qMemX 0x20]
    && exprFixture.nodeCount == 8
    && (exprFixtureAlt.memLeaves == [.literal 0x120, .token qMemBeta, .tokenOffset qMemX 0x20])
    && (QuotientExpr.neg exprFixture).nodeCount == 9
    && (QuotientExpr.neg exprFixture).memLeaves == exprFixture.memLeaves
    && (QuotientExpr.const (BitVec.ofNat 256 0)).memLeaves == []
    && (QuotientExpr.add exprFixture exprFixtureAlt).memLeaves
        == exprFixture.memLeaves ++ exprFixtureAlt.memLeaves

/-- Every payload field participates in equality, on all the types that carry one.
    This is the R-40 F4 / Api.lean:1717 discipline: a variant whose payload is dropped
    still prints and still compares equal to the wrong thing, and the only cheap defence
    is to assert the inequality directly. -/
def payloadFieldsParticipateInEquality_ok : Bool :=
  QuotientExpr.const (BitVec.ofNat 256 1) != QuotientExpr.const (BitVec.ofNat 256 2)
    && QuotientExpr.mem (QuotientMem.literal 0x100) != QuotientExpr.mem (QuotientMem.literal 0x120)
    && QuotientExpr.mem (QuotientMem.token 1) != QuotientExpr.mem (QuotientMem.tokenOffset 1 0)
    && exprFixture != exprFixtureAlt
    && QuotientExpr.add exprFixture exprFixtureAlt != QuotientExpr.mul exprFixture exprFixtureAlt
    && QuotientExpr.neg exprFixture != exprFixture
    && QuotientMem.literal 0x100 != QuotientMem.token 0x100
    && QuotientMem.tokenOffset qMemL0 0x20 != QuotientMem.tokenOffset qMemBeta 0x20
    && QuotientMem.tokenOffset qMemL0 0x20 != QuotientMem.tokenOffset qMemL0 0x40
    && QuotientTarget.selector 0 != QuotientTarget.selector 1
    && QuotientTarget.main != QuotientTarget.selector 0
    && QuotientExecutionKind.nativeIdentity 0 != QuotientExecutionKind.nativeIdentity 1
    && QuotientProgramItem.nativeIdentity 0 != QuotientProgramItem.nativeIdentity 1
    && QuotientLeaf.mem (QuotientMem.literal 1) != QuotientLeaf.const (BitVec.ofNat 256 1)
    && (identityFixture 0 .main).meta_.source != (identityFixture 1 .main).meta_.source
    && identityFixture 0 .main != identityFixture 0 (QuotientTarget.selector 0)
    && identityFixture 0 .main != { (identityFixture 0 .main) with var := "u" }
    && identityFixture 0 .main != { (identityFixture 0 .main) with lines := [] }
    && identityFixture 0 .main != { (identityFixture 0 .main) with expr := exprFixtureAlt }

/-- FIELD CENSUS (the R-40 F5a pattern, made structural rather than sampled): each
    record below is CONSTRUCTED with every field named, so adding a field to the Lean
    record - or, reading the same cite the other way, to the Rust struct - stops this
    file from compiling instead of slipping past a gate that inspects four fields out of
    ten. The assertions then pin that the constructed values are what the fields say. -/
def programRecords_fieldsExact_ok : Bool :=
  let build : QuotientProgramBuild :=
    { bytes := ByteArray.mk #[1, 2, 3]
      consts := [BitVec.ofNat 256 9]
      maxStack := 1
      usedOps := ByteArray.mk #[9]
      usedMemTokens := ByteArray.mk #[1] }
  let plan : QuotientProgramPlan :=
    { inlineIdentities := [identityFixture 0 .main]
      items := [QuotientProgramItem.identity (identityFixture 1 .main),
                QuotientProgramItem.nativePermutation, QuotientProgramItem.nativeLookup,
                QuotientProgramItem.nativeIdentity 0]
      nativeIdentities := [identityFixture 2 .main]
      nativePermutationIdentities := [identityFixture 3 .main]
      nativeLookupIdentities := [identityFixture 4 .main]
      structuredTailIdentities := [identityFixture 5 .main]
      sortedSimple := [7, 11]
      hasNativePermutation := true
      hasNativeLookup := false
      selectorFold := { gapsByIdentity := [some 1], tailExponents := [2], maxPower := 2 } }
  let scalar : RepackedProofScalarLayout :=
    { evalOffset := 768, numEvals := 5, qEvalOffset := 1056, numPointSets := 2 }
  let identMeta : QuotientIdentityMetadata :=
    { globalIndex := 3, source := QuotientIdentitySource.permutation 1 }
  bytesToList build.bytes == [1, 2, 3]
    && build.consts.length == 1
    && build.maxStack == 1
    && bytesToList build.usedOps == [9]
    && bytesToList build.usedMemTokens == [1]
    && plan.items.length == 4
    && plan.inlineIdentities.length == 1
    && plan.nativeIdentities.length == 1
    && plan.nativePermutationIdentities.length == 1
    && plan.nativeLookupIdentities.length == 1
    && plan.structuredTailIdentities.length == 1
    && plan.sortedSimple == [7, 11]
    && plan.hasNativePermutation && !plan.hasNativeLookup
    && plan.selectorFold.maxPower == 2
    && scalar.evalOffset == 768 && scalar.numPointSets == 2
    && identMeta.globalIndex == 3
    && (plan.items.filterMap fun it =>
          match it with
          | .identity i => some i.meta_.globalIndex
          | _ => none) == [1]

/-- rust: QVM:347-365 against API:286-303. The two enums are isomorphic and the Rust
    never checks it: `quotient_execution_entry` (QVM:478-489) takes the kind as a
    parameter and the manifest conversion is a field copy, so a divergence is invisible
    to the compiler. This gate is the tie: the map is injective on all six variants, the
    payload survives, and the image is exactly the api.rs enum's six constructors. -/
def executionKind_agreesWithQuotientIdentityExecution_ok : Bool :=
  let kinds : List QuotientExecutionKind :=
    [.inline, .interpreted, .nativePermutation, .nativeLookup, .nativeIdentity 3,
     .structuredTail]
  let executions : List QuotientIdentityExecution :=
    [.inline, .interpreted, .nativePermutation, .nativeLookup, .nativeIdentity 3,
     .structuredTail]
  kinds.length == 6
    && (kinds.all fun k =>
          (kinds.filter fun k2 => executionOfKind k == executionOfKind k2).length == 1)
    && (kinds.all fun k => executions.contains (executionOfKind k))
    && (executions.all fun e => kinds.any fun k => executionOfKind k == e)
    && executionOfKind (.nativeIdentity 3) == QuotientIdentityExecution.nativeIdentity 3
    && executionOfKind (.nativeIdentity 3) != executionOfKind (.nativeIdentity 4)

/-- rust: QVM:167-225. The repacked proof frame, with pairwise DISTINCT counts in every
    position so no term can be dropped or duplicated without changing the total:
    6 prefix G1s, 5 evals, 2 point sets. Pins the five-term shape of both lengths, that
    the padded form is the larger by exactly (prefix + 2) * (G1_BYTES -
    G1_COMPRESSED_BYTES), and that the scalar offsets are the partial sums of the same
    frame. -/
def repackedProofLayout_arithmetic_ok : Bool :=
  let plan : RepackedProofLayoutPlan :=
    { g1Groups := [3, 2, 1], numEvals := 5, numPointSets := 2 }
  plan.prefixG1Count == 6
    && plan.compressedLen == 6 * 48 + 5 * 32 + 48 + 2 * 32 + 48
    && plan.repackedLen == 6 * 128 + 5 * 32 + 128 + 2 * 32 + 128
    && plan.compressedLen == 608
    && plan.repackedLen == 1248
    && plan.repackedLen - plan.compressedLen == (plan.prefixG1Count + 2) * (128 - 48)
    && plan.scalarLayout.evalOffset == 6 * 128
    && plan.scalarLayout.qEvalOffset == 6 * 128 + 5 * 32 + 128
    && plan.scalarLayout.numEvals == 5
    && plan.scalarLayout.numPointSets == 2
    && plan.scalarLayout.qEvalOffset + plan.numPointSets * wordBytes + g1Bytes
        == plan.repackedLen

/-- The two G1 widths must not be interchangeable: this is the single most likely
    transcription error in the pair of length functions above, and a swap changes both
    totals by the same amount it leaves the offsets at. -/
def repackedProofLayout_widthsDiffer_ok : Bool :=
  g1Bytes == 128 && g1CompressedBytes == 48 && g1Bytes != g1CompressedBytes
    && wordBytes == 32
    && (let plan : RepackedProofLayoutPlan :=
          { g1Groups := [3, 2, 1], numEvals := 5, numPointSets := 2 }
        plan.repackedLen != plan.compressedLen)

/-- rust: QVM:177-187 against Abi.lean:472-480. The repacked plan is derived from the
    typed calldata layout, so the two ports must agree: the group list is the ABI
    layout's, the eval counts are the two word sections, and the last group is the
    unconditional quotient push. Rules out the plan being rebuilt from a different
    source than the layout the proof decoder uses. -/
def repackedProofLayout_fromProofLayout_ok : Bool :=
  let plan := RepackedProofLayoutPlan.fromProofLayout proofLayoutFixture
  plan.numEvals == 5
    && plan.numPointSets == 2
    && plan.g1Groups == proofLayoutFixture.commitmentReadGroups
    && plan.g1Groups.getLast? == some 3
    && plan.g1Groups.length == proofLayoutFixture.commitmentReadGroups.length
    && !hasDuplicateNat plan.g1Groups

/-- rust: QVM:507-513. The three ways `gap_for` can produce `None` are separated: an
    in-range entry that is itself `None`, an out-of-range index, and the default plan.
    A gap of 0 is pinned as distinguishable from no gap, which is the collapse a
    `getD 0`-style port would introduce. -/
def selectorFoldPlan_gapFor_ok : Bool :=
  let plan : SelectorFoldPlan :=
    { gapsByIdentity := [some 4, none, some 0], tailExponents := [7, 3], maxPower := 7 }
  plan.gapFor (identityFixture 0 .main) == some 4
    && plan.gapFor (identityFixture 1 .main) == none
    && plan.gapFor (identityFixture 2 .main) == some 0
    && plan.gapFor (identityFixture 3 .main) == none
    && plan.gapFor (identityFixture 99 .main) == none
    && selectorFoldPlanDefault.gapFor (identityFixture 0 .main) == none
    && selectorFoldPlanDefault.tailExponents == []
    && selectorFoldPlanDefault.maxPower == 0
    && plan.tailExponents.length == 2

/-- The opcode names are ABI in a second sense: they are the keys the template constants
    are rendered under, so a rename is a silent loss of a switch arm rather than a
    compile error. This pins the 31 names as a literal list, independent of the table. -/
def opcodeNames_pinned_ok : Bool :=
  (quotientVmSpec.opcodes.map fun s => s.name) ==
    ["push_const", "push_mem_literal", "push_mem_token", "push_mem_token_offset",
     "push_mem_u16", "add", "mul", "neg", "push_const_u8", "fold_main", "fold_selector",
     "add_const_u8", "mul_const_u8", "add_const", "mul_const", "add_mem_u16",
     "mul_mem_u16", "add_mul_mem_mem_const_u8", "add_mul_const_u8_mem_u16",
     "add_mul_mem_mem", "run_add_mul_mem_mem_const_u8", "run_add_mul_const_u8_mem_u16",
     "native_permutation", "native_lookup", "native_identity", "lin7", "bilin7_row",
     "bilin7_pairwise", "modarith7", "pow5", "affine_sum"]
  && (quotientMemTokenTable.map fun s => s.name) ==
      ["L_0_MPTR", "L_LAST_MPTR", "L_BLIND_MPTR", "BETA_MPTR", "GAMMA_MPTR", "X_MPTR",
       "THETA_MPTR", "TRASH_CHALLENGE_MPTR", "INSTANCE_EVAL_MPTR"]


end Midfall.Generator.QuotientVmKats

#eval Midfall.Generator.QuotientVmKats.templateArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_matchesYulTemplateCases_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_caseCoverageIsExact_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_noStaleNativeTrashCase_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.memTokenTable_matchesYulTemplateCases_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.memTokenTable_caseCoverageIsExact_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_lengthsAreDerivedFromEncoding_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_pinnedByteLengths_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_is31DistinctOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeConstants_matchTableOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeSpec_lookup_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeTable_matchesRenderedTemplateConstants_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.memTokenTable_matchesRenderedTemplateConstants_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.quotientVmSpec_fieldsMatchTheConstants_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbCounts_crossCheckAccumulatorLimbs_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbOpcodeWidthsTrackTheLimbCount_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.quotientMem_widthsAndFixture_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.quotientMem_noTruncation_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbPointerU16Boundary_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbShapeCarriesNoGateLabel_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbShapeArityNotEnforcedByType_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbShapeMisRecognition_fallsBack_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.limbWidthSensitivity_onlyLimbEncodings_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.productAdd_matchesFusedOpcodeEncodings_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.quotientExpr_structuralRecursion_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.payloadFieldsParticipateInEquality_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.programRecords_fieldsExact_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.executionKind_agreesWithQuotientIdentityExecution_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.repackedProofLayout_arithmetic_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.repackedProofLayout_widthsDiffer_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.repackedProofLayout_fromProofLayout_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.selectorFoldPlan_gapFor_ok -- expect true
#eval Midfall.Generator.QuotientVmKats.opcodeNames_pinned_ok -- expect true

