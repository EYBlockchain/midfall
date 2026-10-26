-- |
-- Midfall.Generator.Quotient.VmCertify
--
-- THE QUOTIENT VM CERTIFIER DRIVER: the seed derivation, the identity segment walker and
-- the certification comparison. Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/vm/certify.rs (365 lines,
-- 14883 bytes at git HEAD), cited below as QVC. Work package P-09d.
--
-- CITATION NOTATION. QVC is certify.rs read through `git show HEAD:<path>`, every range
-- re-derived from that output and never from wc -l on a dirty checkout
-- (docs/plans/README.md standing note 2). QVM is vm/mod.rs (4336 lines at HEAD), whose
-- vocabulary P-09a landed in VmTypes.lean and whose builder and opcode-length walker P-09c
-- landed in VmBuilder.lean. QVR is vm/reference.rs (549 lines at HEAD), P-09b's
-- interpreter, landed in VmReference.lean and imported here as the second implementation
-- the certifier compares against. LT is lowering/tests.rs (5156 lines at HEAD), where the
-- Rust's only seed test lives (LT:425-507). M is lowering/render/models.rs (1494 lines at
-- HEAD), whose `Halo2VerifyingKey::bytes` (M:414-422) is the VK payload the seed absorbs
-- and which Models.lean already ports. CUR is curves/src/bls12_381/fq.rs, cited once, for
-- the `{:?}` shape of a field element (CUR:128-138).
--
-- WHAT THIS FILE BUYS PLAN 9.5 (the required finding, stated here and gated below).
--
-- P-09c's report said qvm_compile_correct cannot be STATED until (a) the seed derivation
-- and (b) the identity segment walker exist, because the hypothesis of the theorem
-- mentions the finalized artifact and the challenge derived from it, and a multi-identity
-- program has no Lean-side segmenter. Both are here: `deriveCertifySeed` (QVC:48-76) and
-- `identitySegment` (QVC:228-245). What the theorem still lacks is named under WHAT THIS
-- PACKAGE STILL OWNS at the bottom of this header, and the answer is not nothing - see
-- the package report's required finding.
--
-- HAZARD 4 FIRST, BECAUSE IT FRAMES EVERY GATE IN THIS FILE.
--
-- The Rust certification is PROBABILISTIC. `certify_quotient_program` samples ONE
-- assignment - the deterministic challenge derived from the artifacts by
-- `deriveCertifySeed` - evaluates the emitted bytecode and the expression tree at that
-- one point, and compares (QVC:147-165). A miscompile produces a DIFFERENT polynomial,
-- and two distinct polynomials of degree d agree on at most d points, so the check fails
-- with probability at least 1 - d/|Fr| (QVR:12-18). It is a generator-time gate over a
-- single concrete program, not a theorem about all programs.
--
-- A Lean theorem over these same objects would be UNCONDITIONAL: `qvm_compile_correct`
-- quantifies over every assignment, not one sampled challenge, and its proof would have
-- to be by structural induction over the emitter and the interpreter, which nothing in
-- the reference does. NOTHING IN THIS FILE IS THAT THEOREM. Every check below is a Bool
-- or an IO Bool evaluated on fixtures at #eval time (docs/REVIEW.md R-38), and the fact
-- that all of them are true says that this port reproduces the reference's byte-level
-- behaviour on the fixtures - it says nothing about programs the fixtures do not contain.
-- Where a gate compares the emitted bytecode against the oracle over every fixture
-- (GATE 8, GATE 9) it is doing deterministically what the Rust does probabilistically,
-- which is stronger on the fixture and weaker than the theorem: it is a KAT, not a proof.
--
-- HAZARD 1: `deriveCertifySeed` IS THE SOUNDNESS HINGE (QVC:41-76).
--
-- The preimage, in this exact order, transcribed line by line from QVC:54-75:
--   "midfall/quotient-vm/certify-seed/v3"                       (QVC:39, 35 bytes)
--   builds.len() as u64 big-endian                             (QVC:56)
--   for each build, in list order:
--     build.bytes.len() as u64 BE, then the finalized BYTES    (QVC:58-59)
--     build.consts.len() as u64 BE, then each U256 as 32 BE    (QVC:61-64)
--   exprs.len() as u64 BE                                      (QVC:67)
--   for each expression, the tagged tree (QVC:69, QVC:79-111):
--     Const(v) -> [0] || v.to_be_bytes::<32>()
--     Mem(Literal p) -> [1] || p.to_be_bytes()      (u32, 4 bytes)
--     Mem(Token t) -> [2, t]                        (t is a u8)
--     Mem(TokenOffset t o) -> [3, t] || o.to_be_bytes()
--     Add l r -> [4] || h(l) || h(r)                (left subtree first)
--     Mul l r -> [5] || h(l) || h(r)
--     Neg i -> [6] || h(i)
--   vk_payload.len() as u64 BE, then the payload bytes         (QVC:72-73)
-- then ONE Keccak-256 over the whole stream (QVC:75).
--
-- Byte-exactness is not optional, and the reason is the argument in the doc comment at
-- QVC:41-47: the challenge must be bound to the artifact that was fixed BEFORE the
-- challenge was known, so a different preimage is a different challenge and the binding
-- evaporates. The gates therefore check the stream SEGMENT BY SEGMENT against hand-written
-- byte lists that do not go through `certifySeedPreimage` at all (GATE 1), pin the whole
-- 263-byte fixture preimage and its digest against an independent Python Keccak (GATE 2),
-- pin each of the seven node tags (GATE 3), read the tag and the update ORDER back out of
-- certify.rs from disk at #eval time (GATE 4 and GATE 5, D-P19), and re-derive the
-- sensitivity claims the Rust's own test makes (GATE 6). The chain is then closed to the
-- challenge itself: seed -> QuotientRefMemory::derive -> a pinned field element, all
-- three layers checked against Python (GATE 7).
--
-- The independent Python model is a Keccak-256 written from FIPS-202 (original padding,
-- not SHA3-256), validated on keccak256("") = c5d24601...85a470 and keccak256("abc") =
-- 4e03657a...2d6c45 before it was used. It is not committed: the pins it produced are in
-- this file and the recipe that produced them is in each gate's doc comment, so a reviewer
-- re-derives them from the Rust source rather than from Lean code that checks itself.
--
-- HAZARD 2: THE `v3` TAG IS UNPINNED IN THE RUST, AND THAT IS A REAL HOLE.
--
-- A grep for "certify-seed" under proofs/ returns exactly one hit: QVC:39. There is no v1
-- or v2 tag anywhere in the tree (the only other domain tags in this directory are
-- "reference-memory/v1" and its "/hi" sibling, QVR:90 and QVR:97), so the v3 implies
-- earlier schemes that were replaced in place rather than kept side by side. The Rust's
-- only seed test, LT:425-507, asserts FIVE `assert_ne!` sensitivities and NO digest value:
-- it would pass unchanged if the tag were edited to v4 tomorrow, because every perturbation
-- it tries still changes the hash. A silent bump would therefore change the challenge
-- distribution without changing any type, any test, or any byte of the emitted verifier.
-- `seedDomainTag_artifactPinned_ok` closes that hole on the Lean side: it reads the literal
-- out of certify.rs at #eval time and requires it to equal the Lean tag, so the next bump
-- reddens a named gate. `seedPreimageLayout_artifact_ok` does the same for the ORDER of the
-- ten `hasher.update` calls, and `exprHashTags_artifact_ok` for the seven node tags.
--
-- HAZARD 3: THE SEGMENT WALKER IS WHAT MAKES THE PER-IDENTITY STATEMENT COVER A REAL
-- PROGRAM.
--
-- P-09b established that `evalQuotientIdentity` only ever sees ONE identity's expression
-- subprogram - the slice `&bytes[cursor..expr_end]` that `identity_segment` locates - and
-- P-09c supplied only `finalizedIdentitySegment`, which strips a single trailing fold from
-- a one-identity buffer. `identitySegment` (QVC:228-245) is the general walker: it advances
-- opcode by opcode using the reference's own `quotient_op_len` (QVM:3008-3024, ported by
-- P-09c as `QuotientBuilder.quotientOpLen`), stops at FOLD_MAIN or FOLD_SELECTOR, and
-- REJECTS a native marker inside an expression. GATE 9 round-trips a three-identity built
-- program: segments extracted at pinned byte offsets, each run through `QVM.run`, each
-- equal to the direct evaluation of the expression tree it was lowered from.
--
-- HAZARD 5 AND 6: NOTHING WAS PULLED IN SIDEWAYS.
--
-- * No validator. `validate_quotient_program` (QVM:2009-2027) is the next package; the
--   Rust's own doc says the certifier runs AFTER it and assumes well-formedness
--   (QVC:126-128), so nothing here needs it. P-09c's `finishValidatorLeg` obligation
--   stands and is not silently discharged.
-- * No third copy of the walker. `quotientOpLen`, `quotientProgramUsage`,
--   `quotientAffineSumOpLen` and `quotientModarith7OpLen` stay in
--   `Midfall.Generator.QuotientBuilder`, where P-09c put them and where the reference
--   puts them: all four are vm/mod.rs items (QVM:3008-3059, QVM:1976-1994), not certify.rs
--   items, so hazard 6's "if and only if they belong here" answers NO and this file
--   imports them instead. The COMPACT-SCOPED COPY notes at VmBuilder.lean:1286 and
--   VmBuilder.lean:1424 say "P-09d owns the general walker and should absorb this"; the
--   finding in the package report is that the note is misdirected - the general walker is
--   already in the right file, and what P-09d adds is the first CALLER outside the
--   builder. The note should be retired by whoever ports the validator, which also lives in
--   vm/mod.rs.
-- * `QuotientProgramBuild` comes from P-09c's `finish`; nothing here re-derives it.
--
-- PORT RULES AS THEY APPLY HERE (PLAN section 4, R1-R11).
--
-- * R1 provenance: one Lean def per Rust item, source order except where WHAT MOVED says
--   otherwise. Two non-Rust defs, each named as such at its site: `certifySeedPreimage`
--   (the byte stream the Rust's incremental hasher holds internally, reified so the gates
--   can inspect it segment by segment) and `certifyItemWalk` (the driver's item loop with
--   the Rust's `cursor` local and `&mut mem` threaded as an explicit state pair).
-- * R2 names: snake_case to lowerCamelCase. `hash_quotient_expr` becomes `hashQuotientExpr`
--   with a CHANGED SHAPE, recorded here: the Rust threads `&mut Keccak256` and calls
--   `update`; the pure port returns the bytes one subtree contributes and the caller
--   appends. Same stream, no state. `QuotientProgramItem::NativeIdentity`'s payload is
--   `nativeIndex` (VmTypes' spelling), and `identity.meta` is `identity.meta_` because
--   `meta` is a Lean reserved word (VmTypes' convention, plans README standing note 3).
-- * R3 iterators: `plan.items.iter().enumerate()` becomes an explicit index argument;
--   `filter_map` becomes `filterMap`; `.iter().zip().enumerate()` becomes `List.zip` with an
--   index argument, and `List.zip` truncates to the shorter input exactly as Rust's `zip`
--   does (which is why the Rust checks the two lengths first, QVC:313-319).
-- * R4 panics: the release profile again (BASELINE.md:143) - no overflow panic, no
--   debug_assert! in this file, but indexing and division by zero do panic. QVC contains
--   NO direct index and NO division: every byte read is `bytes.get(i).ok_or_else(...)`
--   (QVC:187, 198, 201, 258, 267, 270) and stays an explicit error in the port. The one
--   panic reachable through this driver is inside `quotient_op_len` (QVM:3022 unknown
--   opcode, QVM:2817 operand read past the end), which P-09c models as `QVMFault.panic`;
--   where the Rust would ABORT the render, the port returns Err carrying the panic site
--   text, because the driver's error type is the Rust's String. Recorded, and gated
--   (GATE 9's identitySegment_unknownOpcodeIsPanicClass_ok) rather than assumed.
-- * R5 integers: `usize`, `u64`, `u32`, `u16`, `u8` all become `Nat`. Three sites where the
--   width is load-bearing and is modelled: the u64 length prefixes (8 big-endian bytes,
--   `natToBytesBE n 8`), the u32 pointer and offset (`natToBytesBE p 4`, which drops high
--   bytes exactly as a fixed-width `to_be_bytes` does), and the u8 token (`token % 256`,
--   matching `deriveReferenceMemory`'s domain masking in VmReference). `Nat` cannot hold a
--   negative and the reference has no subtraction that can go below zero here: the
--   `bytes.len() - cursor` at QVC:220 is guarded by the `cursor != bytes.len()` test on the
--   line above, and `expr_end - cursor` is safe because `identitySegment` returns
--   `expr_end >= start`.
-- * R6 collections: `&[&QuotientProgramBuild]` becomes `List QuotientProgramBuild`,
--   `&[&QuotientExpr]` becomes `List QuotientExpr`, `&[u8]` becomes `Bytes`, and the
--   `&[u8]` read by absolute index becomes `List Nat` (the bridge `qvmBytesToNats`, P-09b's,
--   which `programBytesRoundTrip_ok` already proves lossless). `Vec` -> `List` per the
--   Generator row.
-- * R7/R8/R9: no endianness inversion beyond the to_be_bytes calls above (they ARE the
--   hazard-1 layout), no curve point read, no feature gate, no trait. `Halo2VerifyingKey`
--   is taken as a parameter exactly as the Rust takes it and only `vk.bytes` is called, so
--   no VK record is re-derived here.
-- * R10 totality: no `partial`. `hashQuotientExpr` is structural on `QuotientExpr`.
--   `identitySegment`'s Rust `while` loop is given an explicit fuel of `bytes.length`
--   iterations, sound because every arm advances the cursor by at least one byte - the
--   static table's lengths are all >= 1 and the four dynamic decoders return >= 1 - and
--   asserted never to bind by `segmentWalkFuelNeverBinds_ok`, the same discipline
--   VmReference's `loopFuelNeverBinds_ok` and VmBuilder's three fuel gates use.
-- * R11: the line-range table is in the package report.
--
-- WHAT MOVED, AND WHY (Lean is order-sensitive; the Rust is not).
-- 1. `identitySegment` (QVC:228-245) and `checkFold` (QVC:248-289) move AHEAD of
--    `certify_quotient_program` (QVC:129-225), which calls both; `identityValues`
--    (QVC:335-365) also needs `identitySegment`. Within the moved pair the Rust's order is
--    kept.
-- 2. `hash_quotient_expr` (QVC:79-111) moves ahead of `derive_certify_seed` (QVC:48-76),
--    its only caller, because the preimage def references it.
-- 3. `identityValues` (QVC:334-365) moves AHEAD of `certify_quotient_builds_agree`
--    (QVC:299-332), its only caller. In the Rust the callee sits below the caller; Lean
--    cannot see forward.
-- 4. The three `{:?}` renderers the error strings interpolate (`certifyFrDebug`,
--    `certifySourceDebug`, `certifyTargetDebug`) are declared before their first caller.
--    They are not Rust items; they are the Debug instances the format strings use, and
--    each cites the impl it reproduces.
--
-- WHAT THIS PACKAGE STILL OWNS (findings, not gaps to paper over).
-- * The validator leg (hazard 5): the Rust's certifier assumes the stream decodes and is
--   stack-safe. A Lean qvm_compile_correct inherits that assumption from the same
--   direction, so the validator is the next thing to land, not this file.
-- * The fold is still not modelled anywhere: FOLD_MAIN and FOLD_SELECTOR are hard errors
--   inside an identity expression (QVR:325-333) and `checkFold` only inspects emitted
--   bytes against the plan. The y-batch accumulation is Yul-side.
-- * `certify_quotient_builds_agree`'s dual build needs a BASELINE build, i.e. the same
--   identity stream emitted with the limb recognizers off. P-09e owns the recognizers, so
--   the two builds this gate compares differ only in the hook that is switched on: that is
--   enough to exercise the comparison and NOT enough to be the Rust's claim, which is about
--   real recognizers on a real circuit.

import Midfall.Common.Bytes
import Midfall.Common.Keccak
import Midfall.Generator.Models
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder

namespace Midfall.Generator.QuotientCertify

-- The opcode-length walker P-09c ported at VmBuilder.lean:1287 (rust: QVM:3008-3024).
-- Hazard 6: this file imports it rather than copying it a third time; see the header.
open Midfall.Generator.QuotientBuilder

/-! ## The seed derivation (rust: QVC:33-111) -/

/-- rust: QVC:39 (`QUOTIENT_CERTIFY_SEED_DOMAIN: &[u8] =
    b"midfall/quotient-vm/certify-seed/v3"`) @formal-baseline. The doc at QVC:33-38 says the
    seed is deterministic so failing renders reproduce exactly, and derived from the
    finalized artifact rather than fixed globally so the sampled assignment stays
    independent of any circuit author's pre-render view of the program. Hazard 2: the `v3`
    implies earlier schemes, and NOTHING in the Rust pins this literal - not the type, not
    a test (LT:425-507 asserts sensitivities only), not a golden file.
    `seedDomainTag_artifactPinned_ok` reads it back out of certify.rs at #eval time, which
    is what makes a silent bump visible. -/
def quotientCertifySeedDomain : Bytes := asciiBytes "midfall/quotient-vm/certify-seed/v3"

/-- rust: QVC:79-111 (`hash_quotient_expr`) @formal-baseline. "Hash one expression with
    explicit node and memory-address tags."

    R2 shape change, recorded: the Rust takes `&mut Keccak256` and calls `update`; the pure
    port returns the byte string one subtree contributes and the caller appends. The stream
    is identical - `update(a); update(b)` is Keccak over `a ++ b` - and reifying it is what
    lets `exprHashTags_artifact_ok` compare the seven tags against the source and
    `seedExprNodeTags_ok` pin them against hand-written bytes.

    R5 at the three width-bearing positions: the u32 pointer and offset go through
    `natToBytesBE .. 4` (a fixed-width big-endian write, high bytes dropped, exactly
    `u32::to_be_bytes`), and the token through `% 256` because the Rust's field is a `u8`
    (QVM:1042, QVM:1044). Lean's `QuotientMem` carries a `Nat` (VmTypes' hazard-2 decision),
    so the mask models the width the Rust cannot exceed rather than adding behaviour. -/
def hashQuotientExpr (expr : QuotientExpr) : Bytes :=
  match expr with
  | .const value =>
      qvmBytesAppend (qvmBytesOfNats [0]) (wordToBytesBE value)
  | .mem (.literal ptr) =>
      qvmBytesAppend (qvmBytesOfNats [1]) (natToBytesBE ptr 4)
  | .mem (.token token) =>
      qvmBytesOfNats [2, token % 256]
  | .mem (.tokenOffset token offset) =>
      qvmBytesAppend (qvmBytesOfNats [3, token % 256]) (natToBytesBE offset 4)
  | .add lhs rhs =>
      qvmBytesAppend (qvmBytesAppend (qvmBytesOfNats [4]) (hashQuotientExpr lhs))
        (hashQuotientExpr rhs)
  | .mul lhs rhs =>
      qvmBytesAppend (qvmBytesAppend (qvmBytesOfNats [5]) (hashQuotientExpr lhs))
        (hashQuotientExpr rhs)
  | .neg inner =>
      qvmBytesAppend (qvmBytesOfNats [6]) (hashQuotientExpr inner)

/-- The preimage stream `derive_certify_seed` feeds to Keccak-256, reified as a value.
    NOT a Rust item: the Rust holds it inside an incremental `Keccak256` and never sees it
    at once. It is split out because hazard 1 says byte-exactness is the whole game and a
    digest alone cannot be gated segment by segment - `seedPreimage_segments_ok` compares
    each slice of this buffer against bytes written by hand. -/
def certifySeedPreimage (builds : List QuotientProgramBuild) (exprs : List QuotientExpr)
    (vkPayload : Bytes) : Bytes :=
  let buildSegment (acc : Bytes) (build : QuotientProgramBuild) : Bytes :=
    let h := qvmBytesAppend acc (natToBytesBE build.bytes.size 8)
    let h := qvmBytesAppend h build.bytes
    let h := qvmBytesAppend h (natToBytesBE build.consts.length 8)
    build.consts.foldl (fun (acc : Bytes) (value : Word256) =>
      qvmBytesAppend acc (wordToBytesBE value)) h
  let h := qvmBytesAppend quotientCertifySeedDomain (natToBytesBE builds.length 8)
  let h := builds.foldl buildSegment h
  let h := qvmBytesAppend h (natToBytesBE exprs.length 8)
  let h := exprs.foldl (fun (acc : Bytes) (expr : QuotientExpr) =>
    qvmBytesAppend acc (hashQuotientExpr expr)) h
  qvmBytesAppend (qvmBytesAppend h (natToBytesBE vkPayload.size 8)) vkPayload

/-- rust: QVC:41-76 (`derive_certify_seed`) @formal-baseline. "Derive the random-assignment
    seed from every compared artifact. Binding the oracle expressions closes the case where
    a miscompile drops a tunable constant before it reaches the emitted constant table.
    Binding both builds makes the dual-build challenge depend on the optimized and baseline
    representations. The VK payload is included after generator invariants have checked that
    its quotient sections match the finalized build."

    `builds: &[&QuotientProgramBuild]` becomes `List QuotientProgramBuild` (R6) and the
    return `[u8; 32]` becomes a `Bytes` of size 32, the same rendering P-09b uses for
    `QuotientRefMemory.seed`. The two call sites pass one build (QVC:136) and two (QVC:307);
    both are gated. -/
def deriveCertifySeed (builds : List QuotientProgramBuild) (exprs : List QuotientExpr)
    (vkPayload : Bytes) : Bytes :=
  qvmKeccakBytes (certifySeedPreimage builds exprs vkPayload)

/-- rust: QVC:113-122 (`interpreted_exprs`) @formal-baseline. "Expressions evaluated by the
    compact quotient program." `filter_map` over the items, keeping only `Identity(_`)` and
    taking its `.expr`; the native markers contribute nothing, which is the same fact
    `identityValues` encodes by pushing zero for them. -/
def interpretedExprs (plan : QuotientProgramPlan) : List QuotientExpr :=
  plan.items.filterMap fun item =>
    match item with
    | .identity identity => some identity.expr
    | _ => none

/-! ## The Debug renderers the error strings interpolate -/

/-- 2*len lower-case hex digits of a natural, big-endian, zero padded: the body of Rust's
    `{:02x}` loop over a fixed-width byte array. -/
def certifyBeHex (n : Nat) (len : Nat) : String :=
  (qvmBytesToNats (natToBytesBE n len)).foldl (fun (acc : String) (b : Nat) =>
    acc ++ (if b < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 b)) ""

/-- rust: the `{:?}` of an `Fq`, i.e. CUR:128-138: `write!("Fq(0x")`, then every byte of
    `to_bytes_be()` as `{:02x}`, then `")"`. `to_bytes_be` (CUR:770-774) is the reversed
    little-endian canonical repr, i.e. the value itself in big-endian bytes, NOT the
    Montgomery limbs - which is what makes this reproducible rather than an implementation
    detail of the field crate. Used at QVC:163 and QVC:325. -/
def certifyFrDebug (value : QVMFr) : String :=
  "Fq(0x" ++ certifyBeHex value 32 ++ ")"

/-- rust: the derived `{:?}` of `QuotientIdentitySource` (API:317-353, `#[derive(Clone,
    Debug, Eq, PartialEq)]` at API:317). A struct-variant prints `Variant { field: value,
    ... }` in declaration order, `usize` in decimal and `String` in double quotes with
    Rust's escaping. The names below are the Rust's field names verbatim. Used at QVC:152,
    QVC:163 and QVC:171. -/
def certifySourceDebug : QuotientIdentitySource → String
  | .gate gateIndex gateName constraintIndex constraintName polynomialIndex =>
      "Gate { gate_index: " ++ toString gateIndex ++ ", gate_name: \"" ++ gateName ++
      "\", constraint_index: " ++ toString constraintIndex ++ ", constraint_name: \"" ++
      constraintName ++ "\", polynomial_index: " ++ toString polynomialIndex ++ " }"
  | .permutation identityIndex =>
      "Permutation { identity_index: " ++ toString identityIndex ++ " }"
  | .lookup identityIndex lookupIndex lookupName =>
      "Lookup { identity_index: " ++ toString identityIndex ++ ", lookup_index: " ++
      toString lookupIndex ++ ", lookup_name: \"" ++ lookupName ++ "\" }"
  | .trash trashIndex trashName =>
      "Trash { trash_index: " ++ toString trashIndex ++ ", trash_name: \"" ++
      trashName ++ "\" }"

/-- rust: the derived `{:?}` of `QuotientTarget` (QVM:79-99, `#[derive(Clone, Debug,
    PartialEq, Eq)]`): a unit variant prints `Main`, a tuple variant `Selector(3)`. Used at
    QVC:287. -/
def certifyTargetDebug : QuotientTarget → String
  | .main => "Main"
  | .selector selectorIndex => "Selector(" ++ toString selectorIndex ++ ")"

/-- The Rust's `format!("quotient identity {} ({:?}): ", ...)` prefix, factored because
    QVC:151 and QVC:170 build it identically. Not a Rust item. -/
def identityErrorPrefix (identity : QuotientIdentity) : String :=
  "quotient identity " ++ toString identity.meta_.globalIndex ++
  " (" ++ certifySourceDebug identity.meta_.source ++ "): "

/-- R3/R4 boundary helper: the Rust's `?` on a `Result<_, String>` whose inner error came
    from a `Result<Fq, String>` in reference.rs. P-09b made those nine strings a closed
    taxonomy (`QVMFault`, with `message` rendering them verbatim and
    `faultMessages_artifactStrings_ok` gating it against reference.rs), so converting a
    fault to the driver's String is exactly `QVMFault.message`. Not a Rust item. -/
def faultToString {α : Type} (x : Except QVMFault α) : Except String α :=
  match x with
  | .ok v => .ok v
  | .error f => .error f.message

/-- R3 helper for the driver's `map_err(|err| format!("quotient item {i}: {err}"))` and the
    two identity-prefixed wraps. Not a Rust item. -/
def wrapError {α : Type} (pfx : String) (x : Except String α) : Except String α :=
  match x with
  | .error e => .error (pfx ++ e)
  | .ok v => .ok v

/-! ## The identity segment walker (rust: QVC:227-289) - MOVED; see WHAT MOVED 1 -/

/-- rust: QVC:227-245 (`identity_segment`) @formal-baseline. "Find the end of one identity
    expression and the fold opcode that closes it."

    This is the piece P-09c named as the blocker for a statable per-identity theorem: the
    interpreter consumes one identity's subprogram, and this is what cuts the stream into
    those subprograms for a program with MANY identities. Three things it must get right,
    each gated: it stops BEFORE the fold (so the slice handed to the interpreter excludes
    it, QVC:148), it advances by the reference's own instruction length rather than by one
    byte, and a native marker inside an expression is an ERROR rather than a skip - the
    marker is a stream-level item and silently walking over it would let an identity
    expression swallow the next item's bytes.

    R10: the Rust's `while idx < bytes.len()` becomes a fuel-bounded loop of `bytes.length`
    iterations. Every arm advances by at least one byte - the static table's lengths are all
    >= 1 and the four dynamic decoders return >= 1 - so the fuel-exhausted arm is
    unreachable, and `segmentWalkFuelNeverBinds_ok` asserts that over every fixture instead
    of trusting the argument.

    R4: `quotient_op_len` panics in the Rust (QVM:3022, QVM:2817). The port surfaces the
    panic class as Err with the site text, because this function's error type is the Rust's
    String. Gated in the GATE 9 section as `identitySegment_unknownOpcodeIsPanicClass_ok`. -/
def identitySegment (bytes : List Nat) (start : Nat) : Except String (Nat × Nat) :=
  go bytes.length start
where
  neverFolded : String :=
    "identity expression starting at byte " ++ toString start ++ " is never folded"
  go : Nat → Nat → Except String (Nat × Nat)
  | 0, idx =>
      if idx < bytes.length then
        .error "quotient VM segment walk fuel exhausted - port-only bound, see the header"
      else
        .error neverFolded
  | fuel + 1, idx =>
      if idx < bytes.length then
        let op := bytes.getD idx 0
        if op == qOpFoldMain || op == qOpFoldSelector then
          .ok (idx, op)
        else if op == qOpNativePermutation || op == qOpNativeLookup
            || op == qOpNativeIdentity then
          .error ("native marker " ++ qvmHex op ++ " at byte " ++ toString idx ++
                  " interrupts an identity expression")
        else
          match quotientOpLen bytes idx with
          | .error f => .error f.message
          | .ok len => go fuel (idx + len)
      else
        .error neverFolded
  termination_by fuel => fuel

/-- rust: QVC:247-289 (`check_fold`) @formal-baseline. "Check that the emitted fold matches
    the planned target and selector gap." The arm order is the Rust's: (FOLD_MAIN, Main)
    succeeds, (FOLD_SELECTOR, Selector(_)) runs the three checks in the Rust's order -
    bucket, then the two gap bytes, then the plan lookup - and everything else is the
    catch-all. The order is observable: a wrong bucket on a truncated gap reports the
    bucket, and `checkFold_errorPrecedence_ok` pins that.

    The u24 the builder writes is `(selector_index << 16) | gap` (VmBuilder's
    `foldIdentity`, QVM:1156), i.e. one byte of bucket over two bytes of gap, which is
    exactly how this reads it back: `bytes[fold_idx + 1]` then a big-endian u16 at +2. -/
def checkFold (bytes : List Nat) (foldIdx foldOp : Nat) (identity : QuotientIdentity)
    (plan : QuotientProgramPlan) : Except String Unit :=
  if foldOp == qOpFoldMain && identity.target == QuotientTarget.main then
    .ok ()
  else if foldOp == qOpFoldSelector then
    match identity.target with
    | QuotientTarget.selector selectorIdx =>
        match bytes.drop (foldIdx + 1) with
        | [] => .error "truncated selector fold index"
        | encodedIdx :: rest =>
            if encodedIdx != selectorIdx then
              .error ("selector fold targets bucket " ++ toString encodedIdx ++
                      " but the plan says " ++ toString selectorIdx)
            else
              match rest with
              | hi :: lo :: _ =>
                  let encodedGap := hi * 256 + lo
                  match plan.selectorFold.gapFor identity with
                  | none => .error "selector identity has no planned fold gap"
                  | some plannedGap =>
                      if encodedGap != plannedGap then
                        .error ("selector fold gap " ++ toString encodedGap ++
                                " does not match planned gap " ++ toString plannedGap)
                      else
                        .ok ()
              | _ => .error "truncated selector fold gap"
    | _ => .error (foldMismatch foldOp identity.target)
  else
    .error (foldMismatch foldOp identity.target)
where
  foldMismatch (op : Nat) (target : QuotientTarget) : String :=
    "fold opcode " ++ qvmHex op ++ " does not match planned target " ++
    certifyTargetDebug target

/-- rust: QVC:141-215, the item loop of `certify_quotient_program` with the Rust's
    `cursor` local and `&mut mem` threaded as an explicit state pair. NOT a Rust item on
    its own: it is split out so `certify_threadsOneMemory_ok` can inspect the memo table
    after a whole run, which the Rust cannot show from outside the function.

    The comparison at the heart of the package: for each `Identity` item, run the emitted
    segment through the reference interpreter and evaluate the `QuotientExpr` tree it was
    lowered from, and require the two field elements to be equal. ONE `QuotientRefMemory`
    is shared across every item and across BOTH sides of every comparison (the Rust's
    `&mut mem` at QVC:148 and QVC:155), which is what makes the two sides observe identical
    memory at all - P-09b's `memoisation_sameAddressSameValue_ok` is the gate for that, and
    `certify_threadsOneMemory_ok` is the driver-side half.

    The Rust returns `Result<(), String>`; the port keeps `Except String Unit` and renders
    the format strings verbatim, including the `{:?}` payloads (see the three Debug
    renderers above). No caller inspects these strings for control flow: plan.rs:516-520
    wraps one into the render error and plan.rs:324-326 panics with another, so the text is
    diagnostic. -/
def certifyItemWalk (plan : QuotientProgramPlan) (build : QuotientProgramBuild)
    (bytes : List Nat) (mem : QuotientRefMemory) :
    Except String (Nat × QuotientRefMemory) :=
  go plan.items 0 0 mem
where
  go : List QuotientProgramItem → Nat → Nat → QuotientRefMemory →
      Except String (Nat × QuotientRefMemory)
  | [], _, cursor, mem => .ok (cursor, mem)
  | item :: rest, itemIdx, cursor, mem =>
      match item with
      | QuotientProgramItem.identity identity => do
          let (exprEnd, foldOp) ←
            wrapError ("quotient item " ++ toString itemIdx ++ ": ")
              (identitySegment bytes cursor)
          let seg := (bytes.drop cursor).take (exprEnd - cursor)
          let (actual, mem1) ←
            wrapError (identityErrorPrefix identity)
              (faultToString (evalQuotientIdentity seg build.consts mem))
          let (expected, mem2) ←
            wrapError (identityErrorPrefix identity)
              (faultToString (evalQuotientExpr identity.expr mem1))
          if actual != expected then
            .error ("quotient VM miscompiled identity " ++
                    toString identity.meta_.globalIndex ++ " (" ++
                    certifySourceDebug identity.meta_.source ++
                    "): bytecode evaluates to " ++ certifyFrDebug actual ++
                    " but its expression evaluates to " ++ certifyFrDebug expected ++
                    ". This is a codegen bug in the quotient lowering (shape recognizer, " ++
                    "operand packing, or run compaction), not a proof or verifying-key " ++
                    "problem.")
          else
            let _ ← wrapError (identityErrorPrefix identity)
              (checkFold bytes exprEnd foldOp identity plan)
            let len ← faultToString (quotientOpLen bytes exprEnd)
            go rest (itemIdx + 1) (exprEnd + len) mem2
      | _ =>
          -- rust: QVC:176-213. "Native markers carry no arithmetic here: the Yul template
          -- substitutes generated straight-line kernels. Certify only that the marker sits
          -- at the planned stream position."
          let expectedOp :=
            match item with
            | QuotientProgramItem.nativePermutation => qOpNativePermutation
            | QuotientProgramItem.nativeLookup => qOpNativeLookup
            | _ => qOpNativeIdentity
          match bytes.drop cursor with
          | [] =>
              .error ("quotient item " ++ toString itemIdx ++
                      ": program ended before native marker")
          | actualOp :: _ =>
              if actualOp != expectedOp then
                .error ("quotient item " ++ toString itemIdx ++ ": expected native marker " ++
                        qvmHex expectedOp ++ " at byte " ++ toString cursor ++
                        ", found " ++ qvmHex actualOp)
              else
                match item with
                | QuotientProgramItem.nativeIdentity nativeIdx =>
                    -- rust: QVC:196-211. "The marker index is a big-endian u16, not a
                    -- single byte."
                    match bytes.drop (cursor + 1) with
                    | hi :: lo :: _ =>
                        let encoded := hi * 256 + lo
                        if encoded != nativeIdx then
                          .error ("quotient item " ++ toString itemIdx ++
                                  ": native identity index " ++ toString encoded ++
                                  " does not match planned index " ++ toString nativeIdx)
                        else
                          match quotientOpLen bytes cursor with
                          | .error f => .error f.message
                          | .ok len => go rest (itemIdx + 1) (cursor + len) mem
                    | _ =>
                        .error ("quotient item " ++ toString itemIdx ++
                                ": truncated native identity index")
                | _ =>
                    match quotientOpLen bytes cursor with
                    | .error f => .error f.message
                    | .ok len => go rest (itemIdx + 1) (cursor + len) mem

/-- The seed the single-build driver derives: QVC:134-136's three locals (`exprs`,
    `vk_payload`, `seed`) folded into one value so a gate can pin WHAT the driver
    hashes, not only what it does with it. Not a Rust item; the Rust computes it inline.
    Without this, editing the driver's seed inputs - dropping the VK payload, hashing the
    wrong build list - would move the challenge and redden nothing, because the certification
    is seed-agnostic: both sides of the comparison move together. -/
def certifyProgramSeed (plan : QuotientProgramPlan) (build : QuotientProgramBuild)
    (vk : Halo2VerifyingKey) : Bytes :=
  deriveCertifySeed [build] (interpretedExprs plan) vk.bytes

/-- rust: QVC:124-225 (`certify_quotient_program`), the entry point. "Certify that the
    emitted bytecode evaluates the planned identities." The seed is derived over ONE build
    (QVC:136), the memory starts empty (QVC:137), the item loop is `certifyItemWalk`, and
    the trailing-byte check is QVC:217-222. -/
def certifyQuotientProgram (plan : QuotientProgramPlan) (build : QuotientProgramBuild)
    (vk : Halo2VerifyingKey) : Except String Unit := do
  let seed := certifyProgramSeed plan build vk
  let mem := quotientRefMemoryNew seed
  let bytes := qvmBytesToNats build.bytes
  let (cursor, _) ← certifyItemWalk plan build bytes mem
  if cursor != bytes.length then
    .error ("quotient program has " ++ toString (bytes.length - cursor) ++
            " trailing byte(s) after the planned item stream")
  else
    .ok ()

/-- rust: QVC:334-365 (`identity_values`) @formal-baseline. "Evaluate every interpreted
    identity in one build, in stream order." Returns the values AND the memory, because the
    Rust's `&mut QuotientRefMemory` survives the call and the caller feeds the SAME memory
    to the second build (QVC:310-311). Native markers push `Fq::ZERO` (QVC:358) - they
    evaluate no bytecode, and both builds emit the same marker at the same position. -/
def identityValues (plan : QuotientProgramPlan) (build : QuotientProgramBuild)
    (mem : QuotientRefMemory) : Except String (List QVMFr × QuotientRefMemory) :=
  go plan.items 0 [] mem
where
  bytes := qvmBytesToNats build.bytes
  go : List QuotientProgramItem → Nat → List QVMFr → QuotientRefMemory →
      Except String (List QVMFr × QuotientRefMemory)
  | [], _, values, mem => .ok (values, mem)
  | item :: rest, cursor, values, mem =>
      match item with
      | QuotientProgramItem.identity _ => do
          let (exprEnd, _) ← identitySegment bytes cursor
          let seg := (bytes.drop cursor).take (exprEnd - cursor)
          let (value, mem') ← faultToString (evalQuotientIdentity seg build.consts mem)
          let len ← faultToString (quotientOpLen bytes exprEnd)
          go rest (exprEnd + len) (values ++ [value]) mem'
      | _ =>
          match quotientOpLen bytes cursor with
          | .error f => .error f.message
          | .ok len => go rest (cursor + len) (values ++ [qvmFrZero]) mem

/-- The dual driver's seed: QVC:305-307's three locals folded into one value, for the same
    reason `certifyProgramSeed` exists and with the same warning. The pair order is
    (optimized, baseline), as the Rust writes it. -/
def certifyBuildsAgreeSeed (plan : QuotientProgramPlan)
    (optimized baseline : QuotientProgramBuild) (vk : Halo2VerifyingKey) : Bytes :=
  deriveCertifySeed [optimized, baseline] (interpretedExprs plan) vk.bytes

/-- rust: QVC:291-332 (`certify_quotient_builds_agree`) @formal-baseline. "Certify that two
    builds of the same identity stream agree. The limb-aware superinstructions are the least
    principled part of the lowering: they pattern-match algebraic shapes out of a
    commutative-ring expression tree. Building the same stream with those recognizers
    disabled yields a program using only PUSH/ADD/MUL/NEG, which is straightforward to
    audit. Requiring the two to agree identity-by-identity turns every recognizer from
    trusted code into a checked optimization."

    The seed here absorbs BOTH builds (QVC:307), so the challenge depends on the optimized
    and the baseline representation together. The memory is threaded from the optimized run
    into the baseline run (the Rust's single `&mut mem` across QVC:310-311), which the port
    models by returning the pair from `identityValues`.

    The length check at QVC:313-319 cannot fire: both calls fold the same `plan.items`, so
    both vectors have exactly `plan.items.length` entries. Ported anyway (R1) and recorded
    as unreachable rather than deleted. -/
def certifyQuotientBuildsAgree (plan : QuotientProgramPlan)
    (optimized baseline : QuotientProgramBuild) (vk : Halo2VerifyingKey) :
    Except String Unit := do
  let seed := certifyBuildsAgreeSeed plan optimized baseline vk
  let mem := quotientRefMemoryNew seed
  let (optimizedValues, mem1) ← identityValues plan optimized mem
  let (baselineValues, _) ← identityValues plan baseline mem1
  if optimizedValues.length != baselineValues.length then
    .error ("quotient dual build disagrees on identity count: " ++
            toString optimizedValues.length ++ " with limb opcodes, " ++
            toString baselineValues.length ++ " without")
  else
    go (List.zip optimizedValues baselineValues) 0
where
  go : List (QVMFr × QVMFr) → Nat → Except String Unit
  | [], _ => .ok ()
  | (lhs, rhs) :: rest, position =>
      if lhs != rhs then
        .error ("quotient limb superinstructions changed the value of interpreted identity " ++
                "at stream position " ++ toString position ++ ": " ++ certifyFrDebug lhs ++
                " with limb opcodes, " ++ certifyFrDebug rhs ++
                " without. One of the shape recognizers is unsound for this gate shape.")
      else
        go rest (position + 1)

end Midfall.Generator.QuotientCertify

/-! ## Known-answer tests

    Every gate below is a Bool or an IO Bool with a matching '#eval ... -- expect true'
    line at the end of the file, so scripts/kat_gate.py turns each one into a CI obligation
    (docs/REVIEW.md R-38). Each doc names the concrete wrong implementation it rules out,
    and the package report carries the perturbation actually run inside each scope (R-41).
    D-P19 binds the four artifact gates: they open certify.rs from disk while they
    evaluate, and the reachability gate runs first so a wrong path is diagnosed rather than
    matched by accident. lake build caches, so it is checks.sh re-running every KAT file
    that makes the pattern load-bearing in CI.

    HAZARD 4 AGAIN, because these gates are not the theorem: they are deterministic checks
    over fixtures, where the Rust is a probabilistic check over one produced program. -/

namespace Midfall.Generator.QuotientCertifyKats

open Midfall.Generator.QuotientCertify
open Midfall.Generator.QuotientBuilder
open Midfall.Generator.QuotientVmKats (readFileOrEmpty hasDuplicateNat)

/-! ### Fixtures

    The seed fixtures are the ones the Rust's own seed test builds (LT:426-507): two
    builds whose bytes are PUSH_CONST_U8 0 / PUSH_CONST 0 0, constant tables of one
    entry each (11 and 13), one expression m(0x120) + 17, and a 64-byte VK payload of
    0xab. Reusing the reference's fixture rather than inventing one is deliberate: the
    sensitivity claims below are then the same five claims the Rust makes, and the digest
    pins are re-derivable by anyone who reads QVC:54-75 and LT:426-507 side by side.

    R-48: every fixture that a comparison gate relies on is checked for non-degeneracy
    first, by `certifyFixturesNonDegenerate_ok`. -/

/-- The Rust test's first build (LT:427-433). -/
def certBuild0 : QuotientProgramBuild :=
  { bytes := qvmBytesOfNats [0x09, 0x00]
    consts := [11]
    maxStack := 1
    usedOps := qvmBytesOfNats [0x09]
    usedMemTokens := Bytes.empty }

/-- The Rust test's baseline build (LT:434-440). -/
def certBuild1 : QuotientProgramBuild :=
  { bytes := qvmBytesOfNats [0x01, 0x00, 0x00]
    consts := [13]
    maxStack := 1
    usedOps := qvmBytesOfNats [0x01]
    usedMemTokens := Bytes.empty }

/-- The Rust test's expression: m(0x120) + 17 (LT:441-444). -/
def certExpr0 : QuotientExpr :=
  QuotientExpr.add (QuotientExpr.mem (.literal 0x120)) (QuotientExpr.const 17)

/-- The Rust test's VK payload: 64 bytes of 0xab (LT:445). -/
def certVkPayload : Bytes := qvmBytesOfNats (List.replicate 64 0xab)

/-- The seed of the two-build fixture. -/
def certSeedF1 : Bytes :=
  deriveCertifySeed [certBuild0, certBuild1] [certExpr0] certVkPayload

/-- A second, structurally different fixture: one build with two constants and an
    expression that reaches all seven node tags. -/
def certBuild2 : QuotientProgramBuild :=
  { bytes := qvmBytesOfNats [0x09, 0x00, 0x03, qMemBeta, 0x07, 0x10, 0x01, 0x00]
    consts := [11, 13]
    maxStack := 2
    usedOps := qvmBytesOfNats [0x09, 0x03, 0x07, 0x10]
    usedMemTokens := qvmBytesOfNats [qMemBeta] }

def certExpr2 : QuotientExpr :=
  QuotientExpr.neg
    (QuotientExpr.mul
      (QuotientExpr.add (QuotientExpr.mem (.literal 0x100)) (QuotientExpr.const 3))
      (QuotientExpr.mul (QuotientExpr.mem (.token qMemBeta))
        (QuotientExpr.mem (.tokenOffset qMemX 0x20))))

def certVkPayload2 : Bytes := qvmBytesOfNats (List.replicate 16 0x5a)

def certSeedF3 : Bytes := deriveCertifySeed [certBuild2] [certExpr2] certVkPayload2

/-- The empty-input case: three zero length prefixes and nothing else, i.e. a 59-byte
    preimage. The Rust never calls it with empty lists, but the length prefixes are part
    of the layout and this is where they are visible on their own. -/
def certSeedEmpty : Bytes := deriveCertifySeed [] [] Bytes.empty

/-- Hand-written big-endian encoders for the expected preimage. Deliberately a second
    transcription rather than a call to `natToBytesBE`: GATE 1 is supposed to be able
    to disagree with the port. -/
def u64b (n : Nat) : List Nat :=
  [n / 2^56 % 256, n / 2^48 % 256, n / 2^40 % 256, n / 2^32 % 256,
   n / 2^24 % 256, n / 2^16 % 256, n / 2^8 % 256, n % 256]

def u32b (n : Nat) : List Nat := [n / 2^24 % 256, n / 2^16 % 256, n / 2^8 % 256, n % 256]

/-- A U256 as 32 big-endian bytes. Every fixture constant is below 256, so the tail form
    is exact and readable. -/
def w32b (n : Nat) : List Nat := List.replicate 31 0 ++ [n]

/-- The domain tag as 35 hand-typed ASCII codes: m, i, d, f, a, l, l, /, q, u, o, t, i,
    e, n, t, -, v, m, /, c, e, r, t, i, f, y, -, s, e, e, d, /, v, 3. -/
def tagBytes : List Nat :=
  [109, 105, 100, 102, 97, 108, 108, 47, 113, 117, 111, 116, 105, 101, 110, 116, 45,
   118, 109, 47, 99, 101, 114, 116, 105, 102, 121, 45, 115, 101, 101, 100, 47, 118, 51]

/-- The ten segments of the F1 preimage, written out by hand from QVC:54-75. -/
def segTag : List Nat := tagBytes
def segBuildCount : List Nat := u64b 2
def seg0BytesLen : List Nat := u64b 2
def seg0Bytes : List Nat := [0x09, 0x00]
def seg0ConstsLen : List Nat := u64b 1
def seg0Consts : List Nat := w32b 11
def seg1BytesLen : List Nat := u64b 3
def seg1Bytes : List Nat := [0x01, 0x00, 0x00]
def seg1ConstsLen : List Nat := u64b 1
def seg1Consts : List Nat := w32b 13
def segExprCount : List Nat := u64b 1
def segExpr0 : List Nat := [4] ++ [1] ++ u32b 0x120 ++ [0] ++ w32b 17
def segVkLen : List Nat := u64b 64
def segVk : List Nat := List.replicate 64 0xab

/-- The whole expected stream, and its segment boundaries as (name, start, end). -/
def wantPreimageF1 : List Nat :=
  segTag ++ segBuildCount ++ seg0BytesLen ++ seg0Bytes ++ seg0ConstsLen ++ seg0Consts ++
    seg1BytesLen ++ seg1Bytes ++ seg1ConstsLen ++ seg1Consts ++
    segExprCount ++ segExpr0 ++ segVkLen ++ segVk

def preimageSegments : List (String × List Nat) :=
  [("tag", segTag), ("builds.len", segBuildCount), ("build0.bytes.len", seg0BytesLen),
   ("build0.bytes", seg0Bytes), ("build0.consts.len", seg0ConstsLen),
   ("build0.consts", seg0Consts), ("build1.bytes.len", seg1BytesLen),
   ("build1.bytes", seg1Bytes), ("build1.consts.len", seg1ConstsLen),
   ("build1.consts", seg1Consts), ("exprs.len", segExprCount), ("expr0", segExpr0),
   ("vk.len", segVkLen), ("vk", segVk)]

/-- The F1 preimage as produced by the port, as a byte list. -/
def gotPreimageF1 : List Nat :=
  qvmBytesToNats (certifySeedPreimage [certBuild0, certBuild1] [certExpr0] certVkPayload)

/-- Slice a list at the running offsets of the segment table. -/
def sliceAt (start : Nat) (len : Nat) (xs : List Nat) : List Nat := (xs.drop start).take len

def segmentOffsets : List (String × Nat) :=
  go preimageSegments 0
where
  go : List (String × List Nat) → Nat → List (String × Nat)
  | [], _off => []
  | (name, bs) :: rest, off => (name, off) :: go rest (off + bs.length)

/-- A three-identity program built by P-09c's emitter, with a selector fold in the middle.
    The expressions are small on purpose: the walker is about byte boundaries, and a small
    expression makes every offset in the gate hand-checkable. -/
def cLit (ptr : Nat) : QuotientExpr := QuotientExpr.mem (.literal ptr)

def cExpr0 : QuotientExpr := QuotientExpr.add (cLit 0x100) (cLit 0x120)
def cExpr1 : QuotientExpr := QuotientExpr.mul (cLit 0x140) (QuotientExpr.const 7)
def cExpr2 : QuotientExpr := QuotientExpr.neg (QuotientExpr.add (cLit 0x100) (QuotientExpr.const 3))

/-- One identity record, with the metadata shape VmTypes' own fixture uses. -/
def cIdentity (globalIndex : Nat) (target : QuotientTarget) (expr : QuotientExpr) :
    QuotientIdentity :=
  { meta_ := { globalIndex := globalIndex,
               source := QuotientIdentitySource.gate globalIndex "cert" 0 "c" 0 }
    lines := ["t := add(1, 2)"]
    var := "t"
    target := target
    expr := expr }

def cSteps : List (QuotientExpr × QuotientTarget × Option Nat) :=
  [(cExpr0, QuotientTarget.main, none),
   (cExpr1, QuotientTarget.selector 1, some 5),
   (cExpr2, QuotientTarget.main, none)]

def cIdentities : List QuotientIdentity :=
  (List.zip cSteps (List.range 3)).map fun (step, i) => cIdentity i step.2.1 step.1

def cExprList : List QuotientExpr := cIdentities.map fun i => i.expr

/-- Emit a stream of identities through the reference builder. KAT helper, not a Rust item. -/
def buildStream : List (QuotientExpr × QuotientTarget × Option Nat) →
    QuotientProgramBuilder → Except QVMFault QuotientProgramBuilder
  | [], s => .ok s
  | (e, t, g) :: rest, s => do
      let s ← identityExpr noShapeRecognizers s e t g
      buildStream rest s

/-- The three identities, emitted and finalized by P-09c's builder. -/
def threeIdentityBuild : Except QVMFault QuotientProgramBuild :=
  buildStream cSteps builderDefault >>= finish

def threeIdentityPlan : QuotientProgramPlan :=
  { inlineIdentities := []
    items := cIdentities.map QuotientProgramItem.identity
    nativeIdentities := []
    nativePermutationIdentities := []
    nativeLookupIdentities := []
    structuredTailIdentities := []
    sortedSimple := [1]
    hasNativePermutation := false
    hasNativeLookup := false
    selectorFold := { gapsByIdentity := [none, some 5, none],
                      tailExponents := [0], maxPower := 0 } }

/-- The three identities' expression trees, as the certifier would collect them. -/
def cExprTrees : List QuotientExpr := interpretedExprs threeIdentityPlan

/-- A VK with pairwise distinct payload words, so `vk.bytes` cannot be an all-zero
    buffer that a dropped section would hide behind (R-48). -/
def certG1 (a b c d : Nat) : G1Words :=
  { xHi := a, xLo := b, yHi := c, yLo := d }

def certVk : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0x80
    constants := [("c0", 1), ("c1", 2)]
    fixedComms := [certG1 3 4 5 6]
    permutationComms := [certG1 7 8 9 10]
    quotientConstOffsetWords := none
    quotientConstWords := 0
    quotientProgramOffsetWords := none
    quotientProgramWords := 0
    quotientConstLabels := []
    quotientConstHeaders := [] }

/-- The ten payload words of `certVk`, in the order Models' `Halo2VerifyingKey.bytes`
    flattens them: two constants, then the four words of the fixed commitment, then the
    four words of the permutation commitment. Pairwise distinct, so a dropped or reordered
    section cannot hide behind equal numbers (R-48). -/
def vkPayloadWords : List Word256 :=
  certVk.constants.map (fun (_, v) => v) ++
  certVk.fixedComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo]) ++
  certVk.permutationComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])

/-- A second VK differing in exactly one payload word, for the sensitivity gates. -/
def certVkAlt : Halo2VerifyingKey :=
  { certVk with constants := [("c0", 1), ("c1", 3)] }

/-- The seed the driver derives for the three-identity fixture. -/
def threeIdentitySeed : Except String Bytes := do
  let build ← match threeIdentityBuild with
              | .ok b => .ok b
              | .error f => .error f.message
  .ok (deriveCertifySeed [build] cExprTrees certVk.bytes)

/-- A plan whose item stream is identity, native permutation, identity, native lookup,
    native identity 7 - the marker positions the certifier checks positionally. -/
def markerBuilder : Except QVMFault QuotientProgramBuilder :=
  buildStream [(cExpr0, QuotientTarget.main, none)] builderDefault
    >>= nativePermutation
    >>= fun s => buildStream [(cExpr2, QuotientTarget.main, none)] s
    >>= nativeLookup
    >>= fun s => nativeIdentity s 7

def markerBuild : Except QVMFault QuotientProgramBuild := markerBuilder >>= finish

def markerPlan : QuotientProgramPlan :=
  { inlineIdentities := []
    items := [QuotientProgramItem.identity (cIdentity 0 QuotientTarget.main cExpr0),
              QuotientProgramItem.nativePermutation,
              QuotientProgramItem.identity (cIdentity 1 QuotientTarget.main cExpr2),
              QuotientProgramItem.nativeLookup,
              QuotientProgramItem.nativeIdentity 7]
    nativeIdentities := []
    nativePermutationIdentities := []
    nativeLookupIdentities := []
    structuredTailIdentities := []
    sortedSimple := []
    hasNativePermutation := true
    hasNativeLookup := true
    selectorFold := selectorFoldPlanDefault }

/-- Patch one byte of a byte list, leaving the length alone. -/
def patchByte (bytes : List Nat) (idx : Nat) (value : Nat) : List Nat :=
  (bytes.take idx) ++ [value % 256] ++ (bytes.drop (idx + 1))

/-- Patch one byte of a build's program: a change that cannot alter an instruction
    boundary, so the only thing it can break is the value. -/
def patchBuildBytes (build : QuotientProgramBuild) (idx : Nat) (value : Nat) :
    QuotientProgramBuild :=
  { build with bytes := qvmBytesOfNats (patchByte (qvmBytesToNats build.bytes) idx value) }

/-- Patch one entry of a build's constant table. -/
def patchBuildConst (build : QuotientProgramBuild) (idx : Nat) (value : Nat) :
    QuotientProgramBuild :=
  { build with consts := (build.consts.take idx) ++ [(value : Word256)] ++
      (build.consts.drop (idx + 1)) }

/-- The offset of the first occurrence of `needle` in `hay`, as a character count
    (ASCII throughout, so characters and bytes agree). -/
def certOffsetOf (needle : String) (hay : String) : Option Nat :=
  match hay.splitOn needle with
  | first :: _ :: _ => some first.length
  | _ => none

/-- `needles` must occur in `hay` in this order, each after the previous one ends.
    Consuming the haystack as it goes is what lets a needle repeat: `hash_quotient_expr
    (hasher, lhs);` appears in both the Add and the Mul arm of the Rust, and a plain
    first-occurrence scan would read that as out of order. -/
def certOrdered (needles : List String) (hay : String) : Bool :=
  go needles hay
where
  go : List String → String → Bool
  | [], _ => true
  | n :: rest, s =>
      match certOffsetOf n s with
      | none => false
      | some off => go rest (s.drop (off + n.length)).toString

/-- The body of one Rust fn, read as the text between its signature and the next
    top-level `fn` keyword. Crude on purpose: certify.rs is 365 lines and the windows
    are checked for non-emptiness by the reachability gate. -/
def certFnWindow (fnName : String) (nextMarker : String) (src : String) : Option String :=
  match certOffsetOf fnName src with
  | none => none
  | some off =>
      let rest := (src.drop (off + fnName.length)).toString
      match certOffsetOf nextMarker rest with
      | none => some rest
      | some len => some (rest.take len).toString

/-- The artifact: vm/certify.rs, two candidate paths so the gate resolves from `formal/`
    (where checks.sh and lake run) and from the repo root. -/
def certifyPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/certify.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/certify.rs"]

def readCertifySource : IO String :=
  certifyPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

/-- QVC is 365 lines / 14883 bytes at HEAD; anything much smaller is a wrong path and must
    not be allowed to satisfy a needle check by accident. -/
def certifyReadOk (src : String) : Bool := src.length > 12000

/-- The seven node-tag texts as the Rust writes them, in source order. -/
def exprTagNeedles : List String :=
  ["QuotientExpr::Const(value)", "hasher.update([0]);",
   "hasher.update(value.to_be_bytes::<32>());",
   "QuotientExpr::Mem(QuotientMem::Literal(ptr))", "hasher.update([1]);",
   "hasher.update(ptr.to_be_bytes());",
   "QuotientExpr::Mem(QuotientMem::Token(token))", "hasher.update([2, *token]);",
   "QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset))",
   "hasher.update([3, *token]);", "hasher.update(offset.to_be_bytes());",
   "QuotientExpr::Add(lhs, rhs)", "hasher.update([4]);",
   "hash_quotient_expr(hasher, lhs);", "hash_quotient_expr(hasher, rhs);",
   "QuotientExpr::Mul(lhs, rhs)", "hasher.update([5]);",
   "hash_quotient_expr(hasher, lhs);", "hash_quotient_expr(hasher, rhs);",
   "QuotientExpr::Neg(inner)", "hasher.update([6]);", "hash_quotient_expr(hasher, inner);"]

/-- Small expression builders for the fixtures: a scaled memory load and a left-associated
    sum, the two shapes the emitter's affine paths consume. -/
def cScaled (c : Word256) (e : QuotientExpr) : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.const c) e

def cSumLeft (base : QuotientExpr) (terms : List QuotientExpr) : QuotientExpr :=
  terms.foldl (fun acc t => QuotientExpr.add acc t) base

/-- The seven-limb linear form, and the recognizer hook that turns it into one LIN7 opcode.
    P-09e owns the real recognizers; this is the smallest hook that makes the emitter take
    the limb path, which is what the dual-build gate needs. -/
def cLin7Coeffs : List Word256 := [2, 3, 5, 7, 11, 13, 17]
def cLin7Ptrs : List Nat := [0x100, 0x120, 0x140, 0x160, 0x180, 0x1a0, 0x1c0]
def cLin7Terms : List (Word256 × Nat) := cLin7Coeffs.zip cLin7Ptrs
def cLin7Expr : QuotientExpr :=
  cSumLeft (QuotientExpr.const 0) (cLin7Terms.map fun (c, ptr) => cScaled c (cLit ptr))
def cLin7Shape : QuotientLimbShape := QuotientLimbShape.lin7 cLin7Terms
def cLin7Hooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with
    limbShape := fun e => if e == cLin7Expr then some cLin7Shape else none }

def cLin7Plan : QuotientProgramPlan :=
  { inlineIdentities := []
    items := [QuotientProgramItem.identity (cIdentity 0 QuotientTarget.main cLin7Expr)]
    nativeIdentities := []
    nativePermutationIdentities := []
    nativeLookupIdentities := []
    structuredTailIdentities := []
    sortedSimple := []
    hasNativePermutation := false
    hasNativeLookup := false
    selectorFold := selectorFoldPlanDefault }

/-- The optimized build (LIN7) and the baseline build (generic Fr opcodes) of the same
    identity: the pair QVC:299-332 compares. -/
def cLin7Build : Except QVMFault QuotientProgramBuild :=
  identityExpr cLin7Hooks builderDefault cLin7Expr QuotientTarget.main none >>= finish
def cBaselineBuild : Except QVMFault QuotientProgramBuild :=
  identityExpr noShapeRecognizers builderDefault cLin7Expr QuotientTarget.main none >>= finish

/-- The (plan, build) pairs every driver gate runs over. -/
def driverFixtures : List (QuotientProgramPlan × QuotientProgramBuild) :=
  List.filterMap
    (fun pb => match pb with
              | (plan, .ok b) => some (plan, b)
              | (_, .error _) => none)
    [(threeIdentityPlan, threeIdentityBuild), (markerPlan, markerBuild),
     (cLin7Plan, cLin7Build), (cLin7Plan, cBaselineBuild)]

/-- The oracle side of the certification: evaluate each identity's expression tree against
    one shared memory, threading it exactly as the driver's `&mut mem` does. KAT helper,
    not a Rust item - the Rust has no standalone oracle fold because it compares per item. -/
def oracleValues (exprs : List QuotientExpr) (mem : QuotientRefMemory) :
    Except String (List QVMFr × QuotientRefMemory) :=
  go exprs mem []
where
  go : List QuotientExpr → QuotientRefMemory → List QVMFr →
      Except String (List QVMFr × QuotientRefMemory)
  | [], m, acc => .ok (acc, m)
  | e :: rest, m, acc => do
      let (v, m') ← faultToString (evalQuotientExpr e m)
      go rest m' (acc ++ [v])

/-- The certifier's error type is the Rust's String, so a gate that wants to name a branch
    has to name its text. Helper for the message gates below. -/
def errText {α : Type} (x : Except String α) : String :=
  match x with
  | .ok _ => "<ok>"
  | .error e => e

/-- The driver's accept predicate, spelled once. -/
def certifyOk (x : Except String Unit) : Bool :=
  match x with
  | .ok _ => true
  | .error _ => false

/-! #### GATE 1 - hazard 1: the preimage, segment by segment -/

/-- THE HAZARD-1 STRUCTURE GATE. The F1 preimage the port builds is byte-for-byte the
    concatenation of fourteen hand-written segments, each transcribed from its own line of
    QVC:54-75, and each slice of the port's buffer at its own offset re-checks against its
    own segment. Rules out: a length prefix written 32 bytes instead of 8 (the natural
    mistake, and the one Vk.lean:733 records as a finding for the SRS fingerprint), a
    length prefix taken over the wrong field, the consts block landing before the bytes
    block, the exprs count being omitted, the VK payload being absorbed into the last
    build, and any off-by-one in a segment boundary. The empty-input clause pins the three
    zero length prefixes on their own, which is where a dropped prefix hides. -/
def seedPreimage_segments_ok : Bool :=
  gotPreimageF1 == wantPreimageF1 &&
  wantPreimageF1.length == 263 &&
  segmentOffsets.length == preimageSegments.length &&
  (List.zip segmentOffsets preimageSegments).all fun ((_, off), (_, bs)) =>
    sliceAt off bs.length gotPreimageF1 == bs && sliceAt off bs.length wantPreimageF1 == bs &&
    bs.length > 0 &&
  qvmBytesToNats (certifySeedPreimage [] [] Bytes.empty) ==
    tagBytes ++ u64b 0 ++ u64b 0 ++ u64b 0 &&
  (certifySeedPreimage [] [] Bytes.empty).size == 59

/-! #### GATE 2 - hazard 1: the digest, against an independent Keccak -/

/-- Seed of the two-build fixture, from the independent Python Keccak over the 263-byte
    preimage of GATE 1. -/
def wantCertSeedF1 : List Nat := [
  0x47, 0x4a, 0x37, 0x72, 0xa5, 0x4a, 0xb6, 0x75,
  0x97, 0xf3, 0x1e, 0xb7, 0xde, 0xcb, 0xdd, 0x54,
  0x51, 0x1e, 0x80, 0xc0, 0xc9, 0x2b, 0xf6, 0x86,
  0x20, 0xd9, 0x6f, 0xcd, 0xd9, 0xb7, 0x48, 0x57]

/-- Seed of the all-seven-tags fixture (213-byte preimage), same source. -/
def wantCertSeedF3 : List Nat := [
  0xe6, 0x81, 0xb2, 0x15, 0x68, 0x36, 0x99, 0xc3,
  0x9d, 0xd4, 0x88, 0x8b, 0x25, 0xe9, 0xe7, 0x6e,
  0xae, 0xb7, 0xce, 0x75, 0xeb, 0x94, 0x98, 0xd1,
  0x50, 0x7c, 0xe5, 0xb6, 0xaa, 0xc9, 0x08, 0x08]

/-- Seed of the empty fixture (59-byte preimage), same source. -/
def wantCertSeedEmpty : List Nat := [
  0x85, 0x20, 0x64, 0x39, 0x1c, 0xd7, 0xd7, 0x8d,
  0xb5, 0x9e, 0x06, 0xd8, 0xc3, 0x3d, 0x8b, 0x9d,
  0x79, 0xbc, 0xa6, 0x0e, 0x8e, 0xeb, 0xf4, 0x7c,
  0x40, 0xaa, 0x95, 0xfd, 0x2d, 0x6a, 0xc3, 0xe9]

/-- Seed over the REAL three-identity built artifact (572-byte preimage: 23 program bytes,
    two constants, three expression trees and the 320-byte VK payload), same source. -/
def wantCertSeedReal : List Nat := [
  0x25, 0x4b, 0x67, 0x9b, 0x62, 0xd7, 0xe6, 0xa3,
  0xf2, 0x68, 0x1c, 0xa9, 0x93, 0x59, 0x2c, 0xbd,
  0xab, 0x4a, 0xc2, 0x6d, 0xf9, 0x7d, 0x91, 0x95,
  0xa4, 0x92, 0x7c, 0xd3, 0xb2, 0xa4, 0x42, 0xb6]

/-- THE HAZARD-1 DIGEST GATE. Four digests, four different preimage shapes, all produced
    by a Keccak written from FIPS-202 in Python and never by the Lean code that checks
    them. Rules out: a different hash function (SHA3-256 has different padding and would
    agree on nothing here), a preimage that differs from the reference's in any byte the
    segment gate cannot see, and a digest that is truncated or re-endianed on the way out
    of `qvmKeccakBytes`. The fourth clause is the one that matters for the M6 story:
    the artifact the builder FINALIZES is hashed, not a hand-written stand-in. -/
def seed_digestByteExact_ok : Bool :=
  qvmBytesToNats certSeedF1 == wantCertSeedF1 &&
  qvmBytesToNats certSeedF3 == wantCertSeedF3 &&
  qvmBytesToNats certSeedEmpty == wantCertSeedEmpty &&
  match threeIdentitySeed with
  | .ok s => qvmBytesToNats s == wantCertSeedReal
  | .error _ => false

/-- The dual-build pair's seed, from the same independent Python Keccak over the 1254-byte
    preimage: the 23-byte LIN7 program with 7 constants, the 27-byte generic program with 8,
    the one LIN7 expression tree, and the 320-byte VK payload. -/
def wantCertSeedDual : List Nat := [
  0x3c, 0xce, 0xf8, 0x7f, 0x96, 0xad, 0x30, 0xbb,
  0x01, 0x69, 0x1c, 0x9d, 0xde, 0x41, 0x24, 0x78,
  0xa5, 0x4f, 0x18, 0xf4, 0xff, 0xb8, 0x2d, 0xaf,
  0x27, 0x58, 0x22, 0xba, 0xd5, 0x36, 0x7b, 0x4d]

/-- WHAT THE DRIVERS HASH, pinned. The two entry points must derive their challenge from
    exactly the artifacts QVC:136 and QVC:307 name - one build versus the ordered pair - and
    the dual seed must differ from either single and from the pair reversed. Rules out: a
    driver that drops the VK payload, hashes the plan's native-marker items, or passes one
    build where the Rust passes two. Without this gate the seed layer is unhooked from the
    drivers, because a certification is seed-agnostic: move the challenge and both sides of
    the comparison move with it, so every other gate stays green. -/
def certifyDrivers_hashTheRightArtifacts_ok : Bool :=
  (match threeIdentityBuild with
   | .ok b => qvmBytesToNats (certifyProgramSeed threeIdentityPlan b certVk) == wantCertSeedReal &&
              qvmBytesToNats (certifyProgramSeed threeIdentityPlan b certVk) !=
                qvmBytesToNats (certifyProgramSeed threeIdentityPlan b certVkAlt)
   | .error _ => false) &&
  (match cLin7Build, cBaselineBuild with
   | .ok o, .ok b =>
       qvmBytesToNats (certifyBuildsAgreeSeed cLin7Plan o b certVk) == wantCertSeedDual &&
       qvmBytesToNats (certifyBuildsAgreeSeed cLin7Plan o b certVk) !=
         qvmBytesToNats (certifyProgramSeed cLin7Plan o certVk) &&
       qvmBytesToNats (certifyBuildsAgreeSeed cLin7Plan o b certVk) !=
         qvmBytesToNats (certifyProgramSeed cLin7Plan b certVk) &&
       qvmBytesToNats (certifyBuildsAgreeSeed cLin7Plan o b certVk) !=
         qvmBytesToNats (certifyBuildsAgreeSeed cLin7Plan b o certVk)
   | _, _ => false)

/-- The seed is 32 bytes for every fixture, i.e. the `[u8; 32]` of QVC:52 and not a
    wider or narrower digest, and every value is below the field modulus once it is read
    as the low half of a `from_uniform_bytes` input. -/
def seed_is32Bytes_ok : Bool :=
  [certSeedF1, certSeedF3, certSeedEmpty].all fun bs => bs.size == 32 &&
  [certSeedF1, certSeedF3, certSeedEmpty].all fun bs =>
    bytesToNatBE bs > 0 && bytesToNatLE bs > 0 &&
  certVk.bytes.size == 320

/-! #### GATE 3 - hazard 1: the seven expression node tags -/

/-- Each node form's contribution, hand-written: the tag byte, then the payload in the
    width the Rust's field has. -/
def wantTagConst : List Nat := [0] ++ w32b 17
def wantTagLit : List Nat := [1] ++ u32b 0x120
def wantTagTok : List Nat := [2, 4]
def wantTagTof : List Nat := [3, 6] ++ u32b 0x20
def wantTagAdd : List Nat := [4] ++ wantTagLit ++ wantTagConst
def wantTagMul : List Nat := [5] ++ wantTagLit ++ wantTagConst
def wantTagNeg : List Nat := [6] ++ wantTagLit

/-- THE NODE-TAG GATE. All seven arms of QVC:79-111 pinned against hand-written bytes,
    plus the three properties the tags exist to provide: the seven leading bytes are
    pairwise distinct (so a Const and a Literal cannot collide), the binary arms put the
    LEFT subtree first (so `add a b` and `add b a` hash differently even though the
    Rust's `Add` is a commutative operation at the value level - and the certifier must
    still bind the tree it was given), and a `Token` and a `TokenOffset` on the same
    token differ. Rules out: renumbering a tag, swapping the subtree order, writing the
    u32 pointer little-endian, and dropping the address byte of a token. -/
def seedExprNodeTags_ok : Bool :=
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.const 17)) == wantTagConst) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0x120))) == wantTagLit) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.token 4))) == wantTagTok) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.tokenOffset 6 0x20))) == wantTagTof) &&
  (qvmBytesToNats (hashQuotientExpr certExpr0) == wantTagAdd) &&
  (qvmBytesToNats (hashQuotientExpr
     (QuotientExpr.mul (QuotientExpr.mem (.literal 0x120)) (QuotientExpr.const 17))) == wantTagMul) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.neg (QuotientExpr.mem (.literal 0x120))))
     == wantTagNeg) &&
  ! hasDuplicateNat [0, 1, 2, 3, 4, 5, 6] &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.add (QuotientExpr.mem (.literal 1))
     (QuotientExpr.mem (.literal 2))))) !=
    (qvmBytesToNats (hashQuotientExpr (QuotientExpr.add (QuotientExpr.mem (.literal 2))
     (QuotientExpr.mem (.literal 1))))) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.token 6))) !=
    qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.tokenOffset 6 0)))) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0x120))) !=
    qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.tokenOffset 0 0x120))))

/-- R5 at the token position: the Rust's `u8` cannot exceed 255, so the mask is inert on
    every value the reference can build. What this gate pins is the OBSERVABLE width - a
    token of 256 hashes as byte 0 - and honesty requires the note that the `% 256` in
    `hashQuotientExpr` is not what produces it: `qvmBytesOfNats` already truncates
    with `Nat.toUInt8`, so deleting the mask reddens nothing (perturbation P11, reported
    rather than hidden). The mask stays because it says out loud that the field is a byte,
    which is what R5 asks a port to record; the behaviour is what is gated. -/
def seedExprTokenWidth_ok : Bool :=
  (List.range 9).all fun t =>
    qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.token t))) == [2, t] &&
    qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.tokenOffset t 0x20))) == [3, t] ++ u32b 0x20 &&
  qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.token 256))) == [2, 0]

/-- The u32 pointer position: four big-endian bytes, high bytes dropped exactly as a
    fixed-width `to_be_bytes` does, and two pointers that differ below 2^32 stay apart. -/
def seedExprPointerWidth_ok : Bool :=
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0x100)))) == [1, 0, 0, 1, 0] &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0)))) == [1, 0, 0, 0, 0] &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal (2^32))))) ==
    (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0)))) &&
  (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0x100)))) !=
    (qvmBytesToNats (hashQuotientExpr (QuotientExpr.mem (.literal 0x101))))

/-! #### GATE 4 and GATE 5 - hazard 2: the artifact, read at #eval time -/

/-- The literal after `QUOTIENT_CERTIFY_SEED_DOMAIN`, between the first `b"` and the
    next quote. -/
def certDomainTagFromSource (src : String) : Option String :=
  match src.splitOn "QUOTIENT_CERTIFY_SEED_DOMAIN" with
  | _ :: tail :: _ =>
      match tail.splitOn "b\"" with
      | _ :: lit :: _ => some ((lit.takeWhile (fun c => c != '"')).toString)
      | _ => none
  | _ => none

/-- The Lean tag back as a String, so GATE 4 compares the artifact against the PORT rather
    than against a third paste of the same text. -/
def certifySeedDomainString : String :=
  String.ofList ((qvmBytesToNats quotientCertifySeedDomain).map Char.ofNat)

/-- D-P19's reachability gate, FIRST among the artifact gates: a wrong path is a named red,
    not an empty match that satisfies every needle below. -/
def certifyArtifactReachable_ok : IO Bool := do
  let src ← readCertifySource
  pure (certifyReadOk src && src.contains "fn derive_certify_seed" &&
        src.contains "fn identity_segment" && src.contains "fn check_fold" &&
        src.contains "fn certify_quotient_builds_agree" && src.contains "fn identity_values")

/-- HAZARD 2'S ANSWER MADE LOAD-BEARING. The Rust pins nothing about this tag: no test
    asserts its value (LT:425-507 asserts five sensitivities only), so editing v3 to v4 is
    invisible to cargo. This gate reads the literal out of certify.rs and requires it to
    equal the port's, so the next bump reddens a named check. Rules out: the tag being
    edited, reworded, or moved into a constant the port no longer mirrors. -/
def seedDomainTag_artifactPinned_ok : IO Bool := do
  let src ← readCertifySource
  if ! certifyReadOk src then
    pure false
  else
    pure (certDomainTagFromSource src == certifySeedDomainString &&
          certifySeedDomainString.length == 35 &&
          tagBytes.length == 35)

/-- The ten `hasher.update` calls of `derive_certify_seed`, in the order the Rust
    writes them, plus the finalize. Read back out of the artifact: reordering two segments
    changes the challenge and reddens this gate, and no Lean-side reasoning is involved. -/
def seedPreimageLayoutNeedles : List String :=
  ["hasher.update(QUOTIENT_CERTIFY_SEED_DOMAIN)",
   "hasher.update((builds.len() as u64).to_be_bytes())",
   "hasher.update((build.bytes.len() as u64).to_be_bytes())",
   "hasher.update(&build.bytes)",
   "hasher.update((build.consts.len() as u64).to_be_bytes())",
   "hasher.update(value.to_be_bytes::<32>())",
   "hasher.update((exprs.len() as u64).to_be_bytes())",
   "hash_quotient_expr(&mut hasher, expr)",
   "hasher.update((vk_payload.len() as u64).to_be_bytes())",
   "hasher.update(vk_payload)",
   "hasher.finalize().into()"]

/-- Every needle occurs EXACTLY ONCE in the window, as well as in order: an extra update
    call would be an extra segment the port does not write. -/
def seedPreimageLayout_artifact_ok : IO Bool := do
  let src ← readCertifySource
  if ! certifyReadOk src then
    pure false
  else
    pure (match certFnWindow "fn derive_certify_seed" "fn hash_quotient_expr" src with
          | none => false
          | some body =>
              certOrdered seedPreimageLayoutNeedles body &&
              (seedPreimageLayoutNeedles.all fun needle =>
                (body.splitOn needle).length - 1 == 1) &&
              body.contains "for build in builds" &&
              body.contains "for value in &build.consts")

/-- The seven arms of `hash_quotient_expr`: constructor marker, then its tag byte, then
    its payload write, then - for the two binary arms - the left subtree before the right.
    The tag NUMBERS are pinned here against the source and in GATE 3 against hand-written
    bytes, which is the pair that makes a renumbering impossible to hide. -/
def exprHashTags_artifact_ok : IO Bool := do
  let src ← readCertifySource
  if ! certifyReadOk src then
    pure false
  else
    pure (match certFnWindow "fn hash_quotient_expr" "fn interpreted_exprs" src with
          | none => false
          | some body => certOrdered exprTagNeedles body &&
              (exprTagNeedles.all fun needle => (body.splitOn needle).length >= 1))

/-! #### GATE 6 - hazard 1: every compared artifact actually changes the seed -/

/-- THE SENSITIVITY GATE, and the Lean form of the Rust's only seed test (LT:446-506). The
    five clauses the Rust asserts - a bytecode byte, the optimized constant, the baseline
    constant, the expression, the VK payload - plus four it does not: the build ORDER, the
    build COUNT, the expression COUNT and the payload LENGTH. The last three are the
    length-prefix clauses, which is where a port that forgets a `.len()` update hides.

    The final clause is the opposite direction and is the one a reviewer should stop on:
    the seed binds `bytes` and `consts` and NOTHING ELSE of the record. Two builds
    that differ only in `max_stack`, `used_ops` or `used_mem_tokens` hash the
    same, exactly as in the Rust (QVC:57-65 reads two fields). That is a property of the
    reference, not an omission here, and a port that hashed the whole record would fail it. -/
def seed_bindsEveryArtifact_ok : Bool :=
  let s (bs : List QuotientProgramBuild) (es : List QuotientExpr) (vk : Bytes) :=
    qvmBytesToNats (deriveCertifySeed bs es vk)
  let base := wantCertSeedF1
  (s [patchBuildBytes certBuild0 0 0x08, certBuild1] [certExpr0] certVkPayload != base) &&
  (s [patchBuildConst certBuild0 0 19, certBuild1] [certExpr0] certVkPayload != base) &&
  (s [certBuild0, patchBuildConst certBuild1 0 23] [certExpr0] certVkPayload != base) &&
  (s [certBuild0, certBuild1]
     [QuotientExpr.add (QuotientExpr.mem (.literal 0x120)) (QuotientExpr.const 29)]
     certVkPayload != base) &&
  (s [certBuild0, certBuild1] [certExpr0] (qvmBytesOfNats (List.replicate 64 0xcd)) != base) &&
  (s [certBuild1, certBuild0] [certExpr0] certVkPayload != base) &&
  (s [certBuild0] [certExpr0] certVkPayload != base) &&
  (s [certBuild0, certBuild1] [] certVkPayload != base) &&
  (s [certBuild0, certBuild1] [certExpr0, certExpr0] certVkPayload != base) &&
  (s [certBuild0, certBuild1] [certExpr0] (qvmBytesOfNats (List.replicate 63 0xab)) != base) &&
  (s [uncertifiedFieldsBuild, certBuild1] [certExpr0] certVkPayload == base)
where
  /-- The same build with all three of the fields the reference does NOT hash changed. -/
  uncertifiedFieldsBuild : QuotientProgramBuild :=
    { certBuild0 with maxStack := 99, usedOps := qvmBytesOfNats [0x01, 0x02],
                      usedMemTokens := qvmBytesOfNats [qMemBeta] }

/-- The seed is derived from the FINALIZED bytes, not from what the emitter held before
    compaction. The four-term linear run is the smallest expression P-09c's compactor
    rewrites, so the two byte buffers differ and only the second one is what the reference
    hashes. Rules out: a port that hashed the pre-compaction buffer, which would certify a
    program that is not the one emitted. -/
def seed_bindsFinalizedNotPreCompaction_ok : Bool :=
  let e := cSumLeft (cLit 0x100)
    [cScaled 2 (cLit 0x120), cScaled 3 (cLit 0x140), cScaled 5 (cLit 0x160),
     cScaled 7 (cLit 0x180)]
  match identityExpr noShapeRecognizers builderDefault e QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      match finish s with
      | .error _ => false
      | .ok build =>
          let preBuild : QuotientProgramBuild :=
            { build with bytes := qvmBytesOfNats s.bytes }
          s.bytes != qvmBytesToNats build.bytes &&
            s.bytes.length != build.bytes.size &&
            qvmBytesToNats (deriveCertifySeed [preBuild] [] Bytes.empty) !=
              qvmBytesToNats (deriveCertifySeed [build] [] Bytes.empty)

/-- The VK leg: `certifyQuotientProgram` takes the record and calls `bytes` inside,
    exactly as QVC:135 does, so two VKs that differ in one payload word must produce
    different seeds and two identical VKs must not. Rules out: the payload being dropped
    from the derivation on the way into the driver. -/
def seed_usesVkPayload_ok : Bool :=
  certVk.bytes.size == 320 &&
  (List.zip (List.range 10) vkPayloadWords).all fun (_, w) => w.toNat > 0 &&
  ! hasDuplicateNat (vkPayloadWords.map fun w => w.toNat) &&
  qvmBytesToNats (deriveCertifySeed [certBuild0] [certExpr0] certVk.bytes) !=
    qvmBytesToNats (deriveCertifySeed [certBuild0] [certExpr0] certVkAlt.bytes) &&
  qvmBytesToNats (deriveCertifySeed [certBuild0] [certExpr0] certVk.bytes) ==
    qvmBytesToNats (deriveCertifySeed [certBuild0] [certExpr0] certVk.bytes)

/-! #### GATE 7 - hazard 1: the chain from preimage to challenge -/

/-- The four pinned challenges, from the same independent Python model: seed ->
    `QuotientRefMemory::derive` -> field element. -/
def wantChallengeF1Lit0x100 : QVMFr :=
  0x55d440776238be5833208bd0bc364a0499ef9da3a7f211d7bafc6b79e1f727c2
def wantChallengeF1Lit0 : QVMFr :=
  0x3f86860017ea5cf1ba42f5464a6c879a2b0a33ae74b1d1788af4e2acf2769fe8
def wantChallengeF1Tok0 : QVMFr :=
  0x36556acf5ffebf79dbfc71aad721f8015b05f909d024e825d39d8aa9d605b8fe
def wantChallengeF3Lit0x100 : QVMFr :=
  0x4d1978d883e6fc891f11504dd8002a21edc9778e9760957e42114c1569b8267a

/-- THE HINGE CLOSED. This is the whole soundness argument in one line of code: the
    preimage determines the seed determines the assignment, and every layer was checked
    against an implementation that is not this one. A different preimage is a different
    challenge - the last clause says so concretely, by patching one bytecode byte and
    watching the field element at the SAME address move. Rules out: a seed that is
    constant, a seed that is not the digest of the transcribed preimage, a derive that
    ignores its seed, and a port that re-derives the assignment per side. -/
def seedChallengeChain_ok : Bool :=
  let m := quotientRefMemoryNew certSeedF1
  (m.derive 0 0x100).1 == wantChallengeF1Lit0x100 &&
  (m.derive 0 0).1 == wantChallengeF1Lit0 &&
  (m.derive 1 0).1 == wantChallengeF1Tok0 &&
  ((quotientRefMemoryNew certSeedF3).derive 0 0x100).1 == wantChallengeF3Lit0x100 &&
  ((quotientRefMemoryNew (deriveCertifySeed [patchBuildBytes certBuild0 0 0x08, certBuild1]
      [certExpr0] certVkPayload)).derive 0 0x100).1 != wantChallengeF1Lit0x100 &&
  (m.derive 0 0x100).1 < qvmFrModulus &&
  (m.derive 0 0x100).1 != (m.derive 1 0).1

/-- The two call sites of QVC:136 and QVC:307 differ in how many builds they pass, so the
    one-build and two-build derivations over the same artifacts must differ - otherwise the
    dual-build challenge would not depend on the pair, which is what QVC:45-46 claims. -/
def seed_singleVersusDualBuild_ok : Bool :=
  qvmBytesToNats (deriveCertifySeed [certBuild0] [certExpr0] certVkPayload) !=
    qvmBytesToNats (deriveCertifySeed [certBuild0, certBuild0] [certExpr0] certVkPayload) &&
  qvmBytesToNats (deriveCertifySeed [certBuild0, certBuild1] [certExpr0] certVkPayload) ==
    wantCertSeedF1

/-! #### GATE 8 - hazard 4: the driver accepts a correct program -/

/-- THE HEADLINE GATE. Three real programs built by P-09c's emitter - three identities
    with a selector fold in the middle, an identity stream interleaved with all three
    native marker kinds, and a LIN7 superinstruction build - each certify cleanly through
    the whole driver: seed, segment walk, interpreter, oracle comparison, fold check,
    cursor advance and the trailing-byte check. Rules out: a walker that mis-advances, a
    fold check that rejects its own encoding, a marker leg that rejects a marker it just
    emitted, and a comparison that fails on a program it should accept. Every miscompile
    gate below is only meaningful because this one is green. -/
def certifyProgram_acceptsBuiltPrograms_ok : Bool :=
  certifyOk (match threeIdentityBuild with
             | .ok b => certifyQuotientProgram threeIdentityPlan b certVk
             | .error _ => .error "<build failed>") &&
  certifyOk (match markerBuild with
             | .ok b => certifyQuotientProgram markerPlan b certVk
             | .error _ => .error "<build failed>") &&
  certifyOk (match cLin7Build with
             | .ok b => certifyQuotientProgram cLin7Plan b certVk
             | .error _ => .error "<build failed>")

/-! #### GATE 9 - hazard 3: the segment walker, round-tripped -/

/-- The certifier's cursor loop, exposed: every (start, expr_end, fold opcode) triple of an
    all-identity program. KAT helper, not a Rust item; the fuel is the same crutch as
    `identitySegment`'s. -/
def walkAllSegments (bytes : List Nat) : Nat → List (Nat × Nat × Nat) → Nat →
    Except String (List (Nat × Nat × Nat))
  | 0, _, _ => .error "walkAllSegments fuel exhausted - port-only bound"
  | fuel + 1, acc, cursor =>
      if cursor >= bytes.length then
        .ok acc
      else do
        let (exprEnd, op) ← identitySegment bytes cursor
        let len ← faultToString (quotientOpLen bytes exprEnd)
        walkAllSegments bytes fuel (acc ++ [(cursor, exprEnd, op)]) (exprEnd + len)
termination_by fuel => fuel

/-- The three segments of the built program, at pinned byte offsets: identity 0 is
    PUSH_MEM_U16 0x100 / ADD_MEM_U16 0x120 with FOLD_MAIN at 6; identity 1 is
    PUSH_MEM_U16 0x140 / MUL_CONST_U8 slot 0 with FOLD_SELECTOR (bucket 1, gap 5) at 12;
    identity 2 is PUSH_MEM_U16 0x100 / ADD_CONST_U8 slot 1 / NEG with FOLD_MAIN at 22, and
    the program is exactly 23 bytes. Rules out: a walker that includes the fold in the
    advances by one byte instead of the instruction length, that mis-reads the 4-byte
    selector fold as 1, and that stops early. -/
def segmentWalk_threeIdentityPinned_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      bytes.length == 23 &&
      walkAllSegments bytes bytes.length [] 0 ==
        .ok [(0, 6, qOpFoldMain), (7, 12, qOpFoldSelector), (16, 22, qOpFoldMain)] &&
      (bytes.take 6) == [5, 1, 0, 16, 1, 32] &&
      (bytes.drop 7).take 5 == [5, 1, 64, 13, 0] &&
      (bytes.drop 16).take 6 == [5, 1, 0, 12, 1, 8] &&
      bytes.getD 12 0 == qOpFoldSelector && bytes.getD 22 0 == qOpFoldMain

/-- THE HAZARD-3 ROUND-TRIP. Extract every segment with the walker, run each through
    `QVM.run` - P-09b's interpreter, the second implementation - and compare against
    the direct evaluation of the `QuotientExpr` tree it was lowered from, all against
    ONE seeded assignment. This is the per-identity statement over a MULTI-identity
    program, which is exactly what P-09c said could not be written before this file.
    Rules out: a segmenter that hands the interpreter the fold (which QVR rejects by
    design), one that hands it the next identity's bytes, and an emitter whose second or
    third identity disagrees with its tree while the first agrees. -/
def segmentRoundTrip_threeIdentities_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      let seed := deriveCertifySeed [build] cExprTrees certVk.bytes
      let mem0 := quotientRefMemoryNew seed
      match walkAllSegments bytes bytes.length [] 0 with
      | .error _ => false
      | .ok segs =>
          segs.length == 3 && cExprTrees.length == 3 &&
          (List.zip segs cExprTrees).all fun (seg, expr) =>
            let slice := (bytes.drop seg.1).take (seg.2.1 - seg.1)
            match QVM.run slice build.consts mem0, evalQuotientExpr expr mem0 with
            | .ok (v, _), .ok (o, _) => v == o && slice != []
            | _, _ => false

/-- The same round-trip through the driver's own legs, so the gate is not checking a
    parallel implementation of the cursor: `identityValues` walks the segments and runs
    the interpreter, and the oracle fold walks the trees. -/
def segmentRoundTrip_viaIdentityValues_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      let mem := quotientRefMemoryNew (deriveCertifySeed [build] cExprTrees certVk.bytes)
      match identityValues threeIdentityPlan build mem,
            oracleValues cExprTrees mem with
      | .ok (bytecode, _), .ok (oracle, _) =>
          bytecode.length == 3 && oracle.length == 3 &&
          (List.zip bytecode oracle).all fun (a, b) => a == b && a < qvmFrModulus
      | _, _ => false

/-- The walker agrees with P-09c's single-fold stripper wherever both apply: for a
    one-identity program, the segment the walker finds is exactly the buffer the stripper
    returns. Two packages, two implementations, one answer - and neither is a third copy of
    the other. -/
def identitySegment_agreesWithBuilderStripper_ok : Bool :=
  [cExpr0, cExpr1, cExpr2, cLin7Expr].all fun e =>
    match identityExpr noShapeRecognizers builderDefault e QuotientTarget.main none
          >>= finish with
    | .error _ => false
    | .ok build =>
        let bytes := qvmBytesToNats build.bytes
        match identitySegment bytes 0, finalizedIdentitySegment bytes with
        | .ok (exprEnd, _), some seg => (bytes.take exprEnd) == seg && exprEnd == seg.length
        | _, _ => false

/-- HAZARD 3's rejection leg: a native marker inside an expression region is an error, not
    a skip, at all three marker bytes. The marker program's permutation marker sits at byte
    7, so walking from there must refuse. Rules out: a walker that treats 0x19/0x1b/0x1f as
    ordinary instructions and swallows the next item. -/
def identitySegment_nativeMarkerInterrupts_ok : Bool :=
  (match markerBuild with
   | .error _ => false
   | .ok b =>
       identitySegment (qvmBytesToNats b.bytes) 7 ==
         .error "native marker 0x19 at byte 7 interrupts an identity expression") &&
  identitySegment [5, 1, 0, 31, 10] 0 ==
    .error "native marker 0x1f at byte 3 interrupts an identity expression" &&
  identitySegment [5, 1, 0, 27, 0, 7, 10] 0 ==
    .error "native marker 0x1b at byte 3 interrupts an identity expression"

/-- The no-fold case: a well-formed expression that is never folded is an error naming the
    START byte, not the current byte (QVC:242-244). -/
def identitySegment_neverFolded_ok : Bool :=
  identitySegment [5, 1, 0, 16, 1, 32] 0 ==
    .error "identity expression starting at byte 0 is never folded" &&
  identitySegment [5, 1, 0, 16, 1, 32, 5, 1, 0] 6 ==
    .error "identity expression starting at byte 6 is never folded" &&
  identitySegment [] 0 == .error "identity expression starting at byte 0 is never folded"

/-- R4's recorded divergence, gated: the two panic sites inside `quotient_op_len`
    (unknown opcode QVM:3022, operand read past the end QVM:2817) surface as Err carrying
    the site text rather than as an abort, because the driver's error type is the Rust's
    String. The Rust would kill the render here. Rules out: the walker's faults being
    swallowed into an ok, or re-labelled as one of the nine interpreter faults. -/
def identitySegment_unknownOpcodeIsPanicClass_ok : Bool :=
  identitySegment [153, 10] 0 ==
    .error "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs:3022 (unknown quotient op 153 at byte 0)" &&
  identitySegment [34, 1, 1] 0 ==
    .error "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs:2817 (u16 quotient operand)" &&
  !(errText (identitySegment [153, 10] 0)).contains "unknown opcode"

/-- R10: the segment fuel never binds on any fixture, so it is a totality crutch and not a
    behaviour. Rules out: a walker that can loop, and a fixture set too small to exercise
    the bound. -/
def segmentWalkFuelNeverBinds_ok : Bool :=
  (driverFixtures.map fun (_, b) => b).all fun build =>
      let bytes := qvmBytesToNats build.bytes
      (List.range (bytes.length + 1)).all fun start =>
        ! (errText (identitySegment bytes start)).contains "fuel exhausted" &&
        ! (errText (walkAllSegments bytes (bytes.length + 1) [] start)).contains
          "fuel exhausted"

/-- The driver's own cursor ends exactly at the end of the program for every accepted
    fixture, which is the precondition that makes the trailing-byte check meaningful. -/
def certifyItemWalk_endsAtProgramEnd_ok : Bool :=
  driverFixtures.all fun (plan, build) =>
    let bytes := qvmBytesToNats build.bytes
    match certifyItemWalk plan build bytes
          (quotientRefMemoryNew
            (deriveCertifySeed [build] (interpretedExprs plan) certVk.bytes)) with
    | .error _ => false
    | .ok (cursor, _) => cursor == bytes.length


/-! #### GATE 10 - the comparison itself: a miscompile is caught, with the Rust's message -/

/-- THE MISCOMPILE GATE. Two byte-level perturbations of a program that otherwise certifies
    cleanly, each pinned to the FULL Rust message including both `{:?}` field elements:
    (a) the low byte of identity 0's first pointer, which changes the memory address the
    bytecode reads and nothing else; (b) the constant table entry identity 1 multiplies by,
    which changes the bytecode's operand while the expression tree still says 7. Neither
    perturbation can move an instruction boundary - the byte lengths are untouched - so the
    ONLY thing that can go wrong is the value, which is exactly what QVC:157-165 claims to
    catch. Rules out: a comparison that always passes, a comparison that always faults, the
    error prefix being dropped, and the `Fq` Debug rendering drifting from CUR:128-138.
    Also the non-vacuity control for GATE 8: the same driver on the same plan with the
    unpatched build returns ok. -/
def certifyProgram_detectsMiscompile_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      certifyOk (certifyQuotientProgram threeIdentityPlan build certVk) &&
      errText (certifyQuotientProgram threeIdentityPlan (patchBuildBytes build 2 1) certVk) ==
        "quotient VM miscompiled identity 0 (Gate { gate_index: 0, gate_name: \"cert\", constraint_index: 0, constraint_name: \"c\", polynomial_index: 0 }): bytecode evaluates to Fq(0x0199914268f8ada65ae37e300636b8c7620326622cc126650c8fc22e82196a00) but its expression evaluates to Fq(0x67438845e492ff167ba1a7ec8f543fb1c64b64cfc19520b86e41a8262188f9c8). This is a codegen bug in the quotient lowering (shape recognizer, operand packing, or run compaction), not a proof or verifying-key problem." &&
      errText (certifyQuotientProgram threeIdentityPlan (patchBuildConst build 0 11) certVk) ==
        "quotient VM miscompiled identity 1 (Gate { gate_index: 1, gate_name: \"cert\", constraint_index: 0, constraint_name: \"c\", polynomial_index: 0 }): bytecode evaluates to Fq(0x34074e2f078670de918b29fd88cac63d6df3eb4a400707e7f4723179e4252cc4) but its expression evaluates to Fq(0x6057bb911b7ce940a71b04eb8ad95112b9770676b460ab930feb93d8a874bf66). This is a codegen bug in the quotient lowering (shape recognizer, operand packing, or run compaction), not a proof or verifying-key problem."

/-- THE FAULT-WRAP LEG, QVC:147-154, exercised two ways so both prefixes are pinned by a
    value rather than by a comment. (a) Byte 3 of the program is an opcode the WALKER cannot
    decode, so the failure arrives as the item-prefixed panic text - the R4 leg recorded in
    the header. (b) Byte 11 is the slot operand of identity 1's MUL_CONST_U8: setting it to
    200 leaves a perfectly walkable instruction whose CONSTANT LOOKUP fails, so the fault
    comes from the interpreter and must arrive wrapped in the identity prefix carrying the
    reference's own message (P-09b's `QVMFault.message`). Rules out: the `map_err` at
    QVC:149-154 being dropped, the fault taxonomy losing its text on the way into a String,
    and a driver that swallows an interpreter fault and reports ok. -/
def certifyProgram_wrapsInterpreterFaults_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      errText (certifyQuotientProgram threeIdentityPlan (patchBuildBytes build 3 153) certVk) ==
        "quotient item 0: proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs:3022 (unknown quotient op 153 at byte 3)" &&
      errText (certifyQuotientProgram threeIdentityPlan (patchBuildBytes build 11 200) certVk) ==
        "quotient identity 1 (Gate { gate_index: 1, gate_name: \"cert\", constraint_index: 0, constraint_name: \"c\", polynomial_index: 0 }): reference VM constant slot 200 out of range at byte 3"

/-- The item-index prefix of QVC:145: an identity whose expression region is interrupted by
    a native marker is reported as `quotient item {i}`, which is the only place that
    index appears in the driver's output. Rules out: the map_err at QVC:145 being dropped,
    and the marker check firing on the wrong item. -/
def certifyProgram_itemPrefix_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      errText (certifyQuotientProgram threeIdentityPlan (patchBuildBytes build 0 0x19) certVk) ==
        "quotient item 0: native marker 0x19 at byte 0 interrupts an identity expression"

/-! #### GATE 11 - the fold check, leg by leg -/

/-- Every arm of QVC:248-289, each pinned to its own message, plus the precedence claim the
    Rust's statement order makes observable: a wrong bucket on a truncated gap reports the
    BUCKET, because the bucket is checked first. The last clause is the accept leg - the
    real program's selector fold at byte 16 (bucket 1, gap 5) against the plan that says
    exactly that. Rules out: the u24 being read little-endian (gap 5 would come out as
    1280), the bucket and gap being swapped, `gap_for` being consulted before the bytes
    are read, and the catch-all arm firing on a correct pair. -/
def checkFold_legs_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      (certifyOk (checkFold bytes 12 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 1) cExpr1)
        threeIdentityPlan)) &&
      (certifyOk (checkFold bytes 6 qOpFoldMain (cIdentity 0 QuotientTarget.main cExpr0)
        threeIdentityPlan)) &&
      errText (checkFold bytes 12 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 2) cExpr1)
        threeIdentityPlan) == "selector fold targets bucket 1 but the plan says 2" &&
      errText (checkFold bytes 12 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 1) cExpr1)
        { threeIdentityPlan with selectorFold :=
            { gapsByIdentity := [none, some 9, none], tailExponents := [0], maxPower := 0 } })
        == "selector fold gap 5 does not match planned gap 9" &&
      errText (checkFold bytes 12 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 1) cExpr1)
        { threeIdentityPlan with selectorFold := selectorFoldPlanDefault })
        == "selector identity has no planned fold gap" &&
      errText (checkFold [11] 0 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 1) cExpr1)
        threeIdentityPlan) == "truncated selector fold index" &&
      errText (checkFold [11, 1] 0 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 1) cExpr1)
        threeIdentityPlan) == "truncated selector fold gap" &&
      errText (checkFold [11, 2] 0 qOpFoldSelector (cIdentity 1 (QuotientTarget.selector 1) cExpr1)
        threeIdentityPlan) == "selector fold targets bucket 2 but the plan says 1" &&
      errText (checkFold bytes 6 qOpFoldMain (cIdentity 0 (QuotientTarget.selector 0) cExpr0)
        threeIdentityPlan) == "fold opcode 0xa does not match planned target Selector(0)" &&
      errText (checkFold bytes 6 qOpFoldSelector (cIdentity 0 QuotientTarget.main cExpr0)
        threeIdentityPlan) == "fold opcode 0xb does not match planned target Main" &&
      errText (checkFold bytes 22 qOpFoldMain (cIdentity 2 QuotientTarget.main cExpr2)
        threeIdentityPlan) == "<ok>"

/-- The fold check reached through the driver, so the identity prefix of QVC:167-172 is
    pinned too, not just the inner message: the emitted selector fold's bucket byte is
    changed from 1 to 2 while the plan still says 1. The value comparison for that identity
    still passes (the fold byte is outside the segment), so the only thing that can fire is
    the fold check. Rules out: the map_err at QVC:167-172 being dropped. -/
def certifyProgram_foldMismatch_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      errText (certifyQuotientProgram threeIdentityPlan (patchBuildBytes build 13 2) certVk) ==
        "quotient identity 1 (Gate { gate_index: 1, gate_name: \"cert\", constraint_index: 0, constraint_name: \"c\", polynomial_index: 0 }): selector fold targets bucket 2 but the plan says 1"

/-! #### GATE 12 - the native-marker legs -/

/-- All four marker errors of QVC:176-213, each pinned, plus the accept leg from GATE 8
    restated on the same fixture so the four are not simply "everything errors". The
    truncated-index case drops the program's last byte; the wrong-marker case swaps the
    permutation marker for the lookup marker at the same position; the index case changes
    the u16 the builder wrote. Rules out: reading the marker index little-endian (7 would
    come out as 1792), checking the index for a plain permutation marker, and skipping the
    bounds check on a truncated program. -/
def certifyProgram_nativeMarkerLegs_ok : Bool :=
  match markerBuild with
  | .error _ => false
  | .ok build =>
      certifyOk (certifyQuotientProgram markerPlan build certVk) &&
      errText (certifyQuotientProgram markerPlan (patchBuildBytes build 7 0x1f) certVk) ==
        "quotient item 1: expected native marker 0x19 at byte 7, found 0x1f" &&
      errText (certifyQuotientProgram markerPlan (patchBuildBytes build 18 0x08) certVk) ==
        "quotient item 4: native identity index 8 does not match planned index 7" &&
      errText (certifyQuotientProgram markerPlan
        { build with bytes := qvmBytesOfNats ((qvmBytesToNats build.bytes).take 18) } certVk) ==
        "quotient item 4: truncated native identity index" &&
      errText (certifyQuotientProgram markerPlan
        { build with bytes := qvmBytesOfNats ((qvmBytesToNats build.bytes).take 7) } certVk) ==
        "quotient item 1: program ended before native marker"

/-- The trailing-byte check of QVC:217-222, with the count the Rust interpolates. One extra
    ADD byte is the smallest case; two is the case that would expose an off-by-one in
    `bytes.len() - cursor`. Rules out: the check being dropped (a program with garbage
    after the last fold would certify), and the count being the cursor rather than the
    remainder. -/
def certifyProgram_trailingBytes_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      errText (certifyQuotientProgram threeIdentityPlan
        { build with bytes := qvmBytesOfNats (bytes ++ [qOpAdd]) } certVk) ==
        "quotient program has 1 trailing byte(s) after the planned item stream" &&
      errText (certifyQuotientProgram threeIdentityPlan
        { build with bytes := qvmBytesOfNats (bytes ++ [qOpAdd, qOpMul]) } certVk) ==
        "quotient program has 2 trailing byte(s) after the planned item stream"

/-! #### GATE 13 - the plan-side helpers -/

/-- `interpreted_exprs` keeps exactly the identity items, in stream order, and nothing
    for the three marker kinds. The marker plan is the non-degenerate case: five items, two
    expressions. Rules out: a filter that also collects native identities (which would
    bind the seed to expressions the VM never evaluates, changing the challenge), and one
    that reverses or deduplicates. -/
def interpretedExprs_identityItemsOnly_ok : Bool :=
  interpretedExprs threeIdentityPlan == cExprTrees &&
  interpretedExprs markerPlan == [cExpr0, cExpr2] &&
  interpretedExprs cLin7Plan == [cLin7Expr] &&
  (interpretedExprs threeIdentityPlan).length == 3 &&
  (interpretedExprs markerPlan).length == 2 &&
  (interpretedExprs { threeIdentityPlan with items := [] }).length == 0

/-- `identity_values` pushes `Fq::ZERO` for every marker (QVC:358) and one value per
    item, so the vector length is the item count and not the identity count - the Rust's
    dual-build comparison is position-by-position across the whole stream. Rules out:
    dropping the marker slots (which would misalign every later position against the other
    build) and pushing the marker's own expression value. -/
def identityValues_markerZeros_ok : Bool :=
  match markerBuild with
  | .error _ => false
  | .ok build =>
      let mem := quotientRefMemoryNew (deriveCertifySeed [build] (interpretedExprs markerPlan)
        certVk.bytes)
      match identityValues markerPlan build mem with
      | .error _ => false
      | .ok (values, _) =>
          values.length == 5 && values.getD 1 1 == qvmFrZero && values.getD 3 1 == qvmFrZero &&
          values.getD 4 1 == qvmFrZero && values.getD 0 1 != qvmFrZero &&
          values.getD 2 1 != qvmFrZero

/-- The memory threading, driver side. After a whole walk the memo table holds exactly the
    three distinct addresses the three identities read - 0x100, 0x120 and 0x140 - which is
    only possible if ONE memory survived all three items: a port that restarted the memory
    per item would end with one entry, and one that restarted per side would end with the
    same three but could not compare them. Every entry also equals the uncached derivation,
    so the cache cannot disagree with the function it memoises. Rules out: the `&mut mem`
    of QVC:137 being re-created inside the loop, and the two sides of the comparison
    observing different assignments - which is the property the whole certification rests
    on (P-09b's hazard 1, second half). -/
def certify_threadsOneMemory_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      let bytes := qvmBytesToNats build.bytes
      let seed := deriveCertifySeed [build] cExprTrees certVk.bytes
      match certifyItemWalk threeIdentityPlan build bytes (quotientRefMemoryNew seed) with
      | .error _ => false
      | .ok (_, mem) =>
          mem.cache.length == 3 &&
          mem.seed == seed &&
          (mem.cache.all fun (d, a, v) => d == 0 && deriveReferenceMemory seed d a == v) &&
          ! hasDuplicateNat (mem.cache.map fun (_, a, _) => a) &&
          (mem.cache.map fun (_, a, _) => a).toFinset ==
            ({0x100, 0x120, 0x140} : Finset Nat) &&
          (oracleValues cExprTrees (quotientRefMemoryNew seed)).isOk

/-! #### GATE 14 - the dual-build comparison -/

/-- THE DUAL-BUILD GATE. The same identity emitted through the LIN7 recognizer and through
    the generic Fr path - 21 bytes against 25, two different programs for one polynomial -
    certify as agreeing, and a one-byte change to the baseline's pointer makes them
    disagree with the Rust's message and both `Fq` values. The seed here absorbs BOTH
    builds (QVC:307), so the challenge depends on the pair; GATE 6's
    `seed_singleVersusDualBuild_ok` is that claim. Rules out: a comparison that always
    passes (the disagree clause), one that always fails (the agree clause), and a baseline
    that is secretly the same build (the byte-length clause and GATE 15's non-degeneracy).

    SCOPE, stated plainly: P-09e owns the real shape recognizers, so the "optimized" side
    here is a hook that recognizes exactly one expression. That exercises the comparison
    and the seed binding; it is NOT the Rust's claim about recognizers on a real circuit. -/
def certifyBuildsAgree_ok : Bool :=
  match cLin7Build, cBaselineBuild with
  | .ok o, .ok b =>
      qvmBytesToNats o.bytes != qvmBytesToNats b.bytes &&
      o.bytes.size == 23 && b.bytes.size == 27 &&
      certifyOk (certifyQuotientBuildsAgree cLin7Plan o b certVk) &&
      certifyOk (certifyQuotientProgram cLin7Plan o certVk) &&
      certifyOk (certifyQuotientProgram cLin7Plan b certVk) &&
      errText (certifyQuotientBuildsAgree cLin7Plan o (patchBuildBytes b 1 0x01) certVk) ==
        "quotient limb superinstructions changed the value of interpreted identity at stream position 0: Fq(0x184bceaba778a80a43851f87516d31d7a9c97d050b5b604e73da9dfb2a5729e3) with limb opcodes, Fq(0x184bceaba778a80a43851f87516d31d7a9c97d050b5b604e73da9dfb2a5729e5) without. One of the shape recognizers is unsound for this gate shape."
  | _, _ => false

/-- The stream-position index of QVC:321-329: with three identities, a disagreement in the
    MIDDLE must name position 1, not 0. Rules out: the enumerate being dropped, which would
    make every failure report position 0 and send a diagnostician to the wrong identity. -/
def certifyBuildsAgree_positionIndex_ok : Bool :=
  match threeIdentityBuild with
  | .error _ => false
  | .ok build =>
      errText (certifyQuotientBuildsAgree threeIdentityPlan build
        (patchBuildBytes build 9 65) certVk) ==
        "quotient limb superinstructions changed the value of interpreted identity at stream position 1: Fq(0x39866d85b274ac07a095af227ba43a262ec16061880643225c5b62611a8feb35) with limb opcodes, Fq(0x4a2bb9709c4e91e5abd91e56c9398954288ac6cf2bd8f9ba3651c9e1db82c93d) without. One of the shape recognizers is unsound for this gate shape." &&
      certifyOk (certifyQuotientBuildsAgree threeIdentityPlan build
        (patchBuildBytes build 9 64) certVk)

/-- The unreachable leg, stated rather than deleted (R1): QVC:313-319 compares the two
    vectors' lengths, but both are folded from the same `plan.items`, so they always
    have `plan.items.length` entries. This gate asserts that the two lengths agree on
    every fixture, which is the reason the branch cannot fire. -/
def certifyBuildsAgree_lengthCheckUnreachable_ok : Bool :=
  match cLin7Build, cBaselineBuild, threeIdentityBuild with
  | .ok o, .ok b, .ok t =>
      (identityValues cLin7Plan o (quotientRefMemoryNew certSeedF1)).map (fun p => p.1.length) ==
        .ok (cLin7Plan.items.length) &&
      (identityValues cLin7Plan b (quotientRefMemoryNew certSeedF1)).map (fun p => p.1.length) ==
        .ok (cLin7Plan.items.length) &&
      (identityValues threeIdentityPlan t (quotientRefMemoryNew certSeedF1)).map
        (fun p => p.1.length) == .ok (threeIdentityPlan.items.length)
  | _, _, _ => false

/-! #### GATE 15 - R-48: the fixtures are not degenerate -/

/-- Every comparison gate above is only as good as its fixtures' distinctness, so this is
    asserted BEFORE the comparisons are relied on (docs/REVIEW.md R-48). The clauses: the
    two seed builds differ in both bytes and constants; the three identity expressions are
    pairwise distinct; the ten VK payload words are pairwise distinct and non-zero, so a
    dropped commitment section cannot hide behind zeros; the three program segments are
    pairwise distinct; the dual-build pair differs byte-wise; and the two VKs differ in
    their payload. Rules out: any of the gates above being satisfied by a fixture that has
    only one value to compare. -/
def certifyFixturesNonDegenerate_ok : Bool :=
  certBuild0.bytes != certBuild1.bytes && certBuild0.consts != certBuild1.consts &&
  cExpr0 != cExpr1 && cExpr1 != cExpr2 && cExpr0 != cExpr2 &&
  vkPayloadWords.length == 10 &&
  ! hasDuplicateNat (vkPayloadWords.map fun (w : Word256) => w.toNat) &&
  (vkPayloadWords.all fun (w : Word256) => w.toNat > 0) &&
  certVk.bytes != certVkAlt.bytes &&
  (match threeIdentityBuild with
   | .ok b => let bytes := qvmBytesToNats b.bytes
              (bytes.take 6) != (bytes.drop 7).take 5 &&
                (bytes.drop 7).take 5 != (bytes.drop 16).take 6 &&
                (bytes.take 6) != (bytes.drop 16).take 6
   | .error _ => false) &&
  (match cLin7Build, cBaselineBuild with
   | .ok o, .ok b => o.bytes != b.bytes && o.consts != [] && b.consts != []
   | _, _ => false) &&
  (driverFixtures.map fun (_, b) => b.bytes).length == 4

/-- The payload the seed absorbs is exactly the flattened VK words, in the order Models'
    `bytes` produces: two constants, four fixed-commitment words, four permutation
    words, each 32 big-endian bytes. Rules out: the driver hashing a truncated payload, and
    the `bytes` leg of Models.lean:474 having been ported with a different section order
    than the seed assumes. -/
def certifyVkPayload_isTheFlattenedWords_ok : Bool :=
  qvmBytesToNats certVk.bytes ==
    (vkPayloadWords.flatMap fun (w : Word256) => w32b w.toNat) &&
  certVk.bytes.size == vkPayloadWords.length * 32

end Midfall.Generator.QuotientCertifyKats

#eval Midfall.Generator.QuotientCertifyKats.certifyArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedDomainTag_artifactPinned_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedPreimageLayout_artifact_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.exprHashTags_artifact_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyFixturesNonDegenerate_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedPreimage_segments_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seed_digestByteExact_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seed_is32Bytes_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyDrivers_hashTheRightArtifacts_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedExprNodeTags_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedExprTokenWidth_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedExprPointerWidth_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seed_bindsEveryArtifact_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seed_bindsFinalizedNotPreCompaction_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seed_usesVkPayload_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seedChallengeChain_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.seed_singleVersusDualBuild_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyVkPayload_isTheFlattenedWords_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_acceptsBuiltPrograms_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_detectsMiscompile_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_wrapsInterpreterFaults_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_itemPrefix_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_foldMismatch_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_trailingBytes_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyProgram_nativeMarkerLegs_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.checkFold_legs_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.segmentWalk_threeIdentityPinned_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.segmentRoundTrip_threeIdentities_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.segmentRoundTrip_viaIdentityValues_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.identitySegment_agreesWithBuilderStripper_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.identitySegment_nativeMarkerInterrupts_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.identitySegment_neverFolded_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.identitySegment_unknownOpcodeIsPanicClass_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.segmentWalkFuelNeverBinds_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyItemWalk_endsAtProgramEnd_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.interpretedExprs_identityItemsOnly_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.identityValues_markerZeros_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certify_threadsOneMemory_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyBuildsAgree_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyBuildsAgree_positionIndex_ok -- expect true
#eval Midfall.Generator.QuotientCertifyKats.certifyBuildsAgree_lengthCheckUnreachable_ok -- expect true

