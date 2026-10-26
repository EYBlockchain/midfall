-- |
-- Midfall.Generator.Api
--
-- The caller-facing API surface of the Solidity verifier crate: a port of
-- proofs/solidity-verifier/src/api.rs (761 lines at git HEAD) in full and in
-- source order (rule R1) - every top-level item, including the private helpers
-- and every impl block.
--
-- CITATION NOTATION. Three prefixes, each named with its file and its line count,
-- because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites that
-- silently pointed at the wrong file or at a declaration that does not exist:
--
-- * API: proofs/solidity-verifier/src/api.rs (761 lines at HEAD) - the file this
--   module ports.
-- * LM:  proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines) - the
--   layout constants api.rs reaches through layout::: G1_COMPRESSED_BYTES
--   (LM:74), WORD_BYTES (LM:17, already ported as Layout.lean's wordBytes) and
--   four of the five in the pub(crate) mod accumulator block at LM:288-304 -
--   LIMBS, LIMB_BITS, IDENTITY_FLAG_WORDS and CARRIED_SCALARS. The fifth,
--   LIMBS_PER_WORD (LM:299), is read by nothing in api.rs; it is ported anyway
--   because hazard 4 is precisely the claim that api.rs's derived
--   limbs-per-instance and the layout's stated LIMBS_PER_WORD are the same
--   number.
-- * LIB: proofs/solidity-verifier/src/lib.rs (96 lines) - the two feature-gated
--   constants RenderDiagnostics::default reads (LIB:50, LIB:60).
--
-- Two further Rust files are cited IN FULL and never by prefix, because one of
-- them has the same basename as the file being ported and R-38 F3 is exactly the
-- failure mode a bare prefix would create between them:
-- proofs/solidity-verifier/src/builder/api.rs (162 lines - the crate's only
-- non-test caller of validate_for_num_instances) and
-- proofs/solidity-verifier/src/lowering/tests.rs (5156 lines - whose two
-- accumulator tests are mapped to gates below).
--
-- REFERENCE HYGIENE, AND A CORRECTION TO THE PLAN.
-- docs/plans/P-06-api.md states that HEAD is 818 lines and warns that a working
-- copy reading 875 means you are reading the uncommitted version. Measured on
-- this tree: HEAD IS 761 LINES AND THE WORKING COPY IS 818. The uncommitted
-- 57-line addition is real and is exactly what the plan describes -
-- RenderedArtifacts::named_bytes plus a #[cfg(test)] mod, working-copy 530-586 -
-- and it is NOT ported here. The plan's ranges are working-copy coordinates, so
-- they coincide with HEAD up to API:528 and sit 57 lines higher after it (with
-- one to four lines of slop at the ends of each range). That is why its row
-- "508-587 RenderedArtifacts + impl" straddles the uncommitted impl: at HEAD
-- RenderedArtifacts is API:507-528 and has NO impl block, and the crate's
-- RepackError starts at HEAD 531 where the plan says 589. Every range in this
-- file is HEAD's, re-derived line by line from
-- git show HEAD:proofs/solidity-verifier/src/api.rs, and the report's R11 table
-- corrects the plan's table against them.
--
-- WHAT THIS FILE DOES NOT PORT, AND WHY.
--
-- * Working-copy 530-586 (RenderedArtifacts::named_bytes and
--   rendered_artifacts_tests): uncommitted, so outside the baseline. Said again
--   at RenderedArtifacts, because that is where a reader looks.
-- * API:590 and API:683, impl std::error::Error for RepackError {} and for
--   GeneratorError {}. Both are empty marker impls - no methods, nothing to carry
--   - and Lean has no error trait. Listed rather than dropped silently because R1
--   counts them as items.
-- * The #[derive(...)] lines. Clone and Copy are Lean's value semantics, so there
--   is no operation to port. Debug is not ported anywhere in this row
--   (Protocol.lean derives BEq and nothing else). PartialEq/Eq become deriving
--   BEq - on every type EXCEPT QuotientProbeArtifacts, which derives only
--   Clone, Debug at API:199 and so carries no BEq here either; its gate
--   destructures it instead of comparing it.
-- * API:8-12, the use statements. std::fmt becomes String-returning defs;
--   ruint::aliases::U256 becomes Midfall.Word256, the row's model (Encoding.lean
--   says so out loud at its line 87); crate::lowering::layout becomes Layout.lean's
--   wordBytes plus the LM constants landed below.
-- * Doc comments are not translated wholesale. They are carried where the port
--   depends on the fact they state - the "seven radix-2^56 limbs, packed four
--   limbs per public-input field element" claim at API:30-32 is gated at
--   accumulatorDerivedNumbers_agreeWithDocs_ok, because it is the only place the
--   reference says out loud what coordinate_words is supposed to compute.
--
-- DECISIONS RECORDED RATHER THAN TAKEN SILENTLY (rules R4, R5, R6, R8).
--
-- * usize is Nat, u32 is Nat, i32 is Int, bool is Bool, String is String,
--   &'static str is String, Option<T> is Option T, [u8; 32] is Midfall.Bytes,
--   U256 is Midfall.Word256.
-- * Vec is List, following Layout.lean, Models.lean, Protocol.lean, Encoding.lean
--   and Abi.lean rather than PLAN Section 4's literal "Vec becomes Array" - the
--   same recorded divergence Protocol.lean's header states (R-43 F5). Every Vec
--   here is a field, never an algorithm: entries, selectorColumns,
--   simpleSelectorCols, selectorTailExponents. Nothing iterates them in this file,
--   so the two readings cannot differ here at all.
-- * Result<_, GeneratorError> is Except ApiFault, where ApiFault is this row's
--   error sum: GeneratorError plus rule R4's panic channel. It is scaffolding,
--   not a Rust item, and it is the same shape Fault has at Exec/Error.lean:56-58
--   specialised to this file's error type. The reason is hazard 1: api.rs has
--   exactly one panic site (API:104, an integer division by zero, which panics in
--   the release profile too - R4) and it sits UNDERNEATH three Result-returning
--   functions, so a port whose error channel carries only GeneratorError must
--   either drop the panic or let Lean's 254 / 0 = 0 answer where the reference
--   aborts. ApiFault keeps both.
-- * No type in api.rs derives Ord - every derive is
--   Clone, Copy?, Debug, Eq?, PartialEq?, Default? - so, unlike Protocol.lean,
--   field and variant order here is documentation rather than behaviour: nothing
--   sorts these values and no BTreeSet reads one. Order is still kept (R1), and
--   variant order is what the matches! at API:121 and the two Display matches
--   read.
-- * R8 (features) appears three times and each is resolved explicitly rather than
--   at compile time: #[cfg(feature = "evm")] on QuotientProbeArtifacts (API:197),
--   and cfg!(feature = "solidity-trace") / cfg!(feature =
--   "solidity-gas-checkpoints") behind LIB:50 and LIB:60. evm is ON in the
--   recorded profile (BASELINE.md: evm, truncated-challenges,
--   in-circuit-fewer-point-sets), so the probe type exists and is ported. The two
--   diagnostics features are OFF in it, so the two constants are false; they are
--   NOT among the four flags Midfall.Halo2.Features carries
--   (Exec/Features.lean:11-20) and this package does not own that file - finding
--   F-4.
-- * Lean reserved words: none of api.rs's identifiers collide with one, so this
--   file has no foo_ deviation. The plans README asks for every such deviation to
--   be recorded; this bullet is the record that there are none.
-- * One R2 name collision, recorded at the site.
--   FULLY_COLLAPSED_PUBLIC_INPUT_WORDS (API:77) and
--   fully_collapsed_public_input_words (API:136) both lowerCamelCase to
--   fullyCollapsedPublicInputWords. The FUNCTION keeps the exact name - it is the
--   one the reference's own test calls
--   (proofs/solidity-verifier/src/lowering/tests.rs:2084-2093) and the one a
--   later package must reach - and the constant takes a Const suffix, the
--   resolution Layout.lean:84-92 applied to G1_WORDS.
--   POINT_PAIR_PUBLIC_INPUT_WORDS (API:80) does NOT collide with anything
--   (point_pair_words is a different name), but it takes the same Const suffix
--   for symmetry with its sibling; said again at the site so the suffix is not
--   read as a second collision.
--
-- WHAT MOVED, AND WHY (the only four deviations from source order; Lean is
-- order-sensitive and the reference is not).
--
-- 1. AccumulatorEncodingKind (API:48-57) is declared before AccumulatorEncoding
--    (API:35-45), which has a field of that type.
-- 2. RepackError, GeneratorError and their impls (API:531-690) are declared
--    before the impl AccumulatorEncoding block (API:71-189), because three of its
--    methods return Result<_, GeneratorError> (API:136, API:143, API:175).
--    Moving the error types rather than the impl block keeps each Rust impl block
--    contiguous and keeps the struct next to its methods.
-- 3. Inside the manifest / certificate cluster (API:215-367) the seven types are
--    declared in dependency order: Execution (286), Source (317), ManifestTarget
--    (356), ManifestEntry (306), Manifest (215), CertificateEntry (266),
--    Certificate (238).
-- 4. The LM constants (LM:74, LM:294-304) are landed here rather than in
--    Layout.lean, which is their row - finding F-2.

import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Generator.Layout
import Midfall.Halo2.Exec.Arith

namespace Midfall.Generator
open Midfall Midfall.Halo2

/-! ## The layout:: constants api.rs reads (LM:74, LM:288-304)

Not Rust items of api.rs - they are pub(crate) constants of the layout module,
ported here because api.rs is the file that consumes them and the Layout row does
not carry them (finding F-2). Midfall.g1CompressedWidth (Common/Codec.lean:89)
states the compressed-G1 width from the codec side, and
layoutConstants_agreeWithTheirRows_ok is what stops the two copies drifting -
the R-20 pattern one level down. -/

/-- rust: LM:74 (G1_COMPRESSED_BYTES: usize = 48) @formal-baseline. Read at
    API:579, in the InvalidCompressedG1 display range. -/
def g1CompressedBytes : Nat := 48

/-- rust: LM:296 (accumulator::LIMB_BITS: usize = 56) @formal-baseline. Read at
    API:75. -/
def accumulatorLimbBits : Nat := 56

/-- rust: LM:297 (accumulator::LIMBS: usize = 7) @formal-baseline. Read at
    API:73. -/
def accumulatorLimbs : Nat := 7

/-- rust: LM:299 (accumulator::LIMBS_PER_WORD: usize = 4) @formal-baseline.
    "Four 56-bit limbs fit in one scalar word with unused high bits." Nothing in
    api.rs reads this constant - coordinate_words DERIVES the same number from
    254 / num_limb_bits - and that is exactly what hazard 4 asks to be checked, so
    accumulatorDerivedNumbers_agreeWithDocs_ok pins the derived value against this
    stated one. -/
def accumulatorLimbsPerWord : Nat := 4

/-- rust: LM:302 (accumulator::IDENTITY_FLAG_WORDS: usize = 1) @formal-baseline.
    Read at API:111. -/
def accumulatorIdentityFlagWords : Nat := 1

/-- rust: LM:304 (accumulator::CARRIED_SCALARS: usize = 2) @formal-baseline.
    Read at API:128. -/
def accumulatorCarriedScalars : Nat := 2

/-! ## usize arithmetic the reference's own sentinel makes reachable (R4, R5)

The reference profile is release (BASELINE.md), so + and - on usize WRAP and
debug_assert! is compiled out, while division by zero still panics. Layout.lean's
header argues that a usize in this row never approaches 2^64 and models it as a
plain Nat. That argument holds everywhere in api.rs EXCEPT where the reference
puts usize::MAX into the arithmetic itself: API:137 passes it as a bound, API:160
compares against it, and API:177 then subtracts with plain -. At those three lines
the boundary is reachable by construction, so the three operators that matter are
ported rather than approximated. -/

/-- rust: usize::MAX on the 64-bit reference target - the value API:137 passes to
    validate_for_num_instances as "no length bound", and the saturation point of
    saturating_add at API:160. -/
def usizeMax : Nat := 2^64 - 1

/-- rust: usize::saturating_add (API:160). Deliberate in the reference: with a
    plain + the sum would wrap in release and the > test would then pass for a
    tail that does not fit. Hazard 3. -/
def usizeSaturatingAdd (a b : Nat) : Nat :=
  if a + b > usizeMax then usizeMax else a + b

/-- rust: the plain + of API:177 (self.offset + self.fixed_payload_words()), which
    WRAPS in the release profile. Ported as wrapping because API:137's usize::MAX
    sentinel lets a caller reach it past the boundary; for every offset a real
    config can produce, (a + b) % 2^64 == a + b. -/
def usizeAdd (a b : Nat) : Nat := (a + b) % 2^64

/-- rust: the plain - of API:177 (num_instances - (...)), wrapping for the same
    reason. b % 2^64 comes first so the Lean subtraction cannot truncate: a Rust
    usize is already below 2^64 and a Lean Nat is not. -/
def usizeSub (a b : Nat) : Nat := (a + (2^64 - b % 2^64)) % 2^64

/-! ## AccumulatorEncodingKind (rust: API:48-57) -/

/-- rust: API:48-57 (enum AccumulatorEncodingKind) @formal-baseline. Variant
    order is the source order (R1). MOVED above AccumulatorEncoding, which has a
    field of this type - deviation 1 in the header. -/
inductive AccumulatorEncodingKind
  /-- rust: API:50-52 (PointAndScalar) - lhs point, lhs scalar, rhs point, rhs
      scalar, then an optional fixed-base scalar tail. -/
  | pointAndScalar
  /-- rust: API:53-56 (PointPair) - already collapsed lhs point, rhs point, both
      carried scalars implicitly one, and NO tail accepted. That last clause is
      fixed_scalar_count's error arm at API:178-186, gated at
      fixedScalarCount_bothArms_ok. -/
  | pointPair
  deriving BEq

/-! ## CommittedInstanceCommitmentKind (rust: API:65-69) -/

/-- rust: API:65-69 (enum CommittedInstanceCommitmentKind) @formal-baseline. One
    variant: the generated verifier mirrors the Midfall / zk-stdlib path where the
    committed-instance commitment absorbed into the transcript is the G1 identity,
    and it is not a generic caller-supplied-commitment verifier. The crate pins it
    at proofs/solidity-verifier/src/builder/api.rs:19-20
    (SUPPORTED_COMMITTED_INSTANCE_COMMITMENT), which is a later package's item. -/
inductive CommittedInstanceCommitmentKind
  /-- rust: API:67-68 (Identity) - absorb and use G1::identity() for every
      committed instance column. -/
  | identity
  deriving BEq

/-! ## RepackError (rust: API:531-590) - MOVED above the AccumulatorEncoding impl -/

/-- rust: API:531-560 (enum RepackError) @formal-baseline. Variant and field
    order preserved. MOVED up from API:531 - deviation 2 in the header. -/
inductive RepackError
  /-- rust: API:534-545 (LengthMismatch) - the native compressed proof does not
      match the generated proof schema. -/
  | lengthMismatch (expected actual prefixG1 numEvals numPointSets : Nat)
  /-- rust: API:547-552 (InvalidCompressedG1) - one compressed G1 commitment
      failed host-side decompression. bytes_hex is Rust String, already hexed by
      the caller: the Display impl only splices it after a literal 0x. -/
  | invalidCompressedG1 (offset : Nat) (bytesHex : String)
  /-- rust: API:554-559 (NonCanonicalScalar) - one proof scalar is not a canonical
      Fr element (>= r). -/
  | nonCanonicalScalar (offset : Nat) (bytesHex : String)
  deriving BEq

/-- rust: API:562-588 (impl fmt::Display for RepackError) @formal-baseline. Named
    printRepackError on the precedent Filters.lean:87 sets for a Display impl
    (printValue, printPtr, printWord): R2 has no rule for a trait impl, and
    inventing a fmt method name would be worse.

    The three strings are verbatim, including the ", +f_com+pi" clause and the 0x
    that is OUTSIDE the interpolation on the two hex arms - so a caller that
    already hexed bytes_hex with a 0x gets 0x0x..., which is what the reference
    does. The two ranges print offset + G1_COMPRESSED_BYTES and
    offset + WORD_BYTES with a plain +: offset is a byte index into a proof and
    cannot approach 2^64, so R5's "emulate wrapping only where it can occur" says
    leave it. -/
def printRepackError (self : RepackError) : String :=
  match self with
  | .lengthMismatch expected actual prefixG1 numEvals numPointSets =>
    "compressed proof length mismatch: expected " ++ toString expected
      ++ " bytes (prefix_g1=" ++ toString prefixG1
      ++ ", num_evals=" ++ toString numEvals
      ++ ", num_point_sets=" ++ toString numPointSets
      ++ ", +f_com+pi), got " ++ toString actual
  | .invalidCompressedG1 offset bytesHex =>
    "invalid compressed G1 at compressed[" ++ toString offset ++ ".."
      ++ toString (offset + g1CompressedBytes) ++ "]: bytes = 0x" ++ bytesHex
  | .nonCanonicalScalar offset bytesHex =>
    "non-canonical Fr scalar at compressed[" ++ toString offset ++ ".."
      ++ toString (offset + wordBytes) ++ "]: bytes = 0x" ++ bytesHex

-- rust: API:590 (impl std::error::Error for RepackError {}). An empty marker
-- impl: nothing to port, recorded at the site as well as in the header.

/-! ## GeneratorError (rust: API:595-690) - MOVED with RepackError -/

/-- rust: API:595-636 (enum GeneratorError) @formal-baseline. Variant and field
    order preserved. UnsupportedInstanceColumnShape's four fields carry no doc
    comment in the reference (API:604-607) and none here.

    RotatedInstanceQuery's rotation is Rust i32 (rotation.0, fed from a Rotation
    at proofs/solidity-verifier/src/builder/api.rs:58-61), so it is Int and NOT
    Nat: a rotation of -1 must print as -1. -/
inductive GeneratorError
  /-- rust: API:597-599 (NoAdviceColumns) - a verifier with no advice commitments
      has no proof commitment phase to bind into the transcript. -/
  | noAdviceColumns
  /-- rust: API:601-608 (UnsupportedInstanceColumnShape) - the generated
      transcript and instance-evaluation path supports exactly one committed and
      one non-committed instance column. -/
  | unsupportedInstanceColumnShape
      (total committed expectedCommitted expectedNonCommitted : Nat)
  /-- rust: API:610-611 (RotatedInstanceQuery) - instance columns are read as
      direct public inputs and Lagrange-interpolated only at the current row. -/
  | rotatedInstanceQuery (column : Nat) (rotation : Int)
  /-- rust: API:613-621 (UnsupportedAccumulatorEncoding) - the optional public
      accumulator pairing batch supports only the Midnight BLS12-381 public-input
      encoding used by the IVC decider fixtures. reason is Rust &'static str, so
      it is one of exactly three literals in this file; nothing in the reference
      compares it (hazard 6) and the three construction sites are its only
      sources. -/
  | unsupportedAccumulatorEncoding
      (offset numLimbs numLimbBits numInstances : Nat) (reason : String)
  /-- rust: API:623-628 (Planning) - internal render/layout planning failed before
      Solidity was emitted. -/
  | planning (stage message : String)
  /-- rust: API:630-633 (Render) - formatting the Askama model into a Solidity
      string failed. -/
  | render (artifact : String)
  /-- rust: API:635 (Repack(RepackError)) - a tuple variant; the field is named
      err after the From impl's binding at API:687, because Lean needs a name. -/
  | repack (err : RepackError)
  deriving BEq

/-- rust: API:638-681 (impl fmt::Display for GeneratorError) @formal-baseline.
    Seven arms in source order, strings verbatim.

    The non_committed sub-expression at API:651-654 is
    total.checked_sub(*committed).map_or_else(|| format!("invalid: committed
    {committed} exceeds total {total}"), |n| n.to_string()): checked_sub is
    Option, so the None arm is committed > total and the Some arm is the
    difference. Both arms are gated - the Some arm is the one a port written as a
    plain Nat subtraction keeps and the None arm is the one it loses. -/
def printGeneratorError (self : GeneratorError) : String :=
  match self with
  | .noAdviceColumns => "at least one advice column is required"
  | .unsupportedInstanceColumnShape total committed expectedCommitted
      expectedNonCommitted =>
    let nonCommitted :=
      if committed <= total then toString (total - committed)
      else "invalid: committed " ++ toString committed ++ " exceeds total "
        ++ toString total
    "unsupported instance column shape: got total=" ++ toString total
      ++ ", committed=" ++ toString committed
      ++ ", non_committed=" ++ nonCommitted
      ++ "; expected exactly " ++ toString expectedCommitted
      ++ " identity-committed and " ++ toString expectedNonCommitted
      ++ " non-committed"
  | .rotatedInstanceQuery column rotation =>
    "rotated instance query is not supported: column " ++ toString column
      ++ ", rotation " ++ toString rotation
  | .unsupportedAccumulatorEncoding offset numLimbs numLimbBits numInstances
      reason =>
    "unsupported accumulator encoding: offset=" ++ toString offset
      ++ ", num_limbs=" ++ toString numLimbs
      ++ ", num_limb_bits=" ++ toString numLimbBits
      ++ ", num_instances=" ++ toString numInstances
      ++ "; " ++ reason
  | .planning stage message =>
    "generator planning failed during " ++ stage ++ ": " ++ message
  | .render artifact => "failed to render " ++ artifact
  | .repack err => printRepackError err

-- rust: API:683 (impl std::error::Error for GeneratorError {}) - empty marker
-- impl, nothing to port.

/-- rust: API:685-690 (impl From<RepackError> for GeneratorError)
    @formal-baseline. From::from has no snake_case name to convert; the row
    renders From<A> for B as bFromA (Models.lean:525 valueFromNat is
    From<usize> for Value), so inside the GeneratorError namespace this is
    fromRepackError. Except chains in the later packages want exactly this
    coercion - hazard 6. -/
def GeneratorError.fromRepackError (err : RepackError) : GeneratorError :=
  GeneratorError.repack err

/-- The port's error sum for api.rs: rule R3's Result<_, GeneratorError> plus rule
    R4's panic channel. NOT a Rust item - see the header's decision bullet. Same
    shape as Fault (Exec/Error.lean:56-58), specialised to this row's error type,
    because Fault.error is fixed to Midfall.Halo2.Error and this package does not
    own it. -/
inductive ApiFault where
  | error (e : GeneratorError)
  | panic (site : String)
  deriving BEq

/-! ## AccumulatorEncoding (rust: API:35-45) and its impl (API:71-189) -/

/-- rust: API:35-45 (struct AccumulatorEncoding) @formal-baseline. Field order is
    the Rust's (R1); nothing sorts this type, so - unlike Protocol.lean's QueryKey
    - the order is documentation rather than behaviour.

    The doc comment at API:21-34 is load-bearing and is what hazard 4 checks: the
    accumulator is a TAIL of the non-committed public-input vector starting at
    offset, laid out as lhs point, lhs scalar, rhs point, rhs scalar, with each
    coordinate as seven radix-2^56 limbs packed four per public-input word and
    each point followed by one identity-flag word, and any words after the fixed
    payload read as the optional RHS fixed-base scalar tail. -/
structure AccumulatorEncoding where
  /-- rust: API:37-38 (offset: usize) - offset of the accumulator limbs in
      instances. -/
  offset : Nat
  /-- rust: API:39-40 (num_limbs: usize) - limbs per base-field element. -/
  numLimbs : Nat
  /-- rust: API:41-42 (num_limb_bits: usize) - bits per limb. -/
  numLimbBits : Nat
  /-- rust: API:43-44 (kind: AccumulatorEncodingKind) - public-input layout. -/
  kind : AccumulatorEncodingKind
  deriving BEq

/-- rust: API:73 (SUPPORTED_NUM_LIMBS = layout::accumulator::LIMBS)
    @formal-baseline. -/
def AccumulatorEncoding.supportedNumLimbs : Nat := accumulatorLimbs

/-- rust: API:75 (SUPPORTED_NUM_LIMB_BITS = layout::accumulator::LIMB_BITS)
    @formal-baseline. -/
def AccumulatorEncoding.supportedNumLimbBits : Nat := accumulatorLimbBits

/-- rust: API:77 (FULLY_COLLAPSED_PUBLIC_INPUT_WORDS: usize = 12)
    @formal-baseline. R2 collision: the function at API:136 lowerCamelCases to the
    same name, so the constant takes a Const suffix and the function keeps the
    exact one (Layout.lean:84-92 precedent).

    This is a LITERAL, not a derived number: fully_collapsed_public_input_words
    returns fixed_payload_words(), which is computed from the layout constants,
    and nothing in api.rs asserts the two agree. The reference's own test
    (proofs/solidity-verifier/src/lowering/tests.rs:2063-2067) checks the constant
    against a real circuit encoding instead. That is hazard 4, and
    accumulatorDerivedNumbers_agreeWithDocs_ok is where it is checked here. -/
def AccumulatorEncoding.fullyCollapsedPublicInputWordsConst : Nat := 12

/-- rust: API:78-80 (POINT_PAIR_PUBLIC_INPUT_WORDS: usize = 10)
    @formal-baseline. Same literal-versus-derived status as
    fullyCollapsedPublicInputWordsConst. The Const suffix here is SYMMETRY, not a
    collision: point_pair_words (API:115) is a different name, so nothing forced
    this one. -/
def AccumulatorEncoding.pointPairPublicInputWordsConst : Nat := 10

/-- rust: API:83-90 (AccumulatorEncoding::new) @formal-baseline. -/
def AccumulatorEncoding.new (offset numLimbs numLimbBits : Nat) :
    AccumulatorEncoding :=
  { offset := offset, numLimbs := numLimbs, numLimbBits := numLimbBits,
    kind := AccumulatorEncodingKind.pointAndScalar }

/-- rust: API:93-100 (AccumulatorEncoding::point_pair) @formal-baseline. The only
    difference from new is the kind - both take the limb shape from the caller and
    validate it later. -/
def AccumulatorEncoding.pointPair (offset numLimbs numLimbBits : Nat) :
    AccumulatorEncoding :=
  { offset := offset, numLimbs := numLimbs, numLimbBits := numLimbBits,
    kind := AccumulatorEncodingKind.pointPair }

/-- rust: API:103-106 (AccumulatorEncoding::coordinate_words, PRIVATE, hence
    ported per R1) @formal-baseline.

    HAZARD 1, part 1 - the panic. API:104 is 254 / self.num_limb_bits, an integer
    division by ZERO when num_limb_bits == 0. Division by zero panics in the
    release profile too (R4), so this is a panic site and not an unreachable one,
    and it is ported as ApiFault.panic rather than being allowed to answer Lean's
    254 / 0 = 0.

    HAZARD 1, part 2 - the call graph, enumerated over the whole crate
    (grep -rn 'point_words|coordinate_words' proofs/solidity-verifier/src):

    * coordinate_words has exactly ONE caller: point_words (API:111).
    * point_words is pub(crate) and has two: point_pair_words (API:116) and
      proofs/solidity-verifier/src/lowering/tests.rs:2040, a test that builds
      AccumulatorEncoding::new(0, 7, 56) - supported limb shape by hand, so no
      panic.
    * point_pair_words is private with exactly one caller: fixed_payload_words
      (API:126).
    * fixed_payload_words is private with three:
      fully_collapsed_public_input_words (API:138, reached only after
      validate_for_num_instances(usize::MAX) at API:137 has rejected any
      num_limb_bits != 56), validate_for_num_instances itself (API:159, which is
      AFTER its own shape check at API:147-157 - the || short-circuits, so the
      only way to reach 159 is with the supported shape), and fixed_scalar_count
      (API:177, after the validate at 176).
    * The crate's only non-test entry into the type is
      proofs/solidity-verifier/src/builder/api.rs:49-51, which calls
      validate_for_num_instances(config.num_instances).

    So every path in the crate that reaches the division has already rejected
    num_limb_bits != 56, EXCEPT point_words' own pub(crate) visibility, which the
    reference cannot see future callers of. The panic is therefore ported rather
    than argued away, and coordinateWords_divZero_panics_ok exercises it through
    pointWords, pointPairWords and fixedPayloadWords so the guard cannot be
    hoisted or dropped without a gate going red.

    The literal 254 is the bit width of the field the public inputs live in, not
    the 381 of the emulated BLS12-381 coordinate the doc comment at API:30 names,
    and the reference gives it no name. At the supported constants the two
    readings agree (254 / 56 = 4 and 381 / 56 = 6 both give div_ceil 7 _ = 2),
    which is why the choice is invisible - finding F-6. -/
def AccumulatorEncoding.coordinateWords (self : AccumulatorEncoding) :
    Except ApiFault Nat := do
  if self.numLimbBits == 0 then
    throw (ApiFault.panic "proofs/solidity-verifier/src/api.rs:104")
  else
    -- API:104 (254 / self.num_limb_bits).max(1). The .max(1) is not cosmetic: it
    -- is what stops num_limb_bits > 254 from making the divisor zero, and a zero
    -- divisor would be a second panic the reference never reaches.
    -- coordinateWords_divZero_panics_ok pins both.
    let limbsPerInstance := Nat.max (254 / self.numLimbBits) 1
    -- API:105 self.num_limbs.div_ceil(limbs_per_instance). divCeil is
    -- Exec/Arith.lean:53; its divCeil a 0 = 0 is unreachable here because of the
    -- .max 1 above.
    pure (divCeil self.numLimbs limbsPerInstance)

/-- rust: API:108-112 (AccumulatorEncoding::point_words, pub(crate))
    @formal-baseline: x words, y words, then the identity flag. pub(crate) is why
    the panic below is reachable at all - hazard 1 at coordinateWords. -/
def AccumulatorEncoding.pointWords (self : AccumulatorEncoding) :
    Except ApiFault Nat := do
  let cw ← self.coordinateWords
  pure (2 * cw + accumulatorIdentityFlagWords)

/-- rust: API:114-117 (AccumulatorEncoding::point_pair_words, private)
    @formal-baseline: the lhs and rhs G1 points. -/
def AccumulatorEncoding.pointPairWords (self : AccumulatorEncoding) :
    Except ApiFault Nat := do
  let pw ← self.pointWords
  pure (2 * pw)

/-- rust: API:119-122 (AccumulatorEncoding::has_carried_scalars, pub(crate))
    @formal-baseline. The reference writes matches!(self.kind,
    AccumulatorEncodingKind::PointAndScalar); on a two-variant enum with derived
    BEq that is exactly equality with the one variant, and
    hasCarriedScalars_andConstructors_ok asserts BOTH kinds so the arm cannot be
    flipped or widened. -/
def AccumulatorEncoding.hasCarriedScalars (self : AccumulatorEncoding) : Bool :=
  self.kind == AccumulatorEncodingKind.pointAndScalar

/-- rust: API:124-132 (AccumulatorEncoding::fixed_payload_words, private)
    @formal-baseline: both points, plus the carried scalars when the layout has
    them. -/
def AccumulatorEncoding.fixedPayloadWords (self : AccumulatorEncoding) :
    Except ApiFault Nat := do
  let ppw ← self.pointPairWords
  pure (ppw + if self.hasCarriedScalars then accumulatorCarriedScalars else 0)

/-! The three defs below are a Lean mutual block, not a reordering: Rust
source order puts fully_collapsed_public_input_words (API:136) before
validate_for_num_instances (API:143), and the first calls the second. Lean is
order-sensitive for definitions as well as types, so Protocol.lean's precedent -
"the seven members of the impl block sit in one mutual block" - is what keeps API
source order here rather than moving validate above. -/
mutual
/-- rust: API:134-139 (AccumulatorEncoding::fully_collapsed_public_input_words)
    @formal-baseline.

    HAZARD 2. The usize::MAX at API:137 is not a placeholder and must not be
    simplified into a separate unvalidated path: it is passed SPECIFICALLY so the
    tail bound at API:160 cannot fire, because saturating_add can never exceed
    usize::MAX. Ported as the sentinel plus the real call, and gated at
    fullyCollapsedPublicInputWords_sentinel_ok, which shows an encoding with a
    huge offset returning Ok here and Err at a realistic num_instances. -/
def AccumulatorEncoding.fullyCollapsedPublicInputWords
    (self : AccumulatorEncoding) : Except ApiFault Nat := do
  let _ ← self.validateForNumInstances usizeMax
  self.fixedPayloadWords

/-- rust: API:141-171 (AccumulatorEncoding::validate_for_num_instances,
    pub(crate)) @formal-baseline. Two checks, in this order, and the order is
    observable: a config that fails BOTH reports the limb-shape reason, because
    the first if returns. validate_ordering_shapeBeforeTail_ok pins that.

    The bound at API:160 is offset.saturating_add(required_words) > num_instances
    - saturating (hazard 3), strict > (so a tail that ends exactly at
    num_instances is fine), and reached only with the supported limb shape, which
    is what makes coordinateWords safe on this path. -/
def AccumulatorEncoding.validateForNumInstances (self : AccumulatorEncoding)
    (numInstances : Nat) : Except ApiFault Unit := do
  if self.numLimbs ≠ AccumulatorEncoding.supportedNumLimbs
      || self.numLimbBits ≠ AccumulatorEncoding.supportedNumLimbBits then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "expected 7 radix-2^56 limbs per BLS12-381 base-field coordinate")))
  -- API:159. Safe with respect to the panic at API:104: the check above has
  -- already rejected every num_limb_bits other than 56.
  let requiredWords ← self.fixedPayloadWords
  if usizeSaturatingAdd self.offset requiredWords > numInstances then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "accumulator public-input tail exceeds num_instances")))
  pure ()

/-- rust: API:173-188 (AccumulatorEncoding::fixed_scalar_count, pub(crate))
    @formal-baseline.

    HAZARD 5: both arms are reachable and both are exercised at
    fixedScalarCount_bothArms_ok, on the reference's own numbers
    (proofs/solidity-verifier/src/lowering/tests.rs:2088-2101). PointAndScalar
    accepts a tail of any length and returns its size; PointPair rejects a
    non-zero tail.

    HAZARD 3's second half: API:177 is num_instances - (offset +
    fixed_payload_words()) with PLAIN + and -, not the saturating_add of API:160.
    In the release profile both wrap, and the usize::MAX sentinel of API:137 is
    what makes the difference reachable: validate passes when
    saturating_add offset required == usizeMax == num_instances, and the plain
    arithmetic then wraps. fixedScalarCount_wrappingTail_ok pins that case - a
    port using Nat + and truncated Nat - gets 0 where the reference gets
    2^64 - 12. Finding F-3 records that the reference's own two operators
    disagree with each other about the same three numbers. -/
def AccumulatorEncoding.fixedScalarCount (self : AccumulatorEncoding)
    (numInstances : Nat) : Except ApiFault Nat := do
  let _ ← self.validateForNumInstances numInstances
  let required ← self.fixedPayloadWords
  let tail := usizeSub numInstances (usizeAdd self.offset required)
  if self.kind == AccumulatorEncodingKind.pointPair && tail ≠ 0 then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "point-pair accumulator encoding does not support a fixed-base scalar tail")))
  pure tail
end

/-! ## QuotientProbeArtifacts (rust: API:191-208) - TEST-ONLY -/

/-- TEST-ONLY. rust: API:191-208 (struct QuotientProbeArtifacts)
    @formal-baseline.

    HAZARD 7, decided explicitly: PORTED, marked test-only. The reference marks it
    three ways - #[cfg(feature = "evm")] (API:197), #[doc(hidden)] (API:198) and
    "not a verifier" (API:193) - and it is a crate-root export
    (proofs/solidity-verifier/src/lib.rs:21) built only by
    proofs/solidity-verifier/src/builder/render.rs:185-210. R8 resolves the
    feature: evm is ON in the recorded profile (BASELINE.md), so the type is part
    of the baseline build and dropping it would make the port's surface smaller
    than the reference's. Nothing in this file or in any ported module constructs
    it yet, so its gate only pins that the three fields hold what they are given.

    No BEq: the Rust derives only Clone, Debug here (API:199), unlike every other
    type in this file. -/
structure QuotientProbeArtifacts where
  /-- rust: API:201-202 (verifier: String) - probe contract source. -/
  verifier : String
  /-- rust: API:203-204 (verifying_key: String) - separate VK contract the probe
      is deployed against. -/
  verifyingKey : String
  /-- rust: API:205-207 (selector_columns: Vec<usize>) - simple-selector fixed
      columns in output order: word 1 + s is the accumulator of
      selector_columns[s]. -/
  selectorColumns : List Nat

/-! ## The manifest and certificate cluster (rust: API:215-367) - MOVED -/

/-- rust: API:286-303 (enum QuotientIdentityExecution) @formal-baseline. Declared
    first because QuotientCertificateEntry has a field of this type and Lean is
    order-sensitive - deviation 3 in the header. Variant order preserved. -/
inductive QuotientIdentityExecution
  /-- rust: API:288-289 (Inline) - direct Yul emitted before the compact VM loop. -/
  | inline
  /-- rust: API:290-291 (Interpreted) - compact VM bytecode expression followed by
      a fold opcode. -/
  | interpreted
  /-- rust: API:292-293 (NativePermutation) - native callback replacing the full
      permutation identity range. -/
  | nativePermutation
  /-- rust: API:294-295 (NativeLookup) - native callback replacing the full lookup
      identity range. -/
  | nativeLookup
  /-- rust: API:296-300 (NativeIdentity { native_index }) - native callback
      replacing one selected heavy gate identity. -/
  | nativeIdentity (nativeIndex : Nat)
  /-- rust: API:301-302 (StructuredTail) - structured Yul emitted after the VM
      loop. -/
  | structuredTail
  deriving BEq

/-- rust: API:317-353 (enum QuotientIdentitySource) @formal-baseline. Declared
    here for the same order reason; variant and field order preserved. Every
    payload field is gated at quotientIdentitySource_payloads_ok, because a source
    whose payload is dropped still prints and still compares equal to the wrong
    thing. -/
inductive QuotientIdentitySource
  /-- rust: API:320-331 (Gate) - a normal custom-gate polynomial from
      vk.cs().gates(). -/
  | gate (gateIndex : Nat) (gateName : String) (constraintIndex : Nat)
      (constraintName : String) (polynomialIndex : Nat)
  /-- rust: API:333-336 (Permutation) - a permutation argument identity. -/
  | permutation (identityIndex : Nat)
  /-- rust: API:338-345 (Lookup) - a LogUp lookup argument identity. -/
  | lookup (identityIndex : Nat) (lookupIndex : Nat) (lookupName : String)
  /-- rust: API:347-352 (Trash) - a trash argument identity. -/
  | trash (trashIndex : Nat) (trashName : String)
  deriving BEq

/-- rust: API:356-367 (enum QuotientIdentityManifestTarget) @formal-baseline. -/
inductive QuotientIdentityManifestTarget
  /-- rust: API:358-359 (Main) - fully evaluated identity accumulated into the
      quotient numerator scalar. -/
  | main
  /-- rust: API:360-366 (Selector { selector_index, fixed_column }) -
      simple-selector identity accumulated into a selector commitment bucket. -/
  | selector (selectorIndex : Nat) (fixedColumn : Nat)
  deriving BEq

/-- rust: API:306-314 (struct QuotientIdentityManifestEntry) @formal-baseline. -/
structure QuotientIdentityManifestEntry where
  /-- rust: API:308-309 (global_index: usize) - position in the global y-batch. -/
  globalIndex : Nat
  /-- rust: API:310-311 (source: QuotientIdentitySource) -/
  source : QuotientIdentitySource
  /-- rust: API:312-313 (target: QuotientIdentityManifestTarget) -/
  target : QuotientIdentityManifestTarget
  deriving BEq

/-- rust: API:211-229 (struct QuotientIdentityManifest) @formal-baseline. "Not
    part of the Solidity verifier ABI": a host-side inspection API for confirming
    which custom gates and argument identities a generated verifier evaluates. -/
structure QuotientIdentityManifest where
  /-- rust: API:217-218 (entries: Vec<QuotientIdentityManifestEntry>) - identities
      in the exact global y-batch order the verifier uses. -/
  entries : List QuotientIdentityManifestEntry
  /-- rust: API:219-220 (gate_identities: usize) -/
  gateIdentities : Nat
  /-- rust: API:221-222 (permutation_identities: usize) -/
  permutationIdentities : Nat
  /-- rust: API:223-224 (lookup_identities: usize) -/
  lookupIdentities : Nat
  /-- rust: API:225-226 (trash_identities: usize) -/
  trashIdentities : Nat
  /-- rust: API:227-228 (simple_selector_cols: Vec<usize>) - fixed-column indices
      for simple selector buckets, SORTED BY COLUMN. The producer sorts it;
      nothing here re-sorts it, so the port must not either. -/
  simpleSelectorCols : List Nat
  deriving BEq

/-- rust: API:264-282 (struct QuotientCertificateEntry) @formal-baseline. One
    quotient identity as certified after representation choices are applied. -/
structure QuotientCertificateEntry where
  /-- rust: API:268-269 (global_index: usize) -/
  globalIndex : Nat
  /-- rust: API:270-271 (source: QuotientIdentitySource) -/
  source : QuotientIdentitySource
  /-- rust: API:272-273 (target: QuotientIdentityManifestTarget) -/
  target : QuotientIdentityManifestTarget
  /-- rust: API:274-275 (selector_gap: Option<usize>) - gap used by
      selector-bucket forward folding for selector identities. -/
  selectorGap : Option Nat
  /-- rust: API:276-277 (execution: QuotientIdentityExecution) -/
  execution : QuotientIdentityExecution
  /-- rust: API:278-279 (expression_hash: U256) - Keccak256 over the canonical
      expression encoding. -/
  expressionHash : Word256
  /-- rust: API:280-281 (expression_encoding_len: usize) - byte length of that
      encoding. -/
  expressionEncodingLen : Nat
  deriving BEq

/-- rust: API:231-262 (struct QuotientCertificate) @formal-baseline. "A host-side
    diagnostic and release artifact; it is not embedded in, or checked by, any
    generated contract", and the hash "intentionally ignores display-only names" -
    which is why entries carries a QuotientIdentitySource with its names while the
    hashes come from the canonical encoding rather than from this record. -/
structure QuotientCertificate where
  /-- rust: API:240-241 (version: u32) - canonical certificate format version.
      u32 is Nat here (R5): nothing in this file adds to or shifts a version, so
      the two readings cannot differ. -/
  version : Nat
  /-- rust: API:242-243 (entries: Vec<QuotientCertificateEntry>) -/
  entries : List QuotientCertificateEntry
  /-- rust: API:244-245 (gate_identities: usize) -/
  gateIdentities : Nat
  /-- rust: API:246-247 (permutation_identities: usize) -/
  permutationIdentities : Nat
  /-- rust: API:248-249 (lookup_identities: usize) -/
  lookupIdentities : Nat
  /-- rust: API:250-251 (trash_identities: usize) -/
  trashIdentities : Nat
  /-- rust: API:252-253 (simple_selector_cols: Vec<usize>) -/
  simpleSelectorCols : List Nat
  /-- rust: API:254-255 (selector_tail_exponents: Vec<usize>) - final
      selector-bucket tail exponents. -/
  selectorTailExponents : List Nat
  /-- rust: API:256-257 (vm_bytecode_hash: U256) - Keccak256 over the quotient VM
      bytecode bytes. -/
  vmBytecodeHash : Word256
  /-- rust: API:258-259 (quotient_constants_hash: U256) - Keccak256 over the
      canonical quotient constant table encoding. -/
  quotientConstantsHash : Word256
  /-- rust: API:260-261 (certificate_hash: U256) - Keccak256 over the full
      canonical certificate encoding. -/
  certificateHash : Word256
  deriving BEq

/-! ## GeneratorConfig (rust: API:369-399) -/

/-- rust: API:369-382 (struct GeneratorConfig) @formal-baseline. "Immutable
    generator configuration": the constructor validates the whole shape up front
    (proofs/solidity-verifier/src/builder/api.rs:38-51) and post-construction
    mutation is intentionally unsupported, so render and repack always see the
    same public-instance and accumulator schema. This is the g.cfg of PLAN 9.5. -/
structure GeneratorConfig where
  /-- rust: API:376-377 (num_instances: usize) - non-committed public-input values
      verifyProof expects. -/
  numInstances : Nat
  /-- rust: API:378-379 (num_committed_instances: usize) - instance columns
      committed to in the proof transcript. -/
  numCommittedInstances : Nat
  /-- rust: API:380-381 (accumulator: Option<AccumulatorEncoding>) - the optional
      public accumulator pairing-batch encoding; PLAN 9.5's acc field quantifies
      over it. -/
  accumulator : Option AccumulatorEncoding
  deriving BEq

/-- rust: API:384-392 (GeneratorConfig::new) @formal-baseline: no accumulator
    verification. -/
def GeneratorConfig.new (numInstances numCommittedInstances : Nat) :
    GeneratorConfig :=
  { numInstances := numInstances,
    numCommittedInstances := numCommittedInstances,
    accumulator := none }

/-- rust: API:394-398 (GeneratorConfig::with_accumulator) @formal-baseline. Rust
    takes mut self and writes one field; Lean writes the same field with a
    structure update, which is the same function. It sets ONLY the accumulator -
    generatorConfig_withAccumulator_ok pins the other two fields so a builder that
    rebuilt the record from the encoding cannot pass. -/
def GeneratorConfig.withAccumulator (self : GeneratorConfig)
    (accumulator : AccumulatorEncoding) : GeneratorConfig :=
  { self with accumulator := some accumulator }

/-! ## RenderVk, RenderQuotient, QuotientLowering (rust: API:401-461) -/

/-- rust: API:401-410 (enum RenderVk) @formal-baseline. #[derive(Default)] with
    #[default] on Embedded; Lean cannot derive Default for an inductive, and the
    row resolves a Rust Default to an explicit def anyway - the R-40 F5a lesson,
    that an explicit definition fails to compile when a field or variant is added
    while a silent default does not. -/
inductive RenderVk
  /-- rust: API:405-407 (Embedded, the #[default]) - embed the generated VK payload
      directly in Halo2Verifier.sol. -/
  | embedded
  /-- rust: API:408-409 (Separate) - render Halo2Verifier.sol plus
      Halo2VerifyingKey.sol. -/
  | separate
  deriving BEq

/-- rust: API:404 (Default derive on RenderVk) and API:406 (#[default] on
    Embedded). -/
def RenderVk.default : RenderVk := RenderVk.embedded

/-- rust: API:412-425 (enum RenderQuotient) @formal-baseline. -/
inductive RenderQuotient
  /-- rust: API:416-417 (Inline, the #[default] at API:416) - render quotient
      reconstruction inside the verifier. -/
  | inline
  /-- rust: API:418-424 (ExternalPinned { runtime_len, codehash }) - link to a
      separately deployed, hard-pinned quotient evaluator. -/
  | externalPinned (runtimeLen : Nat) (codehash : Word256)
  deriving BEq

/-- rust: API:414 (Default derive) and API:416 (#[default] on Inline). -/
def RenderQuotient.default : RenderQuotient := RenderQuotient.inline

/-- rust: API:427-461 (enum QuotientLowering) @formal-baseline. How the quotient
    numerator - the y-batched identity sum - is lowered to Yul for an inline
    quotient render. Both arms consume the same identity stream and produce the
    same expected_eval and selector-bucket scalars (API:430-433).

    HAZARD 8: Vm carries the #[default] (API:440-441), which is the Phase 0 merge
    requirement - BASELINE.md's conflict-resolution section says so in words:
    "QuotientLowering::{Vm, Direct} kept, Vm the default". The reference does pick
    Vm, so hazard 8's finding condition does not fire;
    renderDefaults_areTheReferenceOnes_ok is the gate that would catch a future
    flip, and R-36/D-P13 make the golden target a VM-path render. -/
inductive QuotientLowering
  /-- rust: API:436-441 (Vm, the #[default]) - compact bytecode VM: the identity
      arithmetic is a program in the VK payload, interpreted by one Yul loop, with
      native callbacks for selected heavy gates and structured permutation /
      lookup / trash loops. -/
  | vm
  /-- rust: API:442-460 (Direct) - one Yul function per gate identity,
      transliterated node by node, with two recognised foreign-field sub-tree
      shapes lowered to shared helper calls and every identity folded explicitly
      as bucket += y^(m-1-j) * e. "Only supported with RenderQuotient::Inline"
      (API:459). -/
  | direct
  deriving BEq

/-- rust: API:435 (Default derive) and API:440 (#[default] on Vm). -/
def QuotientLowering.default : QuotientLowering := QuotientLowering.vm

/-! ## RenderDiagnostics and RenderOptions (rust: API:463-504) -/

/-- rust: LIB:50 (pub const SOLIDITY_TRACE_ENABLED: bool =
    cfg!(feature = "solidity-trace")) @formal-baseline. R8 resolves the feature at
    the recorded profile: BASELINE.md's Features.solidity is
    evm,truncated-challenges,in-circuit-fewer-point-sets, which does NOT include
    solidity-trace, so the reference's value in the baseline build is false.
    Finding F-4: these two features are not among the four flags
    Midfall.Halo2.Features carries, and this package does not own that file. -/
def solidityTraceEnabled : Bool := false

/-- rust: LIB:60 (pub const SOLIDITY_GAS_CHECKPOINTS_ENABLED: bool =
    cfg!(feature = "solidity-gas-checkpoints")) @formal-baseline; same R8
    resolution and the same finding. BASELINE.md says it in words: "the Moonlight
    Sepolia artifact was rendered without gas checkpoints". -/
def solidityGasCheckpointsEnabled : Bool := false

/-- rust: API:463-470 (struct RenderDiagnostics) @formal-baseline. Diagnostic
    render knobs. PLAN 9.5's production field reads these two booleans, which is
    why the defaults are gated rather than assumed. -/
structure RenderDiagnostics where
  /-- rust: API:466-467 (trace: bool) - emit trace logs. -/
  trace : Bool
  /-- rust: API:468-469 (gas_checkpoints: bool) - emit section gas checkpoints. -/
  gasCheckpoints : Bool
  deriving BEq

/-- rust: API:472-481 (impl Default for RenderDiagnostics) @formal-baseline.
    Hand-written in the reference rather than derived, and the doc comment says
    why: "default diagnostics are feature-gated so normal library callers get the
    same render shape as the crate was compiled for". Both fields are written out
    so a third knob fails to compile here rather than defaulting past the gate. -/
def RenderDiagnostics.default : RenderDiagnostics :=
  { trace := solidityTraceEnabled,
    gasCheckpoints := solidityGasCheckpointsEnabled }

/-- rust: API:483-504 (struct RenderOptions) @formal-baseline. Main render options
    for generated Solidity artifacts. #[derive(Default)], ported as the explicit
    def below. -/
structure RenderOptions where
  /-- rust: API:486-487 (vk: RenderVk) - VK artifact mode. -/
  vk : RenderVk
  /-- rust: API:488-489 (quotient: RenderQuotient) - quotient numerator artifact
      mode. -/
  quotient : RenderQuotient
  /-- rust: API:490-491 (quotient_lowering: QuotientLowering) - "compact VM by
      default". -/
  quotientLowering : QuotientLowering
  /-- rust: API:492-493 (diagnostics: RenderDiagnostics) -/
  diagnostics : RenderDiagnostics
  /-- rust: API:494-503 (provenance: Option<[u8; 32]>) - optional 32-byte
      provenance tag folded into the emitted BUILD_ID constant (P10/L-8). None
      keeps BUILD_ID a pure function of the feature profile, VK and SRS, so
      repository fixtures stay byte-stable across commits. [u8; 32] is
      Midfall.Bytes (Common/Bytes.lean:27, the row's Vec<u8> model); the length-32
      discipline is the producer's and this file never inspects it. -/
  provenance : Option Bytes
  deriving BEq

/-- rust: API:484 (#[derive(..., Default, ...)] on RenderOptions)
    @formal-baseline: each field's own Default, i.e. Embedded, Inline, Vm, the
    feature-gated diagnostics, and None. Written field by field so hazard 8's
    default is a value a gate can see rather than one a derive hides. -/
def RenderOptions.default : RenderOptions :=
  { vk := RenderVk.default,
    quotient := RenderQuotient.default,
    quotientLowering := QuotientLowering.default,
    diagnostics := RenderDiagnostics.default,
    provenance := none }

/-! ## RenderedArtifacts (rust: API:506-528) -/

/-- rust: API:506-528 (struct RenderedArtifacts) @formal-baseline. Five String /
    Option String fields and a derived Default.

    NOT PORTED, and said here because this is where a reader looks: the working
    copy carries an uncommitted impl RenderedArtifacts with named_bytes
    (working-copy 530-549) plus a #[cfg(test)] mod (working-copy 551-586).
    Neither is in HEAD, so neither is in the baseline, so neither is here. The
    plan's range for this row ("508-587 RenderedArtifacts + impl") is working-copy
    numbering and includes that impl - see the header's reference-hygiene
    section. -/
structure RenderedArtifacts where
  /-- rust: API:509-510 (verifier: String) - always-rendered verifier source. -/
  verifier : String
  /-- rust: API:511-512 (verifying_key: Option<String>) - separate VK source when
      RenderVk::Separate is selected. -/
  verifyingKey : Option String
  /-- rust: API:513-515 (quotient_evaluator: Option<String>) - quotient evaluator
      source when RenderQuotient::ExternalPinned is selected. -/
  quotientEvaluator : Option String
  /-- rust: API:516-522 (quotient_listing: Option<String>) - annotated disassembly
      of the compact quotient-VM program by identity j, decoded from the program
      bytes in the rendered VK payload; a separate text artifact that never changes
      the rendered Solidity. -/
  quotientListing : Option String
  /-- rust: API:523-527 (quotient_manifest: Option<String>) - JSON identity
      manifest matching quotient_listing. -/
  quotientManifest : Option String
  deriving BEq

/-- rust: API:507 (#[derive(..., Default, ...)] on RenderedArtifacts)
    @formal-baseline: String::default() is the empty string and Option::default()
    is None, so the default artifact set is an empty verifier and four absent
    artifacts. Written out field by field. -/
def RenderedArtifacts.default : RenderedArtifacts :=
  { verifier := "", verifyingKey := none, quotientEvaluator := none,
    quotientListing := none, quotientManifest := none }

/-! ## ProofEvaluationCounts (rust: API:692-761) -/

/-- rust: API:692-725 (struct ProofEvaluationCounts) @formal-baseline.
    Field-evaluation counts for the proof layout the generated Solidity verifier
    consumes. Thirteen usize counts; #[derive(Default)] is the explicit def below. -/
structure ProofEvaluationCounts where
  /-- rust: API:696-697 (committed_instance) - committed instance-query
      evaluations read from the proof. -/
  committedInstance : Nat
  /-- rust: API:698-700 (computed_instance) - non-committed instance-query
      evaluations reconstructed from calldata public inputs, NOT read from the
      proof. The only count here that is not a proof scalar, which is why
      proof_main_total excludes it and instance_total_for_identities includes
      it. -/
  computedInstance : Nat
  /-- rust: API:701-702 (advice) -/
  advice : Nat
  /-- rust: API:703-704 (fixed) - non-simple fixed-column evaluations. -/
  fixed : Nat
  /-- rust: API:705-707 (simple_selector_fixed) - simple selector fixed columns
      handled via selector commitments instead of proof eval scalars, so it is in
      NO total below. -/
  simpleSelectorFixed : Nat
  /-- rust: API:708-709 (permutation_common) -/
  permutationCommon : Nat
  /-- rust: API:710-712 (permutation_product) - z_cur, z_next and non-final
      z_last. -/
  permutationProduct : Nat
  /-- rust: API:713-714 (permutation_sets) - number of permutation product sets;
      metadata, in no total below. -/
  permutationSets : Nat
  /-- rust: API:715-716 (lookup_multiplicity) -/
  lookupMultiplicity : Nat
  /-- rust: API:717-718 (lookup_helper) -/
  lookupHelper : Nat
  /-- rust: API:719-720 (lookup_accumulator) - z, z_next. -/
  lookupAccumulator : Nat
  /-- rust: API:721-722 (trash) -/
  trash : Nat
  /-- rust: API:723-724 (dummy) - dummy eval scalars appended for the
      fewer-point-sets PCS layout; excluded from proof_main_total and included in
      proof_total. -/
  dummy : Nat
  deriving BEq

/-- rust: API:694 (#[derive(..., Default, ...)] on ProofEvaluationCounts)
    @formal-baseline: every count zero. All thirteen written out, so a fourteenth
    field is a compile error here rather than an invisible default (the R-40 F5a
    fix pattern). -/
def ProofEvaluationCounts.default : ProofEvaluationCounts :=
  { committedInstance := 0, computedInstance := 0, advice := 0, fixed := 0,
    simpleSelectorFixed := 0, permutationCommon := 0, permutationProduct := 0,
    permutationSets := 0, lookupMultiplicity := 0, lookupHelper := 0,
    lookupAccumulator := 0, trash := 0, dummy := 0 }

/-- rust: API:728-740 (ProofEvaluationCounts::proof_main_total) @formal-baseline.
    Nine terms, in the Rust's order: committed_instance, advice, fixed,
    permutation_common, permutation_product, lookup_multiplicity, lookup_helper,
    lookup_accumulator, trash. It EXCLUDES computed_instance (not read from the
    proof), simple_selector_fixed (handled via commitments), permutation_sets
    (metadata) and dummy (added by proof_total). Dropping any one of the nine, or
    adding one of the four, changes the proof scalar stream without changing the
    field count - proofEvaluationCounts_totals_ok pins each sum against thirteen
    distinct values so no term can be swapped for another. -/
def ProofEvaluationCounts.proofMainTotal (self : ProofEvaluationCounts) : Nat :=
  self.committedInstance + self.advice + self.fixed
    + self.permutationCommon + self.permutationProduct
    + self.lookupMultiplicity + self.lookupHelper + self.lookupAccumulator
    + self.trash

/-- rust: API:741-744 (ProofEvaluationCounts::proof_total) @formal-baseline. -/
def ProofEvaluationCounts.proofTotal (self : ProofEvaluationCounts) : Nat :=
  self.proofMainTotal + self.dummy

/-- rust: API:746-750 (ProofEvaluationCounts::instance_total_for_identities)
    @formal-baseline: the instance evals available to identity reconstruction,
    including those computed locally from public inputs. -/
def ProofEvaluationCounts.instanceTotalForIdentities
    (self : ProofEvaluationCounts) : Nat :=
  self.committedInstance + self.computedInstance

/-- rust: API:752-755 (ProofEvaluationCounts::permutation_total) @formal-baseline.
    Note it excludes permutationSets. -/
def ProofEvaluationCounts.permutationTotal (self : ProofEvaluationCounts) : Nat :=
  self.permutationCommon + self.permutationProduct

/-- rust: API:757-760 (ProofEvaluationCounts::lookup_total) @formal-baseline. -/
def ProofEvaluationCounts.lookupTotal (self : ProofEvaluationCounts) : Nat :=
  self.lookupMultiplicity + self.lookupHelper + self.lookupAccumulator

end Midfall.Generator


/-! # Known-answer gates

Twenty-one gates. Every expected number and string below is read off the reference
source or off the reference's own two accumulator tests -
proofs/solidity-verifier/src/lowering/tests.rs:2024-2082
(accumulator_word_counts_match_circuit_encoding) and
proofs/solidity-verifier/src/lowering/tests.rs:2084-2122
(accumulator_encoding_validation_rejects_dead_configs) - and not produced by the
definitions under test. The reason strings are re-typed here rather than imported
from the sites that construct them, because a gate that reused the def's own
literal could not catch that literal being edited.

Each gate names the concrete wrong implementation it rules out (the rule docs/
REVIEW.md R-38 ends with), and every perturbation claimed was actually run; the
results, including the ones that did not redden what this section first expected,
are in the package report.

Lean scaffolding note: core has no BEq instance on Except and no Except.ok?, so
every gate reads an Except through okOf / isOk / errIs / panickedAtSite rather
than comparing it with ==. -/

namespace Midfall.Generator.ApiKats

open Midfall Midfall.Halo2 Midfall.Generator

/-- The one panic site in api.rs, spelled once so every gate says which line it
    means. -/
def panicSite104 : String := "proofs/solidity-verifier/src/api.rs:104"

/-- The three reason literals of API:155, API:166 and API:184, re-typed here on
    the rule that a gate must not borrow the text of the thing it pins. -/
def reasonShape : String :=
  "expected 7 radix-2^56 limbs per BLS12-381 base-field coordinate"

/-- rust: API:166. -/
def reasonTail : String := "accumulator public-input tail exceeds num_instances"

/-- rust: API:184. -/
def reasonPair : String :=
  "point-pair accumulator encoding does not support a fixed-base scalar tail"

/-- The success payload of an Except, or none: Lean core has no Except.ok?. -/
def okOf {ε α : Type} (e : Except ε α) : Option α :=
  match e with
  | .ok a => some a
  | .error _ => none

/-- Reading an Except ApiFault as "it succeeded at all". -/
def isOk {α : Type} (e : Except ApiFault α) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

/-- Reading an Except ApiFault as "it aborted at exactly this panic site", the
    strongest thing a panic can express while Fault.panic carries no payload
    (docs/REVIEW.md R-43 F2). -/
def panickedAtSite {α : Type} (e : Except ApiFault α) (site : String) : Bool :=
  match e with
  | .error (ApiFault.panic s) => s == site
  | _ => false

/-- Reading an Except ApiFault as "it failed with exactly this GeneratorError",
    payload and all. Strictly stronger than the reference's own
    matches!(err, GeneratorError::UnsupportedAccumulatorEncoding { reason: .., ..
    }) at tests.rs:2098-2112, which ignores four of the five fields. -/
def errIs {α : Type} (e : Except ApiFault α) (want : GeneratorError) : Bool :=
  match e with
  | .error (ApiFault.error g) => g == want
  | _ => false

/-- The formatted text of a failure, so a gate can assert the whole Display string
    or use the reference's own contains-subset assertion. A panic formats as the
    empty string, which makes every errText conjunct below also assert "this was
    an error, not an abort". -/
def errText {α : Type} (e : Except ApiFault α) : String :=
  match e with
  | .error (ApiFault.error g) => printGeneratorError g
  | .error (ApiFault.panic _) => ""
  | .ok _ => ""

/-- Shorthand for the one error variant the accumulator checks build. -/
def ua (offset numLimbs numLimbBits numInstances : Nat) (reason : String) :
    GeneratorError :=
  GeneratorError.unsupportedAccumulatorEncoding (offset := offset)
    (numLimbs := numLimbs) (numLimbBits := numLimbBits)
    (numInstances := numInstances) (reason := reason)

/-- HAZARD 4, first half: the layout constants api.rs reads are the numbers the
    reference says they are, and the two independent copies of the compressed-G1
    width agree. g1CompressedBytes is LM:74 read from the layout side and
    Midfall.g1CompressedWidth (Common/Codec.lean:89) is the same number read from
    the codec side; R-20 is the story of one number typed into a second file and
    being wrong, so the equality is asserted rather than assumed.

    Rules out: a constant ported one off, and - because the two
    AccumulatorEncoding constants are defined AS these - a layout constant being
    edited without the derived numbers being re-checked. 

    PERTURBATION RUN: accumulatorLimbBits := 32 reddens nine gates (this one
    and every accumulator-arithmetic gate below); g1CompressedBytes := 32
    reddens this, repackError_display_ok and generatorError_display_ok;
    accumulatorLimbsPerWord := 5 reddens this and
    accumulatorDerivedNumbers_agreeWithDocs_ok.
-/
def layoutConstants_agreeWithTheirRows_ok : Bool :=
  accumulatorLimbs == 7
    && accumulatorLimbBits == 56
    && accumulatorLimbsPerWord == 4
    && accumulatorIdentityFlagWords == 1
    && accumulatorCarriedScalars == 2
    && AccumulatorEncoding.supportedNumLimbs == 7
    && AccumulatorEncoding.supportedNumLimbBits == 56
    && g1CompressedBytes == 48
    && g1CompressedBytes == g1CompressedWidth
    && wordBytes == 32

/-- HAZARD 4, the check the plan asked for and the reference never makes: the
    DERIVED arithmetic and the two LITERAL constants must agree, and the doc
    comment's "seven radix-2^56 limbs, packed four limbs per public-input field
    element" (API:30-31) must be what the arithmetic actually does.

    With the supported constants: coordinate_words is 2, point_words is 2*2 + 1 =
    5, point_pair_words is 10, and fixed_payload_words is 12 for PointAndScalar
    and 10 for PointPair - equal to FULLY_COLLAPSED_PUBLIC_INPUT_WORDS and
    POINT_PAIR_PUBLIC_INPUT_WORDS. The reference checks those constants only
    against a real circuit encoding (tests.rs:2063-2082), never against its own
    arithmetic, so a constant bump with the arithmetic unchanged - or the reverse
    - is invisible to every non-EVM test in the crate. The plan says STOP and
    report if they disagree; they agree, so the agreement is what is pinned.

    The last conjunct is tests.rs:2080-2082 (2 * words_per_point ==
    POINT_PAIR_PUBLIC_INPUT_WORDS) restated over the port. 

    PERTURBATION RUN: accumulatorCarriedScalars := 1 reddens seven gates
    including this one;
    AccumulatorEncoding.fullyCollapsedPublicInputWordsConst := 11 reddens
    EXACTLY this gate and fullyCollapsedPublicInputWords_sentinel_ok - the two
    places where the literal and the derived number are compared against each
    other.
-/
def accumulatorDerivedNumbers_agreeWithDocs_ok : Bool :=
  let enc := AccumulatorEncoding.new 0 7 56
  let pp := AccumulatorEncoding.pointPair 0 7 56
  let cw := okOf enc.coordinateWords
  let pw := okOf enc.pointWords
  let ppw := okOf enc.pointPairWords
  let fpw := okOf enc.fixedPayloadWords
  let fpwPair := okOf pp.fixedPayloadWords
  let collapsed := okOf enc.fullyCollapsedPublicInputWords
  let collapsedPair := okOf pp.fullyCollapsedPublicInputWords
  Nat.max (254 / 56) 1 == accumulatorLimbsPerWord
    && cw == some 2
    && pw == some 5
    && ppw == some 10
    && fpw == some 12
    && fpw == some AccumulatorEncoding.fullyCollapsedPublicInputWordsConst
    && fpwPair == some 10
    && fpwPair == some AccumulatorEncoding.pointPairPublicInputWordsConst
    && collapsed == some AccumulatorEncoding.fullyCollapsedPublicInputWordsConst
    && collapsedPair == some AccumulatorEncoding.pointPairPublicInputWordsConst
    && 2 * (pw.getD 0) == AccumulatorEncoding.pointPairPublicInputWordsConst
    && collapsed == some 12

/-- HAZARD 1: the division by zero at API:104 is a PANIC and is ported as one.
    Five probes: num_limb_bits = 0 aborts at api.rs:104 through each of the four
    defs above it on the call chain (coordinateWords, pointWords, pointPairWords,
    fixedPayloadWords), so the guard cannot be hoisted one level up or dropped
    without a red gate. The four shape probes pin the arithmetic, including the
    .max(1): at num_limb_bits = 300 the raw quotient 254/300 is 0, and without the
    max the div_ceil would divide by zero - in Lean silently (divCeil a 0 = 0,
    Exec/Arith.lean:53) where Rust would panic. That is the R-30 shape: a default
    where the reference aborts. 

    PERTURBATION RUN, three of them, each reddening ONLY this gate: testing
    numLimbs instead of numLimbBits in the zero guard (the guard stops firing
    for the four probes that carry limbs); deleting Nat.max 1; and changing
    the literal 254 to 381, which reddens only the num_limb_bits = 127
    conjunct - 381/56 = 6 and 381/300 = 1 still give the same
    coordinate_words. That last result is finding F-6 made concrete: the two
    candidate readings of the literal differ only outside the supported shape.
-/
def coordinateWords_divZero_panics_ok : Bool :=
  let zero := AccumulatorEncoding.new 0 7 0
  let ppZero := AccumulatorEncoding.pointPair 4 0 0
  let ok56 := AccumulatorEncoding.new 0 7 56
  let w300 := okOf (AccumulatorEncoding.new 0 7 300).coordinateWords
  let w254 := okOf (AccumulatorEncoding.new 0 7 254).coordinateWords
  let w127 := okOf (AccumulatorEncoding.new 0 7 127).coordinateWords
  let w56 := okOf ok56.coordinateWords
  panickedAtSite zero.coordinateWords panicSite104
    && panickedAtSite zero.pointWords panicSite104
    && panickedAtSite zero.pointPairWords panicSite104
    && panickedAtSite zero.fixedPayloadWords panicSite104
    && panickedAtSite ppZero.fixedPayloadWords panicSite104
    && w300 == some 7
    && w254 == some 7
    && w127 == some 4
    && w56 == some 2
    && isOk ok56.pointWords

/-- The limb-shape rejection on the reference's own numbers (tests.rs:2104-2112:
    new(4, 8, 32) at num_instances 16), plus the two single-field cases that make
    the disjunction a disjunction: new(4, 8, 56) has the right limb width and the
    wrong limb count, new(4, 7, 32) the reverse, and BOTH must be rejected. A port
    that wrote && instead of || accepts both, and no other gate in this file would
    notice. errText asserts the whole formatted string, which the reference's
    matches! does not: it checks num_limbs and num_limb_bits and ignores offset,
    num_instances and reason. 

    PERTURBATION RUN: || -> && in the shape test reddens ONLY this gate, and
    only through the two single-field conjuncts new(4,8,56) and new(4,7,32)
    that the disjunction exists to catch - the both-wrong case the reference
    tests survives the change. Dropping the '; ' before the reason in
    printGeneratorError reddens this and generatorError_display_ok.
-/
def validateForNumInstances_rejectsWrongLimbShape_ok : Bool :=
  let both := AccumulatorEncoding.new 4 8 32
  let limbsOnly := AccumulatorEncoding.new 4 8 56
  let bitsOnly := AccumulatorEncoding.new 4 7 32
  let good := AccumulatorEncoding.new 4 7 56
  let goodPair := AccumulatorEncoding.pointPair 4 7 56
  let e := both.validateForNumInstances 16
  errIs e (ua 4 8 32 16 reasonShape)
    && errText e == "unsupported accumulator encoding: offset=4, num_limbs=8, \
num_limb_bits=32, num_instances=16; " ++ reasonShape
    && errIs (limbsOnly.validateForNumInstances 16) (ua 4 8 56 16 reasonShape)
    && errIs (bitsOnly.validateForNumInstances 16) (ua 4 7 32 16 reasonShape)
    && isOk (good.validateForNumInstances 16)
    && isOk (goodPair.validateForNumInstances 14)

/-- The two checks in validate_for_num_instances are ORDERED and the order is
    observable: a config that fails both (offset 100 at num_instances 16, and the
    wrong limb shape) reports the limb shape, because API:147-157 returns first.
    A port that ran the tail bound first - the order a skimming reader might infer
    - produces a different reason for the same input and nothing else changes.
    The third conjunct stops the gate being satisfied by a validate that always
    reports the shape: offset 100 with a GOOD shape must report the tail. 

    PERTURBATION RUN: moving the tail check above the shape check (a block
    swap inside validateForNumInstances) reddens ONLY this gate.
-/
def validate_ordering_shapeBeforeTail_ok : Bool :=
  let both := AccumulatorEncoding.new 100 8 32
  let tailOnly := AccumulatorEncoding.new 100 7 56
  let e1 := both.validateForNumInstances 16
  let e2 := tailOnly.validateForNumInstances 16
  errIs e1 (ua 100 8 32 16 reasonShape)
    && ! (errText e1).contains "tail exceeds"
    && errIs e2 (ua 100 7 56 16 reasonTail)

/-- The tail bound at API:160, pinned at the boundary from both sides and for both
    kinds: 4 + 12 == 16 is ACCEPTED (the Rust compares with a strict >), 5 + 12 =
    17 > 16 is rejected (tests.rs:2114-2121), and the point-pair shape needs its
    own boundary because its payload is 10 words, not 12. 

    PERTURBATION RUN: > -> >= in the bound reddens six gates (this one,
    rejectsWrongLimbShape, sentinel, saturatingAdd, bothArms, wrappingTail),
    because every accepted case becomes rejected. Replacing the sentinel at
    API:137 with 0 reddens two.
-/
def validateForNumInstances_tailBound_ok : Bool :=
  let a := AccumulatorEncoding.new 4 7 56
  let b := AccumulatorEncoding.new 5 7 56
  let c := AccumulatorEncoding.new 0 7 56
  let p := AccumulatorEncoding.pointPair 4 7 56
  isOk (a.validateForNumInstances 16)
    && errIs (b.validateForNumInstances 16) (ua 5 7 56 16 reasonTail)
    && isOk (c.validateForNumInstances 12)
    && errIs (c.validateForNumInstances 11) (ua 0 7 56 11 reasonTail)
    && isOk (p.validateForNumInstances 14)
    && errIs (p.validateForNumInstances 13) (ua 4 7 56 13 reasonTail)

/-- HAZARD 2: the usize::MAX sentinel at API:137. An encoding whose offset is
    usize::MAX still returns Ok from fullyCollapsedPublicInputWords - because
    saturating_add cannot exceed usize::MAX, so the tail bound cannot fire - and
    the SAME encoding is rejected by validateForNumInstances at a realistic
    num_instances. That pair is the whole point of the sentinel and what rules out
    the tempting simplification of a separate unvalidated fast path.

    The last conjunct is the sentinel's other face: at num_instances = usizeMax the
    huge offset validates, which is what lets fixedScalarCount reach its wrapping
    arithmetic (fixedScalarCount_wrappingTail_ok). 

    PERTURBATION RUN: replacing the usize::MAX sentinel at API:137 with 0
    reddens this gate and accumulatorDerivedNumbers_agreeWithDocs_ok;
    replacing usizeSaturatingAdd with a plain + at API:160 reddens this,
    saturatingAdd_isSaturationNotNatAdd_ok and
    fixedScalarCount_wrappingTail_ok.
-/
def fullyCollapsedPublicInputWords_sentinel_ok : Bool :=
  let huge := AccumulatorEncoding.new usizeMax 7 56
  let hugePair := AccumulatorEncoding.pointPair usizeMax 7 56
  let collapsed := okOf huge.fullyCollapsedPublicInputWords
  let collapsedPair := okOf hugePair.fullyCollapsedPublicInputWords
  collapsed == some AccumulatorEncoding.fullyCollapsedPublicInputWordsConst
    && collapsed == some 12
    && collapsedPair == some AccumulatorEncoding.pointPairPublicInputWordsConst
    && collapsedPair == some 10
    && errIs (huge.validateForNumInstances 16) (ua usizeMax 7 56 16 reasonTail)
    && isOk (huge.validateForNumInstances usizeMax)

/-- HAZARD 3: saturating_add is not Nat addition. usizeSaturatingAdd (usizeMax - 5)
    12 is usizeMax, not usizeMax + 7, and the bound at API:160 therefore ACCEPTS
    an offset of usizeMax - 4 at num_instances = usizeMax where a plain + would
    reject it. That conjunct is the discriminator: false for the one-token change
    of using +, true for the reference. The sixth pins that one below the
    saturation point the bound still fires. 

    PERTURBATION RUN: plain + at the USE SITE (API:160) reddens this, sentinel
    and wrappingTail - and leaves the helper's own four conjuncts green, which
    is why the helper and its use are both pinned. Plain + inside the
    usizeSaturatingAdd definition reddens the same three.
-/
def saturatingAdd_isSaturationNotNatAdd_ok : Bool :=
  let near := AccumulatorEncoding.new (usizeMax - 4) 7 56
  isOk (near.validateForNumInstances usizeMax)
    && errIs (near.validateForNumInstances (usizeMax - 1))
        (ua (usizeMax - 4) 7 56 (usizeMax - 1) reasonTail)
    && usizeSaturatingAdd 3 4 == 7
    && usizeSaturatingAdd (usizeMax - 5) 12 == usizeMax
    && usizeSaturatingAdd usizeMax usizeMax == usizeMax
    && usizeSaturatingAdd usizeMax 0 == usizeMax
    && usizeMax + 5 > usizeMax

/-- HAZARD 5: both arms of fixed_scalar_count, on the reference's own numbers
    (tests.rs:2088-2101). PointAndScalar accepts a tail of 0, 1 and 3; PointPair
    accepts 0 and rejects 1 with the point-pair reason. The sixth conjunct is the
    reference's wrong-limb-shape case reaching this function through its own
    validate call, and the seventh is a PointAndScalar tail that does not fit. 

    PERTURBATION RUN: making the tail != 0 test never fire (tail != 999)
    reddens ONLY this gate; flipping the kind test to pointAndScalar reddens
    this and fixedScalarCount_wrappingTail_ok.
-/
def fixedScalarCount_bothArms_ok : Bool :=
  let a := AccumulatorEncoding.new 4 7 56
  let p := AccumulatorEncoding.pointPair 4 7 56
  let bad := AccumulatorEncoding.new 4 8 32
  okOf (a.fixedScalarCount 16) == some 0
    && okOf (a.fixedScalarCount 19) == some 3
    && okOf (a.fixedScalarCount 17) == some 1
    && okOf (p.fixedScalarCount 14) == some 0
    && errIs (p.fixedScalarCount 15) (ua 4 7 56 15 reasonPair)
    && errIs (bad.fixedScalarCount 16) (ua 4 8 32 16 reasonShape)
    && errIs (a.fixedScalarCount 15) (ua 4 7 56 15 reasonTail)

/-- HAZARD 3's second half, and the reason this port does not model every usize
    operator as Nat: API:177 uses PLAIN + and -, which wrap in release, while
    API:160 uses saturating_add. The usize::MAX sentinel of API:137 makes the two
    disagree on inputs the reference can actually be handed: offset = usizeMax with
    num_instances = usizeMax validates (saturating_add caps at usizeMax, which is
    not > usizeMax) and the plain arithmetic then wraps to 2^64 - 12 instead of
    truncating to 0.

    Rules out: the whole expression ported with Nat + and Nat -, which gives tail =
    0 - a PointAndScalar config claiming to carry no fixed-base scalars where the
    reference claims 2^64 - 12 of them, and a PointPair config that ACCEPTS where
    the reference rejects. The first two conjuncts keep the wrapping helpers honest
    in the ordinary range, so a mod bug cannot hide behind the boundary case. 

    PERTURBATION RUN: replacing usizeAdd/usizeSub with plain Nat + and - at
    API:177 reddens ONLY this gate - the tail becomes 0 and the point-pair
    rejection disappears with it. Replacing usizeAdd with usizeSaturatingAdd
    also reddens only this gate.
-/
def fixedScalarCount_wrappingTail_ok : Bool :=
  let huge := AccumulatorEncoding.new usizeMax 7 56
  let hugePair := AccumulatorEncoding.pointPair usizeMax 7 56
  usizeAdd 3 4 == 7
    && usizeSub 10 3 == 7
    && usizeAdd usizeMax 12 == 11
    && usizeSub usizeMax 11 == usizeMax - 11
    && okOf (huge.fixedScalarCount usizeMax) == some (usizeMax - 11)
    && errIs (hugePair.fixedScalarCount usizeMax)
        (ua usizeMax 7 56 usizeMax reasonPair)

/-- HAZARD 6, first half: every RepackError Display string verbatim, including the
    ", +f_com+pi" clause, the range end computed as offset + G1_COMPRESSED_BYTES
    (48 + 48 = 96) and offset + WORD_BYTES (32 + 32 = 64), and the 0x that lives in
    the format string rather than in bytes_hex - which is why the empty-hex case is
    pinned too. 

    PERTURBATION RUN: g1CompressedBytes := 32 reddens this,
    layoutConstants_agreeWithTheirRows_ok and generatorError_display_ok (which
    prints a repack error through the From coercion).
-/
def repackError_display_ok : Bool :=
  printRepackError (RepackError.lengthMismatch 100 90 4 21 22)
    == "compressed proof length mismatch: expected 100 bytes (prefix_g1=4, \
num_evals=21, num_point_sets=22, +f_com+pi), got 90"
    && printRepackError (RepackError.invalidCompressedG1 48 "aabbcc")
      == "invalid compressed G1 at compressed[48..96]: bytes = 0xaabbcc"
    && printRepackError (RepackError.nonCanonicalScalar 32 "00ff")
      == "non-canonical Fr scalar at compressed[32..64]: bytes = 0x00ff"
    && printRepackError (RepackError.invalidCompressedG1 0 "")
      == "invalid compressed G1 at compressed[0..48]: bytes = 0x"

/-- HAZARD 6, second half: all seven GeneratorError arms verbatim, and BOTH arms of
    the checked_sub at API:651-654 - the Some arm (total >= committed, printed as a
    number, including the total == committed case that prints 0) and the None arm
    (committed > total, printed as the "invalid:" sentence inside the larger
    message). A port that wrote total - committed with Nat subtraction keeps the
    first two and loses the third, because Lean's - truncates to 0 where Rust's
    checked_sub says the shape is nonsense.

    The negative rotation is the i32 check: Rust prints -1, and a Nat model would
    print a 20-digit wrapped number or refuse to build. 

    PERTURBATION RUN: checked_sub's <= -> < reddens ONLY this gate - the total
    == committed case starts printing the invalid: sentence. Replacing the
    None arm with the same Nat subtraction reddens only this gate. Dropping
    the '; ' before the reason reddens this and
    validateForNumInstances_rejectsWrongLimbShape_ok.
-/
def generatorError_display_ok : Bool :=
  printGeneratorError GeneratorError.noAdviceColumns
    == "at least one advice column is required"
    && printGeneratorError (GeneratorError.unsupportedInstanceColumnShape 2 1 1 1)
      == "unsupported instance column shape: got total=2, committed=1, \
non_committed=1; expected exactly 1 identity-committed and 1 non-committed"
    && printGeneratorError (GeneratorError.unsupportedInstanceColumnShape 1 1 1 0)
      == "unsupported instance column shape: got total=1, committed=1, \
non_committed=0; expected exactly 1 identity-committed and 0 non-committed"
    && printGeneratorError (GeneratorError.unsupportedInstanceColumnShape 2 3 1 1)
      == "unsupported instance column shape: got total=2, committed=3, \
non_committed=invalid: committed 3 exceeds total 2; expected exactly 1 \
identity-committed and 1 non-committed"
    && printGeneratorError (ua 4 7 56 16 reasonPair)
      == "unsupported accumulator encoding: offset=4, num_limbs=7, \
num_limb_bits=56, num_instances=16; " ++ reasonPair
    && printGeneratorError (GeneratorError.rotatedInstanceQuery 0 (-1))
      == "rotated instance query is not supported: column 0, rotation -1"
    && printGeneratorError (GeneratorError.planning "layout" "boom")
      == "generator planning failed during layout: boom"
    && printGeneratorError (GeneratorError.render "Halo2Verifier.sol")
      == "failed to render Halo2Verifier.sol"
    && printGeneratorError (GeneratorError.repack
      (RepackError.invalidCompressedG1 0 "ff"))
      == "invalid compressed G1 at compressed[0..48]: bytes = 0xff"

/-- HAZARD 6's From impl: API:685-690 WRAPS, it does not format. The second
    conjunct pins the Display delegation (Rust's write!(f, "{err}")), and the third
    rules out the plausible "improvement" of flattening the repack failure into a
    Planning error carrying the rendered text - which would print the same string
    and change the variant every later consumer matches on. 

    PERTURBATION RUN: defining fromRepackError as .planning "repack"
    (printRepackError err) - the plausible flattening - reddens ONLY this
    gate.
-/
def fromRepackError_isTheReferenceCoercion_ok : Bool :=
  GeneratorError.fromRepackError (RepackError.nonCanonicalScalar 3 "ab")
    == GeneratorError.repack (RepackError.nonCanonicalScalar 3 "ab")
    && printGeneratorError
        (GeneratorError.fromRepackError (RepackError.lengthMismatch 1 2 3 4 5))
      == printRepackError (RepackError.lengthMismatch 1 2 3 4 5)
    && GeneratorError.fromRepackError (RepackError.invalidCompressedG1 0 "ff")
      != GeneratorError.planning "repack"
        (printRepackError (RepackError.invalidCompressedG1 0 "ff"))

/-- HAZARD 8, plus the default of every type in this file. QuotientLowering.default
    is Vm and NOT Direct - the Phase 0 merge requirement BASELINE.md states in
    words ("QuotientLowering::{Vm, Direct} kept, Vm the default"), and the condition
    hazard 8 says would be a finding. RenderOptions.default is written out field by
    field, so the VM default is a value a gate can see rather than one a derive
    hides, and a sixth knob would fail to compile here.

    The two diagnostics defaults are the R8 resolution of LIB:50 and LIB:60 under
    the recorded profile; the two != conjuncts stop the gate being satisfied by a
    RenderDiagnostics whose booleans nothing reads. 

    PERTURBATION RUN: QuotientLowering.default := direct reddens ONLY this
    gate; that is hazard 8's finding condition, measured rather than asserted.
    solidityTraceEnabled := true reddens only this gate, and so does
    RenderedArtifacts.default.verifier := "x".
-/
def renderDefaults_areTheReferenceOnes_ok : Bool :=
  QuotientLowering.default == QuotientLowering.vm
    && QuotientLowering.default != QuotientLowering.direct
    && RenderVk.default == RenderVk.embedded
    && RenderVk.default != RenderVk.separate
    && RenderQuotient.default == RenderQuotient.inline
    && solidityTraceEnabled == false
    && solidityGasCheckpointsEnabled == false
    && RenderDiagnostics.default == { trace := false, gasCheckpoints := false }
    && RenderDiagnostics.default != { trace := true, gasCheckpoints := false }
    && RenderDiagnostics.default != { trace := false, gasCheckpoints := true }
    && RenderOptions.default ==
      { vk := RenderVk.default,
        quotient := RenderQuotient.default,
        quotientLowering := QuotientLowering.default,
        diagnostics := RenderDiagnostics.default,
        provenance := none }
    && RenderOptions.default.quotientLowering == QuotientLowering.vm
    && RenderOptions.default.provenance == none
    && RenderedArtifacts.default ==
      { verifier := "",
        verifyingKey := none,
        quotientEvaluator := none,
        quotientListing := none,
        quotientManifest := none }

/-- ProofEvaluationCounts::default is all thirteen zeros, asserted field by field
    rather than as one equality: the R-40 F5a lesson is that a default nobody reads
    is a default nobody notices being wrong, and a fourteenth field has to break
    this gate rather than slide past it. 

    PERTURBATION RUN: ProofEvaluationCounts.default.dummy := 1 reddens ONLY
    this gate.
-/
def proofEvaluationCounts_default_ok : Bool :=
  ProofEvaluationCounts.default.committedInstance == 0
    && ProofEvaluationCounts.default.computedInstance == 0
    && ProofEvaluationCounts.default.advice == 0
    && ProofEvaluationCounts.default.fixed == 0
    && ProofEvaluationCounts.default.simpleSelectorFixed == 0
    && ProofEvaluationCounts.default.permutationCommon == 0
    && ProofEvaluationCounts.default.permutationProduct == 0
    && ProofEvaluationCounts.default.permutationSets == 0
    && ProofEvaluationCounts.default.lookupMultiplicity == 0
    && ProofEvaluationCounts.default.lookupHelper == 0
    && ProofEvaluationCounts.default.lookupAccumulator == 0
    && ProofEvaluationCounts.default.trash == 0
    && ProofEvaluationCounts.default.dummy == 0
    && ProofEvaluationCounts.default.proofTotal == 0

/-- The five sums, against thirteen DISTINCT values so no term can be swapped for
    another and still add up: proof_main_total is 1+3+4+6+7+9+10+11+12 = 63 and
    excludes computed_instance (2), simple_selector_fixed (5), permutation_sets (8)
    and dummy (13); proof_total adds dummy for 76; instance_total_for_identities is
    1+2 = 3; permutation_total is 6+7 = 13; lookup_total is 9+10+11 = 30. 

    PERTURBATION RUN: adding computedInstance to proofMainTotal reddens ONLY
    this gate (two conjuncts), and using permutationSets instead of
    permutationProduct in permutationTotal reddens only this gate (one
    conjunct).
-/
def proofEvaluationCounts_totals_ok : Bool :=
  let c : ProofEvaluationCounts :=
    { committedInstance := 1, computedInstance := 2, advice := 3, fixed := 4,
      simpleSelectorFixed := 5, permutationCommon := 6,
      permutationProduct := 7, permutationSets := 8, lookupMultiplicity := 9,
      lookupHelper := 10, lookupAccumulator := 11, trash := 12, dummy := 13 }
  c.proofMainTotal == 63
    && c.proofTotal == 76
    && c.instanceTotalForIdentities == 3
    && c.permutationTotal == 13
    && c.lookupTotal == 30
    && c.proofMainTotal != c.proofTotal

/-- The two constructors and the one predicate that reads the kind.
    has_carried_scalars is a matches! on PointAndScalar only, and the != conjunct
    is what stops a catch-all (always true, or kind != pointPair after a third
    variant is added) passing. The last two conjuncts are the payload of the
    difference: 12 words against 10, hazard 4's two kinds seen from the other side. 

    PERTURBATION RUN: hasCarriedScalars := kind == pointPair reddens seven
    gates - this one and every arithmetic gate that reads the payload size.
-/
def hasCarriedScalars_andConstructors_ok : Bool :=
  let enc := AccumulatorEncoding.new 4 7 56
  let pp := AccumulatorEncoding.pointPair 9 7 56
  enc.kind == AccumulatorEncodingKind.pointAndScalar
    && enc.offset == 4 && enc.numLimbs == 7 && enc.numLimbBits == 56
    && enc.hasCarriedScalars
    && pp.kind == AccumulatorEncodingKind.pointPair
    && pp.offset == 9
    && ! pp.hasCarriedScalars
    && okOf enc.fixedPayloadWords == some 12
    && okOf pp.fixedPayloadWords == some 10
    && AccumulatorEncodingKind.pointAndScalar
      != AccumulatorEncodingKind.pointPair

/-- GeneratorConfig is the g.cfg of PLAN 9.5 and with_accumulator sets exactly one
    field: the other two are pinned after the call, and the original is pinned
    unchanged afterwards. Rust moves self, so there is no aliasing to observe, but a
    port that rebuilt the record from the encoding would drop num_instances and this
    catches it. 

    PERTURBATION RUN: making withAccumulator also set numInstances :=
    accumulator.offset reddens ONLY this gate.
-/
def generatorConfig_withAccumulator_ok : Bool :=
  let enc := AccumulatorEncoding.new 4 7 56
  let cfg := GeneratorConfig.new 16 1
  let withAcc := cfg.withAccumulator enc
  cfg == { numInstances := 16, numCommittedInstances := 1, accumulator := none }
    && withAcc ==
      { numInstances := 16,
        numCommittedInstances := 1,
        accumulator := some enc }
    && withAcc.numInstances == 16
    && withAcc.numCommittedInstances == 1
    && withAcc.accumulator.map (fun a => a.offset) == some 4
    && cfg.accumulator == none

/-- Every payload field of the three quotient enums discriminates, so no field can
    be dropped or merged without a red gate - the R-40 F5 shape, a record whose
    fields are all printed but only some read. The last six conjuncts cover
    QuotientIdentityExecution and QuotientIdentityManifestTarget, whose payloads the
    reference carries and nothing in api.rs inspects. 

    PERTURBATION RUN, INCLUDING TWO THAT FAILED: making a payload field
    inaccessible - | nativeIdentity (_ : Nat) and | lookup ... (_ : String) -
    reddens NOTHING, because an anonymous Lean constructor argument is still
    an argument and the values stay distinct. Deleting the field outright is a
    compile error at this gate (measured: the file does not elaborate, which
    kat_gate.py reports as a hard failure). So this gate's protection is
    structural rather than runtime: it says every field is named and used, and
    it must not be read as claiming a dropped field would turn a conjunct
    false.
-/
def quotientIdentitySource_payloads_ok : Bool :=
  QuotientIdentitySource.gate 0 "g" 1 "c" 2
    != QuotientIdentitySource.gate 0 "g" 1 "c" 3
    && QuotientIdentitySource.gate 0 "g" 1 "c" 2
      != QuotientIdentitySource.gate 1 "g" 1 "c" 2
    && QuotientIdentitySource.gate 0 "g" 1 "c" 2
      != QuotientIdentitySource.gate 0 "G" 1 "c" 2
    && QuotientIdentitySource.gate 0 "g" 1 "c" 2
      != QuotientIdentitySource.gate 0 "g" 2 "c" 2
    && QuotientIdentitySource.gate 0 "g" 1 "c" 2
      != QuotientIdentitySource.gate 0 "g" 1 "C" 2
    && QuotientIdentitySource.permutation 0
      != QuotientIdentitySource.permutation 1
    && QuotientIdentitySource.lookup 0 0 "l"
      != QuotientIdentitySource.lookup 1 0 "l"
    && QuotientIdentitySource.lookup 0 0 "l"
      != QuotientIdentitySource.lookup 0 1 "l"
    && QuotientIdentitySource.lookup 0 0 "l"
      != QuotientIdentitySource.lookup 0 0 "L"
    && QuotientIdentitySource.trash 0 "t" != QuotientIdentitySource.trash 1 "t"
    && QuotientIdentitySource.trash 0 "t" != QuotientIdentitySource.trash 0 "T"
    && QuotientIdentitySource.permutation 0
      != QuotientIdentitySource.trash 0 ""
    && QuotientIdentityExecution.nativeIdentity 0
      != QuotientIdentityExecution.nativeIdentity 1
    && QuotientIdentityExecution.inline != QuotientIdentityExecution.interpreted
    && QuotientIdentityExecution.nativePermutation
      != QuotientIdentityExecution.nativeLookup
    && QuotientIdentityExecution.structuredTail
      != QuotientIdentityExecution.inline
    && QuotientIdentityManifestTarget.main
      != QuotientIdentityManifestTarget.selector 0 0
    && QuotientIdentityManifestTarget.selector 0 1
      != QuotientIdentityManifestTarget.selector 1 1
    && QuotientIdentityManifestTarget.selector 0 1
      != QuotientIdentityManifestTarget.selector 0 2

/-- The two richest records, every field written at construction and every field
    read back. The certificate is the type a later package will hash and compare,
    and a field that is constructed but never read is a field that can be dropped
    silently. selectorGap is the one Option in the cluster and both of its shapes
    are pinned, because an Option that only ever holds some is indistinguishable
    from a plain value in a construction test. 

    PERTURBATION RUN: setting selectorGap := none in the entry literal reddens
    ONLY this gate. As with quotientIdentitySource_payloads_ok the protection
    for a pure record is structural - the literals below list every field, so
    deleting one is a compile error here, not a red conjunct. That is a
    test-literal perturbation, not an implementation one, and it is labelled
    as such.
-/
def manifestAndCertificate_fields_ok : Bool :=
  let entry : QuotientCertificateEntry :=
    { globalIndex := 5, source := QuotientIdentitySource.permutation 2,
      target := QuotientIdentityManifestTarget.selector 1 3,
      selectorGap := some 4, execution := QuotientIdentityExecution.interpreted,
      expressionHash := 0xabcd, expressionEncodingLen := 77 }
  let entryNoGap : QuotientCertificateEntry :=
    { entry with selectorGap := none }
  let cert : QuotientCertificate :=
    { version := 1, entries := [entry], gateIdentities := 2,
      permutationIdentities := 3, lookupIdentities := 4, trashIdentities := 5,
      simpleSelectorCols := [0, 7], selectorTailExponents := [1, 2, 3],
      vmBytecodeHash := 0x11, quotientConstantsHash := 0x22,
      certificateHash := 0x33 }
  let mEntry : QuotientIdentityManifestEntry :=
    { globalIndex := 5,
      source := QuotientIdentitySource.permutation 2,
      target := QuotientIdentityManifestTarget.selector 1 3 }
  let manifest : QuotientIdentityManifest :=
    { entries := [mEntry],
      gateIdentities := 2,
      permutationIdentities := 3,
      lookupIdentities := 4,
      trashIdentities := 5,
      simpleSelectorCols := [0, 7] }
  entry.globalIndex == 5
    && entry.source == QuotientIdentitySource.permutation 2
    && entry.target == QuotientIdentityManifestTarget.selector 1 3
    && entry.selectorGap == some 4
    && entry.execution == QuotientIdentityExecution.interpreted
    && entry.expressionHash == 0xabcd
    && entry.expressionEncodingLen == 77
    && entryNoGap.selectorGap == none
    && entryNoGap.globalIndex == 5
    && cert.version == 1 && cert.entries == [entry]
    && cert.gateIdentities == 2 && cert.permutationIdentities == 3
    && cert.lookupIdentities == 4 && cert.trashIdentities == 5
    && cert.simpleSelectorCols == [0, 7]
    && cert.selectorTailExponents == [1, 2, 3]
    && cert.vmBytecodeHash == 0x11 && cert.quotientConstantsHash == 0x22
    && cert.certificateHash == 0x33
    && manifest.entries.length == 1 && manifest.gateIdentities == 2
    && manifest.simpleSelectorCols == [0, 7]
    && ({ entries := [], gateIdentities := 0, permutationIdentities := 0,
          lookupIdentities := 0, trashIdentities := 0,
          simpleSelectorCols := [] } : QuotientIdentityManifest)
      != manifest

/-- HAZARD 7: the test-only probe type exists and holds what it is given. It is
    destructured rather than compared because the reference derives only Clone and
    Debug for it (API:199) and so the port derives no BEq either - the one type in
    this file where a == b would be an invention. The order-preserving claim in the
    Rust doc comment ("word 1 + s is the accumulator of selector_columns[s]") is
    pinned by the third and fourth conjuncts: a sorted or deduplicated List would
    fail them. 

    PERTURBATION RUN (test literal, not implementation - the type has no
    implementation to perturb): reordering the selectorColumns literal to [0,
    3, 7] reddens ONLY this gate, which is the live proof that the order claim
    in the Rust doc comment is asserted rather than assumed.
-/
def quotientProbeArtifacts_ok : Bool :=
  let probe : QuotientProbeArtifacts :=
    { verifier := "contract P {}", verifyingKey := "contract VK {}",
      selectorColumns := [3, 0, 7] }
  probe.verifier == "contract P {}"
    && probe.verifyingKey == "contract VK {}"
    && probe.selectorColumns == [3, 0, 7]
    && probe.selectorColumns.length == 3
    && probe.selectorColumns.getD 0 9 == 3

#eval layoutConstants_agreeWithTheirRows_ok -- expect true
#eval accumulatorDerivedNumbers_agreeWithDocs_ok -- expect true
#eval coordinateWords_divZero_panics_ok -- expect true
#eval validateForNumInstances_rejectsWrongLimbShape_ok -- expect true
#eval validate_ordering_shapeBeforeTail_ok -- expect true
#eval validateForNumInstances_tailBound_ok -- expect true
#eval fullyCollapsedPublicInputWords_sentinel_ok -- expect true
#eval saturatingAdd_isSaturationNotNatAdd_ok -- expect true
#eval fixedScalarCount_bothArms_ok -- expect true
#eval fixedScalarCount_wrappingTail_ok -- expect true
#eval repackError_display_ok -- expect true
#eval generatorError_display_ok -- expect true
#eval fromRepackError_isTheReferenceCoercion_ok -- expect true
#eval renderDefaults_areTheReferenceOnes_ok -- expect true
#eval proofEvaluationCounts_default_ok -- expect true
#eval proofEvaluationCounts_totals_ok -- expect true
#eval hasCarriedScalars_andConstructors_ok -- expect true
#eval generatorConfig_withAccumulator_ok -- expect true
#eval quotientIdentitySource_payloads_ok -- expect true
#eval manifestAndCertificate_fields_ok -- expect true
#eval quotientProbeArtifacts_ok -- expect true

end Midfall.Generator.ApiKats

