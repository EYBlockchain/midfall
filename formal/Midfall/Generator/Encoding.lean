-- |
-- Midfall.Generator.Encoding
--
-- The codegen metadata and the pointer / value / BLS-encoding layer: a port of
-- proofs/solidity-verifier/src/lowering/encoding/mod.rs (940 lines), every
-- non-test item, in source order (rule R1).
--
-- CITATION NOTATION. Six prefixes, each named with its file and line count,
-- because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites that
-- silently pointed at the wrong file:
--
-- * ENC: proofs/solidity-verifier/src/lowering/encoding/mod.rs (940 lines) - the
--   file this module ports.
-- * PM:  proofs/solidity-verifier/src/lowering/protocol/mod.rs (1252 lines) -
--   the ProtocolPlan row, ported in Midfall/Generator/Protocol.lean.
-- * MEM: proofs/solidity-verifier/src/lowering/layout/memory.rs (1603 lines) -
--   the VerifierMemoryLayout row, ported in Midfall/Generator/Layout.lean.
-- * LM:  proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines) - the
--   byte-width constants ENC:22-26 imports.
-- * M:   proofs/solidity-verifier/src/lowering/render/models.rs (1494 lines) -
--   Halo2VerifyingKey, whose two lengths Data::new reads.
-- * EVM: proofs/solidity-verifier/src/evm.rs - cited once, at to_u256_be_bytes,
--   for the only call sites that fix its type parameter.
--
-- LEAN FILES THAT ALREADY PORT PART OF ENC. Fifteen Rust items in this file were
-- landed by earlier packages - the list below is the whole set, fifteen lines -
-- and Lean forbids declaring a name twice in the Midfall.Generator namespace, so
-- this file cites the existing def at the Rust source position instead of
-- re-declaring it. Each carries BOTH the Rust range and the Lean location:
--
-- * ENC:573-579 enum Location      -> Filters.lean:70-72
-- * ENC:581-592 enum Value         -> Filters.lean:78-80
-- * ENC:594-602 Value::as_usize    -> Layout.lean:996-1000 (plus asUsizeNat at
--   Layout.lean:1007-1010, which is a Layout-side total wrapper, not a Rust item)
-- * ENC:618-623 From<usize> Value  -> Models.lean:525 (valueFromNat)
-- * ENC:626-633 fmt_hex            -> Filters.lean:65-66 (fmtHex)
-- * ENC:635-650 Display for Value  -> Filters.lean:87-93 (printValue)
-- * ENC:680-684 struct Ptr         -> Models.lean:503-505
-- * ENC:696-699 Ptr::memory        -> Models.lean:508 (ptrMemory)
-- * ENC:701-704 Ptr::calldata      -> Models.lean:511 (ptrCalldata)
-- * ENC:706-709 Ptr::loc           -> Models.lean:514 (ptrLoc)
-- * ENC:711-714 Ptr::value         -> Models.lean:520 (ptrValue)
-- * ENC:716-721 Display for Ptr    -> Filters.lean:98 (printPtr)
-- * ENC:764-775 Display for Word   -> Filters.lean:104-107 (printWord)
-- * ENC:821-828 fp48_be_to_hi_lo   -> Models.lean:249-250 (fp48ToHiLo, over the
--   48-bit NUMBER rather than the bytes; the byte reading is ported below and
--   fp48BeToHiLo_agreesWithModels_ok pins the two together)
-- * ENC:835-859 g1_to_u256s        -> Models.lean:257-259 (g1Words, which is the
--   M:178-181 caller over the coordinate split; the identity and off-curve
--   branches were NOT ported there and are ported below)
--
-- The Display side is therefore split across three Lean files, which is a
-- maintenance hazard this package cannot fix without editing another package's
-- file: the Rust keeps all of it in one impl block. valueDisplay_arms_ok,
-- ptrDisplay_ok and wordDisplay_ok are written HERE, in the row that owns the
-- Rust file, so that the whole Display surface is gated even though the
-- definitions live elsewhere. Every cite in the list was re-read against ENC:
-- all fifteen land on the item they name, and four of them (Models.lean's
-- Ptr::memory, Ptr::calldata, Ptr::loc and Ptr::value) stop one line short of the
-- closing brace, which is a style difference and not a mis-citation. None points
-- at the wrong file.
--
-- WHAT MOVED, AND WHY (the only two deviations from source order).
--
-- * ENC:604-678 (Value's Default, From<&'static str>, Add<usize>, Sub<usize>) and
--   ENC:743-813 (Word, EcPoint and their impls) sit ABOVE ConstraintSystemMeta
--   and Data here. Lean is order-sensitive and Data (ENC:226-294) has fields of
--   type Word and EcPoint and a constructor that uses Value.add, so the Rust's
--   order cannot be kept. This is the same forced move Protocol.lean records for
--   its hoisted closure; nothing else is reordered.
-- * ENC:33 (type LookupEvalSlots) also moves down, to just after Word, because it
--   is a tuple of Options of Word.
--
-- WHAT THIS FILE DOES NOT PORT, AND WHY.
--
-- * ENC:926-940, the #[cfg(test)] mod tests: one test,
--   eip2537_encoders_accept_identity_points, mapped to
--   eip2537Encoders_acceptIdentity_ok in the gate section. Its two assertions are
--   reproduced exactly; the G1Projective::identity().to_affine() construction is
--   replaced by the ported point model explained at g1AffineRepr, because there
--   is no concrete curve in this tree (Common/Curve.lean's header, D-P1).
-- * ENC:8-29, the use statements. Three of them have no Lean counterpart and the
--   rest are absorbed: Borrow and PrimeCurveAffine disappear with the point model
--   above; PrimeField disappears with the repr model at feToU256; itertools' izip
--   and Itertools::map_into / collect_vec are ported at their sites (izip!
--   truncates to the SHORTEST input, which matters at ENC:377-381 and is gated);
--   U256 is Midfall.Word256 and UintTryFrom is discussed at toU256BeBytes.
--   ConstraintSystem, ProtocolPlan, EvalRead, PermutationZEval, Column, Any,
--   VerifierMemoryLayout, Halo2VerifyingKey and the layout constants all already
--   exist in this tree, in the rows PLAN Section 8 assigns them to, and rule R1
--   forbids a parallel copy.
-- * The two #[cfg(feature)] sites are not in this file: ConstraintSystemMeta's
--   feature-dependent fields are filled by ProtocolPlan, which takes an explicit
--   Features argument (Protocol.lean's PM:348 note). Data::new's dummy-eval
--   behaviour is feature-dependent only through num_dummy_evals, which is a plain
--   field set by set_num_dummy_evals, so R8 needs no branch here.
--
-- HAZARD 1, THE TWO IMPORTED MAP TYPES, AND WHAT I CONCLUDED. ENC:10 imports BOTH
-- BTreeSet and HashMap. Every use of each, found by grep over the whole reference:
--
-- * BTreeSet appears once, at ENC:101 (simple_selector_cols), and it is a clone of
--   ProtocolPlan's field of the same name (ENC:157), which Protocol.lean already
--   models as an ascending duplicate-free List under natCmp. Ported the same way,
--   same comparator, no new machinery.
-- * HashMap appears five times, all of them fields of Data: permutation_comms
--   (ENC:236, built by izip at ENC:377), committed_instance_evals (ENC:258),
--   advice_evals (ENC:259), fixed_evals (ENC:260) and permutation_evals (ENC:261).
--   CONCLUSION: the iteration order is unobservable, so R6's unordered model is
--   allowed, and here is the evidence rather than an assertion. Every read of all
--   five in the whole reference is either a key lookup or an explicitly sorted
--   iteration:
--     kzg/mod.rs:232, :240, :279, :282, :284 - .get(&k) and [&k], key lookups;
--     quotient_direct.rs:115, :121, :129 - .get(&k) inside a slot resolver;
--     quotient_numerator/vm/mod.rs:2915, :2927, :2939 and yul_emit.rs:786, :794,
--       :800, :848, :857, :1052, :1064, :1115, :363 and quotient.rs:1516 - .get;
--     quotient_listing/mod.rs:368, :379, :390 - `for ... in sorted(&data.X)`,
--       i.e. the ONE place that iterates a whole map sorts it first, and :634,
--       :644, :654 are .get. The listing module's own `sorted` helper is the
--       reference admitting that HashMap order is not something it may rely on.
--   The only `.iter()` on a field named permutation_comms is models.rs:419, and
--   that is Halo2VerifyingKey.permutation_comms, a Vec<G1Words> on a different
--   struct (M:296), not this HashMap.
--   So the model is an association list with update-in-place insert and
--   first-match get (hashMapInsert / hashMapGet below), and hashMapModel_ok gates
--   the two behaviours the reference can actually observe.
--
-- DECISIONS RECORDED RATHER THAN TAKEN SILENTLY (rules R3, R4, R5, R6).
--
-- * usize is Nat, i32 is Int, i32 rotations stay SIGNED (rule R5), and Value's
--   offset stays Int because the Rust stores an isize on purpose: ENC:584-588 says
--   the signedness exists so that `ptr - N` can go negative and still render as
--   `sub(0, 0xNN)`. Sub can and does underflow in practice; that is the feature,
--   and valueAddSub_ok pins it rather than clamping it.
-- * Arithmetic on Value and Ptr is plain Rust +-*, so in the release profile it
--   WRAPS at isize bounds (BASELINE.md: no profile overrides, so release has
--   overflow-checks off and debug has them on). Neither is reachable: the operands
--   are byte offsets and word counts of a verifier's memory map, and reaching
--   2^63 needs an address past 2^63. Stated at each of the four sites, not assumed.
-- * Two infinite iterators, Word::range (ENC:749) and EcPoint::range (ENC:797),
--   become index functions Nat -> T rather than Lists, because Lean has no lazy
--   list and rule R10 forbids anything non-terminating. Every Rust consumer
--   applies .take(n) or zips against a finite Vec, so the port takes a length and
--   maps over List.range n, which is the same finite prefix; the truncation
--   behaviour rule R3 cares about is preserved and gated at
--   dataNew_fixture_ok, where the eval zip is the case that could have gone wrong.
-- * Vec is List, following Layout.lean, Models.lean, Protocol.lean and Abi.lean
--   rather than PLAN Section 4's literal "Vec becomes Array" - the same recorded
--   divergence Protocol.lean's header states.
-- * ENC:432's assert_eq! and the seven expect / panic! sites in Data::new are real
--   aborts in the release profile, so they are Fault.panic (rule R4) at their
--   lines. The two debug_assert_eq! in fp48_be_to_hi_lo (ENC:822) and fe_to_u256
--   (ENC:912) are compiled out in release - and in BOTH cases a non-debug panic
--   sits on the next line (copy_from_slice at ENC:824/826 and ENC:914), so the
--   length discipline survives; each site says which line fires.

import Midfall.Generator.Abi
import Midfall.Yul.Externals
import Midfall.Generator.Layout
import Midfall.Generator.Models
import Midfall.Generator.Protocol
import Midfall.Halo2.Exec.Arith

namespace Midfall.Generator
open Midfall Midfall.Halo2

/-! ## Lean scaffolding, not Rust items

The pieces the port needs in order to honour R6 for HashMap and to compare
pointers in gates, without inventing a set type, a BEq instance on a type this
package does not own, or a curve. -/

/-- Rust's HashMap<K, V> as the port needs it: an association list whose insert
    updates an existing key in place and otherwise appends. Update-in-place is
    what HashMap::insert does to the stored value (the bucket order is what it
    does NOT promise, and the header argues nothing reads it). A duplicate key
    never arises in Data::new - each eval read is inserted once - but the
    semantics are ported anyway so a later package that inserts twice gets the
    Rust's last-write-wins and not a two-entry map. -/
def hashMapInsert {α : Type} [BEq α] {β : Type} (k : α) (v : β)
    (xs : List (α × β)) : List (α × β) :=
  if xs.any (fun e => e.1 == k) then
    xs.map fun e => if e.1 == k then (k, v) else e
  else xs ++ [(k, v)]

/-- HashMap::get, and the Index impl's panic case is the caller's, not this one's:
    a missing key is `none` here and the site decides whether that is an expect. -/
def hashMapGet {α : Type} [BEq α] {β : Type} (xs : List (α × β)) (k : α) : Option β :=
  (xs.find? fun e => e.1 == k).map Prod.snd

/-- Vec::get_mut(i) followed by .expect(site), as ENC:453, ENC:461, ENC:468 and
    ENC:480 write it: out of range is a panic at the expect's line, not at the
    get's. -/
def listGetMut {α : Type} (xs : List α) (i : Nat) (site : String) : Except Fault α :=
  match (xs.drop i).head? with
  | some v => Except.ok v
  | none => Except.error (Fault.panic site)

/-- The write half of the same pattern. -/
def listSetMut {α : Type} (xs : List α) (i : Nat) (v : α) (site : String) :
    Except Fault (List α) :=
  if i < xs.length then Except.ok (xs.take i ++ [v] ++ xs.drop (i + 1))
  else Except.error (Fault.panic site)

/-- Location, Value and Ptr carry no BEq (Filters.lean:70, Filters.lean:78,
    Models.lean:503) and this package does not own them, so gates compare pointers
    through this rendering key instead of adding an instance to a foreign type.
    The key is total over the location and the value expression, which is exactly
    the data Ptr carries. -/
def ptrKey (p : Ptr) : String :=
  (match p.loc with
    | Location.calldata => "calldata:"
    | Location.memory => "memory:") ++ printValue p.value


/-- A byte list as the Rust's [u8; N] / &[u8]. -/
def bytesFromNats (bs : List Nat) : Bytes :=
  ByteArray.mk (bs.map fun b => Nat.toUInt8 b).toArray

def bytesToNats (bs : Bytes) : List Nat := bs.data.toList.map UInt8.toNat

/-! ## Value's impl block and the pointer types (rust: ENC:594-678, ENC:743-813)

MOVED ABOVE ConstraintSystemMeta and Data; see the header. Within this section the
Rust's own order is kept. -/

/-- rust: ENC:604-609 (impl Default for Value) @formal-baseline. `Self::Integer(0)`.
    Note this is NOT what Value's #[derive(Default)] would give - there is no
    derive on the enum (ENC:581 derives Clone, Copy, Debug, PartialEq, Eq only),
    so Default exists solely because of this hand-written impl, and Integer is the
    first variant anyway. -/
def valueDefault : Value := Value.integer 0

/-- rust: ENC:611-616 (impl From<&'static str> for Value) @formal-baseline. The
    Rust's &'static str becomes String here, which is the same widening
    Models.lean and Filters.lean already use for identifier names; nothing in the
    ported scope can tell a static string from a fresh one, because the only thing
    done with the name is printing it. -/
def valueFromStr (ident : String) : Value := Value.identifier ident 0

/-- rust: ENC:652-664 (impl Add<usize> for Value) @formal-baseline. HAZARD 3: the
    Rust uses plain +-*, not checked_* or wrapping_* - there is no checked or
    wrapping op anywhere in ENC:652-678 - so in the release profile the isize
    arithmetic wraps and in debug it panics. Neither is reachable: rhs is a word
    count and the offset a memory or calldata offset, so the product is far below
    2^63 for any layout the generator can build. Said at the site per rule R5.
    The multiplication is by WORD_BYTES, i.e. Ptr arithmetic is in WORDS and the
    rendered value is in BYTES - the single most common off-by-0x20 in this file,
    and valueAddSub_ok is what pins it. -/
def Value.add (self : Value) (rhs : Nat) : Value :=
  match self with
  | .integer int => .integer (int + (rhs : Int) * (wordBytes : Int))
  | .identifier name off => .identifier name (off + (rhs : Int) * (wordBytes : Int))

/-- rust: ENC:666-678 (impl Sub<usize> for Value) @formal-baseline. Same
    release-wrapping note as Value.add. This is the op whose result CAN go negative
    in practice - ENC:584-588 documents that the signedness exists for exactly
    that reason - and a negative Value renders as `sub(0, 0xNN)` or
    `sub(name, 0xNN)`, never as a minus sign. -/
def Value.sub (self : Value) (rhs : Nat) : Value :=
  match self with
  | .integer int => .integer (int - (rhs : Int) * (wordBytes : Int))
  | .identifier name off => .identifier name (off - (rhs : Int) * (wordBytes : Int))

/-- rust: ENC:688-694 (Ptr::new) @formal-baseline. The Rust takes
    `impl Into<Value>`; Lean has no coercion, so callers pass the Value and the
    two From impls (valueFromNat at Models.lean:525, valueFromStr above) are
    applied explicitly at the site. -/
def Ptr.new (loc : Location) (value : Value) : Ptr :=
  { loc := loc, value := value }

/-- rust: ENC:723-731 (impl Add<usize> for Ptr) @formal-baseline. `mut self` in,
    new self out; the location is preserved, which is the whole point of the impl
    and what ptrAddSub_ok checks - a port that rebuilt the pointer as
    Ptr.memory would silently turn a calldata read into an mload in the emitted
    Yul. -/
def Ptr.add (self : Ptr) (rhs : Nat) : Ptr :=
  { self with value := Value.add self.value rhs }

/-- rust: ENC:733-741 (impl Sub<usize> for Ptr) @formal-baseline. -/
def Ptr.sub (self : Ptr) (rhs : Nat) : Ptr :=
  { self with value := Value.sub self.value rhs }

/-- rust: ENC:743-744 (struct Word(Ptr)) @formal-baseline. A Rust newtype. The
    Lean field name doubles as ENC:754-757's `ptr()` accessor, which is what
    Models.lean does for Ptr's two accessors. Declared with `where` rather than
    with a parenthesised binder, because in Lean a parenthesised binder on a
    structure is an INDEX and not a field - `structure Word (ptr : Ptr)` would
    make Word a family Ptr -> Type and every `List Word` below would fail. -/
structure Word where
  /-- rust: ENC:744 (the tuple field of struct Word(Ptr)) -/
  ptr : Ptr

/-- rust: ENC:777-782 (impl From<Ptr> for Word) @formal-baseline. -/
def Word.fromPtr (p : Ptr) : Word := { ptr := p }

/-- rust: ENC:754-757 (Word::ptr) @formal-baseline, served by the field
    projection Word.ptr; named here so the R11 checklist has a Lean address for
    it and so dot notation reads the same as the Rust. -/
abbrev Word.ptrOf (w : Word) : Ptr := w.ptr

/-- rust: ENC:758-761 (Word::loc) @formal-baseline. -/
def Word.loc (w : Word) : Location := w.ptr.loc

/-- rust: ENC:748-752 (Word::range) @formal-baseline. The Rust is
    `(0..).map(move |idx| ptr + idx).map_into()` - an INFINITE iterator, which
    becomes an index function (see the header). Note the order of the two
    conversions: the pointer is advanced first and only then wrapped as a Word,
    so the stride is one WORD of the pointer's own location, and `map_into` is
    Word::fromPtr above. -/
def Word.range (w : Word) : Nat → Word :=
  fun idx => Word.fromPtr (Ptr.add w.ptr idx)

/-- Lean scaffolding, not a Rust item: the gate-side key for Word, placed here
    because the type is declared above and ptrKey above that. It is the EMITTED
    YUL text (ENC:764-775's Display), not a structural key, so every Data gate
    below asserts on the bytes the generator would write. EcPoint has no Display
    impl in the Rust, so ecPointKey stays on the ptrKey form. -/
def wordKey (w : Word) : String := printWord w.ptr.loc w.ptr.value

/-- rust: ENC:785-788 (struct EcPoint { base: Ptr }) @formal-baseline. An EIP-2537
    padded G1 handle: four words, ENC:785's doc comment. -/
structure EcPoint where
  /-- rust: ENC:787 (base: Ptr) -/
  base : Ptr

/-- Lean scaffolding, not a Rust item; see wordKey. -/
def ecPointKey (p : EcPoint) : String := ptrKey p.base

/-- rust: ENC:792-795 (EcPoint::new) @formal-baseline; `impl Into<Ptr>` becomes an
    explicit Ptr, as at Ptr.new. -/
def EcPoint.new (base : Ptr) : EcPoint := { base := base }

/-- rust: ENC:808-813 (impl From<Ptr> for EcPoint) @formal-baseline. -/
def EcPoint.fromPtr (p : Ptr) : EcPoint := EcPoint.new p

/-- rust: ENC:797-801 (EcPoint::range) @formal-baseline. The stride is the LITERAL
    4 at ENC:800, not G1_WORDS: the Rust hardcodes it here while ENC:310 and
    ENC:386 use G1_WORDS. Today 4 == G1_WORDS (LM:63) so the three agree, and
    ecPointRange_strideIsLiteralFour_ok pins both the value and the fact that the
    constant is not read from G1_WORDS - a port that "tidied" it to g1WordsCount
    would be a different program if LM:63 ever changed. Infinite iterator, same
    treatment as Word.range. -/
def EcPoint.range (p : EcPoint) : Nat → EcPoint :=
  fun idx => EcPoint.new (Ptr.add p.base (4 * idx))

/-- rust: ENC:803-805 (EcPoint::ptr) @formal-baseline. -/
def EcPoint.ptr (self : EcPoint) : Ptr := self.base

/-- rust: ENC:33 (type LookupEvalSlots) @formal-baseline, moved below Word. The
    four planned slots of one lookup's eval block: multiplicity, the helper list,
    accumulator current, accumulator next. -/
abbrev LookupEvalSlots := Option Word × List (Option Word) × Option Word × Option Word

/-! ## ConstraintSystemMeta (rust: ENC:70-219) -/

/-- rust: ENC:70-132 (struct ConstraintSystemMeta) @formal-baseline. All
    twenty-two fields in source order, #[derive(Debug, Clone, Default)]. The
    ENC:35-68 comment block above the struct is documentation of the proof byte
    layout that PM:408-580 produces; it is not a Rust item, and the two claims in
    it that later code depends on - that the eval block is
    committed-instance + advice + fixed-non-simple + perm_common + perm_set +
    lookup + trash, and that the PCS block is x1, x2, f_com, x3, q_evals, x4, pi -
    are the orders Protocol.lean's fromConstraintSystem_streamOrder_ok pins. -/
structure ConstraintSystemMeta where
  /-- rust: ENC:73 (protocol: ProtocolPlan) - the typed source plan. -/
  protocol : ProtocolPlan
  /-- rust: ENC:75 (num_fixeds: usize) -/
  numFixeds : Nat
  /-- rust: ENC:77 (permutation_columns: Vec<Column<Any>>) -/
  permutationColumns : List Column
  /-- rust: ENC:79 (permutation_chunk_len: usize) -/
  permutationChunkLen : Nat
  /-- rust: ENC:81 (num_lookups: usize) -/
  numLookups : Nat
  /-- rust: ENC:83 (lookup_chunks: Vec<usize>) -/
  lookupChunks : List Nat
  /-- rust: ENC:85 (num_trashcans: usize) -/
  numTrashcans : Nat
  /-- rust: ENC:87 (num_permutation_zs: usize) -/
  numPermutationZs : Nat
  /-- rust: ENC:89 (num_quotients: usize) -/
  numQuotients : Nat
  /-- rust: ENC:91 (advice_queries: Vec<(usize, i32)>) - the historical tuple
      shape, i.e. QueryKey.tuple of PM:37-39, not QueryKey itself. -/
  adviceQueries : List (Nat × Int)
  /-- rust: ENC:93 (instance_queries: Vec<(usize, i32)>) -/
  instanceQueries : List (Nat × Int)
  /-- rust: ENC:94 (num_simple_selectors: usize) -/
  numSimpleSelectors : Nat
  /-- rust: ENC:101 (simple_selector_cols: BTreeSet<usize>) - ascending and
      duplicate-free under natCmp, the same model Protocol.lean uses for
      PM:289. It is a clone of that field (ENC:157), so the two cannot disagree
      unless a caller overwrites one. -/
  simpleSelectorCols : List Nat
  /-- rust: ENC:102 (num_committed_instances: usize) -/
  numCommittedInstances : Nat
  /-- rust: ENC:110 (num_evals: usize) - main evals PLUS the dummy slots once
      set_num_dummy_evals has run; ENC:104-109 is why. -/
  numEvals : Nat
  /-- rust: ENC:116 (num_dummy_evals: usize) -/
  numDummyEvals : Nat
  /-- rust: ENC:121 (num_point_sets: usize) -/
  numPointSets : Nat
  /-- rust: ENC:123 (num_user_advices: Vec<usize>) -/
  numUserAdvices : List Nat
  /-- rust: ENC:125 (num_user_challenges: Vec<usize>) -/
  numUserChallenges : List Nat
  /-- rust: ENC:127 (advice_indices: Vec<usize>) -/
  adviceIndices : List Nat
  /-- rust: ENC:129 (challenge_indices: Vec<usize>) -/
  challengeIndices : List Nat
  /-- rust: ENC:131 (rotation_last: i32) - SIGNED, and negative for every real
      circuit because PM:402 makes it -(blinding_factors + 1). -/
  rotationLast : Int
  deriving BEq

/-- The #[derive(Default)] of ENC:70: every usize zero, every Vec and BTreeSet
    empty, rotation_last 0, and protocol the PM:264 default. -/
def constraintSystemMetaDefault : ConstraintSystemMeta :=
  { protocol := protocolPlanDefault
    numFixeds := 0
    permutationColumns := []
    permutationChunkLen := 0
    numLookups := 0
    lookupChunks := []
    numTrashcans := 0
    numPermutationZs := 0
    numQuotients := 0
    adviceQueries := []
    instanceQueries := []
    numSimpleSelectors := 0
    simpleSelectorCols := []
    numCommittedInstances := 0
    numEvals := 0
    numDummyEvals := 0
    numPointSets := 0
    numUserAdvices := []
    numUserChallenges := []
    adviceIndices := []
    challengeIndices := []
    rotationLast := 0 }

mutual

/-- rust: ENC:141-168 (ConstraintSystemMeta::new) @formal-baseline. Every field
    is a clone or a map of a field of the plan built at ENC:142, and the two
    lazily-populated counters start at 0 (ENC:160-161).

    The Rust's `ProtocolPlan::from_constraint_system(cs, nb)` aborts through
    PM:642's unwrap_or_else on an invalid plan; the ported version returns
    Except, so that abort is what this function's own error is. Rule R4's site is
    inside ProtocolPlan.fromConstraintSystem, not here, so no panic site is
    invented at this line. -/
def ConstraintSystemMeta.new {F : Type} (feat : Features) (cs : ConstraintSystem F)
    (nbCommittedInstances : Nat) : Except Fault ConstraintSystemMeta := do
  let protocol ← ProtocolPlan.fromConstraintSystem feat cs nbCommittedInstances
  Except.ok
    { protocol := protocol
      numFixeds := protocol.numFixeds
      permutationColumns := protocol.permutationColumns
      permutationChunkLen := protocol.permutationChunkLen
      numLookups := protocol.numLookups
      lookupChunks := protocol.lookupChunks
      numTrashcans := protocol.numTrashcans
      numPermutationZs := protocol.numPermutationZs
      numQuotients := protocol.numQuotients
      adviceQueries := protocol.adviceQueries.map QueryKey.tuple
      instanceQueries := protocol.instanceQueries.map QueryKey.tuple
      numSimpleSelectors := protocol.numSimpleSelectors
      simpleSelectorCols := protocol.simpleSelectorCols
      numCommittedInstances := protocol.numCommittedInstances
      numEvals := protocol.numMainEvals
      numDummyEvals := 0
      numPointSets := 0
      numUserAdvices := protocol.numUserAdvices
      numUserChallenges := protocol.numUserChallenges
      adviceIndices := protocol.adviceIndices
      challengeIndices := protocol.challengeIndices
      rotationLast := protocol.rotationLast }

/-- rust: ENC:171-194 (ConstraintSystemMeta::validate_against_protocol)
    @formal-baseline. The `?` at ENC:172 becomes a bind (rule R3), and the two
    `format!` strings are kept verbatim because they are the function's whole
    observable output - a Result<(), String> is read by its caller as text.

    ENC:174-180 sums SEVEN terms and lists num_lookups TWICE (once for the
    multiplicity commitments and once for the accumulators). Dropping either
    occurrence is the mistake this gate exists to catch, and it is invisible to
    any single-phase single-lookup fixture, which is R-30's lesson restated. -/
def ConstraintSystemMeta.validateAgainstProtocol (self : ConstraintSystemMeta) :
    Except String Unit := do
  self.protocol.validate
  let plannedG1s := self.protocol.numCommitments
  let scheduledG1s :=
    (self.numUserAdvices.foldl (fun a b => a + b) 0) + self.numLookups
      + self.numPermutationZs + (self.lookupChunks.foldl (fun a b => a + b) 0)
      + self.numLookups + self.numTrashcans + self.numQuotients
  if plannedG1s != scheduledG1s then
    throw s!"proof G1 read schedule mismatch: protocol={plannedG1s} metadata={scheduledG1s}"
  if self.protocol.numMainEvals != self.numMainEvals then
    throw s!"proof eval read schedule mismatch: protocol={self.protocol.numMainEvals} metadata={self.numMainEvals}"

/-- rust: ENC:198-200 (ConstraintSystemMeta::set_num_point_sets) @formal-baseline.
    `&mut self` becomes a returned record. -/
def ConstraintSystemMeta.setNumPointSets (self : ConstraintSystemMeta) (n : Nat) :
    ConstraintSystemMeta := { self with numPointSets := n }

/-- rust: ENC:208-211 (ConstraintSystemMeta::set_num_dummy_evals)
    @formal-baseline. Two assignments: the counter is SET and num_evals is
    INCREMENTED, which is what keeps num_main_evals stable across the call -
    ENC:216's subtraction then cancels ENC:210's addition. Setting num_evals
    instead of adding to it is the one-token error this gate is for. -/
def ConstraintSystemMeta.setNumDummyEvals (self : ConstraintSystemMeta) (n : Nat) :
    ConstraintSystemMeta :=
  { self with numDummyEvals := n, numEvals := self.numEvals + n }

/-- rust: ENC:216-218 (ConstraintSystemMeta::num_main_evals) @formal-baseline.
    A usize subtraction. It cannot underflow under the file's own call discipline:
    ENC:160 initialises num_dummy_evals to 0 with num_evals at the plan's count,
    and the only writer (ENC:208-211) adds the same n to both, so
    num_evals >= num_dummy_evals always. In the release profile the subtraction
    would WRAP rather than panic if that invariant were broken, and a wrapped
    usize is a number no Nat can show, so the invariant is stated at the site
    rather than relied on silently; numMainEvals_underflow_ok checks the reachable
    domain and the broken case side by side. -/
def ConstraintSystemMeta.numMainEvals (self : ConstraintSystemMeta) : Nat :=
  self.numEvals - self.numDummyEvals

end

/-! ## Data (rust: ENC:226-571) -/

/-- Lean scaffolding, not a Rust item: the seven `mut` bindings of ENC:418-430
    threaded through the eval loop as one record. The Rust's seven locals are
    written independently of each other, so bundling them cannot change anything
    observable; the field order below is the Rust's declaration order. -/
structure DataEvalSlots where
  committedInstanceEvals : List ((Nat × Int) × Word)
  adviceEvals : List ((Nat × Int) × Word)
  fixedEvals : List ((Nat × Int) × Word)
  permutationEvals : List (Column × Word)
  permutationZSlots : List (Option Word × Option Word × Option Word)
  lookupSlots : List LookupEvalSlots
  trashcanSlots : List (Option Word)

/-- rust: ENC:226-294 (struct Data) @formal-baseline. All twenty-five fields in
    source order, #[derive(Debug, Clone)] - no Default and no Eq, which is why
    there is no dataDefault here and why the gates read fields through wordKey and
    ecPointKey rather than comparing whole records. The four HashMap fields are
    association lists; see the hazard-1 argument in the header. -/
structure Data where
  /-- rust: ENC:229 (challenge_mptr: Ptr) -/
  challengeMptr : Ptr
  /-- rust: ENC:231 (theta_mptr: Ptr) -/
  thetaMptr : Ptr
  /-- rust: ENC:234 (fixed_comms: Vec<EcPoint>) -/
  fixedComms : List EcPoint
  /-- rust: ENC:236 (permutation_comms: HashMap<Column<Any>, EcPoint>) -/
  permutationComms : List (Column × EcPoint)
  /-- rust: ENC:238 (advice_comms: Vec<EcPoint>) - phase-packed memory order. -/
  adviceComms : List EcPoint
  /-- rust: ENC:243 (committed_instance_comms: Vec<EcPoint>) -/
  committedInstanceComms : List EcPoint
  /-- rust: ENC:244 (permutation_z_comms: Vec<EcPoint>) -/
  permutationZComms : List EcPoint
  /-- rust: ENC:245 (lookup_m_comms: Vec<EcPoint>) -/
  lookupMComms : List EcPoint
  /-- rust: ENC:246 (lookup_helper_comms: Vec<Vec<EcPoint>>) -/
  lookupHelperComms : List (List EcPoint)
  /-- rust: ENC:247 (lookup_z_comms: Vec<EcPoint>) -/
  lookupZComms : List EcPoint
  /-- rust: ENC:248 (trashcan_comms: Vec<EcPoint>) -/
  trashcanComms : List EcPoint
  /-- rust: ENC:251 (challenges: Vec<Word>) -/
  challenges : List Word
  /-- rust: ENC:254 (instance_eval: Word) -/
  instanceEval : Word
  /-- rust: ENC:258 (committed_instance_evals: HashMap<(usize, i32), Word>) -/
  committedInstanceEvals : List ((Nat × Int) × Word)
  /-- rust: ENC:259 (advice_evals: HashMap<(usize, i32), Word>) -/
  adviceEvals : List ((Nat × Int) × Word)
  /-- rust: ENC:260 (fixed_evals: HashMap<(usize, i32), Word>) -/
  fixedEvals : List ((Nat × Int) × Word)
  /-- rust: ENC:261 (permutation_evals: HashMap<Column<Any>, Word>) -/
  permutationEvals : List (Column × Word)
  /-- rust: ENC:265 (permutation_z_evals: Vec<(Word, Word, Option<Word>)>) - the
      third slot is None exactly for the last set, ENC:262-264. -/
  permutationZEvals : List (Word × Word × Option Word)
  /-- rust: ENC:267 (lookup_evals: Vec<(Word, Vec<Word>, Word, Word)>) -/
  lookupEvals : List (Word × List Word × Word × Word)
  /-- rust: ENC:268 (trashcan_evals: Vec<Word>) -/
  trashcanEvals : List Word
  /-- rust: ENC:270 (computed_quotient_comm: EcPoint) -/
  computedQuotientComm : EcPoint
  /-- rust: ENC:274 (computed_quotient_eval: Word) - the historical name for the
      expected opening scalar of the linearized commitment, per ENC:271-273. -/
  computedQuotientEval : Word
  /-- rust: ENC:279 (comms_mptr_base: Ptr) -/
  commsMptrBase : Ptr
  /-- rust: ENC:284 (reversed_evals_mptr: Ptr) -/
  reversedEvalsMptr : Ptr
  /-- rust: ENC:293 (dummy_eval_words: Vec<Word>) -/
  dummyEvalWords : List Word

/-- Take the first n elements of an index function, i.e. the Rust's
    `iterator.take(n).collect()` for the two infinite iterators. -/
def takeIter {α : Type} (f : Nat → α) (n : Nat) : List α := (List.range n).map f

/-- rust: ENC:302-553 (Data::new) @formal-baseline. The binding table every
    emitter uses. FORCED R2 DEVIATION, recorded: the Rust parameter is `meta`,
    and `meta` is a reserved word in Lean 4.35 (it is a command modifier, so it
    cannot even be a let binder), so the parameter is `meta_` here - the same
    convention Protocol.lean:378-380 uses for the reserved field name `instance`. The ENC:314-360 comment block is the Step-8 layout note and the
    Optimisation-H3 note; the claim in it that the port has to honour is the one at
    ENC:347-354: eval_cptr is a MEMORY pointer (ENC:361), so every Word built from
    it renders as mload and not calldataload, and dataNew_fixture_ok pins that.

    Four binders are underscore-prefixed (_setIdx, _lookupIdx, _chunk, _index):
    each is an `enumerate()` position that reaches only the `panic!` MESSAGE at
    ENC:489-517, and Fault.panic carries a site and no payload
    (Exec/Error.lean:56-58). The sites are still distinct per slot, which is what
    the four dataNew_*Panic gates can therefore pin. -/
def Data.new (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (memory : VerifierMemoryLayout) : Except Fault Data := do
  -- ENC:309-312
  let fixedCommMptr := Ptr.add memory.vkMptr vk.constants.length
  let permutationCommMptr :=
    Ptr.add fixedCommMptr (g1WordsCount * vk.fixedComms.length)
  let challengeMptr := memory.challengeMptr
  let thetaMptr := memory.thetaMptr
  -- ENC:360-367: the memory bases, straight off the layout.
  let reversedEvalsMptr := memory.reversedEvalsMptr
  let evalCptr := reversedEvalsMptr
  let commsMptrBase := memory.commsMptrBase
  let lookupMCommMemBase := memory.lookupMCommsMptrBase
  let permZCommMemBase := memory.permZCommsMptrBase
  let lookupHelperCommMemBase := memory.lookupHelperCommsMptrBase
  let lookupZCommMemBase := memory.lookupZCommsMptrBase
  let trashcanCommMemBase := memory.trashcanCommsMptrBase
  -- ENC:369
  let fixedComms :=
    takeIter (EcPoint.range (EcPoint.fromPtr fixedCommMptr)) meta_.numFixeds
  -- ENC:375-377
  let committedInstanceComms :=
    (List.range meta_.numCommittedInstances).map fun _ =>
      EcPoint.new (ptrMemory (valueFromStr "G1_IDENTITY_MPTR"))
  -- ENC:378-382: izip! over the permutation columns and an INFINITE point range,
  -- so the result length is the column count (rule R3: izip truncates to the
  -- shortest input). Collected into a HashMap, so the pair list below is the map.
  let permutationCommIter := EcPoint.range (EcPoint.fromPtr permutationCommMptr)
  let permutationComms :=
    meta_.permutationColumns.zip
      ((List.range meta_.permutationColumns.length).map permutationCommIter)
  -- ENC:383-388
  let adviceComms := meta_.adviceIndices.map fun idx =>
    EcPoint.fromPtr (Ptr.add commsMptrBase (g1WordsCount * idx))
  -- ENC:389-393
  let lookupMComms :=
    takeIter (EcPoint.range (EcPoint.fromPtr lookupMCommMemBase)) meta_.numLookups
  let permutationZComms :=
    takeIter (EcPoint.range (EcPoint.fromPtr permZCommMemBase)) meta_.numPermutationZs
  -- ENC:394-401: the helper grouping, with its own cursor advanced by
  -- G1_WORDS * chunks after each row. Vec::with_capacity + push is an append.
  let helperResult := meta_.lookupChunks.foldl
    (fun st chunks =>
      let (cursor, acc) := st
      let row := takeIter (EcPoint.range (EcPoint.fromPtr cursor)) chunks
      (Ptr.add cursor (g1WordsCount * chunks), acc ++ [row]))
    (lookupHelperCommMemBase, [])
  let lookupHelperComms := helperResult.snd
  -- ENC:402-406
  let lookupZComms :=
    takeIter (EcPoint.range (EcPoint.fromPtr lookupZCommMemBase)) meta_.numLookups
  let trashcanComms :=
    takeIter (EcPoint.range (EcPoint.fromPtr trashcanCommMemBase)) meta_.numTrashcans
  let computedQuotientComm := EcPoint.new (ptrMemory (valueFromStr "QUOTIENT_MPTR"))
  -- ENC:408-414
  let challenges := meta_.challengeIndices.map fun idx =>
    Word.fromPtr (Ptr.add challengeMptr idx)
  let instanceEval := Word.fromPtr (ptrMemory (valueFromStr "INSTANCE_EVAL_MPTR"))
  -- ENC:419-430: the seven mutable slot collections.
  let slots0 : DataEvalSlots :=
    { committedInstanceEvals := []
      adviceEvals := []
      fixedEvals := []
      permutationEvals := []
      permutationZSlots := List.replicate meta_.numPermutationZs (none, none, none)
      lookupSlots := meta_.lookupChunks.map fun chunks =>
        (none, List.replicate chunks none, none, none)
      trashcanSlots := List.replicate meta_.numTrashcans none }
  -- ENC:432-436: a real assert_eq!, so it aborts in the release profile too.
  if meta_.protocol.proof.evals.length != meta_.numMainEvals then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:432")
  -- ENC:437: zip of the eval plan against Word::range(eval_cptr). The right side
  -- is infinite, so the length is the plan's; a port that zipped against a
  -- shorter list would silently drop the tail reads.
  let evalWordIter := Word.range (Word.fromPtr evalCptr)
  let pairs := meta_.protocol.proof.evals.zip
    ((List.range meta_.protocol.proof.evals.length).map evalWordIter)
  let slots ← pairs.foldlM
    (fun st pair =>
      let (read, word) := pair
      match read with
      | .committedInstance q =>
        Except.ok ({ st with committedInstanceEvals := hashMapInsert q.tuple word st.committedInstanceEvals } : DataEvalSlots)
      | .advice q =>
        Except.ok ({ st with adviceEvals := hashMapInsert q.tuple word st.adviceEvals } : DataEvalSlots)
      | .fixed q =>
        Except.ok ({ st with fixedEvals := hashMapInsert q.tuple word st.fixedEvals } : DataEvalSlots)
      | .permutationCommon column =>
        Except.ok ({ st with permutationEvals := hashMapInsert column word st.permutationEvals } : DataEvalSlots)
      | .permutationZ set kind => do
        -- ENC:452-458: get_mut(set).expect(...) then one of three field writes.
        let cur ← listGetMut st.permutationZSlots set
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:453"
        let slot := match kind with
          | .cur => (some word, cur.2.1, cur.2.2)
          | .next => (cur.1, some word, cur.2.2)
          | .last => (cur.1, cur.2.1, some word)
        let slots ← listSetMut st.permutationZSlots set slot
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:453"
        Except.ok ({ st with permutationZSlots := slots } : DataEvalSlots)
      | .lookupMultiplicity lookup => do
        -- ENC:460-463
        let row ← listGetMut st.lookupSlots lookup
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:461"
        let row2 := (some word, row.2.1, row.2.2.1, row.2.2.2)
        let slots ← listSetMut st.lookupSlots lookup row2
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:461"
        Except.ok ({ st with lookupSlots := slots } : DataEvalSlots)
      | .lookupHelper lookup chunk => do
        -- ENC:464-470: get_mut(lookup).and_then(get_mut(chunk)).expect(...), so
        -- BOTH out-of-range cases abort at ENC:468, and Option::replace writes
        -- some word without touching anything else in the row.
        let row ← listGetMut st.lookupSlots lookup
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:468"
        let helpers := row.2.1
        -- the and_then's get_mut is the bounds check; the write is the replace
        let _slot ← listGetMut helpers chunk
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:468"
        let helpers2 ← listSetMut helpers chunk (some word)
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:468"
        let row2 := (row.1, helpers2, row.2.2.1, row.2.2.2)
        let slots ← listSetMut st.lookupSlots lookup row2
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:468"
        Except.ok ({ st with lookupSlots := slots } : DataEvalSlots)
      | .lookupAccumulator lookup rotation => do
        -- ENC:471-478: rotation 0 fills slot 2, 1 fills slot 3, anything else is
        -- a panic! at ENC:476. The rotation is an i32, so the comparison is
        -- signed; a Nat reading would make -1 a valid index into the else arm.
        let row ← listGetMut st.lookupSlots lookup
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:472"
        let row2 ←
          if rotation == 0 then Except.ok (row.1, row.2.1, some word, row.2.2.2)
          else if rotation == 1 then Except.ok (row.1, row.2.1, row.2.2.1, some word)
          else throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:476")
        let slots ← listSetMut st.lookupSlots lookup row2
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:472"
        Except.ok ({ st with lookupSlots := slots } : DataEvalSlots)
      | .trash index => do
        -- ENC:479-481: get_mut(index).expect(...) then Option::replace, whose
        -- return value the Rust discards; the bounds check is the expect.
        let _cur ← listGetMut st.trashcanSlots index
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:480"
        let slots ← listSetMut st.trashcanSlots index (some word)
          "proofs/solidity-verifier/src/lowering/encoding/mod.rs:480"
        Except.ok ({ st with trashcanSlots := slots } : DataEvalSlots))
    slots0
  -- ENC:485-493: the four unwrap_or_else(panic!) collections. Each missing slot
  -- is a distinct site, so each keeps its own.
  let permutationZEvals ←
    ((List.range slots.permutationZSlots.length).zip slots.permutationZSlots).mapM
      fun (_setIdx, curNextLast) => do
        let cur ← match curNextLast.1 with
          | some w => Except.ok w
          | none => Except.error (Fault.panic
              "proofs/solidity-verifier/src/lowering/encoding/mod.rs:489")
        let next ← match curNextLast.2.1 with
          | some w => Except.ok w
          | none => Except.error (Fault.panic
              "proofs/solidity-verifier/src/lowering/encoding/mod.rs:490")
        Except.ok (cur, next, curNextLast.2.2)
  let lookupEvals ←
    ((List.range slots.lookupSlots.length).zip slots.lookupSlots).mapM
      fun (_lookupIdx, row) => do
        let m ← match row.1 with
          | some w => Except.ok w
          | none => Except.error (Fault.panic
              "proofs/solidity-verifier/src/lowering/encoding/mod.rs:498")
        let helpers ←
          ((List.range row.2.1.length).zip row.2.1).mapM fun (_chunk, helper) =>
            match helper with
            | some w => Except.ok w
            | none => Except.error (Fault.panic
                "proofs/solidity-verifier/src/lowering/encoding/mod.rs:504")
        let z ← match row.2.2.1 with
          | some w => Except.ok w
          | none => Except.error (Fault.panic
              "proofs/solidity-verifier/src/lowering/encoding/mod.rs:508")
        let zNext ← match row.2.2.2 with
          | some w => Except.ok w
          | none => Except.error (Fault.panic
              "proofs/solidity-verifier/src/lowering/encoding/mod.rs:510")
        Except.ok (m, helpers, z, zNext)
  let trashcanEvals ←
    ((List.range slots.trashcanSlots.length).zip slots.trashcanSlots).mapM
      fun (_index, w) =>
        match w with
        | some w => Except.ok w
        | none => Except.error (Fault.panic
            "proofs/solidity-verifier/src/lowering/encoding/mod.rs:517")
  -- ENC:520
  let computedQuotientEval := Word.fromPtr (ptrMemory (valueFromStr "QUOTIENT_EVAL_MPTR"))
  -- ENC:522-552: the struct literal, in the Rust's literal order (which is NOT
  -- the declaration order above - computed_quotient_comm comes before challenges
  -- here). Lean ignores field order in a literal; the order is kept visible by
  -- writing them in this sequence.
  let data : Data :=
    { challengeMptr := challengeMptr
      thetaMptr := thetaMptr
      fixedComms := fixedComms
      permutationComms := permutationComms
      adviceComms := adviceComms
      committedInstanceComms := committedInstanceComms
      permutationZComms := permutationZComms
      lookupMComms := lookupMComms
      lookupHelperComms := lookupHelperComms
      lookupZComms := lookupZComms
      trashcanComms := trashcanComms
      computedQuotientComm := computedQuotientComm
      challenges := challenges
      instanceEval := instanceEval
      committedInstanceEvals := slots.committedInstanceEvals
      adviceEvals := slots.adviceEvals
      fixedEvals := slots.fixedEvals
      permutationEvals := slots.permutationEvals
      permutationZEvals := permutationZEvals
      lookupEvals := lookupEvals
      trashcanEvals := trashcanEvals
      computedQuotientEval := computedQuotientEval
      commsMptrBase := commsMptrBase
      reversedEvalsMptr := reversedEvalsMptr
      -- ENC:547-551: the comment says the caller populates this later, and the
      -- initialiser is an empty Vec.
      dummyEvalWords := [] }
  Except.ok data

/-- rust: ENC:566-571 (Data::set_dummy_eval_words) @formal-baseline. The two
    `+` are Ptr additions, so the stride is WORD_BYTES per slot, and the base is
    reversed_evals_mptr plus num_main_evals words - i.e. the dummy buffer starts
    immediately after the main reversed-evals buffer, exactly as ENC:286-292
    documents. Note the parameter is num_main_evals and NOT num_evals: passing the
    total would skip past the dummy slots themselves. -/
def Data.setDummyEvalWords (self : Data) (numMainEvals n : Nat) : Data :=
  { self with dummyEvalWords :=
      (List.range n).map fun i =>
        Word.fromPtr (Ptr.add self.reversedEvalsMptr (numMainEvals + i)) }

/-! ## The BLS12-381 EIP-2537 encoders (rust: ENC:816-924) -/

/-- rust: LM:76 (`const BLS_FP_BYTES: usize = 48`) @formal-baseline. The value is
    already ported at Midfall/Yul/Externals.lean:217 as `Midfall.Yul.fpBytes`, so
    this is the re-export this row needs rather than a second copy - the pattern
    Protocol.lean sets for the two trace bases (Protocol.lean:360-364).
    eip2537Widths_matchYul_ok pins the identity. -/
def blsFpBytes : Nat := Midfall.Yul.fpBytes

/-- rust: LM:78 (`const EIP2537_FP_PAD_BYTES: usize = 16`) @formal-baseline; same
    note, Midfall/Yul/Externals.lean:221. -/
def eip2537FpPadBytes : Nat := Midfall.Yul.fpPadBytes

/-- rust: ENC:821-828 (fp48_be_to_hi_lo) @formal-baseline, the BYTE reading.
    Models.lean:249-250 already ports this function over the 48-bit NUMBER
    (`coord / 2^256`, `coord % 2^256`); the Rust takes `&[u8]`, and the byte
    reading is what hazard 4 asks for, because it is where an off-by-one nibble is
    invisible to a number-based check. The two are gated against each other at
    fp48BeToHiLo_agreesWithModels_ok.

    HAZARD 4, the layout itself: the high word is the FIRST 16 bytes of the
    big-endian coordinate, right-aligned in a 32-byte word (16 zero pad bytes in
    front of them), and the low word is the LAST 32 bytes. So a 48-byte Fp becomes
    64 bytes with the pad at the very front, and a padded G1 is
    x_hi || x_lo || y_hi || y_lo = 128 bytes, which is what
    Midfall/Yul/Externals.lean:224-226 states from the artifact and what
    Common/Codec.lean:67-69 states from implementors.rs:283-299 ("16 zero bytes
    || x_BE(48) || 16 zero bytes || y_BE(48)"). Those three sources AGREE with
    this port; had any of them disagreed the package would have stopped, per the
    brief.

    Two panics, and the debug_assert is NOT one of them (rule R4, BASELINE.md):
    * ENC:822 debug_assert_eq!(be.len(), BLS_FP_BYTES) is compiled out in the
      release profile, so it is not ported as a check.
    * ENC:824 `&be[..16]` is a slice range and panics on a short input in BOTH
      profiles, and ENC:826 `copy_from_slice(&be[16..])` panics on a length
      mismatch in both profiles. So the length discipline survives the missing
      debug_assert, at two different lines depending on how short the input is:
      under 16 bytes aborts at 824, and 16 to 47 or over 48 aborts at 826. -/
def fp48BeToHiLo (be : List Nat) : Except Fault (Word256 × Word256) := do
  if be.length < eip2537FpPadBytes then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:824")
  if be.length != blsFpBytes then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:826")
  let hiBytes := List.replicate eip2537FpPadBytes 0 ++ be.take eip2537FpPadBytes
  let loBytes := be.drop eip2537FpPadBytes
  Except.ok (bytesToWordBE (bytesFromNats hiBytes), bytesToWordBE (bytesFromNats loBytes))

/-- rust: ENC:882-887, the `pack_fp` closure inside g2_to_u256s, hoisted (the same
    forced move Protocol.lean records for PM:377-398). It is also what ENC:851-856
    does inline for G1: copy the little-endian repr into a fixed array and reverse
    it. The copy is a `copy_from_slice` into an `[u8; BLS_FP_BYTES]`, so a repr of
    any other length panics - at ENC:852 for x and ENC:855 for y in G1, and at
    ENC:884 here. -/
def fp48LeToBe (repr : List Nat) (site : String) : Except Fault (List Nat) := do
  if repr.length != blsFpBytes then throw (Fault.panic site)
  Except.ok repr.reverse

/-- The two facts `g1_to_u256s` reads out of a `G1Affine`: the `coordinates()`
    result, which is `None` for the identity AND for any off-curve point
    (ENC:839-840), and `is_identity()`. midnight-curves' `G1Affine` is not a Lean
    type - there is no concrete BLS12-381 in this tree (Common/Curve.lean's header,
    decision D-P1) - so the point enters the port as exactly the data the function
    inspects, with the coordinates as the 48-byte little-endian `Fp::to_repr()`
    values ENC:833-834 documents.

    This is the same widening Models.lean:252-259 records for `g1_words`, with one
    addition: Models.lean drops the identity and off-curve branches, and this port
    keeps both, because ENC:845-848 is an `assert!` that aborts in the release
    profile and ENC:839-849 is the difference between encoding a corrupted point as
    the identity and refusing to. -/
structure G1AffineRepr where
  /-- `(x.to_repr(), y.to_repr())` as 48 little-endian bytes each, or `none` when
      `coordinates()` returns None. -/
  coordinates : Option (List Nat × List Nat)
  isIdentity : Bool
  deriving BEq

/-- The G2 analogue: `coordinates()` gives an `Fp2` for each of x and y, and ENC:892-895
    reads `x.c0(), x.c1(), y.c0(), y.c1()` in that order. -/
structure G2AffineRepr where
  coordinates : Option ((List Nat × List Nat) × (List Nat × List Nat))
  isIdentity : Bool
  deriving BEq

/-- rust: ENC:835-859 (g1_to_u256s) @formal-baseline. Four words, returned as a
    List of length 4 (the Rust's [U256; 4]).

    The identity arm returns FOUR ZERO WORDS and nothing else, and the assert in
    front of it is the point of ENC:839-844's comment: an off-curve point would
    otherwise be baked into the verifier as an identity commitment. -/
def g1ToU256s (point : G1AffineRepr) : Except Fault (List Word256) := do
  match point.coordinates with
  | none =>
      -- ENC:845-848: assert!(bool::from(point.is_identity()), "refusing to
      -- EIP-2537 encode an off-curve G1 point as the identity")
      unless point.isIdentity do
        throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:845")
      -- ENC:849: [U256::ZERO; 4]
      Except.ok (List.replicate 4 0)
  | some (xRepr, yRepr) => do
      -- ENC:851-856
      let xBe ← fp48LeToBe xRepr
        "proofs/solidity-verifier/src/lowering/encoding/mod.rs:852"
      let yBe ← fp48LeToBe yRepr
        "proofs/solidity-verifier/src/lowering/encoding/mod.rs:855"
      -- ENC:857-859
      let (xHi, xLo) ← fp48BeToHiLo xBe
      let (yHi, yLo) ← fp48BeToHiLo yBe
      Except.ok [xHi, xLo, yHi, yLo]

/-- rust: ENC:867-901 (g2_to_u256s) @formal-baseline. Eight words, in the order
    ENC:901 writes them: x.c0 hi/lo, x.c1 hi/lo, y.c0 hi/lo, y.c1 hi/lo. The
    (c0, c1) order is the EIP-2537 convention ENC:864-867 states, and swapping the
    two components is the mistake g2ToU256s_wordOrder_ok is written to catch - it
    cannot be caught by any length or count check, because the eight words are the
    same eight words either way. -/
def g2ToU256s (point : G2AffineRepr) : Except Fault (List Word256) := do
  match point.coordinates with
  | none =>
      -- ENC:875-878
      unless point.isIdentity do
        throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:875")
      -- ENC:879: [U256::ZERO; 8]
      Except.ok (List.replicate 8 0)
  | some (x, y) => do
      -- ENC:889-895: x = coords.x(), y = coords.y(), then c0/c1 of each.
      let x0 ← fp48LeToBe x.1 "proofs/solidity-verifier/src/lowering/encoding/mod.rs:884"
      let x1 ← fp48LeToBe x.2 "proofs/solidity-verifier/src/lowering/encoding/mod.rs:884"
      let y0 ← fp48LeToBe y.1 "proofs/solidity-verifier/src/lowering/encoding/mod.rs:884"
      let y1 ← fp48LeToBe y.2 "proofs/solidity-verifier/src/lowering/encoding/mod.rs:884"
      -- ENC:897-901
      let (x0Hi, x0Lo) ← fp48BeToHiLo x0
      let (x1Hi, x1Lo) ← fp48BeToHiLo x1
      let (y0Hi, y0Lo) ← fp48BeToHiLo y0
      let (y1Hi, y1Lo) ← fp48BeToHiLo y1
      Except.ok [x0Hi, x0Lo, x1Hi, x1Lo, y0Hi, y0Lo, y1Hi, y1Lo]

/-- rust: ENC:904-915 (fe_to_u256) @formal-baseline. The Rust is generic over
    `F: PrimeField` with a 32-byte repr; the port takes the repr bytes directly,
    because the only thing done with the field element is `to_repr()`. Every call
    site in the reference instantiates F = Fq (vk.rs:109-117, quotient.rs:1493,
    yul_emit.rs:330, vm/mod.rs:4081, evm.rs:36), so nothing is lost.

    ENC:912 is a debug_assert_eq! and so is compiled out in the release profile -
    but ENC:914's `le.copy_from_slice(bytes)` into an `[u8; 32]` panics on a
    length mismatch in BOTH profiles, so the 32-byte discipline is enforced at
    914, not at 912. That is the site the port uses, and it is a different line
    from the one the message names. -/
def feToU256 (repr : List Nat) : Except Fault Word256 := do
  if repr.length != 32 then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/encoding/mod.rs:914")
  -- ENC:915: U256::from_le_bytes
  Except.ok (bytesToWordLE (bytesFromNats repr))

/-- rust: ENC:918-923 (to_u256_be_bytes) @formal-baseline. The Rust is generic
    over `T` with `U256: UintTryFrom<T>`; the only call sites are evm.rs:31-36,
    where T is usize (three times, plus one usize sum) and U256 itself (through
    `flat_map(to_u256_be_bytes)` over `fe_to_u256` results). For every one of
    those the conversion is exact and cannot fail, so the port takes a Nat. A Nat
    at or above 2^256 has NO Rust counterpart - UintTryFrom would fail and
    `U256::from` panics - and `natToBytesBE` truncates to the low 32 bytes rather
    than faulting, which is stated here rather than left to a reader who might
    assume the widths agree. toU256BeBytes_ok pins the domain the reference can
    actually pass. -/
def toU256BeBytes (value : Nat) : List Nat := bytesToNats (natToBytesBE value 32)

end Midfall.Generator


/-! # Known-answer tests

Three kinds of expected value, in descending strength.

The strongest are copied out of the committed artifact or out of the reference's
own tests, and this file does not control either: the Yul strings in
valueDisplay_arms_ok and wordDisplay_ok are the artifact spellings Filters.lean
records (D:586, D:654, D:656 of the tracked poseidon dump), and
g1ToU256s_generator_ok is the reference's own tests.rs:1705-1732 assertion, whose
right-hand side Models.lean pins to the artifact at D:392-395 and D:401-406.

The second kind is the reference's own arithmetic where it is stated as a number
in ENC or LM: the 4-word stride, the 16-byte pad, the 48-byte coordinate, the
identity encodings.

The third kind is derived here - the Data fixture's addresses, the eval-slot
positions - and each such gate says so and shows the derivation.

Per docs/REVIEW.md R-41 every gate names a perturbation inside its own stated
scope, and every one listed was actually run; the record is in the package report. -/

namespace Midfall.Generator.EncodingKats

open Midfall Midfall.Halo2 Midfall.Generator

/-- Reading an Except Fault as "it failed at exactly this panic site". -/
def panickedAtSite {alpha : Type} (e : Except Fault alpha) (site : String) : Bool :=
  match e with
  | .error (Fault.panic s) => s == site
  | _ => false

/-- Reading an Except String as "it failed with this exact message", stronger than
    the reference's own assertions, which only format the string into a larger
    panic. -/
def errIs {alpha : Type} (e : Except String alpha) (want : String) : Bool :=
  match e with
  | .error m => m == want
  | .ok _ => false

def isOk {alpha : Type} (e : Except String alpha) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

/-- FINDING, and the reason these four defs exist: Location and Value
    (Filters.lean:70, Filters.lean:78) and Ptr (Models.lean:503) carry no BEq
    instance, so nothing in this file can write `a == b` on a pointer, and Word
    and EcPoint are built from Ptr. This package does not own those three types and
    did not add instances to them, so the comparators live here as scaffolding.
    They are structural, not rendering-based: valueBeq compares the integer and
    the (name, offset) pair, so two values that print alike but differ structurally
    cannot slip past. The finding for the orchestrator is that Filters.lean and
    Models.lean should derive BEq on those types; every later package that wants to
    test a pointer will otherwise re-invent this. -/
def valueBeq : Value → Value → Bool
  | .integer a, .integer b => a == b
  | .identifier n1 o1, .identifier n2 o2 => n1 == n2 && o1 == o2
  | _, _ => false

def locationBeq : Location → Location → Bool
  | .calldata, .calldata => true
  | .memory, .memory => true
  | _, _ => false

def ptrBeq (a b : Ptr) : Bool := locationBeq a.loc b.loc && valueBeq a.value b.value
def wordBeq (a b : Word) : Bool := ptrBeq a.ptr b.ptr
def wordKeys (ws : List Word) : List String := ws.map wordKey
def ecPointKeys (ps : List EcPoint) : List String := ps.map ecPointKey

/-! ## Hazard 2: the Display surface, byte-exact -/

/-- rust: ENC:626-633 (fmt_hex) as Filters.lean:65-66 ports it. HAZARD 2's core
    trap: the Rust casts with `as usize` BEFORE formatting, so a negative does not
    print a minus - it prints the 2^64 two's complement as a 16-nibble literal.
    The four negative cases are -1, -32, -256 and isize::MIN.

        PERTURBATION RUN: E2 (fmtHex's negative cast removed, so -1 clamps to 0) reddens THIS
    GATE AND NOTHING ELSE in either file - Filters.lean's own fmtHex_kats_ok stays green,
    because every one of its cases is non-negative. The wrap is invisible unless a negative
    is tested. -/
def fmtHex_negativeWrap_ok : Bool :=
  fmtHex (-1) == "0xffffffffffffffff"
    && fmtHex (-32) == "0xffffffffffffffe0"
    && fmtHex (-256) == "0xffffffffffffff00"
    && fmtHex ((-(2 : Int)^63)) == "0x8000000000000000"
    && fmtHex 0 == "0x00"
    && fmtHex 32 == "0x20"

/-- rust: ENC:635-650 (impl Display for Value), all five arms, as Filters.lean:87-93
    ports them. HAZARD 2: this text goes into the generated contract, so
    byte-exactness is the obligation. The artifact spellings are the ones
    Filters.lean cites - `add(p, 0x20)` at D:654, the bare identifier at D:656,
    `sub(NUM_INSTANCE_CPTR, 0x04)` at D:586 - and the negative-INTEGER arm
    (ENC:641) has no dump site of its own, so it is pinned by the value the
    arithmetic actually produces (see valueAddSub_ok) rather than by the artifact.

    The isize::MIN row is the one place where ENC:641's `-*int` wraps in the
    release profile and hands fmt_hex a NEGATIVE number, which is the only path
    from Display to fmt_hex's wrap. Lean's Int negation does not wrap and the two
    readings still agree: -(-2^63) as an isize wraps to -2^63, whose `as usize` is
    2^63, and Lean's exact 2^63 renders the same 16 nibbles. That agreement is
    load-bearing and is why the row is asserted rather than skipped as absurd.

        PERTURBATIONS RUN: E1 (the add/sub identifier arms swapped in Filters.lean) reddens this
    gate, ptrDisplay_ok, wordDisplay_ok, valueAddSub_ok and Filters' own printValue_kats_ok
    and printWord_kats_ok; E22 (the negative-integer arm dropped) reddens this gate,
    valueAddSub_ok and printValue_kats_ok. -/
def valueDisplay_arms_ok : Bool :=
  printValue (Value.integer 0) == "0x00"
    && printValue (Value.integer 32) == "0x20"
    && printValue (Value.integer 0x1000) == "0x1000"
    && printValue (Value.integer (-32)) == "sub(0, 0x20)"
    && printValue (Value.integer (-4)) == "sub(0, 0x04)"
    && printValue (Value.identifier "x" 0) == "x"
    && printValue (Value.identifier "p" 0) == "p"
    && printValue (Value.identifier "p" 32) == "add(p, 0x20)"
    && printValue (Value.identifier "NUM_INSTANCE_CPTR" (-4))
      == "sub(NUM_INSTANCE_CPTR, 0x04)"
    && printValue (Value.integer ((-(2 : Int)^63))) == "sub(0, 0x8000000000000000)"

/-- rust: ENC:716-721 and ENC:764-775 (Display for Ptr and for Word), as
    Filters.lean:98 and Filters.lean:104-107 port them. The pointer's location is
    NOT printed (ENC:719-720 prints only the value) - a real hazard, because a
    calldata pointer and a memory pointer with the same offset render identically,
    and the only thing that separates them downstream is the calldataload/mload
    choice in Word's Display. The last conjunct is that gap stated as a fact.
        PERTURBATION RUN: E1 (printValue's identifier arms swapped) reddens this gate. The
    location-inclusion variant an earlier draft claimed was not run - and printPtr takes no
    location, so it could not be. -/
def ptrDisplay_ok : Bool :=
  printPtr (Value.identifier "VK_MPTR" 0) == "VK_MPTR"
    && printPtr (Value.integer 0x1000) == "0x1000"
    && printPtr (Value.identifier "mptr_end" (-32)) == "sub(mptr_end, 0x20)"

def wordDisplay_ok : Bool :=
  printWord .calldata (Value.identifier "instance_cptr" 0)
    == "calldataload(instance_cptr)"
    && printWord .memory (Value.identifier "p" 0) == "mload(p)"
    && printWord .memory (Value.identifier "mptr_end" (-32))
      == "mload(sub(mptr_end, 0x20))"
    && printWord .calldata (Value.integer 0x64) == "calldataload(0x64)"
    && printWord .calldata (Value.integer 0x100) != printWord .memory (Value.integer 0x100)

/-- rust: ENC:604-609 and ENC:611-616 (Default for Value, From<&'static str>). -/
def valueDefaultAndFromStr_ok : Bool :=
  valueBeq valueDefault (Value.integer 0)
    && valueBeq (valueFromStr "VK_MPTR") (Value.identifier "VK_MPTR" 0)
    && printValue valueDefault == "0x00"
    && printValue (valueFromStr "TRANSCRIPT_MPTR") == "TRANSCRIPT_MPTR"
    && valueBeq (valueFromNat 32) (Value.integer 32)
    && ! valueBeq (valueFromStr "A") (valueFromStr "B")
    && ! valueBeq (Value.integer 0) (Value.identifier "x" 0)

/-! ## Hazard 3: Add<usize> and Sub<usize> on Value and Ptr -/

/-- rust: ENC:652-678 (Add<usize> and Sub<usize> for Value). HAZARD 3's answer:
    the Rust uses PLAIN +-*, not checked_add or wrapping_add - there is no checked
    or wrapping op anywhere in ENC:652-678 - so in the release profile the isize
    arithmetic wraps and in the debug profile it panics, and neither is reachable
    because the operands are word counts of a verifier memory map. Sub CAN and DOES
    produce a negative value in practice: that is what ENC:584-588 documents the
    signedness for, and rows 5-8 are that case, which renders as sub(0, 0xNN) or
    sub(name, 0xNN) and never as a minus sign.

    The stride is WORD_BYTES per unit: Ptr arithmetic is in WORDS and the rendered
    text is in BYTES. A port that forgot the * 0x20 would emit add(p, 0x01) where
    the contract needs add(p, 0x20) - invisible to every count, fatal to the
    generated reader loop.

        PERTURBATIONS RUN: E3 (the word stride dropped from Value.add) reddens this gate,
    ptrAddSub_ok, rangeStrides_ok and four Data gates; E17 (Value.sub's sign flipped)
    reddens this gate and ptrAddSub_ok; E1 and E22 reach it through printValue. The
    Nat-clamping variant an earlier draft claimed was not run separately - E17 is the same
    observable failure. -/
def valueAddSub_ok : Bool :=
  valueBeq (Value.add (Value.integer 0x100) 3) (Value.integer 0x160)
    && valueBeq (Value.sub (Value.integer 0x100) 3) (Value.integer 0xa0)
    && valueBeq (Value.add (Value.identifier "p" 0) 2) (Value.identifier "p" 64)
    && valueBeq (Value.add (Value.identifier "p" 32) 1) (Value.identifier "p" 64)
    && valueBeq (Value.sub (Value.integer 0) 1) (Value.integer (-32))
    && printValue (Value.sub (Value.integer 0) 1) == "sub(0, 0x20)"
    && valueBeq (Value.sub (Value.identifier "X" 4) 1) (Value.identifier "X" (-28))
    && printValue (Value.sub (Value.identifier "X" 4) 1) == "sub(X, 0x1c)"
    && valueBeq (Value.add (Value.integer 7) 0) (Value.integer 7)
    && valueBeq (Value.sub (Value.integer 7) 0) (Value.integer 7)

/-- rust: ENC:723-741 (Add<usize> and Sub<usize> for Ptr). The location is
    preserved by both - the Rust mutates only `self.value` - and a port that
    rebuilt the pointer through Ptr.calldata or Ptr.memory would silently turn an
    mload into a calldataload in the emitted Yul, which is a different program.
        PERTURBATIONS RUN: E18 (Ptr.add rebuilt through Ptr.memory, dropping the location)
    reddens this gate and nothing else; E3 and E17 also reach it. -/
def ptrAddSub_ok : Bool :=
  valueBeq (Ptr.add (ptrCalldata (valueFromNat 0x64)) 2).value (Value.integer (0x64 + 64))
    && locationBeq (Ptr.add (ptrCalldata (valueFromNat 0x64)) 2).loc Location.calldata
    && locationBeq (Ptr.sub (ptrMemory (valueFromNat 0x1000)) 8).loc Location.memory
    && valueBeq (Ptr.sub (ptrMemory (valueFromNat 0x1000)) 8).value (Value.integer 0xf00)
    && ptrBeq (Ptr.add (Ptr.sub (ptrMemory (valueFromNat 0x100)) 1) 1)
      (ptrMemory (valueFromNat 0x100))
    && locationBeq (ptrLoc (ptrMemory (valueFromNat 0))) Location.memory
    && valueBeq (ptrValue (ptrMemory (valueFromNat 0))) (Value.integer 0)

/-! ## Hazard 1: the HashMap model, and the iterators that feed it -/

/-- rust: ENC:418-421 and ENC:439-449 (the five HashMap fields' inserts) against
    the read sites the header enumerates. The model is an association list with
    update-in-place insert and first-match get. Three behaviours are pinned: a
    fresh key appends, a repeated key REPLACES the value in place (HashMap::insert
    semantics - a two-entry list would let a stale value win the find), and a
    missing key is none rather than a panic, because the reference decides at each
    site whether none is an expect.

    The ORDER claim cannot be gated - an unordered model has no order to check -
    so it is argued in the header from every read site in the reference, and what
    this gate does instead is pin the two properties that argument depends on: get
    returns the last value inserted for a key, and the size is the number of
    distinct keys.     PERTURBATIONS RUN: E10 (hashMapInsert always appends) reddens this gate
    and nothing else. NEGATIVE RESULT, reported rather than hidden: E25 (hashMapGet
    returning the LAST match instead of the first) reddens NOTHING, because update-in-place
    insert never leaves two entries under one key, so first-versus-last is not observable in
    this model. An earlier draft claimed it was; that claim was wrong and this replaces it. -/
def hashMapModel_ok : Bool :=
  hashMapInsert (1 : Nat) "a" [] == [(1, "a")]
    && hashMapGet [(1, "a")] 1 == some "a"
    && hashMapInsert 1 "b" [(1, "a"), (2, "c")] == [(1, "b"), (2, "c")]
    && hashMapGet (hashMapInsert 1 "b" [(1, "a")]) 1 == some "b"
    && hashMapGet [(1, "a")] 2 == none
    && (hashMapInsert 3 "d" (hashMapInsert 3 "e" [])).length == 1

/-- rust: ENC:748-752 and ENC:797-801, the two infinite iterators as index
    functions, plus the literal 4 in EcPoint::range (ENC:800). A padded G1's stride
    is FOUR words = 0x80 bytes and a Word's stride is one word = 0x20. Rules out
    the point stride being read as 2 - the BN254-era value ENC:307-308's comment
    says was replaced - and rules out a stride in bytes instead of words.
        PERTURBATIONS RUN: E4 (EcPoint.range's literal 4 -> 2) reddens this gate and
    dataNew_comms_ok; E20 (Word.range with no stride) reddens this gate and
    dataNew_evalSlots_ok; E3 reaches it too. -/
def rangeStrides_ok : Bool :=
  let memBase := ptrMemory (valueFromNat 0)
  let cdBase := ptrCalldata (valueFromNat 0x64)
  let w0 := Word.fromPtr memBase
  let e0 := EcPoint.fromPtr memBase
  ptrBeq (Word.range w0 0).ptr memBase
    && wordBeq (Word.range w0 0) w0
    && ptrBeq (Word.range w0 3).ptr (ptrMemory (valueFromNat 0x60))
    && ptrBeq (EcPoint.range e0 0).base memBase
    && ptrBeq (EcPoint.range e0 1).base (ptrMemory (valueFromNat 0x80))
    && ptrBeq (EcPoint.range e0 3).base (ptrMemory (valueFromNat 0x180))
    && (takeIter (Word.range w0) 0).isEmpty
    && ecPointKeys (takeIter (EcPoint.range e0) 2) == ["memory:0x00", "memory:0x80"]
    && wordKey (Word.fromPtr cdBase) == "calldataload(0x64)"
    && wordKey (Word.fromPtr memBase) == "mload(0x00)"
    && ptrBeq (EcPoint.ptr (EcPoint.new memBase)) memBase
    && wordBeq (Word.fromPtr (Ptr.add memBase 2)) (Word.fromPtr (Word.range w0 2).ptr)

/-! ## ConstraintSystemMeta (rust: ENC:70-219) -/

/-- The fixture constraint system and the meta it derives, from Protocol.lean's
    fixture (Protocol.lean:1078-1106). Degrading to constraintSystemMetaDefault on
    failure is deliberate: every gate below then goes red loudly rather than
    quietly, the pattern Protocol.lean:1111-1114 sets. -/
def metaFixture : ConstraintSystemMeta :=
  match ConstraintSystemMeta.new Features.solidity Midfall.Generator.ProtocolKats.fixtureCs 1 with
  | .ok m => m
  | .error _ => constraintSystemMetaDefault

/-- rust: ENC:141-168, checked field by field against the plan Protocol.lean's own
    fixture gate pins (Protocol.lean:1352-1385). The two lazily-populated counters
    must start at 0 (ENC:160-161), and the two query vectors must be the TUPLE
    form (ENC:154-155 calls QueryKey::tuple), which is why adviceQueries is a
    List (Nat × Int) and not a List QueryKey - the row below pins the negative
    rotation, which is the part a Nat reading would lose.
        PERTURBATION RUN: E29 (num_dummy_evals initialised to 1 instead of 0) reddens this gate
    and seven others, because ENC:432's assert then fails inside Data::new. -/
def constraintSystemMeta_new_fixture_ok : Bool :=
  metaFixture.numFixeds == 2
    && metaFixture.permutationColumns.length == 4
    && metaFixture.permutationChunkLen == 3
    && metaFixture.numLookups == 1
    && metaFixture.lookupChunks == [2]
    && metaFixture.numTrashcans == 1
    && metaFixture.numPermutationZs == 2
    && metaFixture.numQuotients == 4
    && metaFixture.adviceQueries == [(0, 0), (1, 1), (2, (-1)), (3, 0)]
    && metaFixture.instanceQueries == [(0, 0), (1, 0)]
    && metaFixture.numSimpleSelectors == 1
    && metaFixture.simpleSelectorCols == [0]
    && metaFixture.numCommittedInstances == 1
    && metaFixture.numEvals == 21
    && metaFixture.numDummyEvals == 0
    && metaFixture.numPointSets == 0
    && metaFixture.numUserAdvices == [4]
    && metaFixture.numUserChallenges == [0]
    && metaFixture.adviceIndices == [0, 1, 2, 3]
    && metaFixture.challengeIndices == []
    && metaFixture.rotationLast == -10
    && metaFixture.protocol == Midfall.Generator.ProtocolKats.fixturePlan
    && metaFixture.numMainEvals == 21

/-- rust: ENC:171-194 (validate_against_protocol). The clean case, then each of the
    two error strings in full. The G1 sum at ENC:174-180 counts num_lookups TWICE -
    once for the multiplicity commitments and once for the accumulators - and that
    is the likeliest term for a port to drop, so the broken rows each change one
    field and name the resulting number.
        PERTURBATION RUN: E13 (the second num_lookups term dropped from the schedule sum)
    reddens this gate and nothing else - the clean case goes red exactly as predicted, with
    protocol=15 metadata=14. -/
def constraintSystemMeta_validate_ok : Bool :=
  let badG1 : ConstraintSystemMeta := { metaFixture with numQuotients := 5 }
  let badEvals : ConstraintSystemMeta := { metaFixture with numEvals := 22 }
  let badPlan : ConstraintSystemMeta :=
    { metaFixture with protocol := { metaFixture.protocol with numQuotients := 9 } }
  isOk metaFixture.validateAgainstProtocol
    && errIs badG1.validateAgainstProtocol
      "proof G1 read schedule mismatch: protocol=15 metadata=16"
    && errIs badEvals.validateAgainstProtocol
      "proof eval read schedule mismatch: protocol=21 metadata=22"
    -- ENC:172 runs the protocol's own validate FIRST, so a plan that fails it
    -- reports THAT message and never reaches either comparison above
    && ! isOk badPlan.validateAgainstProtocol

/-- rust: ENC:198-218 (the two setters and num_main_evals). The point is the
    INVARIANT ENC:208-211 establishes: setting the dummy count adds the same n to
    num_evals, so num_main_evals is unchanged. The last row is the broken case the
    invariant rules out, asserted rather than left implicit because the reference
    profile WRAPS where Nat saturates: with num_evals = 1 and num_dummy_evals = 3
    the Rust yields 2^64 - 2 and this port yields 0. The divergence is unreachable
    under the file's own discipline, and pinning the value is what keeps it from
    being discovered by a theorem instead.
        PERTURBATIONS RUN: E21 (num_main_evals returns num_evals) reddens this gate and nothing
    else, because the fixture's dummy count is 0 and only the broken-case row can see it;
    E29 reaches it too. -/
def numMainEvals_underflow_ok : Bool :=
  let broken : ConstraintSystemMeta :=
    { metaFixture with numEvals := 1, numDummyEvals := 3 }
  (metaFixture.setNumDummyEvals 3).numMainEvals == 21
    && (metaFixture.setNumDummyEvals 3).numEvals == 24
    && (metaFixture.setNumDummyEvals 3).numDummyEvals == 3
    && (metaFixture.setNumPointSets 4).numPointSets == 4
    && (metaFixture.setNumPointSets 4).numMainEvals == 21
    && broken.numMainEvals == 0

/-! ## Data (rust: ENC:226-571) -/

/-- Test scaffolding, NOT a ported default: Data derives Debug and Clone only
    (ENC:226), so there is no Rust Default for it and this file must not invent one
    a later package could mistake for ENC's. It exists so a failed Data::new
    degrades to a value every gate below rejects loudly instead of a sorry. -/
def dataEmpty : Data :=
  { challengeMptr := ptrMemory (valueFromNat 0)
    thetaMptr := ptrMemory (valueFromNat 0)
    fixedComms := []
    permutationComms := []
    adviceComms := []
    committedInstanceComms := []
    permutationZComms := []
    lookupMComms := []
    lookupHelperComms := []
    lookupZComms := []
    trashcanComms := []
    challenges := []
    instanceEval := Word.fromPtr (ptrMemory (valueFromNat 0))
    committedInstanceEvals := []
    adviceEvals := []
    fixedEvals := []
    permutationEvals := []
    permutationZEvals := []
    lookupEvals := []
    trashcanEvals := []
    computedQuotientComm := EcPoint.new (ptrMemory (valueFromNat 0))
    computedQuotientEval := Word.fromPtr (ptrMemory (valueFromNat 0))
    commsMptrBase := ptrMemory (valueFromNat 0)
    reversedEvalsMptr := ptrMemory (valueFromNat 0)
    dummyEvalWords := [] }

/-- A memory map whose commitment bases are all DISTINCT, which
    LayoutKats.verifierLayoutFixture is not (every base there is 0, which would make
    a wrong base assignment invisible). The addresses are arbitrary; what matters
    is that no two regions overlap, so every EcPoint in the result names the base it
    came from. -/
def memFixture : VerifierMemoryLayout :=
  { Midfall.Generator.LayoutKats.verifierLayoutFixture with
    vkMptr := ptrMemory (valueFromNat 0x4000)
    challengeMptr := ptrMemory (valueFromNat 0x2000)
    thetaMptr := ptrMemory (valueFromNat 0x2200)
    reversedEvalsMptr := ptrMemory (valueFromNat 0x3000)
    commsMptrBase := ptrMemory (valueFromNat 0x5000)
    lookupMCommsMptrBase := ptrMemory (valueFromNat 0x6000)
    permZCommsMptrBase := ptrMemory (valueFromNat 0x6100)
    lookupHelperCommsMptrBase := ptrMemory (valueFromNat 0x6200)
    lookupZCommsMptrBase := ptrMemory (valueFromNat 0x6300)
    trashcanCommsMptrBase := ptrMemory (valueFromNat 0x6400) }

/-- The reference VK of Layout.lean:1485-1495: 39 constants and 2 fixed
    commitments, which is what makes ENC:309-310's two cursor steps visible. -/
def vkFixture : Halo2VerifyingKey := Midfall.Generator.LayoutKats.referenceTestVk

def dataFixture : Data :=
  match Data.new metaFixture vkFixture memFixture with
  | .ok d => d
  | .error _ => dataEmpty

/-- THE COMMITMENT HANDLES, against hand-computed addresses. The derivation, so a
    reviewer can redo it without running anything:
    * fixed_comm_mptr = VK_MPTR + constants.len() words = 0x4000 + 39*0x20 = 0x44e0
      (ENC:309); the stride is 4 words = 0x80, so the two fixed comms are 0x44e0
      and 0x4560.
    * permutation_comm_mptr = 0x44e0 + G1_WORDS * 2 words = 0x45e0 (ENC:310), and
      izip over the FOUR permutation columns gives 0x45e0, 0x4660, 0x46e0, 0x4760 -
      four, not two: the COUNT comes from the columns and the BASE from the fixed
      commitments. Swapping those two is what this row catches, and no length check
      can see it.
    * advice_comms = comms_mptr_base + G1_WORDS * idx for idx in advice_indices =
      [0,1,2,3] (ENC:383-388).
    * the five per-category bases are the memory map's own, each taken meta.num_*
      items (ENC:389-405), and the helper rows advance their own cursor by
      G1_WORDS * chunks per lookup (ENC:397-401).
        PERTURBATIONS RUN: E15 (fixed_comm_mptr advanced by the fixed-comms count instead of the
    constants count) reddens this gate and nothing else; E28 (permutation_comm_mptr advanced
    by vk.permutation_comms rather than vk.fixed_comms) likewise; E3, E4, E9 and E19 reach
    it too. -/
def dataNew_comms_ok : Bool :=
  ecPointKeys dataFixture.fixedComms == ["memory:0x44e0", "memory:0x4560"]
    && (dataFixture.permutationComms.map fun e => ecPointKey e.snd)
      == ["memory:0x45e0", "memory:0x4660", "memory:0x46e0", "memory:0x4760"]
    && dataFixture.permutationComms.length == 4
    && (dataFixture.permutationComms.map fun e => toString e.fst.index)
      == ["0", "1", "2", "3"]
    && ecPointKeys dataFixture.adviceComms
      == ["memory:0x5000", "memory:0x5080", "memory:0x5100", "memory:0x5180"]
    && ecPointKeys dataFixture.permutationZComms == ["memory:0x6100", "memory:0x6180"]
    && ecPointKeys dataFixture.lookupMComms == ["memory:0x6000"]
    && dataFixture.lookupHelperComms.map ecPointKeys == [["memory:0x6200", "memory:0x6280"]]
    && ecPointKeys dataFixture.lookupZComms == ["memory:0x6300"]
    && ecPointKeys dataFixture.trashcanComms == ["memory:0x6400"]
    && ptrKey dataFixture.commsMptrBase == "memory:0x5000"
    && ptrKey dataFixture.reversedEvalsMptr == "memory:0x3000"
    && ptrKey dataFixture.thetaMptr == "memory:0x2200"
    && ptrKey dataFixture.challengeMptr == "memory:0x2000"
    && dataFixture.challenges.isEmpty
    && dataFixture.dummyEvalWords.isEmpty

/-- The four symbolic pointers ENC:376, ENC:406, ENC:414 and ENC:520 build from
    string identifiers, and the ENC:347-354 claim that the eval block is MEMORY
    rather than CALLDATA. A port that used the calldata eval cursor would produce
    21 identical addresses in a different spelling and every count would still be
    right, so the mload claim is asserted over the whole block, not by example.
        PERTURBATIONS RUN: E26 (eval_cptr made a calldata pointer) reddens this gate and
    dataNew_evalSlots_ok; E9 and E19 reach it through the eval words. -/
def dataNew_symbolicPointers_ok : Bool :=
  ecPointKeys dataFixture.committedInstanceComms == ["memory:G1_IDENTITY_MPTR"]
    && dataFixture.committedInstanceComms.length == 1
    && ecPointKey dataFixture.computedQuotientComm == "memory:QUOTIENT_MPTR"
    && wordKey dataFixture.instanceEval == "mload(INSTANCE_EVAL_MPTR)"
    && wordKey dataFixture.computedQuotientEval == "mload(QUOTIENT_EVAL_MPTR)"
    && (dataFixture.adviceEvals.all fun e => (wordKey e.2).startsWith "mload(")
    && (dataFixture.fixedEvals.all fun e => (wordKey e.2).startsWith "mload(")
    && (dataFixture.trashcanEvals.all fun w => (wordKey w).startsWith "mload(")

/-- The eval-read key lists, as strings, so the negative rotation is visible. -/
def queryKeys (xs : List ((Nat × Int) × Word)) : List String :=
  xs.map fun e => s!"{e.1.1},{e.1.2}={wordKey e.2}"

def permZKey (t : Word × Word × Option Word) : String :=
  let last := match t.2.2 with
    | some w => wordKey w
    | none => "-"
  s!"{wordKey t.1}|{wordKey t.2.1}|{last}"

/-- The four slots of one lookup's eval block, as three separate keys, because
    interpolating a List String through s!` renders without the quotes a reviewer
    would expect and that ambiguity has no business being in a gate. -/
def lookupEvalKeys (t : Word × List Word × Word × Word) : List String :=
  [wordKey t.1, wordKey t.2.2.1, wordKey t.2.2.2]

/-- THE EVAL SLOT ASSIGNMENT, ENC:437-483, element by element. The fixture plan's
    21 eval reads are zipped against Word::range(eval_cptr) from 0x3000, so read i
    lands on 0x3000 + i*0x20; the mapping from EvalRead to slot is the whole point
    of the loop and each of the nine arms is pinned by at least one row. The stream
    order is Protocol.lean:1400-1421's, which this file does not control, so a slot
    written to the wrong place shows up here and nowhere else.

    Two rows deserve to be called out. The advice block includes rotation -1, and
    a Nat reading of the key would make that entry unreachable by every later
    .get(&(col, rot)). The permutation-z block gives set 0 a last and set 1 none,
    because PM:491-506 omits Last for the final set - a port that gave both a last
    or neither one changes the generated verifier's row-boundary term and every
    count still matches.

        PERTURBATIONS RUN: E8 (the permutationZ cur/next arms swapped) reddens this gate and
    nothing else; E19 (accumulator rotation 1 written to the current slot) reddens it and
    four siblings; E9 (the eval word iterator shifted by one) reddens five gates including
    this one; E20 and E26 also reach it. -/
def dataNew_evalSlots_ok : Bool :=
  queryKeys dataFixture.committedInstanceEvals == ["0,0=mload(0x3000)"]
    && queryKeys dataFixture.adviceEvals
      == ["0,0=mload(0x3020)", "1,1=mload(0x3040)", "2,-1=mload(0x3060)",
          "3,0=mload(0x3080)"]
    && queryKeys dataFixture.fixedEvals == ["1,0=mload(0x30a0)"]
    && (dataFixture.permutationEvals.map fun e => wordKey e.2)
      == ["mload(0x30c0)", "mload(0x30e0)", "mload(0x3100)", "mload(0x3120)"]
    && (dataFixture.permutationZEvals.map permZKey)
      == ["mload(0x3140)|mload(0x3160)|mload(0x3180)",
          "mload(0x31a0)|mload(0x31c0)|-"]
    && (dataFixture.lookupEvals.map lookupEvalKeys)
      == [["mload(0x31e0)", "mload(0x3240)", "mload(0x3260)"]]
    && (dataFixture.lookupEvals.map fun t => t.2.1.map wordKey)
      == [["mload(0x3200)", "mload(0x3220)"]]
    && wordKeys dataFixture.trashcanEvals == ["mload(0x3280)"]
    && dataFixture.lookupEvals.length == 1
    && dataFixture.permutationZEvals.length == 2
    && dataFixture.trashcanEvals.length == 1
    && (hashMapGet dataFixture.adviceEvals (2, (-1 : Int))).map wordKey
      == some "mload(0x3060)"
    && (hashMapGet dataFixture.adviceEvals (2, 1)).map wordKey == (none : Option String)

/-- The five abort sites of the slot loop and its collects, each provoked by the
    one change that reaches it and nothing earlier. Every case is "the clean fixture
    builds; this variant aborts at THIS line", so a gate that fires for the wrong
    reason - the ENC:432 count assert firing before the slot loop - shows up as a
    site mismatch rather than a silent pass.
        PERTURBATIONS RUN: E30 (the ENC:432 assert deleted) reddens THIS GATE AND NOTHING ELSE,
    which is what makes row 1 evidence rather than a restatement of the count; E9 and E19
    reach it by making the clean fixture abort. -/
def dataNew_panicSites_ok : Bool :=
  let baseEvals := metaFixture.protocol.proof.evals
  let planWith (evals : List EvalRead) : ProofReadPlan := { metaFixture.protocol.proof with evals := evals }
  let metaWith (evals : List EvalRead) (n : Nat) : ConstraintSystemMeta :=
    { metaFixture with numEvals := n, protocol := { metaFixture.protocol with proof := planWith evals } }
  let withExtraEval (r : EvalRead) : ConstraintSystemMeta := metaWith (baseEvals ++ [r]) 22
  let withoutTrash : ConstraintSystemMeta :=
    metaWith (baseEvals.filter fun e => match e with | .trash _ => false | _ => true) 20
  panickedAtSite (Data.new { metaFixture with numEvals := 22 } vkFixture memFixture)
    "proofs/solidity-verifier/src/lowering/encoding/mod.rs:432"
    && panickedAtSite (Data.new (withExtraEval
        (EvalRead.permutationZ 5 PermutationZEval.cur)) vkFixture memFixture)
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:453"
    && panickedAtSite (Data.new (withExtraEval
        (EvalRead.lookupHelper 0 5)) vkFixture memFixture)
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:468"
    && panickedAtSite (Data.new (withExtraEval
        (EvalRead.lookupAccumulator 0 7)) vkFixture memFixture)
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:476"
    && panickedAtSite (Data.new withoutTrash vkFixture memFixture)
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:517"
    && match Data.new metaFixture vkFixture memFixture with
       | .ok _ => true
       | .error _ => false

/-- rust: ENC:566-571 (set_dummy_eval_words). The stride is one word per slot and
    the base is num_main_evals words past REVERSED_EVALS_MPTR, i.e. the dummy
    buffer starts where the main buffer ends - ENC:286-292 says so and ENC:569 is
    the code. Passing num_evals instead of num_main_evals would skip past the whole
    dummy region, and forgetting the word stride would pack the dummies into
    consecutive bytes.
        PERTURBATIONS RUN: E14 (the num_main_evals offset dropped) reddens this gate and nothing
    else; E3, E9, E19 and E29 reach it too. -/
def setDummyEvalWords_ok : Bool :=
  wordKeys (dataFixture.setDummyEvalWords 21 3).dummyEvalWords
    == ["mload(0x32a0)", "mload(0x32c0)", "mload(0x32e0)"]
    && wordKeys (dataFixture.setDummyEvalWords 21 1).dummyEvalWords
      == ["mload(0x32a0)"]
    && (dataFixture.setDummyEvalWords 0 0).dummyEvalWords.isEmpty
    && ptrKey (dataFixture.setDummyEvalWords 21 3).reversedEvalsMptr == "memory:0x3000"

/-! ## Hazard 4: the EIP-2537 byte layout -/

/-- The two widths, pinned against each other AND against the independent reading
    in Midfall/Yul/Externals.lean:217,221 (which cites LM:76 and LM:78 from the
    artifact side) and against Common/Codec.lean:67-69's description of
    implementors.rs:283-299. HAZARD 4 asked for that cross-check; the three sources
    AGREE, and had any of them disagreed this package was to stop and report. The
    last two conjuncts are the arithmetic that makes a padded G1 exactly 0x80 bytes:
    two coordinates, each 16 bytes of pad plus 48 bytes of value.
        PERTURBATION RUN: E31 (eip2537FpPadBytes 16 -> 8) reddens this gate and five byte-layout
    gates at once. -/
def eip2537Widths_matchYul_ok : Bool :=
  blsFpBytes == 48
    && eip2537FpPadBytes == 16
    && blsFpBytes == Midfall.Yul.fpBytes
    && eip2537FpPadBytes == Midfall.Yul.fpPadBytes
    && eip2537FpPadBytes + blsFpBytes == 64
    && 2 * (eip2537FpPadBytes + blsFpBytes) == g1Bytes
    && eip2537FpPadBytes == Midfall.eipPad.size
    && blsFpBytes == 48 && wordBytes == 32

/-- An independent big-endian byte-to-Nat reading, written as a fold rather than by
    calling bytesToWordBE, so the gates that use it do not lean on the function
    under test. -/
def natOfBytesBE (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- rust: ENC:821-828 (fp48_be_to_hi_lo) on a 48-byte input whose bytes are all
    distinct, which is the only kind of input that can see an off-by-one nibble.
    The high word is the FIRST 16 bytes right-aligned - the pad is at the FRONT of
    the word, not the back - and the low word is the LAST 32 bytes. If the pad were
    appended the high word would be
    0x000102030405060708090a0b0c0d0e0f00000000000000000000000000000000, and if the
    split were at 32/16 instead of 16/32 the halves would trade; both are visible
    here and neither is visible to a symmetric input.
        PERTURBATIONS RUN: E5 (the pad appended instead of prepended) reddens this gate,
    fp48BeToHiLo_agreesWithModels_ok, g1ToU256s_generator_ok and g2ToU256s_wordOrder_ok; E31
    reddens it through the width. The take-32 variant an earlier draft claimed was not run;
    E5 is the same class of error. -/
def fp48BeToHiLo_byteLayout_ok : Bool :=
  let be := List.range 48
  match fp48BeToHiLo be with
  | .error _ => false
  | .ok (hi, lo) =>
    hi.toNat == 0x000102030405060708090a0b0c0d0e0f
      && lo.toNat == 0x101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f
      && hi.toNat == natOfBytesBE (List.replicate 16 0 ++ (List.range 16))
      && lo.toNat == natOfBytesBE ((List.range 48).drop 16)
      && bytesToNats (wordToBytesBE hi) == List.replicate 16 0 ++ List.range 16
      && bytesToNats (wordToBytesBE lo) == (List.range 48).drop 16
      && hi.toNat < 2 ^ 128

/-- The two panic sites of fp48_be_to_hi_lo, which are NOT the debug_assert at
    ENC:822 (compiled out in the release profile, BASELINE.md) but the slice range
    at ENC:824 and the copy_from_slice at ENC:826, both of which abort in every
    profile. The split between them is the interesting part: a 15-byte input dies
    at 824 and a 32-byte input dies at 826, so a port that used one site for both
    is wrong in a way only this gate can see.
        PERTURBATIONS RUN: E16 (the two length sites merged onto 826) reddens this gate and
    nothing else; E31 reaches it too. -/
def fp48BeToHiLo_lengthSites_ok : Bool :=
  panickedAtSite (fp48BeToHiLo (List.replicate 15 0))
    "proofs/solidity-verifier/src/lowering/encoding/mod.rs:824"
    && panickedAtSite (fp48BeToHiLo [])
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:824"
    && panickedAtSite (fp48BeToHiLo (List.replicate 32 0))
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:826"
    && panickedAtSite (fp48BeToHiLo (List.replicate 47 0))
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:826"
    && panickedAtSite (fp48BeToHiLo (List.replicate 49 0))
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:826"
    && match fp48BeToHiLo (List.replicate 48 0) with
       | .ok (hi, lo) => hi == 0 && lo == 0
       | .error _ => false

/-- A 48-bit coordinate as the little-endian repr ENC:833-834 says Fp::to_repr
    returns, i.e. the artifact's big-endian bytes reversed. -/
def leRepr (x : Nat) : List Nat := (bytesToNats (natToBytesBE x 48)).reverse

/-- The byte port and the number port of the same function must agree. Models.lean
    splits the 48-bit value at bit 256; ENC splits the byte string at byte 16.
    Those are the same cut only because the value is exactly 48 bytes wide, which
    is what this gate is really asserting - and it asserts it on the two real
    generator coordinates and the two real 2G coordinates, not on a toy value. It
    also asserts that Models' record equals the artifact-pinned G1Words, because
    that is the chain that makes the next gate evidence rather than a tautology.
        PERTURBATIONS RUN: E5 and E31 both redden this gate. The split-at-byte-15 variant
    claimed earlier was not run; E5 is the stronger version of the same mistake. -/
def fp48BeToHiLo_agreesWithModels_ok : Bool :=
  [((g1GeneratorX, g1GeneratorY), templateConstantsDefault.eip2537.g1Generator),
   ((g1DoubleGeneratorX, g1DoubleGeneratorY),
     templateConstantsDefault.eip2537.g1DoubleGenerator)].all fun pair =>
    let x := pair.fst.1
    let y := pair.fst.2
    let g := pair.snd
    match fp48BeToHiLo (bytesToNats (natToBytesBE x 48)),
          fp48BeToHiLo (bytesToNats (natToBytesBE y 48)) with
    | .ok (xHi, xLo), .ok (yHi, yLo) =>
      xHi == (fp48ToHiLo x).1 && xLo == (fp48ToHiLo x).2
        && yHi == (fp48ToHiLo y).1 && yLo == (fp48ToHiLo y).2
        && xHi == g.xHi && xLo == g.xLo && yHi == g.yHi && yLo == g.yLo
    | _, _ => false

/-- rust: ENC:835-859 (g1_to_u256s) on the generator and on twice the generator.
    This is the reference's OWN assertion, tests.rs:1705-1732: g1_to_u256s of the
    generator must equal TemplateConstants::default().eip2537.g1_generator, and
    likewise for 2G, and the two must DIFFER (tests.rs:1728-1731: "a known-answer
    probe whose expected output equals its input tests nothing"). The right-hand
    side here is Models.lean's record of those four words, and Models.lean pins
    THEM to the tracked artifact at D:392-395 and D:401-406 (Models.lean:261-282),
    so this gate is anchored to committed bytes and not to a value this file chose.

    The third conjunct is the shape Common/Codec.lean:67-69 states from
    implementors.rs:283-299 - 16 zero bytes || x_BE(48) || 16 zero bytes ||
    y_BE(48) - re-derived here from the four words rather than quoted. That is the
    hazard-4 cross-check in its strongest form: a nibble off in either direction
    changes the 128-byte stream and reddens it.

        PERTURBATIONS RUN: E27 (y emitted before x) reddens this gate and nothing else - the
    artifact-anchored half of hazard 4; E5 and E31 reach it too. -/
def g1ToU256s_generator_ok : Bool :=
  let gen : G1AffineRepr :=
    { coordinates := some (leRepr g1GeneratorX, leRepr g1GeneratorY), isIdentity := false }
  let dbl : G1AffineRepr :=
    { coordinates := some (leRepr g1DoubleGeneratorX, leRepr g1DoubleGeneratorY),
      isIdentity := false }
  let g := templateConstantsDefault.eip2537.g1Generator
  let d := templateConstantsDefault.eip2537.g1DoubleGenerator
  match g1ToU256s gen, g1ToU256s dbl with
  | .ok ws, .ok wd =>
    ws == [g.xHi, g.xLo, g.yHi, g.yLo]
      && wd == [d.xHi, d.xLo, d.yHi, d.yLo]
      && ws.flatMap (fun w => bytesToNats (natToBytesBE w.toNat 32))
        == List.replicate 16 0 ++ bytesToNats (natToBytesBE g1GeneratorX 48)
          ++ List.replicate 16 0 ++ bytesToNats (natToBytesBE g1GeneratorY 48)
      && ws.length == 4
      && wd != ws
      && ws != List.replicate 4 (0 : Word256)
  | _, _ => false

/-- rust: ENC:933-940 (eip2537_encoders_accept_identity_points), the one test in
    ENC's own test module, transcribed: the identity encodes as four zero words for
    G1 and eight for G2. The construction G1Projective::identity().to_affine()
    becomes coordinates := none with isIdentity := true, which is exactly the two
    facts ENC:838 and ENC:846 read.
        PERTURBATION RUN: E32 (the G1 identity arm returns eight words instead of four) reddens
    this gate and nothing else. -/
def eip2537Encoders_acceptIdentity_ok : Bool :=
  (match g1ToU256s { coordinates := none, isIdentity := true } with
    | .ok ws => ws == List.replicate 4 (0 : Word256) && ws.length == 4
    | .error _ => false)
    && (match g2ToU256s { coordinates := none, isIdentity := true } with
        | .ok ws => ws == List.replicate 8 (0 : Word256) && ws.length == 8
        | .error _ => false)

/-- rust: ENC:845-848 and ENC:875-878, the two assert!s that refuse to bake an
    off-curve point into the verifier as an identity, plus the repr-length panics
    at ENC:852, ENC:855 and ENC:884. The reference's own test suite does NOT cover
    these - eip2537_encoders_accept_identity_points exercises only the accepting
    side - so this gate is doing work the reference is not. The distinction between
    "coordinates() is None because it is the identity" and "because the point is
    corrupt" is the whole content of ENC:839-844's comment, and a port that dropped
    the assert would turn a corrupted s_g2 into a pairing term that is one.
        PERTURBATION RUN: E7 (the ENC:845 assert replaced by pure ()) reddens this gate and
    nothing else - the reference's own suite never touches this path, so this is the only
    thing standing between a dropped assert and a silent identity encoding. -/
def g1ToU256s_rejectsOffCurve_ok : Bool :=
  panickedAtSite (g1ToU256s { coordinates := none, isIdentity := false })
    "proofs/solidity-verifier/src/lowering/encoding/mod.rs:845"
    && panickedAtSite (g2ToU256s { coordinates := none, isIdentity := false })
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:875"
    && panickedAtSite (g1ToU256s
        { coordinates := some (List.replicate 32 0, leRepr g1GeneratorY),
          isIdentity := false })
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:852"
    && panickedAtSite (g1ToU256s
        { coordinates := some (leRepr g1GeneratorX, List.replicate 47 0),
          isIdentity := false })
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:855"
    && panickedAtSite (g2ToU256s
        { coordinates := some ((List.replicate 47 0, leRepr g1GeneratorY),
                               (leRepr g1GeneratorX, leRepr g1GeneratorY)),
          isIdentity := false })
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:884"

/-- A 48-byte big-endian coordinate whose FIRST byte is the tag, so each of the
    four G2 components has a different high word and no two of the eight output
    words can be confused with each other. -/
def bePattern (tag : Nat) : List Nat := [tag] ++ ((List.range 47).map fun i => i + 1)
def lePattern (tag : Nat) : List Nat := (bePattern tag).reverse

/-- rust: ENC:867-901 (g2_to_u256s), the eight-word ORDER. ENC:864-866 states the
    convention - EIP-2537 expects (c0, c1) for both x and y - and ENC:901 writes
    them out. Because all eight words have the same shape, no length check, count
    check or identity test can see a swap: x0 and x1 differ in one byte of the high
    word, so this is exactly the invisible-off-by-one-nibble hazard. The expected
    words are built from a fold over the byte patterns rather than by calling
    fp48BeToHiLo, so the gate does not lean on the function it checks.
        PERTURBATIONS RUN: E6 (x emitted as (c1, c0)) reddens this gate and nothing else; E5 and
    E31 reach it through the halves. -/
def g2ToU256s_wordOrder_ok : Bool :=
  let hiOf (tag : Nat) : Word256 :=
    BitVec.ofNat 256 (natOfBytesBE (List.replicate 16 0 ++ (bePattern tag).take 16))
  let loOf : Word256 := BitVec.ofNat 256 (natOfBytesBE ((List.range 48).drop 16))
  let pt : G2AffineRepr :=
    { coordinates := some ((lePattern 1, lePattern 2), (lePattern 3, lePattern 4)),
      isIdentity := false }
  match g2ToU256s pt with
  | .error _ => false
  | .ok ws =>
    ws.length == 8
      && hiOf 1 != hiOf 2 && hiOf 3 != hiOf 4
      && ws.getD 0 (BitVec.ofNat 256 0) == hiOf 1
      && ws.getD 1 (BitVec.ofNat 256 0) == loOf
      && ws.getD 2 (BitVec.ofNat 256 0) == hiOf 2
      && ws.getD 3 (BitVec.ofNat 256 0) == loOf
      && ws.getD 4 (BitVec.ofNat 256 0) == hiOf 3
      && ws.getD 5 (BitVec.ofNat 256 0) == loOf
      && ws.getD 6 (BitVec.ofNat 256 0) == hiOf 4
      && ws.getD 7 (BitVec.ofNat 256 0) == loOf

/-- rust: ENC:904-915 (fe_to_u256). The repr is LITTLE-endian and the result is the
    value, so byte 0 is the least significant - the opposite of the Fp path above,
    and the two must not be conflated. ENC:912's debug_assert is compiled out in
    release; ENC:914's copy_from_slice is not, so a 31-byte repr aborts at 914 and
    not at 912.
        PERTURBATIONS RUN: E11 (the repr read big-endian) reddens this gate and nothing else;
    E24 (the length check deleted) reddens it too, on the two panic rows. -/
def feToU256_ok : Bool :=
  (match feToU256 ([1] ++ List.replicate 31 0) with
    | .ok w => w.toNat == 1
    | .error _ => false)
    && (match feToU256 (bytesToNats (natToBytesLE 0xdeadbeef 32)) with
        | .ok w => w.toNat == 0xdeadbeef
        | .error _ => false)
    && (match feToU256 (bytesToNats (natToBytesLE Midfall.Yul.blsR 32)) with
        | .ok w => w.toNat == Midfall.Yul.blsR
        | .error _ => false)
    && panickedAtSite (feToU256 (List.replicate 31 0))
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:914"
    && panickedAtSite (feToU256 (List.replicate 33 0))
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:914"

/-- rust: ENC:918-923 (to_u256_be_bytes). The call sites are evm.rs:31-36, i.e.
    the four ABI head words of verifyProof and the instance words, so the shape
    that matters is "32 bytes, most significant first, value right-aligned". The
    2^255 row is the U256 case (evm.rs:36 goes through fe_to_u256 first) and is the
    only row that tells a 32-byte BE encoding from an 8-byte one padded out.
        PERTURBATION RUN: E12 (little-endian emitted) reddens this gate and nothing else. -/
def toU256BeBytes_ok : Bool :=
  toU256BeBytes 0 == List.replicate 32 0
    && toU256BeBytes 1 == List.replicate 31 0 ++ [1]
    && toU256BeBytes 0x40 == List.replicate 31 0 ++ [0x40]
    && toU256BeBytes (2 ^ 255) == [0x80] ++ List.replicate 31 0
    && (toU256BeBytes 5).length == 32
    && (toU256BeBytes 5).getD 31 0 == 5
    && (bytesToWordBE (bytesFromNats (toU256BeBytes 0x1234))).toNat == 0x1234

#eval fmtHex_negativeWrap_ok -- expect true
#eval valueDisplay_arms_ok -- expect true
#eval ptrDisplay_ok -- expect true
#eval wordDisplay_ok -- expect true
#eval valueDefaultAndFromStr_ok -- expect true
#eval valueAddSub_ok -- expect true
#eval ptrAddSub_ok -- expect true
#eval hashMapModel_ok -- expect true
#eval rangeStrides_ok -- expect true
#eval constraintSystemMeta_new_fixture_ok -- expect true
#eval constraintSystemMeta_validate_ok -- expect true
#eval numMainEvals_underflow_ok -- expect true
#eval dataNew_comms_ok -- expect true
#eval dataNew_symbolicPointers_ok -- expect true
#eval dataNew_evalSlots_ok -- expect true
#eval dataNew_panicSites_ok -- expect true
#eval setDummyEvalWords_ok -- expect true
#eval eip2537Widths_matchYul_ok -- expect true
#eval fp48BeToHiLo_byteLayout_ok -- expect true
#eval fp48BeToHiLo_lengthSites_ok -- expect true
#eval fp48BeToHiLo_agreesWithModels_ok -- expect true
#eval g1ToU256s_generator_ok -- expect true
#eval eip2537Encoders_acceptIdentity_ok -- expect true
#eval g1ToU256s_rejectsOffCurve_ok -- expect true
#eval g2ToU256s_wordOrder_ok -- expect true
#eval feToU256_ok -- expect true
#eval toU256BeBytes_ok -- expect true

end Midfall.Generator.EncodingKats
