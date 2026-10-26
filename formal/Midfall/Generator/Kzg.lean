-- |
-- Midfall.Generator.Kzg
--
-- The codegen-time simulation of the verifier's KZG multi-open and the Yul
-- emitter that follows from it: a port of
-- proofs/solidity-verifier/src/lowering/kzg/mod.rs (2226 lines at git HEAD) -
-- every one of its 33 top-level items, including the private helpers and both
-- impl blocks, in source order (rule R1) except for the two moves recorded under
-- DECISIONS below. The plan's item map counted 32; the 33rd is the second impl
-- block (TrackedG1::new), which the map folded into the TrackedG1 row.
--
-- CITATION NOTATION. Six prefixes, each named with its file and its line count,
-- because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites that
-- silently pointed at the wrong file or at a declaration that does not exist:
--
-- * KZ:  proofs/solidity-verifier/src/lowering/kzg/mod.rs (2226 lines at HEAD) -
--   the file this module ports. Working copy and HEAD agree here: the file is
--   unmodified in this tree (git status shows only api.rs), and every range in
--   this file was re-derived from
--   git show HEAD:proofs/solidity-verifier/src/lowering/kzg/mod.rs, not from
--   wc -l on a checkout.
-- * PM:  proofs/solidity-verifier/src/lowering/protocol/mod.rs (1252 lines) -
--   the ProtocolPlan row, for PcsQuerySource and PermutationZEval, which
--   Midfall/Generator/Protocol.lean ports.
-- * ENC: proofs/solidity-verifier/src/lowering/encoding/mod.rs (940 lines) -
--   the Data row: ConstraintSystemMeta, Data, EcPoint, Location, Ptr, Word,
--   ported in Midfall/Generator/Encoding.lean.
-- * AP:  proofs/solidity-verifier/src/lowering/abi/proof.rs (537 lines) -
--   ProofCalldataLayout, whose total_g1_count is the right-hand side of the
--   count check in validate_absorbed_g1_precompile_coverage (hazard 6).
-- * MEM: proofs/solidity-verifier/src/lowering/layout/memory.rs (1603 lines) -
--   VerifierMemoryLayout, FinalMsmShape and PcsMemoryRequirements, ported in
--   Midfall/Generator/Layout.lean.
-- * LM:  proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines) - the
--   byte widths (G1_BYTES, G1_MSM_PAIR_BYTES, G1ADD_INPUT_BYTES, WORD_BYTES,
--   PCS_STATIC_WORKING_WORDS), gas::g1msm_gas (LM:190-200, ported as
--   Midfall.Yul.g1MsmGasPairs in Yul/Externals.lean:648-657) and
--   trace::PCS_SERIALIZED_POINT_SET_BASE (LM:774-786, ported as
--   Trace.pcsSerializedPointSetBase in Layout.lean:1172), all reached through
--   the layout:: import at KZ:45-57.
--
-- Rust paths under proofs/src/ (the verifier crate) are cited in full, never by
-- prefix. This file reaches one of them through an already-ported Lean def: the
-- upstream construct_intermediate_sets that KZ:393-394 names is
-- Midfall/Halo2/Exec/Kzg/Utils.lean, and nothing here calls into it - the whole
-- point of KZ is that it is the GENERATOR's independent re-derivation of the
-- same partition, and the two are only compared by the Phase 4 lemma.
--
-- WHAT THIS FILE DOES NOT PORT, AND WHY.
--
-- * KZ:1928-2226, the #[cfg(test)] mod tests. Rule R8's convention in this repo
--   (Layout.lean's header states it, Protocol.lean's and Encoding.lean's apply
--   it) is that test items are ported where a ported gate needs them and that
--   what is worth keeping is the ASSERTIONS. There are TEN #[test] fns in that
--   module - the inherited header said nine while listing ten, which is the first
--   finding in the RECOVERY section below - and all ten map to gates in the
--   KzgKats namespace:
--     absorbed_g1_coverage_accepts_later_precompile_input (KZ:1954)
--                                       -> validateG1Coverage_accepts_ok
--     absorbed_g1_coverage_rejects_point_without_precompile_input (KZ:1968)
--                                       -> validateG1Coverage_rejects_ok
--     q_eval_roll_strategy_is_single_source_for_planning_and_emission (KZ:1981)
--                                       -> qEvalStrategy_matchesRustTest_ok
--     intermediate_sets_partitions_by_rotation_set (KZ:2021)
--                                       -> constructIntermediateSets_partitions_ok
--     intermediate_sets_dedups_commitments (KZ:2099)
--                                       -> constructIntermediateSets_dedups_ok
--     compute_dummy_queries_emits_no_dummies_when_all_singletons (KZ:2119)
--     compute_dummy_queries_emits_no_dummies_for_aligned_pairs (KZ:2131)
--     compute_dummy_queries_unifies_two_distinct_pairs (KZ:2144)
--     compute_dummy_queries_matches_midnight_singleton_padding (KZ:2174)
--                                       -> computeDummyQueries_fourRustTests_ok
--     augmented_queries_collapse_to_single_set (KZ:2210)
--                                       -> augmentQueries_collapseToSingleSet_ok
--   The three test helpers pt / ev / calldata_ev (KZ:1934-1944) are reproduced as
--   kzgPt / kzgEv / kzgCalldataEv in the Kats namespace, unchanged in meaning.
--   Nothing in that module is asserted more weakly than the Rust asserts it, and
--   two places are asserted MORE strongly: validateG1Coverage_rejects_ok pins the
--   whole error string where the Rust pins two substrings, and
--   qEvalStrategy_matchesRustTest_ok adds the empty-set and below-threshold arms
--   the Rust test does not touch.
-- * KZ:43-57, the use statements. BTreeMap is modelled at its one site (see the
--   hazard 1 note below); every layout:: and encoding:: name is already ported in
--   Layout.lean and Encoding.lean and rule R1 forbids a parallel copy.
-- * The derives. Clone is Lean's value semantics and Debug is not ported anywhere
--   in this row, so Query, CommitmentEntry, IntermediateSets and TrackedG1 carry no
--   derive at all - and no BEq either, because Word and EcPoint carry none (see
--   valueBeq). Where the Rust derives PartialEq and Eq over fields that DO carry
--   instances (DummyQuery, QEvalStrategy) the Lean has deriving BEq.
-- * The doc-comment structure at KZ:2-41 is not translated wholesale. Two claims
--   in it are load-bearing and are carried at their sites instead: the six-step
--   order of KZ:7-21, which is the shape the Phase 4
--   construct_intermediate_sets lemma will be stated over (so the six blocks are
--   emitted in that order and computations_blockOrder_ok pins it), and the
--   "commitments are OnePiece except for the linearization query" claim at
--   KZ:64-67, which is what makes linearization_term_count expand into limbs.
--
-- DECISIONS RECORDED RATHER THAN TAKEN SILENTLY (rules R3, R4, R5, R6, R8).
--
-- * usize is Nat, i32 is Int (rotations stay SIGNED - see sortSets and
--   intMaxOr/intMinOr, where the signedness is observable), u64 is Nat.
-- * Vec is List, following Layout.lean, Models.lean, Protocol.lean, Encoding.lean
--   and Abi.lean rather than PLAN Section 4's literal "Vec becomes Array" - the
--   same recorded divergence Protocol.lean's header states (docs/REVIEW.md R-43
--   F5). Every Vec operation used here - iter, iter_mut, find, position, push,
--   extend, map, filter, filter_map, enumerate, zip, windows, any, all, sum, max,
--   min, take, skip, reverse, flat_map, dedup, sort_unstable, sort_by_key, to_vec,
--   vec![], with_capacity - is order-preserving or order-independent, EXCEPT the
--   BTreeMap below, which is not a Vec and is handled separately.
-- * KZ:460 is the only BTreeMap in the file (verified: BTreeMap occurs at KZ:43,
--   KZ:460 and in the KZ:494 comment and nowhere else) and it is the one real
--   modelling hazard: see hazard 1 below and the btreeMap* scaffolding.
-- * Lean is order-sensitive and KZ:96 calls query_from_plan (KZ:226),
--   assert_permutation_query_order_is_upstream_equivalent (KZ:136) and
--   construct_intermediate_sets_impl (KZ:421), so those FOUR items sit in ONE
--   mutual block. (The inherited header said six items in the mutual block; the
--   cluster is four, and the other two of the "six" are the moved data types
--   below.) The mutual block keeps Rust source order rather than hoisting three
--   definitions above their callers, which is what R1 asks for; Protocol.lean:82-87
--   sets the precedent for exactly this move. Within the mutual block the Rust's
--   order is kept exactly.
-- * The three record types DummyQuery (KZ:301), CommitmentEntry (KZ:397) and
--   IntermediateSets (KZ:408) are MOVED ABOVE the mutual block, in Rust relative
--   order, because Lean cannot declare a structure inside a mutual block and
--   construct_intermediate_sets_impl returns IntermediateSets. compute_dummy_queries
--   and augment_queries_with_dummies move with them so the KZ:301-390 block stays
--   contiguous. Nothing else in the file moves.
-- * Lean reserved words: KZ:96, KZ:136, KZ:226, KZ:545, KZ:558, KZ:580, KZ:587,
--   KZ:650, KZ:723, KZ:752, KZ:765, KZ:789, KZ:802, KZ:862, KZ:908 and KZ:930 all
--   take a parameter named meta, and meta is a Lean command modifier, so the
--   parameter is meta_ at all sixteen sites - the same convention Encoding.lean
--   records for Data.new (Encoding.lean:610-613) and Protocol.lean for instance.
--   This is an R2 exception and every site says so. (The inherited list had KZ:690
--   in place of KZ:752; validate_g1_precompile_coverage takes no meta at all and
--   linearization_term_count does - corrected here, and the Lean signatures match
--   the Rust.)
-- * R4: every assert!, assert_eq!, expect, unwrap and panic! in this file is a
--   Fault.panic at its own line, and every Vec index that can go out of range is
--   listGetMut / listSetMut with a site. The two debug_asserts (KZ:1194
--   debug_assert_eq! on the row width, KZ:1196 debug_assert! on the memory
--   location) are compiled out in the release profile (BASELINE.md:142-143, rule
--   R4) and are recorded rather than ported; the site says which line would have
--   fired and why neither is reachable.
-- * R8: the fewer-point-sets path is a RUNTIME branch here, not a cfg. KZ:547
--   switches on data.dummy_eval_words.is_empty(), and the feature that decides
--   whether that vector is ever filled is outer-fewer-point-sets at
--   lowering/vk.rs:505-509 - which is FALSE in Features.solidity (BASELINE.md:75),
--   so the raw branch is the one the deployed profile takes. Both branches are
--   ported and both are gated: intermediateSets_featureBranch_ok takes the raw
--   branch on the fixture and the augmented branch on a hand-built Data with
--   dummy words. truncated_challenges and trace are plain bool parameters of
--   computations (KZ:934-935, forwarded from artifacts.rs:151-157 where the
--   first is cfg!(feature = "truncated-challenges") = TRUE in the recorded
--   profile (BASELINE.md:74) and the second is a render option), and all four
--   combinations are gated by computations_traceAndTruncationBranches_ok.
--
-- THE SEVEN PLAN HAZARDS, AND WHERE EACH IS ANSWERED.
--
-- 1. The BTreeMap insertion-order trap. KZ:460-467 assigns point_idx_sets.len() as
--    the VALUE and keys the map by a sorted Vec<usize>, so value order is insertion
--    order and iteration order is key order, and the two differ. Every later use is
--    traced at constructIntermediateSetsImpl and the answer is in the report; the
--    gate is hazard1_insertionOrderOk_ok and the anchor gate is
--    anchorIntermediateSetsShape_ok.
-- 2. EcPoint equality is pointer equality, deliberately. Said at
--    constructIntermediateSetsImpl and gated by ecPointEquality_isPointerEquality_ok.
-- 3. The duplicate-query assert_eq at KZ:445. Both arms ported, both gated:
--    duplicateQuery_bothArms_ok.
-- 4. sort_sets keys on (len, original_index). Gated by sortSets_tiebreak_ok on two
--    equal-cardinality sets. See the finding in the RECOVERY section: whether the
--    tiebreak is observable depends on the stability of the sort model, and the
--    inherited insertionSortBy was not stable.
-- 5. remap[c.set_index]. Totality argued at sortSets and gated by
--    sortSets_remapTotality_ok; the panic is ported anyway per R4.
-- 6. validate_absorbed_g1_precompile_coverage is PLAN 13's points_subgroup_checked
--    risk. It is ported unchanged and RUN on the fixture; the fixture PASSES -
--    every one of the seventeen absorbed proof G1 points reaches a G1MSM or the
--    pairing input - so there is no counterexample and the package does not stop.
--    The evidence is validateAbsorbedCoverage_fixture_ok and the answer is in the
--    package report.
-- 7. Feature branches: see the R8 bullet above.
--
-- P-07R RECOVERY. This file was inherited at 1,493 lines from an agent that was
-- stopped mid-write, and it had never been compiled: it did not parse. What was
-- wrong in the inherited text, stated as findings rather than quietly repaired.
--
--   F1  The header claimed the port was "in full" while computations stopped 60%
--       through its body. KZ:1577-1922 (Block 4's tail, Block 5, Block 6 and the
--       block assembly) were missing entirely and are added here.
--   F2  Kzg.lean:1400 was missing a closing parenthesis on the selLines foldlM of
--       the trace block, and KZ:1409's fold had one in the wrong place; together
--       these are the parse error the recovery brief names. Fixed.
--   F3  The trace block's zero-terms arm returned [] where the pair's first
--       component must be a Nat (the pair_idx counter). It would not have
--       elaborated. Fixed to 0, which is what KZ:1319-1328's continue means.
--   F4  Block 4 appended setBlocks, a List (List String), to a List String. The
--       Rust pushes each set's lines into ONE flat Vec; the port now flattens.
--   F5  Block 4 read rotations through points.getD 0 0 in two places, which is a
--       silent default where the Rust indexes points[0] and points[k]. Replaced
--       with the enumerated value (KZ:1556-1560 carries point_k itself) and with a
--       listGetMut panic site (KZ:1497), per R4.
--   F6  insertionSortBy's doc claimed the model is stable; it was not - inserting
--       x after an equal y REVERSES runs of equal keys. sort_sets never saw it
--       because its (len, i) key is total, but the claim was false and the helper
--       is a trap for the next caller. Made stable, and the perturbation that
--       proves the difference is recorded at sortSets_tiebreak_ok.
--   F7  The header's meta_ site list named KZ:690 (no meta parameter) and omitted
--       KZ:752 (which has one). Corrected above.
--   F8  The header's test count said nine; there are ten. Corrected above.
--   F9  The header cited the layout import as KZ:48-55; the use block is KZ:43-57
--       and the layout:: subtree is KZ:48-55, which is what is cited now.
--   F11 The g1Identity doc says "six separate let-bindings in the Rust" and lists
--       KZ:112, 656, 770, 807, 1300 and 1668. There are SEVEN: it omits KZ:1153,
--       comment_g1_identity, which is Block 3's copy and the one the emitted comment
--       at KZ:1163 reads. The port does cover all seven - g1Identity is used at every
--       one of the seven sites - so this is a doc defect and not a behaviour defect,
--       but it is exactly the kind of count a reviewer would check.
--   F12 The linearizationComm doc cites "the two let-bindings KZ:112 and KZ:657";
--       KZ:112 is a g1_identity line. linearization_comm is bound five times, at
--       KZ:657, 771, 808, 1301 and 1669, and the port reaches all five.
--   F10 Nothing in the inherited 1,493 lines had been checked against the Rust. It
--       has now been re-read item by item and the ported bodies agree; the gates
--       below are the evidence, and the two places where the inherited text was
--       semantically wrong rather than merely unparsable are F3 and F4.
--
-- ONE GENUINE WIDENING, FLAGGED RATHER THAN BURIED. KZ:706 formats the unsupported
-- lookup-accumulator rotation into the panic message. Fault.panic carries a site
-- and no payload (docs/REVIEW.md R-43 F2, and Exec/Error.lean:56-58), so the
-- rotation value is not carried; the site string is distinct, which is what the
-- gate can therefore pin. Same loss at KZ:269. The mirror case is KZ:702-707 and
-- KZ:732-735, where the Rust formats a count, a label and a pointer into an
-- Err(String) - there the payload IS carried, because Result<(), String> keeps the
-- string, so both messages are ported byte for byte and gated on their content.

import Midfall.Generator.Encoding
import Midfall.Yul.Externals

namespace Midfall.Generator
open Midfall Midfall.Halo2

/-! ## Port scaffolding for rules R4, R5 and R6

Nothing here is a Rust item. These are the pieces the port needs in order to
honour R6 for the one BTreeMap in this file, to compare pointers and scalars
without adding a BEq instance to a type this package does not own, and to mirror
the i32 range and extremum idioms of the Yul emitter with the SIGNED reading the
Rust actually has. -/

/-- Lean scaffolding, not a Rust item: the derived PartialEq on Value
    (ENC:581-592) and Location (ENC:573-579), which the Rust reads with ==.
    Neither type carries a BEq instance in this tree - Filters.lean:70 and
    Filters.lean:78 declare them without one, and Models.lean:503 does the same
    for Ptr - and this package does not own them, so the comparators are local.
    Encoding.lean hit the identical wall and reported it (its finding at
    Encoding.lean:1073-1082, queued in docs/plans/README.md as "add deriving BEq
    to Location, Value, Ptr"); the difference is that this file needs them inside
    PORTED code, not only inside gates, because KZ:436 and KZ:446 compare
    commitments and evals. They are structural, not rendering-based: two Values
    that print alike but differ structurally cannot slip past. -/
def valueBeq : Value → Value → Bool
  | .integer a, .integer b => a == b
  | .identifier n1 o1, .identifier n2 o2 => n1 == n2 && o1 == o2
  | _, _ => false

/-- Lean scaffolding, not a Rust item; see valueBeq. -/
def locationBeq : Location → Location → Bool
  | .calldata, .calldata => true
  | .memory, .memory => true
  | _, _ => false

/-- Lean scaffolding, not a Rust item; see valueBeq. This is what the Rust's
    derived PartialEq on Ptr (ENC:680) computes: location AND value. -/
def ptrBeq (a b : Ptr) : Bool := locationBeq a.loc b.loc && valueBeq a.value b.value

/-- Lean scaffolding, not a Rust item; see valueBeq. The Rust's derived
    PartialEq on Word (ENC:743) is a newtype over Ptr, so this is Ptr equality. -/
def wordBeq (a b : Word) : Bool := ptrBeq a.ptr b.ptr

/-- Lean scaffolding, not a Rust item; see valueBeq. KZ:436 and KZ:661 compare
    EcPoints, and ENC:785 derives PartialEq on the newtype over Ptr. -/
def ecPointBeq (a b : EcPoint) : Bool := ptrBeq a.base b.base

/-- Lean scaffolding, not a Rust item: element-wise Word equality, which is what
    KZ:214's g.evals == u.evals means on a Vec<Word>. Length must agree too, which
    Vec's derived Eq does and a bare zip-all would not. -/
def wordListBeq (as bs : List Word) : Bool :=
  as.length == bs.length && (as.zip bs).all fun (a, b) => wordBeq a b

/-- Lean scaffolding, not a Rust item: the handle the Rust rebuilds at KZ:112,
    KZ:656, KZ:770, KZ:807, KZ:1153 (as comment_g1_identity), KZ:1300 and KZ:1668 -
    EcPoint::new(Ptr::memory("G1_IDENTITY_MPTR")), the same symbolic pointer ENC:375
    gives every committed-instance commitment. Seven separate let-bindings in the
    Rust, one def here; the value is identical at all seven, so no behaviour can tell
    them apart, and all seven sites use this one. -/
def g1Identity : EcPoint := EcPoint.new (ptrMemory (valueFromStr "G1_IDENTITY_MPTR"))

/-- Rust's Ord on Vec<usize>: lexicographic, shorter prefix first. This is the
    comparator KZ:460's BTreeMap<Vec<usize>, usize> is keyed by, and the reason
    the key list below is kept ascending under it rather than under any other
    order. natCmp is Protocol.lean's usize comparator. -/
def natListCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => match natCmp x y with
    | .eq => natListCmp xs ys
    | o => o

/-- KZ:466 (point_idx_sets.entry(sorted).or_insert(n)) for the ONE BTreeMap in
    this file, modelled per rule R6 as a list of (key, value) pairs kept ascending
    by key under natListCmp. The value is m.length BEFORE the insert, exactly as
    KZ:465-466 computes it, so values are insertion order while the list order is
    key order. That split is hazard 1 and it is the whole reason this is a def
    rather than a List.find: a port that numbered the sets by their position in
    the sorted list is a different program. btreeMapEntryOrInsert_ok pins the
    three behaviours that matter - a repeat does not renumber, a new key takes the
    next value, and the list stays key-sorted. -/
def btreeMapEntryOrInsert (m : List (List Nat × Nat)) (key : List Nat) :
    List (List Nat × Nat) :=
  if m.any fun (k, _) => k == key then m
  else
    let entry := (key, m.length)
    let (pre, post) := m.span fun (k, _) => natListCmp k key == .lt
    pre ++ entry :: post

/-- KZ:477 (point_idx_sets.get(&sorted_indices)). A lookup, so the list order is
    irrelevant to its result - which is the point hazard 1 asks to be traced. -/
def btreeMapGet (m : List (List Nat × Nat)) (key : List Nat) : Option Nat :=
  (m.find? fun (k, _) => k == key).map Prod.snd

/-- Lean scaffolding, not a Rust item: Rust's slice::sort_by_key, which is a STABLE
    sort, so equal keys keep their input order. KZ:520's key is (len, i) and i is
    unique, so stability is not what makes sort_sets deterministic here - but the
    model is stable anyway, because a helper whose doc claims stability and does not
    have it is a trap for the next caller.

    FINDING, FIXED HERE: the inherited insert placed x AFTER an equal y, which
    REVERSES runs of equal keys rather than preserving them - insertionSortBy
    (fun a b => a < b) [(1,:a), (1,:b)] returned the b-run first. sort_sets never
    saw it because its key is total. The clause below puts x before y unless y is
    strictly smaller, which is the stable reading. -/
def insertionSortBy {alpha : Type} (lt : alpha → alpha → Bool) : List alpha → List alpha
  | [] => []
  | x :: xs => insert x (insertionSortBy lt xs)
where
  insert (x : alpha) : List alpha → List alpha
    | [] => [x]
    | y :: ys => if lt y x then y :: insert x ys else x :: y :: ys

/-- Lean scaffolding, not a Rust item: the (len, original_index) key of KZ:520. -/
def lenIndexLt (lens : List Nat) (i j : Nat) : Bool :=
  match natCmp (lens.getD i 0) (lens.getD j 0) with
  | .eq => natCmp i j == .lt
  | .lt => true
  | .gt => false

/-- Lean scaffolding, not a Rust item: the Rust's v.get(i), which this Lean
    toolchain does not expose for List. Used where an index is in range by
    construction and the caller wants an Option rather than a panic. -/
def listGet? {alpha : Type} (xs : List alpha) (i : Nat) : Option alpha :=
  (xs.drop i).head?

/-- Lean scaffolding, not a Rust item: Vec::push onto the i-th inner Vec, as
    KZ:746 (by_set[c.set_index].push(c)) writes it. Out of range is a Rust index
    panic, so it is a Fault.panic here (rule R4) and not a silent append. -/
def pushAt {alpha : Type} (xss : List (List alpha)) (i : Nat) (x : alpha)
    (site : String) : Except Fault (List (List alpha)) := do
  let xs ← listGetMut xss i site
  listSetMut xss i (xs ++ [x]) site

/-- Lean scaffolding, not a Rust item: iterator().max().copied().unwrap_or(d) over
    a List Int, written with an Option fold. The obvious foldl max 0 is WRONG
    here: on [-3, -1] it answers 0, and KZ:992's max_rot would then emit a
    forward walk the Rust does not emit. intMaxOr_minMaxOr_ok pins the case. -/
def intMaxOr (d : Int) (xs : List Int) : Int :=
  (xs.foldl (fun acc x => match acc with | none => x | some m => max m x) (none : Option Int)).getD d

/-- Lean scaffolding, not a Rust item; the min dual of intMaxOr, for KZ:993. -/
def intMinOr (d : Int) (xs : List Int) : Int :=
  (xs.foldl (fun acc x => match acc with | none => x | some m => min m x) (none : Option Int)).getD d

/-- Lean scaffolding, not a Rust item: Rust's a..=b over i32 (KZ:1011), empty when
    b < a. -/
def intRangeInclusive (lo hi : Int) : List Int :=
  if hi < lo then [] else List.range (Int.toNat (hi - lo + 1)) |>.map fun k => lo + Int.ofNat k

/-- Lean scaffolding, not a Rust item: Rust's a..b over i32 (KZ:1021), empty when
    b <= a. -/
def intRange (lo hi : Int) : List Int :=
  if hi <= lo then [] else List.range (Int.toNat (hi - lo)) |>.map fun k => lo + Int.ofNat k

/-- Lean scaffolding, not a Rust item: the 128-bit mask literal of KZ:940, which
    two emission sites interpolate. -/
def truncMask128 : String := "0xffffffffffffffffffffffffffffffff"

/-- Lean scaffolding, not a Rust item: the synthetic linearization commitment, which
    the Rust rebinds five times - KZ:657, 771, 808, 1301 and 1669 - always as
    data.computed_quotient_comm. The identity handle it is paired with at those sites
    is g1Identity above. -/
def linearizationComm (data : Data) : EcPoint := data.computedQuotientComm


/-! ## Query (rust: KZ:68-87) -/

/-- rust: KZ:68-76 (#[derive(Clone, Debug)] struct Query { rotation: i32, comm:
    EcPoint, eval: Word }) @formal-baseline. Field order is the Rust's. Clone is
    Lean's value semantics and Debug is not ported anywhere in this row, so there
    is no derive here at all - and no BEq either, because Word and EcPoint carry
    none (see valueBeq); the comparators the port needs are the local ones above.

    The doc at KZ:63-67 is load-bearing in one place: "the current emitter assumes
    commitments are OnePiece except for the linearization query" is why
    linearization_term_count (KZ:752) expands one Query into
    num_quotients + simple_selector_cols MSM terms and nothing else does. -/
structure Query where
  /-- rust: KZ:71 (rotation: i32) - the opening point is omega^rotation * x. -/
  rotation : Int
  /-- rust: KZ:73 (comm: EcPoint) -/
  comm : EcPoint
  /-- rust: KZ:75 (eval: Word) -/
  eval : Word

/-- rust: KZ:78-87 (impl Query::new) @formal-baseline. Note the Rust's parameter
    order is (comm, rotation, eval) while the FIELD order is (rotation, comm,
    eval); both are kept exactly, because a port that aligned them would silently
    swap two arguments at all nine call sites. query_new_argumentOrder_ok pins it. -/
def Query.new (comm : EcPoint) (rotation : Int) (eval : Word) : Query :=
  { rotation := rotation, comm := comm, eval := eval }

/-- Lean scaffolding, not a Rust item: matches!(source,
    PcsQuerySource::CommittedInstance(_)) at KZ:115. -/
def isCommittedInstanceSource (s : PcsQuerySource) : Bool :=
  match s with
  | .committedInstance _ => true
  | _ => false

/-- Lean scaffolding, not a Rust item: PcsQuerySource::PermutationZ { .. } at
    KZ:145. -/
def isPermutationZSource (s : PcsQuerySource) : Bool :=
  match s with
  | .permutationZ _ _ => true
  | _ => false

/-- Lean scaffolding, not a Rust item: the kind filter of KZ:165-168, Cur | Next. -/
def permZIsCurOrNext (s : PcsQuerySource) : Bool :=
  match s with
  | .permutationZ _ .cur => true
  | .permutationZ _ .next => true
  | _ => false

/-- Lean scaffolding, not a Rust item: the kind filter of KZ:178-180, Last. -/
def permZIsLast (s : PcsQuerySource) : Bool :=
  match s with
  | .permutationZ _ .last => true
  | _ => false

/-! ## The call cluster (rust: KZ:96-123, KZ:136-223, KZ:226-290, KZ:421-510)

ONE mutual block, and the only deviation from source order in this file. KZ:96
calls query_from_plan (KZ:226) and assert_permutation_query_order_is_upstream_
equivalent (KZ:136), and KZ:136 calls construct_intermediate_sets_impl (KZ:421),
so the four are one forward-reference cluster and Lean has no forward reference
outside a mutual block. They are declared together, IN Rust relative order, at
the position of the last of them; every other item keeps its Rust position
exactly. Protocol.lean:82-87 records the same forced move for its impl block. -/

/-! ## The three data types of the cluster (rust: KZ:301-308, KZ:397-414)

MOVED ABOVE the mutual block, and recorded: Lean cannot declare a structure inside
a mutual block, and construct_intermediate_sets_impl (KZ:421) returns
IntermediateSets, so the two record types KZ:397-414 declare have to be in scope
before it. DummyQuery moves with them so that the three sit together in Rust
relative order (KZ:302, KZ:398, KZ:409). Nothing else in the file moves. -/

/-- rust: KZ:301-308 (#[derive(Clone, Debug, PartialEq, Eq)] struct DummyQuery)
    @formal-baseline. deriving BEq because the Rust derives PartialEq and Eq and
    both fields are Nat and Int, which carry instances - unlike Query, whose
    EcPoint and Word fields do not. -/
structure DummyQuery where
  /-- rust: KZ:305 (query_index: usize) - index into the RAW query list whose
      commitment this dummy reuses. -/
  queryIndex : Nat
  /-- rust: KZ:307 (rotation: i32) - SIGNED. -/
  rotation : Int
  deriving BEq

/-- rust: KZ:310-367 (compute_dummy_queries) @formal-baseline. The fewer-point-sets
    helper. The doc's two claims the port has to honour are the grouping key -
    "using the EcPoint identity, which is the underlying memory pointer", i.e.
    ecPointBeq and not a value comparison of a curve point - and the output order,
    "insertion order of groups * insertion order of points", which is what the
    nested flatMap below preserves.

    The skip arm is the deliberate one: a repeated (commitment, rotation) is
    silently skipped here (KZ:336), and eval consistency is enforced upstream in
    construct_intermediate_sets_impl. That split is the same fact hazard 3 is
    about, seen from the other side, and computeDummyQueries_fourRustTests_ok
    reproduces all four of the Rust's tests for it. -/
def computeDummyQueries (queries : List Query) : List DummyQuery :=
  let groups := groupPass queries [] 0
  let union := unionPass groups []
  -- KZ:354-365: outer loop over groups in insertion order, inner loop over the
  -- union in insertion order.
  groups.flatMap fun (idx, existing) =>
    union.filterMap fun p =>
      if existing.any fun r => r == p then none else some { queryIndex := idx, rotation := p }
where
  groupPass : List Query → List (Nat × List Int) → Nat → List (Nat × List Int)
    | [], gs, _ => gs
    | q :: rest, gs, i =>
        -- KZ:327: find the group whose FIRST query has the same commitment. The
        -- stored index is always in range because it is an enumerate position of a
        -- query already consumed; get? makes that explicit instead of inventing a
        -- default EcPoint.
        match gs.findIdx? fun (idx, _) => (listGet? queries idx).any fun c => ecPointBeq c.comm q.comm with
        | none => groupPass rest (gs ++ [(i, [q.rotation])]) (i + 1)
        | some pos =>
            match listGet? gs pos with
            | none => groupPass rest gs (i + 1)
            | some (idx, pts) =>
              if pts.any fun r => r == q.rotation then
                -- KZ:336: Some(_) => continue
                groupPass rest gs (i + 1)
              else
                -- KZ:328-330
                groupPass rest (gs.take pos ++ [(idx, pts ++ [q.rotation])]
                  ++ gs.drop (pos + 1)) (i + 1)
  unionPass : List (Nat × List Int) → List Int → List Int
    | [], u => u
    | (_, pts) :: rest, u =>
        -- KZ:343-352: singletons contribute nothing to the union, and the union
        -- keeps INSERTION order (Vec + contains, not a BTreeSet).
        unionPass rest (if pts.length <= 1 then u
          else pts.foldl (fun acc p => if acc.any fun x => x == p then acc else acc ++ [p]) u)

/-- rust: KZ:369-390 (augment_queries_with_dummies) @formal-baseline. The
    assert_eq at KZ:377-383 is a real abort: the caller must supply exactly as many
    dummy eval Words as compute_dummy_queries produces, and vk.rs:504-516 is the
    only caller that pairs them. Ported per R4 with its own site; the message's two
    counts are lost to Fault.panic's lack of payload (docs/REVIEW.md R-43 F2).

    KZ:386 indexes raw_queries at d.query_index. Totality: every query_index came
    from an enumerate position of the same vec (KZ:326-337), so it is in range;
    ported as listGetMut anyway, per R4. -/
def augmentQueriesWithDummies (rawQueries : List Query) (dummyEvalWords : List Word) :
    Except Fault (List Query) := do
  let dummies := computeDummyQueries rawQueries
  unless dummies.length == dummyEvalWords.length do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:377")
  -- KZ:384: out = raw.to_vec(), then push - so raw first, dummies after, in the
  -- order compute_dummy_queries emitted them. zip truncates to the shorter input
  -- (rule R3), which after the length assert is the same thing.
  let extra ← (dummies.zip dummyEvalWords).mapM fun (d, eval) => do
    let q ← listGetMut rawQueries d.queryIndex "proofs/solidity-verifier/src/lowering/kzg/mod.rs:386"
    pure (Query.new q.comm d.rotation eval)
  pure (rawQueries ++ extra)



/-- rust: KZ:397-405 (#[derive(Clone, Debug)] struct CommitmentEntry)
    @formal-baseline. Field order is the Rust's. No derive: Clone is value
    semantics, Debug is not ported, and there is no PartialEq to port - the Rust
    derives none, which is why the I-6 comparison at KZ:214 spells out the three
    fields it cares about instead of comparing the structs. -/
structure CommitmentEntry where
  /-- rust: KZ:400 (set_index: usize) - index into the SORTED point_sets. -/
  setIndex : Nat
  /-- rust: KZ:402 (comm: EcPoint) - deduplicated. -/
  comm : EcPoint
  /-- rust: KZ:404 (evals: Vec<Word>) - aligned with point_sets[set_index]. -/
  evals : List Word

/-- rust: KZ:407-414 (#[derive(Clone, Debug)] struct IntermediateSets)
    @formal-baseline. This is the shape the Phase 4 lemma is stated over, which is
    why both fields keep the Rust's order and neither is reordered for convenience. -/
structure IntermediateSets where
  /-- rust: KZ:411 (commitments: Vec<CommitmentEntry>) -/
  commitments : List CommitmentEntry
  /-- rust: KZ:413 (point_sets: Vec<Vec<i32>>) - distinct rotation sets, sorted by
      verifier order. -/
  pointSets : List (List Int)

mutual

/-- rust: KZ:96-123 (queries) @formal-baseline. FORCED R2 DEVIATION, recorded: the
    Rust parameter is meta, reserved in Lean 4.35, so it is meta_ here (see the
    header).

    Three things happen in this order and the order is the Rust's: resolve every
    planned source (KZ:97-103), then the L-2 identity-pin assertion (KZ:104-120),
    then the I-6 permutation-order assertion (KZ:121). The first assert is what
    makes the MSM emitters' habit of skipping identity commitments sound, and the
    second is what makes the generator's interleaved Cur/Next/Last order match
    upstream's grouped order. queries_identityPin_ok gates the first assert's two
    arms and assertPermutationOrder_bothArms_ok gates the second one. -/
def queries (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault (List Query) := do
  -- KZ:97-103: map + collect, order-preserving.
  let queries ← meta_.protocol.pcsQueries.mapM (fun source => queryFromPlan source meta_ data)
  -- KZ:112 is g1Identity above. KZ:113-120: zip is same-length here (queries is a
  -- map over the same vec), and the Rust asserts per pair in order; since
  -- Fault.panic carries no payload (docs/REVIEW.md R-43 F2) the first failure and
  -- an any-match abort are the same observable event, so this is one any.
  if (meta_.protocol.pcsQueries.zip queries).any fun (source, q) =>
      ecPointBeq q.comm g1Identity && ! isCommittedInstanceSource source then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:114")
  assertPermutationQueryOrderIsUpstreamEquivalent meta_ data queries
  return queries

/-- rust: KZ:136-223 (assert_permutation_query_order_is_upstream_equivalent)
    @formal-baseline. The I-6 guard: it re-derives the intermediate sets under the
    UPSTREAM permutation ordering - all (Cur, Next) pairs in forward set order,
    then the Last openings in REVERSE set order - and refuses to plan a circuit
    where the two structures differ.

    Four abort sites, each at its own line: the contiguity assert (KZ:151-154), the
    point_sets equality (KZ:200-205), the commitment-count equality (KZ:206-211)
    and the per-commitment equality (KZ:212-222). The early return at KZ:148-150 is
    kept (rule R3).

    Two faithfulness notes a reviewer will look for. (1) KZ:188 clones the WHOLE
    source vec and KZ:189-191 overwrite only the z slots, so a non-z query keeps
    its position; listSetMut models that exactly, and a port that rebuilt the vec
    from the block alone would drop every advice query. (2) KZ:189's zip truncates
    to the shorter of z_positions and upstream_block (rule R3). They are equal
    length by construction - upstream_block is a Cur|Next filter plus a reversed
    Last filter of the same vec, and every PermutationZ source has exactly one
    kind - but the truncation is modelled anyway rather than assumed away. -/
def assertPermutationQueryOrderIsUpstreamEquivalent (meta_ : ConstraintSystemMeta)
    (data : Data) (generatorOrder : List Query) : Except Fault Unit := do
  let sources := meta_.protocol.pcsQueries
  -- KZ:142-147
  let zPositions := ((List.range sources.length).zip sources).filterMap
    fun (i, s) => if isPermutationZSource s then some i else none
  -- KZ:148-150
  if zPositions.isEmpty then return ()
  -- KZ:151-154: windows(2).all(|w| w[1] == w[0] + 1). Zipping a list against its
  -- own tail is the same set of pairs and truncates the same way.
  unless (zPositions.zip zPositions.tail).all fun (a, b) => b == a + 1 do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:152")
  -- KZ:158
  let zSources ← zPositions.mapM (fun i => listGetMut sources i "proofs/solidity-verifier/src/lowering/kzg/mod.rs:158")
  -- KZ:159-186
  let upstreamBlock :=
    (zSources.filter permZIsCurOrNext) ++ ((zSources.filter permZIsLast).reverse)
  -- KZ:188-191
  let upstreamSources ← (zPositions.zip upstreamBlock).foldlM
    (fun acc (slot, source) => listSetMut acc slot source "proofs/solidity-verifier/src/lowering/kzg/mod.rs:190") sources
  -- KZ:192-196
  let upstreamQueries ← upstreamSources.mapM (fun source => queryFromPlan source meta_ data)
  -- KZ:198-199
  let generatorSets ← constructIntermediateSetsImpl generatorOrder
  let upstreamSets ← constructIntermediateSetsImpl upstreamQueries
  -- KZ:200-205
  unless generatorSets.pointSets == upstreamSets.pointSets do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:201")
  -- KZ:206-211
  unless generatorSets.commitments.length == upstreamSets.commitments.length do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:207")
  -- KZ:212-222. The Rust's assert! is a conjunction of three comparisons and its
  -- message names the commitment and both set indices; the conjunction is ported
  -- whole because nothing downstream reads WHICH conjunct failed.
  for (g, u) in generatorSets.commitments.zip upstreamSets.commitments do
    unless g.setIndex == u.setIndex && ecPointBeq g.comm u.comm
        && wordListBeq g.evals u.evals do
      throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:214")

/-- rust: KZ:226-290 (query_from_plan) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. The ten arms are the ten PcsQuerySource variants in the
    Rust's match order, and each arm reads the Data field the Rust reads - which
    is the whole content of the item, so queryFromPlan_allArms_ok pins all ten
    against hand-computed addresses.

    Abort sites, each at its own line: the four HashMap expect / index reads
    (KZ:234, KZ:242, KZ:279, KZ:282, KZ:284), the permutation Last Option expect
    (KZ:251), the unsupported lookup-accumulator rotation panic (KZ:269), and the
    Vec indices (KZ:229, KZ:237, KZ:245, KZ:254, KZ:257, KZ:258, KZ:261, KZ:262
    twice, KZ:265, KZ:271, KZ:274 twice, KZ:277). KZ:282 and KZ:284 are HashMap
    Index ([&k]), which panics on a missing key rather than returning an Option,
    so they are Fault.panic and not a default.

    KZ:269's message interpolates the offending rotation; Fault.panic carries a
    site and no payload (docs/REVIEW.md R-43 F2), so the value is not carried. The
    site is distinct, which is what queryFromPlan_panics_ok can pin. -/
def queryFromPlan (source : PcsQuerySource) (meta_ : ConstraintSystemMeta) (data : Data) :
    Except Fault Query := do
  match source with
  | .advice q =>
      let comm ← listGetMut data.adviceComms q.column "proofs/solidity-verifier/src/lowering/kzg/mod.rs:229"
      match hashMapGet data.adviceEvals q.tuple with
      | some eval => pure (Query.new comm q.rotation eval)
      | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:234")
  | .committedInstance q =>
      let comm ← listGetMut data.committedInstanceComms q.column "proofs/solidity-verifier/src/lowering/kzg/mod.rs:237"
      match hashMapGet data.committedInstanceEvals q.tuple with
      | some eval => pure (Query.new comm q.rotation eval)
      | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:242")
  | .permutationZ set kind =>
      let (zCur, zNext, zLast) ← listGetMut data.permutationZEvals set "proofs/solidity-verifier/src/lowering/kzg/mod.rs:245"
      let (rotation, eval) ← match kind with
        | .cur => pure (0, zCur)
        | .next => pure (1, zNext)
        | .last => match zLast with
          | some e => pure (meta_.rotationLast, e)
          | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:251")
      let comm ← listGetMut data.permutationZComms set "proofs/solidity-verifier/src/lowering/kzg/mod.rs:254"
      pure (Query.new comm rotation eval)
  | .lookupMultiplicity lookup =>
      let (mEval, _, _, _) ← listGetMut data.lookupEvals lookup "proofs/solidity-verifier/src/lowering/kzg/mod.rs:257"
      let comm ← listGetMut data.lookupMComms lookup "proofs/solidity-verifier/src/lowering/kzg/mod.rs:258"
      pure (Query.new comm 0 mEval)
  | .lookupHelper lookup chunk =>
      let (_, hEvals, _, _) ← listGetMut data.lookupEvals lookup "proofs/solidity-verifier/src/lowering/kzg/mod.rs:261"
      let helpers ← listGetMut data.lookupHelperComms lookup "proofs/solidity-verifier/src/lowering/kzg/mod.rs:262"
      let comm ← listGetMut helpers chunk "proofs/solidity-verifier/src/lowering/kzg/mod.rs:262"
      let eval ← listGetMut hEvals chunk "proofs/solidity-verifier/src/lowering/kzg/mod.rs:262"
      pure (Query.new comm 0 eval)
  | .lookupAccumulator lookup rotation =>
      let (_, _, zEval, zNextEval) ← listGetMut data.lookupEvals lookup "proofs/solidity-verifier/src/lowering/kzg/mod.rs:265"
      let eval ← match rotation with
        | 0 => pure zEval
        | 1 => pure zNextEval
        | _ => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:269")
      let comm ← listGetMut data.lookupZComms lookup "proofs/solidity-verifier/src/lowering/kzg/mod.rs:271"
      pure (Query.new comm rotation eval)
  | .trash index =>
      let comm ← listGetMut data.trashcanComms index "proofs/solidity-verifier/src/lowering/kzg/mod.rs:274"
      let eval ← listGetMut data.trashcanEvals index "proofs/solidity-verifier/src/lowering/kzg/mod.rs:274"
      pure (Query.new comm 0 eval)
  | .fixed q =>
      let comm ← listGetMut data.fixedComms q.column "proofs/solidity-verifier/src/lowering/kzg/mod.rs:277"
      match hashMapGet data.fixedEvals q.tuple with
      | some eval => pure (Query.new comm q.rotation eval)
      | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:279")
  | .permutationCommon column =>
      match hashMapGet data.permutationComms column with
      | some comm =>
        match hashMapGet data.permutationEvals column with
        | some eval => pure (Query.new comm 0 eval)
        | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:284")
      | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:282")
  | .linearization =>
      pure (Query.new data.computedQuotientComm 0 data.computedQuotientEval)

/-- rust: KZ:421-510 (construct_intermediate_sets_impl) @formal-baseline. The
    codegen-time re-derivation of the verifier's point-set partition, and the item
    the Phase 4 correctness lemma will be stated over. Four steps, in the Rust's
    order, because the plan says the lemma will be stated against exactly this
    shape.

    HAZARD 1, ANSWERED IN FULL. KZ:460-467 builds a BTreeMap<Vec<usize>, usize>
    whose VALUE is point_idx_sets.len() taken BEFORE the insert, i.e. insertion
    order, while the KEY is a sorted Vec<usize> and a BTreeMap iterates keys in
    sorted order. The two orders differ as soon as the first commitment's index set
    is not the lexicographically smallest. Every use of point_idx_sets after that
    loop:
      * KZ:477 point_idx_sets.get(&sorted_indices).unwrap() - a LOOKUP by key.
        Order-insensitive. Modelled by btreeMapGet. The unwrap is a real panic site
        and is ported as one, even though step 2 and step 3 cannot disagree: both
        apply sort_unstable + dedup to the same vec.
      * KZ:500 vec![Vec::new(); point_idx_sets.len()] - a LENGTH. Order-insensitive.
      * KZ:501 for (idx_set, &set_idx) in point_idx_sets.iter() - an ITERATION, and
        the only one in the file. It visits in SORTED-KEY order. But the body writes
        point_sets[set_idx], i.e. it indexes by the INSERTION-ORDER VALUE and not by
        the iteration position, so the iteration order is not observable in the
        result: the vector is fully determined by the (key, value) pairs. That is
        the trap. A port that used enumerate() there, or that modelled the map as a
        sorted list and took the position as the set number, would produce
        sorted-key numbering and a different point_sets.
    So the map is modelled with its VALUES carrying insertion order (the R6
    IndexMap rule applied to a BTreeMap whose values are insertion indices) and the
    fold at KZ:501 writes by value. hazard1_insertionOrderOk_ok builds the smallest
    case where the two orders disagree and pins the result, and the anchor gate
    anchorIntermediateSetsShape_ok pins a case where the disagreement survives into
    the sorted output.

    HAZARD 2, ANSWERED. The doc at KZ:417-420 says EcPoint comparisons use derived
    PartialEq, which compares the underlying memory pointer, and that this is the
    wanted semantics: same memory location = same commitment. In the port EcPoint is
    a newtype over Ptr (ENC:785-788) and Ptr is (Location, Value) with Value either
    a concrete byte offset or a symbolic identifier (ENC:581-592), so Lean's
    structural comparison IS pointer comparison and the port is faithful by
    construction - ecPointBeq above is that structural comparison and nothing more.
    This is the same hazard R-7 flagged in the VERIFIER, where CommitmentReference
    uses std::ptr::eq and the port compares values. The difference, and it is why
    there is nothing to fix here, is that the pointer here is a PLANNED MEMORY
    ADDRESS decided by the layout, not a Rust allocation address: two Data fields
    that alias one slot compare equal here and there for the same reason, and every
    committed-instance column shares G1_IDENTITY_MPTR exactly as KZ:437-443
    describes. Gated by ecPointEquality_isPointerEquality_ok.

    HAZARD 3, ANSWERED. KZ:444-450: a repeated (commitment, rotation) pair is legal
    - several columns may point at one slot - and the assert_eq fires only when the
    evals CONFLICT. Both arms are ported: the agreeing repeat continues without
    touching the entry, the conflicting repeat aborts at KZ:446. Getting this wrong
    changes the partition, hence the x1/x2/x3 batching structure of PLAN 9.4.
    duplicateQuery_bothArms_ok gates both. -/
def constructIntermediateSetsImpl (queries : List Query) : Except Fault IntermediateSets := do
  -- KZ:424-456: step 1. commitment_map is a Vec of (comm, point indices, evals) in
  -- first-seen order, and point_index_of is a Vec of rotations in first-seen order.
  -- Both are threaded through a foldlM because the Rust mutates them in place; the
  -- order of the two updates within one query is the Rust's (point index first,
  -- KZ:428-434, then the commitment slot, KZ:436-455).
  let step1 ← queries.foldlM step1Pass ([], [])
  let commitmentMap := step1.fst
  let pointIndexOf := step1.snd
  -- KZ:458-467: step 2. sort_unstable + dedup on Vec<usize> is exactly
  -- btreeSetFromList natCmp (ascending, duplicate-free), and the entry/or_insert is
  -- btreeMapEntryOrInsert.
  let pointIdxSets := commitmentMap.foldl
    (fun m (_, pis, _) => btreeMapEntryOrInsert m (btreeSetFromList natCmp pis)) []
  -- KZ:469-490: step 3.
  let commitments ← commitmentMap.mapM (fun (comm, pointIndices, evals) => do
      let sortedIndices := btreeSetFromList natCmp pointIndices
      let setIndex ← match btreeMapGet pointIdxSets sortedIndices with
        | some i => pure i
        | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:477")
      -- KZ:479-484: aligned_evals starts as vec![None; len] and each (point_index,
      -- eval) pair is written at its sorted position. The zip truncates to the
      -- shorter input (rule R3); the two are equal length by construction because
      -- step 1 pushes one index and one eval together at KZ:451-452.
      let aligned ← (pointIndices.zip evals).foldlM
        (fun acc (pi, ev) => do
          let pos ← match sortedIndices.findIdx? fun p => p == pi with
            | some p => pure p
            | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:482")
          listSetMut acc pos (some ev) "proofs/solidity-verifier/src/lowering/kzg/mod.rs:483")
        (List.replicate sortedIndices.length none)
      -- KZ:488: .map(Option::unwrap). A hole here is a Rust panic, so it is a
      -- panic here too rather than a dropped element.
      let alignedEvals ← aligned.mapM fun o => match o with
        | some e => pure e
        | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:488")
      pure { setIndex := setIndex, comm := comm, evals := alignedEvals })
  -- KZ:492-504: step 4. The iteration is in sorted-key order and the write index is
  -- the insertion-order VALUE. This line is hazard 1.
  let pointSets ← pointIdxSets.foldlM
    (fun ps (idxSet, setIdx) => do
      let rotations ← idxSet.mapM (fun i => listGetMut pointIndexOf i "proofs/solidity-verifier/src/lowering/kzg/mod.rs:502")
      listSetMut ps setIdx rotations "proofs/solidity-verifier/src/lowering/kzg/mod.rs:503")
    (List.replicate pointIdxSets.length [])
  pure { commitments := commitments, pointSets := pointSets }
where
  step1Pass : (List (EcPoint × List Nat × List Word) × List Int) → Query →
      Except Fault (List (EcPoint × List Nat × List Word) × List Int)
    | (commitmentMap, pointIndexOf), query => do
      -- KZ:428-434
      let (pointIndexOf, pointIdx) :=
        match pointIndexOf.findIdx? fun p => p == query.rotation with
        | some i => (pointIndexOf, i)
        | none => (pointIndexOf ++ [query.rotation], pointIndexOf.length)
      -- KZ:436
      match commitmentMap.findIdx? fun (c, _, _) => ecPointBeq c query.comm with
      | none =>
          -- KZ:453-455
          pure (commitmentMap ++ [(query.comm, [pointIdx], [query.eval])], pointIndexOf)
      | some pos => do
          let (comm, pis, evals) ← listGetMut commitmentMap pos "proofs/solidity-verifier/src/lowering/kzg/mod.rs:436"
          match pis.findIdx? fun pi => pi == pointIdx with
          | some existingPos => do
              -- KZ:444-450: HAZARD 3. The index at KZ:446 is slot.2[existing_pos];
              -- existing_pos came from a position in slot.1 and the two vecs are
              -- pushed in lockstep at KZ:451-452, so it is in range - ported as
              -- listGetMut anyway, per R4.
              let prev ← listGetMut evals existingPos "proofs/solidity-verifier/src/lowering/kzg/mod.rs:446"
              unless wordBeq prev query.eval do
                throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:446")
              -- KZ:449: continue. Nothing is appended and the existing entry is left
              -- exactly as it was.
              pure (commitmentMap, pointIndexOf)
          | none =>
              -- KZ:451-452
              let updated ← listSetMut commitmentMap pos (comm, pis ++ [pointIdx],
                evals ++ [query.eval]) "proofs/solidity-verifier/src/lowering/kzg/mod.rs:451"
              pure (updated, pointIndexOf)
end

/-- rust: KZ:512-542 (sort_sets) @formal-baseline.

    HAZARD 4, ANSWERED. The key is (point_sets[i].len(), i): ascending
    cardinality, tiebreak by ORIGINAL index, and the doc at KZ:512-517 says the
    verifier relies on it so that the first point set holds the fixed commitments
    opened at x. The tiebreak is observable only when two sets have the same
    cardinality, and sortSets_tiebreak_ok is exactly that case - two sets of size
    2 whose contents differ, where dropping the second key component would swap
    them. Note the key is the ORIGINAL index, i.e. the insertion-order number from
    hazard 1, not the sorted-key position: the two hazards compose, and the anchor
    gate exercises both at once.

    HAZARD 5, ANSWERED. KZ:533 reads remap[c.set_index] on a vec of length
    point_sets.len(), so an out-of-range set_index is a release-mode index panic,
    not a wrap. It cannot happen for any IntermediateSets that
    construct_intermediate_sets_impl produced: every set_index is a value of the
    KZ:460 map, and those values are 0, 1, .., m-1 with m = point_idx_sets.len() =
    point_sets.len() (KZ:500), which is exactly remap's length (KZ:523). The
    argument is restated at the site and sortSets_remapTotality_ok checks it on the
    fixture and on the anchor case. The panic is ported anyway per R4 rather than
    replaced by a getD, so a hand-built IntermediateSets with a bad set_index
    aborts like the Rust instead of silently pointing at set 0. -/
def sortSets (input : IntermediateSets) : Except Fault IntermediateSets := do
  let n := input.pointSets.length
  -- KZ:519-520
  let lens := input.pointSets.map List.length
  let order := insertionSortBy (lenIndexLt lens) (List.range n)
  -- KZ:522-526: remap[old_idx] = new_idx, over vec![0usize; n].
  let remap ← (List.range order.length).foldlM
    (fun acc newIdx => do
      let oldIdx ← listGetMut order newIdx "proofs/solidity-verifier/src/lowering/kzg/mod.rs:524"
      listSetMut acc oldIdx newIdx "proofs/solidity-verifier/src/lowering/kzg/mod.rs:525")
    (List.replicate n 0)
  -- KZ:528
  let pointSets ← order.mapM (fun i => listGetMut input.pointSets i "proofs/solidity-verifier/src/lowering/kzg/mod.rs:528")
  -- KZ:529-536
  let commitments ← input.commitments.mapM fun c => do
    let r ← listGetMut remap c.setIndex "proofs/solidity-verifier/src/lowering/kzg/mod.rs:533"
    pure { c with setIndex := r }
  pure { commitments := commitments, pointSets := pointSets }

/-- rust: KZ:544-555 (intermediate_sets) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_.

    HAZARD 7, ANSWERED. KZ:547 is the fewer-point-sets switch and it is a runtime
    test on data.dummy_eval_words, not a cfg: the feature decides in vk.rs whether
    the vector is ever filled, and under Features.solidity
    (outer-fewer-point-sets = false, BASELINE.md) it is not, so the RAW branch is
    the deployed one. Both branches are ported here and both are gated by
    intermediateSets_featureBranch_ok, which runs the same Data twice - once with
    an empty dummy vector and once with dummy words - and pins that the second
    collapses the point sets and the first does not. -/
def intermediateSets (meta_ : ConstraintSystemMeta) (data : Data) :
    Except Fault IntermediateSets := do
  let raw ← queries meta_ data
  let queries ← if data.dummyEvalWords.isEmpty then pure raw
    else augmentQueriesWithDummies raw data.dummyEvalWords
  sortSets (← constructIntermediateSetsImpl queries)

/-- rust: KZ:557-560 (num_point_sets) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. Recomputes the whole partition rather than reading
    meta.num_point_sets, which is the ENC:121 lazily-populated mirror that
    vk.rs:519 fills from exactly this call. -/
def numPointSets (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault Nat := do
  let sets ← intermediateSets meta_ data
  pure sets.pointSets.length

/-! ## TrackedG1 and the absorbed-to-precompile coverage invariant
(rust: KZ:562-577, KZ:580-740) -/

/-- rust: KZ:562-567 (#[derive(Clone, Debug, PartialEq, Eq)] struct TrackedG1)
    @formal-baseline. No deriving BEq: the Rust derives PartialEq and Eq, but the
    point field is an EcPoint, which carries no BEq instance in this tree (see
    valueBeq), so the derive cannot be reproduced. Nothing observable is lost - the
    only equality this type is compared by anywhere in the ported scope is on the
    point field, at KZ:697, and that is written with ecPointBeq at its site. -/
structure TrackedG1 where
  /-- rust: KZ:565 (label: String) - a diagnostic label, and the only carrier of
      provenance in this file: it is what the error string at KZ:702-707 prints. -/
  label : String
  /-- rust: KZ:566 (point: EcPoint) -/
  point : EcPoint

/-- rust: KZ:569-577 (impl TrackedG1::new) @formal-baseline. The Rust takes
    impl Into<String>; Lean has no coercion, so callers pass the String and the
    format! calls at KZ:599-640 are written out as concatenation. -/
def TrackedG1.new (label : String) (point : EcPoint) : TrackedG1 :=
  { label := label, point := point }

/-- Lean scaffolding, not a Rust item: Rust's .enumerate() over a List, giving
    (index, item) pairs. Used wherever the reference enumerates, so the pairing
    direction is stated once instead of being re-derived at eight call sites - and
    so that (index, item) rather than (item, index) is not a per-site coin flip. -/
def enumIdx {alpha : Type} (xs : List alpha) : List (Nat × alpha) :=
  (List.range xs.length).zip xs

/-- rust: KZ:579-584 (quotient_limb_comms) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. EcPoint::range is the infinite iterator of ENC:797-801, so
    this is takeIter over an index function (the header's note on the two infinite
    iterators); the stride is the literal 4 words of ENC:800, not g1WordsCount, and
    Encoding.lean:336-342 already pins that difference. -/
def quotientLimbComms (meta_ : ConstraintSystemMeta) (memory : VerifierMemoryLayout) :
    List EcPoint :=
  takeIter (EcPoint.range (EcPoint.fromPtr memory.quotientLimbCommsMptrBase)) meta_.numQuotients

/-- rust: KZ:586-646 (proof_absorbed_g1s) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. Every proof-controlled G1 that common_uncompressed_g1 absorbs
    into Fiat-Shamir, in the Rust's extend order: advice, lookup multiplicity,
    permutation product, per-lookup helper chunks, lookup accumulator, trashcan,
    quotient limbs, then f_com and pi. The order IS the content of the item - it
    decides which missing point the error at KZ:702 names first - so
    proofAbsorbedG1s_fixture_ok pins all seventeen entries and their labels.

    Note what is NOT here: the fixed and permutation-common commitments. They come
    from the VK, not the proof, so they are never absorbed as user-controlled
    points and hazard 6 does not apply to them. -/
def proofAbsorbedG1s (meta_ : ConstraintSystemMeta) (data : Data)
    (memory : VerifierMemoryLayout) : List TrackedG1 :=
  let advice := (enumIdx data.adviceComms).map
    fun (idx, point) => TrackedG1.new ("advice[" ++ toString idx ++ "]") point
  let lookupM := (enumIdx data.lookupMComms).map
    fun (idx, point) => TrackedG1.new ("lookup_multiplicity[" ++ toString idx ++ "]") point
  let permZ := (enumIdx data.permutationZComms).map
    fun (idx, point) => TrackedG1.new ("permutation_product[" ++ toString idx ++ "]") point
  -- KZ:615-621: nested enumerate, so the label carries both indices.
  let helpers := (enumIdx data.lookupHelperComms).flatMap fun (lookupIdx, hs) =>
    (enumIdx hs).map fun (chunkIdx, point) =>
      TrackedG1.new ("lookup_helper[" ++ toString lookupIdx ++ "][" ++ toString chunkIdx ++ "]") point
  let lookupZ := (enumIdx data.lookupZComms).map
    fun (idx, point) => TrackedG1.new ("lookup_accumulator[" ++ toString idx ++ "]") point
  let trash := (enumIdx data.trashcanComms).map
    fun (idx, point) => TrackedG1.new ("trashcan[" ++ toString idx ++ "]") point
  let limbs := (enumIdx (quotientLimbComms meta_ memory)).map
    fun (idx, point) => TrackedG1.new ("quotient_limb[" ++ toString idx ++ "]") point
  -- KZ:642-643
  let tail := [TrackedG1.new "f_com" (EcPoint.new memory.fComMptr),
    TrackedG1.new "pi" (EcPoint.new memory.piMptr)]
  advice ++ lookupM ++ permZ ++ helpers ++ lookupZ ++ trash ++ limbs ++ tail

/-- rust: KZ:648-686 (precompile_validated_g1s) @formal-baseline. FORCED R2
    DEVIATION, recorded: meta_. Every absorbed point the port claims a validating
    EIP-2537 precompile later consumes.

    Three things in here are the whole content of hazard 6 and each is gated.
    (1) KZ:661-663 SKIP the G1 identity outright. That is sound only because the
    identity is not a user-controlled point: ENC:369-377 pins every committed-
    instance commitment to G1_IDENTITY_MPTR and the proof carries 128 zero bytes
    there, so there is nothing to subgroup-check. The skip is gated by
    precompileValidated_identitySkip_ok.
    (2) KZ:665-670 replace the SYNTHETIC linearization commitment with the quotient
    limbs it expands into, because the final MSM (Block 5) never touches
    computed_quotient_comm itself - it touches the limbs. A port that pushed the
    linearization point itself would claim a validation that never happens, and the
    absorbed quotient_limb entries would then be reported missing.
    (3) KZ:676-683 add f_com and pi unconditionally, by NAME rather than by scanning
    the sets: f_com is the output of the final MSM and pi is the pairing input, and
    neither is a PCS query commitment.

    The function reads intermediate_sets, which can abort (hazard 3's assert sits
    under it), so the port returns Except Fault. -/
def precompileValidatedG1s (meta_ : ConstraintSystemMeta) (data : Data)
    (memory : VerifierMemoryLayout) : Except Fault (List TrackedG1) := do
  let sets ← intermediateSets meta_ data
  let linComm := linearizationComm data
  let limbEntries := (enumIdx (quotientLimbComms meta_ memory)).map
    fun (idx, point) =>
      TrackedG1.new ("quotient_limb[" ++ toString idx ++ "] via final PCS G1MSM") point
  -- KZ:660-674
  let validated ← sets.commitments.foldlM (fun validated entry =>
      if ecPointBeq entry.comm g1Identity then
        pure validated
      else if ecPointBeq entry.comm linComm then
        pure (validated ++ limbEntries)
      else
        pure (validated ++ [TrackedG1.new "PCS query commitment" entry.comm])) []
  -- KZ:676-683
  pure (validated ++ [TrackedG1.new "f_com via final PCS G1MSM" (EcPoint.new memory.fComMptr),
    TrackedG1.new "pi via final pairing input" (EcPoint.new memory.piMptr)])

/-- rust: KZ:688-711 (validate_g1_precompile_coverage) @formal-baseline. The set
    cover: every absorbed point must appear, by POINT and not by label, in the
    precompile input list (KZ:697). The error string is ported byte for byte
    including the count, the first missing label and the rendered pointer, because
    unlike a Fault.panic this is a Result payload and the Rust's own test at
    KZ:1976-1977 asserts on its content.

    missing.first() at KZ:701 is the FIRST missing in absorbed order, so the label
    the message names is determined by proof_absorbed_g1s's order - which is why
    that order is ported exactly. -/
def validateG1PrecompileCoverage (absorbed : List TrackedG1)
    (precompileInputs : List TrackedG1) : Except String Unit :=
  let missing := absorbed.filter fun a =>
    ! precompileInputs.any fun candidate => ecPointBeq candidate.point a.point
  match missing.head? with
  | none => .ok ()
  | some first => .error (toString missing.length
      ++ " absorbed proof G1(s) are not consumed by a later EIP-2537 G1MSM/pairing "
      ++ "precompile; first missing: " ++ first.label ++ " at "
      ++ printPtr first.point.base.value)

/-- rust: KZ:713-740 (validate_absorbed_g1_precompile_coverage) @formal-baseline.
    FORCED R2 DEVIATION, recorded: meta_. The PLAN 13 points_subgroup_checked
    boundary, and hazard 6.

    HAZARD 6, ANSWERED. This is the function that decides whether every absorbed
    proof G1 reaches a validating precompile, so it is where PLAN 9.5's
    points_subgroup_checked theorem is either supported or contradicted. It is
    ported unchanged, RUN on the fixture, and the answer is in the package report;
    the gate is validateAbsorbedCoverage_fixture_ok. The two channels are kept
    apart rather than collapsed: the count check and the cover check return
    Err(String) exactly as the Rust does, and the aborts that live UNDER them
    (intermediate_sets, hence hazard 3's assert_eq) are Fault panics, so the port's
    return type is Except Fault (Except String Unit). Collapsing them would let a
    panic masquerade as an invariant failure, which is the wrong direction of error
    for a statement about soundness.

    The count check at KZ:731 compares proof_absorbed_g1s's length against
    ProofCalldataLayout::total_g1_count (AP:266-268). Those are two independent
    derivations of the same number - one from the Data field lengths, one from the
    proof section item counts - so a mismatch is a real cross-module invariant, and
    absorbedCoverage_countMismatch_ok exercises the error arm by handing the
    function a layout with one extra pi. -/
def validateAbsorbedG1PrecompileCoverage (meta_ : ConstraintSystemMeta) (data : Data)
    (memory : VerifierMemoryLayout) (proofLayout : ProofCalldataLayout) :
    Except Fault (Except String Unit) := do
  let absorbed := proofAbsorbedG1s meta_ data memory
  let expected := proofLayout.totalG1Count
  if absorbed.length != expected then
    pure (.error ("absorbed proof G1 count mismatch: generator tracked "
      ++ toString absorbed.length ++ " point(s), proof layout expects "
      ++ toString expected))
  else
    let precompileInputs ← precompileValidatedG1s meta_ data memory
    pure (validateG1PrecompileCoverage absorbed precompileInputs)

/-! ## Set grouping, MSM sizing and the q_eval strategy
(rust: KZ:742-859, KZ:903-923) -/

/-- rust: KZ:742-749 (commitments_by_set) @formal-baseline. The Rust returns
    Vec<Vec<&CommitmentEntry>>; the borrow is not a value, so the port returns the
    entries themselves (rule R6's Vec reading plus the absence of lifetimes in
    Lean). n_sets slots are pre-allocated with vec![Vec::new(); n_sets] and each
    entry is pushed at by_set[c.set_index], so an out-of-range set_index is a
    release-mode index panic - ported per R4 through pushAt, and unreachable for
    the same reason as hazard 5: every set_index is below point_sets.len(), and
    the caller passes exactly that (KZ:867, KZ:872 and KZ:942, KZ:953). -/
def commitmentsBySet (sets : IntermediateSets) (nSets : Nat) :
    Except Fault (List (List CommitmentEntry)) :=
  sets.commitments.foldlM
    (fun acc c => pushAt acc c.setIndex c "proofs/solidity-verifier/src/lowering/kzg/mod.rs:746")
    (List.replicate nSets [])

/-- rust: KZ:751-762 (linearization_term_count) @formal-baseline. FORCED R2
    DEVIATION, recorded: meta_. num_quotients + simple_selector_cols.len(), which
    is the MSM width of the synthetic linearization commitment: one term per
    quotient limb plus one per simple selector, and the comment at KZ:753-760 is
    the reason the outer single-H slice contributes exactly one quotient factor.
    simpleSelectorCols is the ascending duplicate-free BTreeSet model Protocol.lean
    and Encoding.lean both use, so .len() is the cardinality and not a count with
    repeats. -/
def linearizationTermCount (meta_ : ConstraintSystemMeta) : Nat :=
  meta_.numQuotients + meta_.simpleSelectorCols.length

/-- rust: KZ:764-786 (q_com_terms_for_set) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. Three arms per entry: identity contributes 0, the linearization
    commitment contributes linearization_term_count, anything else contributes 1.
    The identity arm is what makes the q_com MSM narrower than the number of
    commitments in the set, and the linearization arm is what makes it wider than
    the number of PCS queries - qComTermsForSet_threeArms_ok pins all three in one
    set. -/
def qComTermsForSet (meta_ : ConstraintSystemMeta) (data : Data)
    (commitmentsInSet : List CommitmentEntry) : Nat :=
  let linCount := linearizationTermCount meta_
  let linComm := linearizationComm data
  (commitmentsInSet.map fun entry =>
    if ecPointBeq entry.comm g1Identity then 0
    else if ecPointBeq entry.comm linComm then linCount
    else 1).foldl (fun a b => a + b) 0

/-- rust: KZ:788-799 (q_com_trace_terms) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. max().unwrap_or(0) over the per-set counts. The Rust's max on
    usize and a Nat foldl max 0 agree on the value and on the empty case, which is
    what unwrap_or(0) is for; the same argument Exec/Circuit.lean:1526 records. -/
def qComTraceTerms (meta_ : ConstraintSystemMeta) (data : Data)
    (bySet : List (List CommitmentEntry)) : Nat :=
  (bySet.map (qComTermsForSet meta_ data)).foldl max 0

/-- rust: KZ:801-825 (final_msm_shape) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. flat_map over the sets, drop the identity entries, expand the
    linearization entry, sum, and add one for f_com. Note the difference from
    q_com_trace_terms: this one is over ALL sets at once and it counts f_com, and
    the +1 is the reason the final MSM is never empty even for an empty query list.
    FinalMsmShape::from_terms is MEM:389-394, already ported in Layout.lean. -/
def finalMsmShape (meta_ : ConstraintSystemMeta) (data : Data)
    (bySet : List (List CommitmentEntry)) : FinalMsmShape :=
  let linCount := linearizationTermCount meta_
  let linComm := linearizationComm data
  let terms := (bySet.flatMap id).filterMap (fun entry =>
      if ecPointBeq entry.comm g1Identity then none
      else some (if ecPointBeq entry.comm linComm then linCount else 1))
      |>.foldl (fun a b => a + b) 0
  FinalMsmShape.fromTerms (terms + 1)

/-- rust: KZ:827-828 (pub(super) const Q_EVAL_ROLL_THRESHOLD: usize = 4)
    @formal-baseline. pub(super), not pub(crate): the layout module's parent sees
    it, which is why the Rust's own test at KZ:1982 can assert the value. -/
def qEvalRollThreshold : Nat := 4

/-- rust: KZ:830-837 (#[derive(Clone, Copy, Debug, Eq, PartialEq)] enum
    QEvalStrategy) @formal-baseline. Declaration order, and deriving BEq because
    the Rust derives Eq and PartialEq. Nothing sorts this enum, so unlike
    Protocol.lean's CommonPoly the order is documentation rather than behaviour. -/
inductive QEvalStrategy
  /-- rust: KZ:833-834 (Rolled) - a loop over memory-backed eval source addresses. -/
  | rolled
  /-- rust: KZ:835-836 (Unrolled) - straight-line arithmetic. -/
  | unrolled
  deriving BEq

/-- rust: KZ:839-859 (q_eval_strategy) @formal-baseline. Three ways to get
    Unrolled and one to get Rolled, and the Rust's own test name says the point:
    this is the SINGLE source of truth shared by the planner (memory_requirements,
    KZ:883) and the emitter (Block 3, KZ:1182), so the two cannot disagree about
    whether the eval source table is needed. An empty set is Unrolled (KZ:841-843);
    fewer than four commitments is Unrolled; and a set whose rows are ragged or
    whose evals are not all memory-backed is Unrolled even when it is wide.
    qEvalStrategy_matchesRustTest_ok reproduces KZ:1981-2018 exactly, including
    the calldata-backed and the popped-row discriminators. -/
def qEvalStrategy (commitments : List CommitmentEntry) : QEvalStrategy :=
  match commitments.head? with
  | none => QEvalStrategy.unrolled
  | some first =>
      if commitments.length < qEvalRollThreshold then QEvalStrategy.unrolled
      else
        let nRot := first.evals.length
        let canRoll := commitments.all fun c =>
          c.evals.length == nRot && c.evals.all (fun eval => locationBeq (Word.loc eval) Location.memory)
        if canRoll then QEvalStrategy.rolled else QEvalStrategy.unrolled

/-- rust: KZ:861-901 (memory_requirements) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. Every PCS scratch window and MSM size the planner needs, and
    the item plan.rs:187, plan.rs:258 and plan.rs:427 all call - the last of them
    re-computes it and compares, so a drift here is a generator error.

    The n_sets == 0 early return at KZ:688-690 hands back
    PcsMemoryRequirements::default(), i.e. all seven fields zero, and it is a real
    arm: an empty query list is a legal (if useless) circuit shape.
    memoryRequirements_empty_ok gates it.

    q_eval_source_table_words is the max over the ROLLED sets only, of
    commitments.len() * rotations.len() - which is exactly the table Block 3
    stages at KZ:1193-1203, so the two must agree or the emitted Yul writes past
    its window. That coupling is what memoryRequirements_rolledTable_ok pins, and
    it is the reason q_eval_strategy is a shared def rather than inlined twice.

    q_com_words is a literal 0 with a comment (KZ:892-895): q_com is fused into the
    final MSM scratch, and the field is kept so a future Q_COM_MPTR user has to
    participate in layout validation. Ported as the literal, not dropped. -/
def memoryRequirements (meta_ : ConstraintSystemMeta) (data : Data) :
    Except Fault PcsMemoryRequirements := do
  let sets ← intermediateSets meta_ data
  let nSets := sets.pointSets.length
  if nSets == 0 then pure pcsMemoryRequirementsDefault
  else do
    let bySet ← commitmentsBySet sets nSets
    -- KZ:873
    let commitmentsPerSet := bySet.map List.length
    -- KZ:875-878: sort_unstable + dedup over Vec<i32>, i.e. SIGNED ascending. This
    -- is the one place in the file where the signedness of a rotation changes an
    -- output: rot_points_words for the fixture is 4 either way, but the ORDER of
    -- distinct_rotations feeds every rot_pt_N index in Block 1 and Block 4, and
    -- under a Nat reading -10 would sort last instead of first.
    -- memoryRequirements_signedRotations_ok pins it.
    let distinctRotations := btreeSetFromList intCmp (sets.pointSets.flatMap id)
    -- KZ:880-886
    let rolledWidths := ((bySet.zip sets.pointSets).filterMap
        fun (commitments, rotations) =>
          if qEvalStrategy commitments == QEvalStrategy.rolled
            then some (commitments.length * rotations.length) else none)
    let rolledTableWords := rolledWidths.foldl max 0
    -- KZ:887
    let qComTrace := qComTraceTerms meta_ data bySet
    pure ({ rotPointsWords := distinctRotations.length
            x1PowersWords := commitmentsPerSet.foldl max 0
            qComWords := 0
            qEvalSetWords := (sets.pointSets.map List.length).foldl (fun a b => a + b) 0
            qEvalSourceTableWords := rolledTableWords
            qComTraceMsm := FinalMsmShape.fromTerms qComTrace
            finalMsm := finalMsmShape meta_ data bySet } : PcsMemoryRequirements)

/-- rust: KZ:903-910 (num_dummy_queries) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. Run over the RAW queries - the doc at KZ:903-907 is explicit
    that this sizes the dummy buffer before the augmented Data exists, and vk.rs:504
    calls it on raw_data for exactly that reason. -/
def numDummyQueries (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault Nat := do
  let qs ← queries meta_ data
  pure (computeDummyQueries qs).length

/-- rust: KZ:916-923 (static_working_memory_size) @formal-baseline. The body is one
    constant read, and the comment around it is the interesting part: the pairing
    precompile needs 2 G1 (8 words) + 2 G2 (16 words) + 1 output = 25 words, and
    PCS_STATIC_WORKING_WORDS rounds that up to 32 for the in-Yul accumulator slots.
    staticWorkingMemorySize_matchesDoc_ok checks the arithmetic the comment claims
    rather than just the constant, because a constant read cannot be wrong and the
    comment can. -/
def staticWorkingMemorySize : Nat := pcsStaticWorkingWords

/-! ## Yul emission (rust: KZ:925-1922) -/

/-- rust: KZ:925-1922 (computations) @formal-baseline. FORCED R2 DEVIATION,
    recorded: meta_. The multi-prepare body, in six blocks, and by far the largest
    item in the file.

    SHAPE. The Rust returns Vec<Vec<String>> where each inner Vec is one Yul code
    block, and the block ORDER is the six-step structure the module doc at KZ:7-21
    states. That order is load-bearing: PLAN section 6 lists the correctness of
    construct_intermediate_sets as a required lemma and it will be stated over this
    shape, so the blocks are emitted in the Rust's order and no block is merged,
    split or reordered. computations_blockOrder_ok pins the block count and the
    first line of every block.

    MUTATION. The Rust accumulates into a mutable lines: Vec<String> with a
    mutable pair_idx counter. Both become folds: lines by appending the segments in
    the Rust's order, pair_idx by threading it through a foldlM that returns the
    pair (counter, lines). The counters are then compared against the pre-computed
    shape at KZ:1395 and KZ:1816, and both asserts are ported as Fault.panic - they
    are the emission-time proof that the fold counted the same terms the planner
    counted, which is exactly the R-30 class of bug (a fold that silently drops
    everything but the last element).

    HEX. Every {:#x} in the Rust is hashHex - "0x" plus minimal lowercase hex with
    NO even-width pad - and not Filters.lean's hexFilter, which pads odd widths.
    The two differ at 0x100 and above, which the scratch addresses reach: 0x20 * 16
    = 0x200 is three nibbles. Models.lean:555-561 records hashHex as a third
    formatter for exactly this reason; computations_hexFormatter_ok pins that the
    emitted offsets are unpadded.

    The two debug_assert sites (KZ:1194 debug_assert_eq! on the row width and
    KZ:1196 debug_assert! on the memory location) are compiled out in the release
    profile (BASELINE.md, rule R4) and are NOT ported. Both are nevertheless true
    of every input the rolled branch can reach, because q_eval_strategy is what
    selects that branch and it checks exactly those two conditions - which is the
    single-source-of-truth property the Rust's own test name at KZ:1981 asserts. -/
def computations (meta_ : ConstraintSystemMeta) (data : Data)
    (memory : VerifierMemoryLayout) (truncatedChallenges : Bool) (trace : Bool) :
    Except Fault (List (List String)) := do
  -- KZ:940 is truncMask128 above.
  let sets ← intermediateSets meta_ data
  let nSets := sets.pointSets.length
  -- KZ:943-945
  if nSets == 0 then return []
  -- KZ:953
  let bySet ← commitmentsBySet sets nSets
  -- KZ:957
  let nbX1Powers := (bySet.map List.length).foldl max 0
  -- KZ:959-964: sort_unstable + dedup over Vec<i32>, SIGNED.
  let distinctRotations := btreeSetFromList intCmp (sets.pointSets.flatMap id)
  -- KZ:992-993
  let maxRot := intMaxOr 0 distinctRotations
  let minRot := intMinOr 0 distinctRotations
  -- KZ:995-1002: the store_rot closure. Option because position() is Option.
  let storeRot : Int → Option String := fun rot =>
    (distinctRotations.findIdx? fun r => r == rot).map fun idx =>
      "mstore(add(ROT_POINTS_MPTR, " ++ hashHex (idx * wordBytes)
        ++ "), x_pow_of_omega)"
  -- KZ:1004-1027: Block 1's rotation walk.
  let b1Head := ["// " ++ toString distinctRotations.length ++ " distinct rotation(s)",
    "let x := mload(X_MPTR)", "let omega := mload(OMEGA_MPTR)",
    "let omega_inv := mload(OMEGA_INV_MPTR)", "let x_pow_of_omega := x"]
    ++ (storeRot 0).toList
  let b1Fwd := (intRangeInclusive 1 maxRot).flatMap fun rot =>
    ["x_pow_of_omega := mulmod(x_pow_of_omega, omega, r)"] ++ (storeRot rot).toList
  let b1Back := if minRot < 0
    then ["x_pow_of_omega := x"]
      ++ (intRange minRot 0).reverse.flatMap fun rot =>
        ["x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)"] ++ (storeRot rot).toList
    else []
  -- KZ:1029-1058: the trace-only serialization of each point set's rotations.
  let b1Trace ← (enumIdx sets.pointSets).mapM fun (setIdx, points) => do
    let stores ← (enumIdx points).mapM fun (pointIdx, rot) => do
      let rotIdx ← match distinctRotations.findIdx? fun r => r == rot with
        | some i => pure i
        | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1045")
      pure ("mstore(add(Q_EVAL_SET_MPTR, " ++ hashHex (pointIdx * wordBytes)
        ++ "), mload(add(ROT_POINTS_MPTR, " ++ hashHex (rotIdx * wordBytes) ++ ")))")
    pure (["// trace serialized PCS point set " ++ toString setIdx ++ " ("
      ++ toString points.length ++ " point(s))"] ++ stores
      ++ ["log1(Q_EVAL_SET_MPTR, " ++ hashHex (points.length * wordBytes) ++ ", "
        ++ toString (Trace.pcsSerializedPointSetBase + setIdx) ++ ")"])
  let block1 := b1Head ++ b1Fwd ++ b1Back ++ (if trace then b1Trace.flatten else [])
  -- KZ:1063-1115: Block 2, x1 powers, emitted only when there is at least one.
  let block2 := ["// pre-compute " ++ toString nbX1Powers ++ " x1 power(s)",
      "let x1 := mload(X1_MPTR)", "mstore(X1_POWERS_MPTR, 1)"]
      ++ (if nbX1Powers > 1 then
            ["let acc := 1", "let p := X1_POWERS_MPTR",
             "for { let i := 0 } lt(i, " ++ hashHex (nbX1Powers - 1) ++ ") { i := add(i, 1) } {",
             "    p := add(p, " ++ hashHex wordBytes ++ ")",
             "    acc := mulmod(acc, x1, r)"]
            ++ [if truncatedChallenges
                  then "    mstore(p, and(acc, " ++ truncMask128 ++ "))"
                  else "    mstore(p, acc)"]
            ++ ["}"]
          else [])
  -- KZ:1117-1290: Block 3, one block per point set.
  let evalSrcTableMptr := memory.pcsQEvalSourceTableMptr
  let block3 ← (enumIdx bySet).mapM fun (setIdx, commitmentsInSet) => do
    -- KZ:1156: computed and then dropped at KZ:1288 ("kept for symmetry"). Ported
    -- as a let so the line exists and is not silently missing from the port.
    let qEvalBase := "add(Q_EVAL_SET_MPTR, " ++ hashHex (setIdx * wordBytes) ++ ")"
    let _ := qEvalBase
    let m := commitmentsInSet.length
    -- KZ:1163-1164: the MSM-skips-identity count, reported next to the eval count
    -- so the comment cannot contradict the pair count below it (L-2/P7).
    let commitmentTerms := (commitmentsInSet.filter fun c =>
      ! ecPointBeq c.comm g1Identity).length
    -- KZ:1177: &commitments_in_set[0]. Totality: every set index in point_idx_sets
    -- was created BY a commitment at KZ:466, so no slot of by_set is empty. Ported
    -- as listGetMut per R4 anyway; see hazard 5's argument at sortSets.
    let first ← listGetMut commitmentsInSet 0 "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1177"
    let nRot := first.evals.length
    -- KZ:1179-1180: the cumulative |sets[<s]| offset.
    let setEvalOffsetWords := (sets.pointSets.take setIdx).map List.length
      |>.foldl (fun a b => a + b) 0
    let seeds := (enumIdx first.evals).map fun (k, ev) =>
      "let q_eval_set_" ++ toString k ++ " := " ++ wordKey ev
    let persist := (List.range nRot).map fun k =>
      "mstore(add(Q_EVAL_SET_MPTR, " ++ hashHex ((setEvalOffsetWords + k) * wordBytes)
        ++ "), q_eval_set_" ++ toString k ++ ")"
    if qEvalStrategy commitmentsInSet == QEvalStrategy.rolled then do
      -- KZ:1189-1203: stage the eval source addresses, row-major over commits.
      let stage := (enumIdx commitmentsInSet).flatMap fun (i, c) =>
        (enumIdx c.evals).map fun (k, ev) =>
          "mstore(" ++ hashHex (evalSrcTableMptr + (i * nRot + k) * wordBytes) ++ ", "
            ++ printPtr ev.ptr.value ++ ")"
      let nRotStride := nRot * wordBytes
      -- KZ:1234-1246: the loop body. k == 0 is written WITHOUT the add(eval_p, ..)
      -- because the offset is zero, and the Rust spells that arm out separately at
      -- KZ:1235-1245 rather than formatting 0x0 - a port that collapsed the two
      -- would emit add(eval_p, 0x0) and change the bytes.
      let body := (List.range nRot).map fun k =>
        if k == 0 then
          "    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(mload(eval_p)), pow, r), r)"
        else
          "    q_eval_set_" ++ toString k ++ " := addmod(q_eval_set_" ++ toString k
            ++ ", mulmod(mload(mload(add(eval_p, " ++ hashHex (k * wordBytes)
            ++ "))), pow, r), r)"
      pure (["// q_eval_set[" ++ toString setIdx ++ "]: " ++ toString m
          ++ " evaluation term(s), " ++ toString commitmentTerms
          ++ " commitment term(s) (rolled, m>=" ++ toString qEvalRollThreshold ++ ")",
          "// stage per-(commit, rotation) eval source addresses"] ++ stage ++ seeds
        ++ ["let pow_p := add(X1_POWERS_MPTR, " ++ hashHex wordBytes ++ ")",
            "let eval_p := add(" ++ hashHex evalSrcTableMptr ++ ", " ++ hashHex nRotStride ++ ")",
            "for { let i := 1 } lt(i, " ++ hashHex m ++ ") { i := add(i, 1) } {",
            "    let pow := mload(pow_p)"] ++ body
        ++ ["    pow_p := add(pow_p, " ++ hashHex wordBytes ++ ")",
            "    eval_p := add(eval_p, " ++ hashHex nRotStride ++ ")", "}"] ++ persist)
    else do
      -- KZ:1266-1276: straight-line fold, skipping commitment 0 (it seeded).
      let folds := ((enumIdx commitmentsInSet).drop 1).flatMap fun (i, c) =>
        let x1Pow := "mload(add(X1_POWERS_MPTR, " ++ hashHex (i * wordBytes) ++ "))"
        (enumIdx c.evals).map fun (k, ev) =>
          "q_eval_set_" ++ toString k ++ " := addmod(q_eval_set_" ++ toString k
            ++ ", mulmod(" ++ wordKey ev ++ ", " ++ x1Pow ++ ", r), r)"
      pure (["// q_eval_set[" ++ toString setIdx ++ "]: " ++ toString m
          ++ " evaluation term(s), " ++ toString commitmentTerms
          ++ " commitment term(s)"] ++ seeds ++ folds ++ persist)
  -- KZ:1292-1420: the trace-only q_com materialisation. Skipped entirely when
  -- trace is false, which is the deployed profile's default at the call site.
  let traceBlock ← do
    let linComm := linearizationComm data
    let simpleSelectorCols := meta_.simpleSelectorCols
    let linTermCount := linearizationTermCount meta_
    let traceScratch := memory.pcsQComTraceScratchMptr
    let perSet ← (enumIdx bySet).mapM fun (setIdx, commitmentsInSet) => do
      let nonIdentityTerms := (commitmentsInSet.map fun entry =>
        if ecPointBeq entry.comm g1Identity then 0
        else if ecPointBeq entry.comm linComm then linTermCount
        else 1).foldl (fun a b => a + b) 0
      if nonIdentityTerms == 0 then
        -- KZ:1319-1328
        pure (0, ["mcopy(" ++ hashHex traceScratch ++ ", G1_IDENTITY_MPTR, "
          ++ hashHex g1Bytes ++ ")",
          "trace_point(" ++ toString (40000 + setIdx) ++ ", " ++ hashHex traceScratch ++ ")"])
      else do
        let (pairIdxEnd, ls) ← (enumIdx commitmentsInSet).foldlM
            (fun st (commitmentIdx, c) => do
              if ecPointBeq c.comm g1Identity then pure st
              else do
                let (pairIdx, acc) := st
                let scalar := if commitmentIdx == 0 then "1"
                  else "mload(add(X1_POWERS_MPTR, " ++ hashHex (commitmentIdx * wordBytes) ++ "))"
                if ecPointBeq c.comm linComm then do
                  let linQueryVar := "q_com_lin_query_scalar_" ++ toString setIdx ++ "_"
                    ++ toString commitmentIdx
                  let linCurVar := "q_com_lin_cur_scalar_" ++ toString setIdx ++ "_"
                    ++ toString commitmentIdx
                  let limbLines ← (List.range meta_.numQuotients).foldlM
                      (fun (st2 : Nat × List String) qIdx => do
                        let pairBase := traceScratch + st2.1 * g1MsmPairBytes
                        let mut1 := ["mcopy(" ++ hashHex pairBase
                            ++ ", add(QUOTIENT_LIMB_COMMS_MPTR_BASE, " ++ hashHex (qIdx * g1Bytes)
                            ++ "), " ++ hashHex g1Bytes ++ ")",
                          "mstore(" ++ hashHex (pairBase + g1Bytes) ++ ", " ++ linCurVar ++ ")"]
                        if qIdx + 1 != meta_.numQuotients then
                          pure (st2.1 + 1, st2.2 ++ mut1
                            ++ [linCurVar ++ " := mulmod(" ++ linCurVar
                                ++ ", mload(QUOTIENT_MPTR), r)"])
                        else pure (st2.1 + 1, st2.2 ++ mut1))
                      (pairIdx, [])
                  let selLines ← (enumIdx simpleSelectorCols).foldlM
                      (fun (st2 : Nat × List String) (selIdx, col) => do
                        let pairBase := traceScratch + st2.1 * g1MsmPairBytes
                        let fixed ← listGetMut data.fixedComms col
                          "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1376"
                        let selectorScalar := "mload(add(SELECTOR_ACC_MPTR, "
                          ++ hashHex (selIdx * wordBytes) ++ "))"
                        pure (st2.1 + 1, st2.2 ++ ["mcopy(" ++ hashHex pairBase ++ ", "
                            ++ printPtr fixed.base.value ++ ", " ++ hashHex g1Bytes ++ ")",
                          "mstore(" ++ hashHex (pairBase + g1Bytes) ++ ", mulmod(" ++ linQueryVar
                            ++ ", " ++ selectorScalar ++ ", r))"]))
                      (limbLines.1, [])
                  pure (selLines.1, acc ++ ["let " ++ linQueryVar ++ " := " ++ scalar,
                    "let " ++ linCurVar ++ " := mulmod(" ++ linQueryVar
                      ++ ", mload(add(QUOTIENT_MPTR, " ++ hashHex wordBytes ++ ")), r)"]
                    ++ limbLines.2 ++ selLines.2)
                else do
                  let pairBase := traceScratch + pairIdx * g1MsmPairBytes
                  pure (pairIdx + 1, acc ++ ["mcopy(" ++ hashHex pairBase ++ ", "
                    ++ printPtr c.comm.base.value ++ ", " ++ hashHex g1Bytes ++ ")",
                    "mstore(" ++ hashHex (pairBase + g1Bytes) ++ ", " ++ scalar ++ ")"]))
            (0, [])
        unless pairIdxEnd == nonIdentityTerms do
          throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1396")
        let msmLen := nonIdentityTerms * g1MsmPairBytes
        pure (pairIdxEnd, ls ++ ["// exact EIP-2537 G1MSM cost for " ++ toString nonIdentityTerms
            ++ " pair(s)",
          "let q_com_trace_ok_" ++ toString setIdx ++ " := staticcall("
            ++ toString (Midfall.Yul.g1MsmGasPairs nonIdentityTerms) ++ ", 0x0c, "
            ++ hashHex traceScratch ++ ", " ++ hashHex msmLen ++ ", " ++ hashHex traceScratch
            ++ ", " ++ hashHex g1Bytes ++ ")",
          "q_com_trace_ok_" ++ toString setIdx ++ " := and(q_com_trace_ok_" ++ toString setIdx
            ++ ", eq(returndatasize(), " ++ hashHex g1Bytes ++ "))",
          "if iszero(q_com_trace_ok_" ++ toString setIdx ++ ") { mstore(TRACE_U256_MPTR, "
            ++ toString (40000 + setIdx) ++ ") revert(TRACE_U256_MPTR, " ++ hashHex wordBytes
            ++ ") }",
          "trace_point(" ++ toString (40000 + setIdx) ++ ", " ++ hashHex traceScratch ++ ")"])
    pure ("// materialize per-set q_com inputs for trace logging" :: perSet.flatMap Prod.snd)
  -- KZ:1422-1648: Block 4, f_eval by Horner over reverse(point_sets).
  let block4 ← do
    let rotPtRefs ← (enumIdx distinctRotations).mapM fun (i, _rot) =>
        pure ("let rot_pt_" ++ toString i ++ " := mload(add(ROT_POINTS_MPTR, "
          ++ hashHex (i * wordBytes) ++ "))")
    let rotPtRef : Int → Except Fault String := fun rot =>
      match distinctRotations.findIdx? fun r => r == rot with
      | some idx => pure ("rot_pt_" ++ toString idx)
      | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1469")
    let setBlocks ← ((List.range nSets).reverse).mapM fun setIdx => do
      let points ← listGetMut sets.pointSets setIdx "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1474"
      let m := points.length
      let proofEval := "calldataload(add(Q_EVAL_CPTR, " ++ hashHex (setIdx * wordBytes) ++ "))"
      let setEvalOffsetWords := (sets.pointSets.take setIdx).map List.length
        |>.foldl (fun a b => a + b) 0
      let head := ["// --- set " ++ toString setIdx ++ " (cardinality " ++ toString m ++ ") ---", "{"]
      if m == 1 then do
        -- KZ:1496-1510: the |set| == 1 special case. r_eval = evals[0], den = dx[0].
        -- KZ:1497 indexes points[0]. m == 1 makes it in range, but the Rust index
        -- is a panic site like any other, so it is listGetMut and not a getD default.
        let p0 ← listGetMut points 0 "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1497"
        let pt ← rotPtRef p0
        let ev := "mload(add(Q_EVAL_SET_MPTR, " ++ hashHex (setEvalOffsetWords * wordBytes) ++ "))"
        pure (head ++ ["let dx0 := addmod(x3, sub(r, " ++ pt ++ "), r)",
          "let dx0_inv := scalar_inv(dx0)",
          "let eval := mulmod(addmod(" ++ proofEval ++ ", sub(r, " ++ ev ++ "), r), dx0_inv, r)",
          "f_eval := addmod(mulmod(f_eval, x2, r), eval, r)", "}"])
      else do
        let dxLines ← (enumIdx points).mapM fun (j, point) => do
          let pt ← rotPtRef point
          pure ("let dx_" ++ toString j ++ " := addmod(x3, sub(r, " ++ pt ++ "), r)")
        let lbasisLines ← (enumIdx points).mapM fun (j, pointJ) => do
          let pj ← rotPtRef pointJ
          -- KZ:1556-1564: the inner enumerate carries point_k itself, so the
          -- reference is rot_pt_ref(*point_k) and not a re-index of points.
          let inner := (enumIdx points).filterMap fun (k, pointK) =>
            if k == j then none else some pointK
          let terms ← inner.mapM fun pointK => do
            let pk ← rotPtRef pointK
            pure ("lbasis_" ++ toString j ++ " := mulmod(lbasis_" ++ toString j
              ++ ", addmod(" ++ pj ++ ", sub(r, " ++ pk ++ "), r), r)")
          pure (["let lbasis_" ++ toString j ++ " := 1"] ++ terms)
        -- KZ:1569-1576: batch inputs are dx_0..dx_{m-1} then lbasis_0..lbasis_{m-1}.
        let batchInputs := (List.range m).map (fun j => "dx_" ++ toString j)
          ++ (List.range m).map (fun j => "lbasis_" ++ toString j)
        let n := batchInputs.length
        let bpLines := ["let bp_0 := " ++ batchInputs.getD 0 ""]
          ++ ((enumIdx batchInputs).drop 1).map fun (i, inp) =>
              "let bp_" ++ toString i ++ " := mulmod(bp_" ++ toString (i - 1) ++ ", " ++ inp ++ ", r)"
        let invName : Nat → String := fun idx =>
          if idx < m then "dx_inv_" ++ toString idx else "lbasis_inv_" ++ toString (idx - m)
        let bqLines := ((List.range n).drop 1).reverse.flatMap fun i =>
          ["let " ++ invName i ++ " := mulmod(bq, bp_" ++ toString (i - 1) ++ ", r)",
           "bq := mulmod(bq, " ++ batchInputs.getD i "" ++ ", r)"]
        let denInvLines := ["let den_inv := dx_inv_0"]
          ++ ((List.range m).drop 1).map (fun j => "den_inv := mulmod(den_inv, dx_inv_" ++ toString j ++ ", r)")
        let termLines ← (List.range m).mapM fun j => do
          let evJ := "mload(add(Q_EVAL_SET_MPTR, " ++ hashHex ((setEvalOffsetWords + j) * wordBytes) ++ "))"
          pure (["let term_" ++ toString j ++ " := mulmod(mulmod(" ++ evJ ++ ", dx_inv_" ++ toString j
            ++ ", r), lbasis_inv_" ++ toString j ++ ", r)",
            "eval := addmod(eval, sub(r, term_" ++ toString j ++ "), r)"])
        pure (head ++ dxLines ++ lbasisLines.flatten ++ bpLines
          ++ ["let bq := scalar_inv(bp_" ++ toString (n - 1) ++ ")"] ++ bqLines
          ++ ["let " ++ invName 0 ++ " := bq"] ++ denInvLines
          ++ ["let eval := mulmod(" ++ proofEval ++ ", den_inv, r)"]
          ++ termLines.flatten
          ++ ["f_eval := addmod(mulmod(f_eval, x2, r), eval, r)", "}"])
    pure (["// f_eval via Horner over " ++ toString nSets ++ " reversed set(s)",
      "let x2 := mload(X2_MPTR)", "let x3 := mload(X3_MPTR)", "let f_eval := 0",
      "let Q_EVAL_CPTR := mload(Q_EVAL_CPTR_MPTR)"] ++ rotPtRefs ++ setBlocks.flatten
      ++ ["mstore(F_EVAL_MPTR, f_eval)"])
  -- KZ:1650-1837: Block 5, the fused final commitment MSM with x4 powers.
  let block5 ← do
    let linComm := linearizationComm data
    let simpleSelectorCols := meta_.simpleSelectorCols
    -- KZ:1671-1673: the shape comes from the SAME final_msm_shape the planner
    -- (KZ:899) hands to the layout validator, which is what the assert below is
    -- protecting.
    let shape := finalMsmShape meta_ data bySet
    let finalMsmTerms := shape.terms
    let finalMsmLen := shape.inputBytes
    -- KZ:1677-1681: a real assert_eq!, so it aborts in the release profile too
    -- (rule R4). It is unreachable for a FinalMsmShape built by from_terms, which
    -- defines input_bytes as terms * G1_MSM_PAIR_BYTES (MEM:389-394); ported
    -- anyway rather than argued away, because the assert is the only thing that
    -- would catch a future from_terms that stops being a plain product.
    unless finalMsmTerms * g1MsmPairBytes == finalMsmLen do
      throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1677")
    let finalMsmScratch := memory.pcsFinalMsmScratchMptr
    let head := ["// build final_com and v (KZG single-opening proof, fused MSM)",
      "// final MSM input length from circuit/VK shape: " ++ toString finalMsmTerms
        ++ " term(s)",
      "let x4 := mload(X4_MPTR)", "let lin_x_split := mload(QUOTIENT_MPTR)",
      "let lin_one_minus_x_n := mload(add(QUOTIENT_MPTR, " ++ hashHex wordBytes ++ "))",
      -- Resolve the calldata pointer to the q_evals block once.
      "let Q_EVAL_CPTR := mload(Q_EVAL_CPTR_MPTR)"]
    -- KZ:1701-1715: the x4 power walk. Under truncated_challenges the accumulator
    -- x4_pow_full stays at full precision and each emitted power is and-ed down to
    -- 128 bits; otherwise each power is a plain mulmod off the previous one. Note
    -- the two arms declare DIFFERENT variable names (x4_pow_full is declared only
    -- in the truncated arm), so a port that merged them would emit Yul that does
    -- not compile. computations_traceAndTruncationBranches_ok pins both arms.
    let x4Lines := (if truncatedChallenges then ["let x4_pow_full := 1"]
        else ["let x4_pow_0 := 1"])
      ++ (List.range nSets).flatMap fun k =>
        let s := k + 1
        if truncatedChallenges then
          ["x4_pow_full := mulmod(x4_pow_full, x4, r)",
           "let x4_pow_" ++ toString s ++ " := and(x4_pow_full, " ++ truncMask128 ++ ")"]
        else ["let x4_pow_" ++ toString s ++ " := mulmod(x4_pow_" ++ toString (s - 1)
                ++ ", x4, r)"]
    -- KZ:1717-1727: v = sum_s x4^s * q_evals[s] + x4^n_sets * f_eval. The loop is
    -- 1..n_sets, i.e. it STOPS before n_sets, and the f_eval term below is what
    -- supplies s == n_sets. A port that wrote 1..=n_sets would double-count.
    let vLines := ["let v := calldataload(Q_EVAL_CPTR)"]
      ++ (((List.range nSets).drop 1).map fun s =>
          "v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, " ++ hashHex (s * wordBytes)
            ++ ")), x4_pow_" ++ toString s ++ ", r), r)")
      ++ ["v := addmod(v, mulmod(mload(F_EVAL_MPTR), x4_pow_" ++ toString nSets
            ++ ", r), r)"]
    -- KZ:1732-1747: the scalar closure. Three arms and a shared x1_pow, kept in
    -- this order: (0, _) wins over (_, 0), so set 0 commitment 0 renders as "1"
    -- and not as x4_pow_0.
    let scalarExpr : Nat → Nat → String := fun setIdx commitmentIdx =>
      let x1Pow := if commitmentIdx == 0 then "1"
        else "mload(add(X1_POWERS_MPTR, " ++ hashHex (commitmentIdx * wordBytes) ++ "))"
      if setIdx == 0 then x1Pow
      else if commitmentIdx == 0 then "x4_pow_" ++ toString setIdx
      else "mulmod(" ++ x1Pow ++ ", x4_pow_" ++ toString setIdx ++ ", r)"
    -- KZ:1731, 1749-1807: ONE pair_idx across all sets, so the inner fold starts
    -- from the outer accumulator and not from 0. A port that reset it per set would
    -- stage every set at the same scratch offsets and the assert at KZ:1816 would
    -- then under-count.
    let (pairIdxEnd, msmLines) ← (enumIdx bySet).foldlM
        (fun outer (setIdx, commitmentsInSet) =>
          (enumIdx commitmentsInSet).foldlM
              (fun st (commitmentIdx, c) => do
                if ecPointBeq c.comm g1Identity then pure st
                else do
                  let (pairIdx, acc) := st
                  let scalar := scalarExpr setIdx commitmentIdx
                  if ecPointBeq c.comm linComm then do
                    let linQueryVar := "lin_query_scalar_" ++ toString pairIdx
                    let linCurVar := "lin_cur_scalar_" ++ toString pairIdx
                    let limbLines ← (List.range meta_.numQuotients).foldlM
                        (fun (st2 : Nat × List String) qIdx => do
                          let pairBase := finalMsmScratch + st2.1 * g1MsmPairBytes
                          let mut1 := ["mcopy(" ++ hashHex pairBase
                              ++ ", add(QUOTIENT_LIMB_COMMS_MPTR_BASE, " ++ hashHex (qIdx * g1Bytes)
                              ++ "), " ++ hashHex g1Bytes ++ ")",
                            "mstore(" ++ hashHex (pairBase + g1Bytes) ++ ", " ++ linCurVar ++ ")"]
                          if qIdx + 1 != meta_.numQuotients then
                            pure (st2.1 + 1, st2.2 ++ mut1
                              ++ [linCurVar ++ " := mulmod(" ++ linCurVar ++ ", lin_x_split, r)"])
                          else pure (st2.1 + 1, st2.2 ++ mut1))
                        (pairIdx, [])
                    let selLines ← (enumIdx simpleSelectorCols).foldlM
                        (fun (st2 : Nat × List String) (selIdx, col) => do
                          let pairBase := finalMsmScratch + st2.1 * g1MsmPairBytes
                          let fixed ← listGetMut data.fixedComms col
                            "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1788"
                          let selectorScalar := "mload(add(SELECTOR_ACC_MPTR, "
                            ++ hashHex (selIdx * wordBytes) ++ "))"
                          pure (st2.1 + 1, st2.2 ++ ["mcopy(" ++ hashHex pairBase ++ ", "
                              ++ printPtr fixed.base.value ++ ", " ++ hashHex g1Bytes ++ ")",
                            "mstore(" ++ hashHex (pairBase + g1Bytes) ++ ", mulmod(" ++ linQueryVar
                              ++ ", " ++ selectorScalar ++ ", r))"]))
                        (limbLines.1, [])
                    pure (selLines.1, acc ++ ["let " ++ linQueryVar ++ " := " ++ scalar,
                      "let " ++ linCurVar ++ " := mulmod(" ++ linQueryVar
                        ++ ", lin_one_minus_x_n, r)"] ++ limbLines.2 ++ selLines.2)
                  else do
                    let pairBase := finalMsmScratch + pairIdx * g1MsmPairBytes
                    pure (pairIdx + 1, acc ++ ["mcopy(" ++ hashHex pairBase ++ ", "
                        ++ printPtr c.comm.base.value ++ ", " ++ hashHex g1Bytes ++ ")",
                      "mstore(" ++ hashHex (pairBase + g1Bytes) ++ ", " ++ scalar ++ ")"])
              ) outer)
        (0, [])
    let fComBase := finalMsmScratch + pairIdxEnd * g1MsmPairBytes
    -- KZ:1816-1819: the assert is on the counter AFTER the f_com bump, so the
    -- comparison here is pairIdxEnd + 1 and not pairIdxEnd. Off-by-one here is the
    -- R-30 class of bug the header names.
    unless pairIdxEnd + 1 == finalMsmTerms do
      throw (Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1816")
    -- KZ:1821-1834. The staticcall is INSIDE "if success {" - the Rust's success
    -- local was established by an earlier block and is not declared here; the port
    -- reproduces the text exactly, including that the final MSM's own return value
    -- is bound to success and not to a fresh name.
    pure (head ++ x4Lines ++ vLines ++ msmLines
      ++ ["mcopy(" ++ hashHex fComBase ++ ", F_COM_MPTR, " ++ hashHex g1Bytes ++ ")",
          "mstore(" ++ hashHex (fComBase + g1Bytes) ++ ", x4_pow_" ++ toString nSets ++ ")"]
      ++ ["if success {",
          "    // exact EIP-2537 G1MSM cost for " ++ toString finalMsmTerms ++ " pair(s)",
          "    success := staticcall(" ++ toString (Midfall.Yul.g1MsmGasPairs finalMsmTerms)
            ++ ", 0x0c, " ++ hashHex finalMsmScratch ++ ", " ++ hashHex finalMsmLen
            ++ ", FINAL_COM_MPTR, " ++ hashHex g1Bytes ++ ")",
          "    success := and(success, eq(returndatasize(), " ++ hashHex g1Bytes ++ "))",
          "}",
          "mstore(V_MPTR, v)"])
  -- KZ:1839-1919: Block 6, the pairing inputs. No loop and no counter, so this one
  -- is a plain list: PAIRING_LHS = pi, PAIRING_RHS = final_com - v*G + x3*pi, built
  -- as two G1MSM-1s and two G1ADDs because the 3-pair MSM is dearer at this size
  -- (the note at KZ:1850-1853). The three gas names are literal Yul macro names in
  -- the Rust's format strings, not interpolated values, so they stay as text.
  let block6 : List String :=
    let scratch := memory.pcsPairingScratchMptr
    let scratchG1B := scratch + g1Bytes
    let scratchG1AddScalar := scratch + g1AddInputBytes
    ["// Scale z*pi - vG before the final pairing check",
     "// pairing inputs (LHS = pi; RHS = final_com - v*G + x3*pi)",
     -- PAIRING_LHS = pi (paired against G2_BASE).
     "mcopy(PAIRING_LHS_MPTR, PI_MPTR, " ++ hashHex g1Bytes ++ ")",
     -- tmp = (-v) * G.
     "mcopy(" ++ hashHex scratch ++ ", G1_BASE_MPTR, " ++ hashHex g1Bytes ++ ")",
     "mstore(" ++ hashHex scratchG1B ++ ", addmod(0, sub(r, mload(V_MPTR)), r))",
     "if success {",
     "    success := staticcall(G1MSM_GAS_1PAIR, 0x0c, " ++ hashHex scratch ++ ", "
       ++ hashHex g1MsmPairBytes ++ ", " ++ hashHex scratch ++ ", " ++ hashHex g1Bytes ++ ")",
     "    success := and(success, eq(returndatasize(), " ++ hashHex g1Bytes ++ "))",
     "}",
     -- tmp += final_com.
     "mcopy(" ++ hashHex scratchG1B ++ ", FINAL_COM_MPTR, " ++ hashHex g1Bytes ++ ")",
     "if success {",
     "    success := staticcall(G1ADD_GAS, 0x0b, " ++ hashHex scratch ++ ", "
       ++ hashHex g1AddInputBytes ++ ", " ++ hashHex scratch ++ ", " ++ hashHex g1Bytes ++ ")",
     "    success := and(success, eq(returndatasize(), " ++ hashHex g1Bytes ++ "))",
     "}",
     -- tmp += x3 * pi.
     "mcopy(" ++ hashHex scratchG1B ++ ", PI_MPTR, " ++ hashHex g1Bytes ++ ")",
     "mstore(" ++ hashHex scratchG1AddScalar ++ ", mload(X3_MPTR))",
     "if success {",
     "    success := staticcall(G1MSM_GAS_1PAIR, 0x0c, " ++ hashHex scratchG1B ++ ", "
       ++ hashHex g1MsmPairBytes ++ ", " ++ hashHex scratchG1B ++ ", " ++ hashHex g1Bytes ++ ")",
     "    success := and(success, eq(returndatasize(), " ++ hashHex g1Bytes ++ "))",
     "}",
     "if success {",
     "    success := staticcall(G1ADD_GAS, 0x0b, " ++ hashHex scratch ++ ", "
       ++ hashHex g1AddInputBytes ++ ", " ++ hashHex scratch ++ ", " ++ hashHex g1Bytes ++ ")",
     "    success := and(success, eq(returndatasize(), " ++ hashHex g1Bytes ++ "))",
     "}",
     -- Persist as PAIRING_RHS = final_com - v*G + x3*pi.
     "mcopy(PAIRING_RHS_MPTR, " ++ hashHex scratch ++ ", " ++ hashHex g1Bytes ++ ")"]
  -- KZ:1921: the six blocks in the Rust's push order. Block 2 is pushed only when
  -- nb_x1_powers > 0 (KZ:1068) and the q_com trace block only when trace (KZ:1292);
  -- Block 3 is not one block but one per point set (KZ:1287 is inside the loop).
  pure ([block1]
    ++ (if nbX1Powers > 0 then [block2] else [])
    ++ block3
    ++ (if trace then [traceBlock] else [])
    ++ [block4, block5, block6])
end Midfall.Generator

/-! # Known-answer tests for the KZG port

Every gate names the wrong implementation it rules out, in the sense docs/REVIEW.md
R-38 states at the end of its entry and R-41 turns into a rule: a gate's stated scope
is justified only by a perturbation INSIDE that scope, actually run, and the notes
below say what reddened and - in the cases marked FAILED TO REDDEN - what did not.

The expected sides come in two kinds, and the kinds are not equally strong.

The strongest are the assertions of KZ:1928-2226, the reference's own #[cfg(test)]
mod tests, which this file does not control: ten #[test] fns, all ten reproduced
below. The second kind is arithmetic derived here from the ported definitions - the
Encoding.lean fixture's 22 queries, its five point sets, its emitted Yul. Those are
checked against the port and not against an outside source, and each says so. The
fixture itself is NOT re-derived here: metaF and dataF are Encoding.lean's own
metaFixture and dataFixture (Encoding.lean:1290, Encoding.lean:1426), whose
commitment addresses Encoding.lean's dataNew_comms_ok pins against hand-computed
memory.

PERTURBATION LOG. Each perturbation named below was applied to this file, the module
rebuilt with lake build, the set of red gates recorded, and the edit reverted and
re-verified green. Perturbations that produced no red are reported under FAILED TO
REDDEN. -/

namespace Midfall.Generator.KzgKats

open Midfall Midfall.Halo2 Midfall.Generator

/-! ## Reading helpers -/

/-- Reading an Except Fault as its value, degrading to a caller-chosen wrong value so
    that a panic makes the gate red rather than unelaboratable. -/
def unFault {α : Type} (e : Except Fault α) (d : α) : α :=
  match e with | .ok a => a | .error _ => d

/-- Reading an Except Fault as "it succeeded at all". -/
def okFault {α : Type} (e : Except Fault α) : Bool :=
  match e with | .ok _ => true | .error _ => false

/-- Reading an Except Fault as "it failed at exactly this panic site", the strongest
    reading Fault.panic allows: it carries a site and no payload (Exec/Error.lean:56-58,
    docs/REVIEW.md R-43 F2). -/
def panickedAt {α : Type} (e : Except Fault α) (site : String) : Bool :=
  match e with | .error (Fault.panic s) => s == site | _ => false

def okStr {α : Type} (e : Except String α) : Bool :=
  match e with | .ok _ => true | .error _ => false

def errStrContains {α : Type} (e : Except String α) (want : String) : Bool :=
  match e with | .error m => m.contains want | .ok _ => false

def errStrIs {α : Type} (e : Except String α) (want : String) : Bool :=
  match e with | .error m => m == want | .ok _ => false

/-- The three test handles of KZ:1934-1944 (pt / ev / calldata_ev), renamed with a
    kzg prefix so they cannot collide with anything Encoding.lean exports into the
    namespace this file opens. Same meaning: a memory-backed G1, a memory-backed
    scalar, a calldata-backed scalar. -/
def kzgPt (off : Nat) : EcPoint := EcPoint.new (ptrMemory (valueFromNat off))
def kzgEv (off : Nat) : Word := Word.fromPtr (ptrMemory (valueFromNat off))
def kzgCalldataEv (off : Nat) : Word := Word.fromPtr (ptrCalldata (valueFromNat off))

/-- A CommitmentEntry as a comparable string: which commitment, which set, which evals. -/
def entryKey (c : CommitmentEntry) : String :=
  ecPointKey c.comm ++ "/set" ++ toString c.setIndex ++ "/"
    ++ String.intercalate "," (c.evals.map wordKey)

/-- The Rust's Debug of a PcsQuerySource, reduced to the shortest tag that names the
    variant and its payload indices; used to label rows, never to compare them. -/
def srcTag (s : PcsQuerySource) : String := match s with
  | .advice k => "advice " ++ toString k.column
  | .committedInstance k => "ci " ++ toString k.column
  | .permutationZ set kind => "pz " ++ toString set ++ " "
      ++ (match kind with | .cur => "cur" | .next => "next" | .last => "last")
  | .lookupMultiplicity l => "lm " ++ toString l
  | .lookupHelper l c => "lh " ++ toString l ++ "." ++ toString c
  | .lookupAccumulator l r => "la " ++ toString l ++ "." ++ toString r
  | .trash i => "trash " ++ toString i
  | .fixed k => "fixed " ++ toString k.column
  | .permutationCommon c => "pc " ++ toString c.index
  | .linearization => "lin"

/-! ## The fixtures

metaF and dataF are Encoding.lean's, unchanged, so the query list this file plans is
the query list Encoding.lean already pins. memF is Encoding.lean's memFixture with
SEVEN more bases overridden, and the override is not decoration: in
LayoutKats.verifierLayoutFixture every PCS base is 0, so f_com, pi and
quotient_limb[0] are all memory:0x00 and the hazard-6 cover check - which compares
POINTS and nothing else - would let one hit cover three. Distinct bases are what
make validateAbsorbedCoverage_fixture_ok mean anything. Data.new never reads these
seven fields, so dataF stays consistent with memF for everything it was built from. -/

def metaF : ConstraintSystemMeta := Midfall.Generator.EncodingKats.metaFixture
def dataF : Data := Midfall.Generator.EncodingKats.dataFixture

def memF : VerifierMemoryLayout :=
  { Midfall.Generator.EncodingKats.memFixture with
    quotientLimbCommsMptrBase := ptrMemory (valueFromNat 0x7000)
    fComMptr := ptrMemory (valueFromNat 0x9000)
    piMptr := ptrMemory (valueFromNat 0x9020)
    pcsQEvalSourceTableMptr := 0x8000
    pcsQComTraceScratchMptr := 0x8100
    pcsFinalMsmScratchMptr := 0x8200
    pcsPairingScratchMptr := 0x9200 }

/-- The proof calldata layout of the fixture plan, built the way Abi.lean's own
    fixture case builds it (Abi.lean:1049): proof_cptr 0, num_main_evals, and 22 as
    the point-set count, which total_g1_count does not read. Its total_g1_count is 17,
    which is what absorbedCoverage_countMismatch_ok breaks by one. -/
def proofLayoutF : ProofCalldataLayout :=
  match ProofCalldataLayout.fromProtocol metaF.protocol 0 metaF.numMainEvals 22 with
  | .ok l => l
  | .error _ => proofCalldataLayoutDefault

/-- The fixture query list; the empty list if planning panics, which makes every gate
    that reads it go red rather than silently pass. -/
def qsF : List Query := unFault (queries metaF dataF) []

/-- A meta whose plan is exactly the given sources. -/
def metaOnly (sources : List PcsQuerySource) : ConstraintSystemMeta :=
  { metaF with protocol := { metaF.protocol with pcsQueries := sources } }

def adviceSrc (col : Nat) (rot : Int) : PcsQuerySource :=
  PcsQuerySource.advice { column := col, rotation := rot }

/-! ## Scaffolding gates -/

/-- THE BTreeMap MODEL, hazard 1's machinery. Three behaviours of KZ:466 that a
    shortcut loses: a repeat of an existing key does NOT renumber (or_insert keeps
    the old value), a new key takes m.length - the count BEFORE the insert - and the
    list stays ascending by key under Rust's Vec<usize> Ord, lexicographic with the
    shorter prefix first. Rules out modelling the map as a plain insertion-ordered
    list (the last row would then sit after [0, 1, 2] and not before it) and as a
    sorted list numbered by position (the second row would be 0 and not 1).

    PERTURBATION RUN, AS ACTUALLY OBSERVED: numbering by the insertion position in
    the sorted list (the span length instead of m.length) reddens THIS GATE plus
    nine others - hazard1_insertionOrderOk_ok, anchorIntermediateSetsShape_ok,
    sortSets_remapTotality_ok, intermediateSets_featureBranch_ok,
    memoryRequirements_rolledTable_ok, memoryRequirements_signedRotations_ok,
    computations_blockOrder_ok, computations_hexFormatter_ok and
    computations_traceAndTruncationBranches_ok - because the whole partition is
    renumbered. Dropping the m.any guard (so a repeat renumbers) reddens this gate
    and ten others, but NOT duplicateQuery_bothArms_ok: the renumbered duplicate
    still agrees with itself. Making the list insertion-ordered instead of
    key-sorted reddens this gate and nothing else. -/
def btreeMapEntryOrInsert_ok : Bool :=
  let m1 := btreeMapEntryOrInsert [] [0, 1]
  let m2 := btreeMapEntryOrInsert m1 [0]
  let m3 := btreeMapEntryOrInsert m2 [0, 1]
  let m4 := btreeMapEntryOrInsert m3 [2]
  m1 == [([0, 1], 0)]
    && m2 == [([0], 1), ([0, 1], 0)]
    && m3 == [([0], 1), ([0, 1], 0)]
    && m4 == [([0], 1), ([0, 1], 0), ([2], 2)]
    && btreeMapGet m4 [0] == some 1
    && btreeMapGet m4 [0, 1] == some 0
    && btreeMapGet m4 [7] = none
    && natListCmp [0] [0, 1] == .lt
    && natListCmp [1] [0, 1] == .gt
    && natListCmp [] [] == .eq

/-- intMaxOr and intMinOr are Option folds and NOT foldl max 0, and the difference is
    observable twice over: KZ:992-993 takes max and min over the SIGNED distinct
    rotations, and unwrap_or's an EMPTY list where Rust's iterator max is None and
    not Some(0). A foldl max 0 would answer 0 for [-3, -1] and Block 1 would then
    emit no backward walk at all.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: intMaxOr as (xs.foldl max 0 d) reddens
    THIS GATE AND NOTHING ELSE, and intMinOr as (xs.foldl min 0 d) reddens this gate
    and nothing else - the last two rows are what make the min dual visible, and
    without them (the inherited gate's rows) the intMinOr perturbation reddened
    NOTHING AT ALL, which is reported here rather than hidden. Neither reaches
    computations_blockOrder_ok, because the fixture's rotations straddle zero so the
    naive foldl agrees with the Option fold on both ends. FAILED TO REDDEN: swapping
    the two helpers at their call sites does not redden this gate, which tests the
    helpers and not the call sites. -/
def intMaxOr_minMaxOr_ok : Bool :=
  intMaxOr 0 [-3, -1] == -1
    && intMinOr 0 [-3, -1] == -3
    && intMaxOr 0 [(-10), (-1), 0, 1] == 1
    && intMinOr 0 [(-10), (-1), 0, 1] == -10
    && intMaxOr 0 [] == 0
    && intMinOr 0 [] == 0
    && intMaxOr 7 [2, 5] == 5
    && intMinOr 7 [2, 5] == 2
    && intMinOr 0 [2, 5] == 2
    && intMaxOr 0 [(-5), (-2)] == -2
    && intRangeInclusive 1 3 == [1, 2, 3]
    && intRangeInclusive 1 0 == []
    && intRange (-3) 0 == [-3, -2, -1]
    && intRange 0 0 == []

/-- Query::new takes (comm, rotation, eval) while the struct declares (rotation,
    comm, eval) - KZ:69-76 against KZ:78-87. A port that "fixed" the misalignment
    would swap two arguments at all nine call sites. This pins that the first
    argument lands in comm and the second in rotation.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: reordering the FIELDS of structure Query
    reddens NOTHING - Lean's structure literals are named, so field order is
    documentation in Lean even where it is behaviour in Rust, and this gate cannot
    see it. That is reported rather than claimed away. What does redden: perturbing
    Query.new's body so rotation is off by one reddens this gate and twelve others,
    which shows the gate is live on the argument-to-field mapping even though the
    parameter-order risk itself cannot be perturbed without a type error (EcPoint and
    Int are not interchangeable, so a port that swapped comm and rotation in the
    signature would not compile). -/
def query_new_argumentOrder_ok : Bool :=
  let q := Query.new (kzgPt 0x100) 5 (kzgEv 0x200)
  ecPointBeq q.comm (kzgPt 0x100) && q.rotation == 5 && wordBeq q.eval (kzgEv 0x200)
    && (Query.new (kzgPt 0x100) (-1) (kzgEv 0x200)).rotation == -1
    && (List.range 3).all fun i =>
        (Query.new (kzgPt 0x100) (Int.ofNat i) (kzgEv 0x200)).rotation == Int.ofNat i

/-! ## queries, query_from_plan and the I-6 guard -/

/-- ALL TEN ARMS of query_from_plan, on the fixture Data, in the plan's order: the
    twenty-two rows are the ten PcsQuerySource variants (all ten occur in the fixture
    plan) and each pins the triple its arm must produce. Three rows are the ones a
    port loses silently: the committed-instance arm returns G1_IDENTITY_MPTR, so a
    port that compared curve values instead of pointers would not notice; the
    permutation-Z Last arm takes meta.rotation_last = -10 and not 0; and the
    lookup-accumulator arm reads the THIRD and FOURTH slots of the lookup-eval tuple
    and not the first two.

    The comm addresses are hand-derived from Encoding.lean's dataNew_comms_ok (advice
    0x5000 + 0x80*i, permZ base 0x6100, lookup-m 0x6000, helpers 0x6200 and 0x6280,
    lookup-z 0x6300, trash 0x6400, fixed 0x4560, permutation-common 0x45e0..0x4760,
    linearization QUOTIENT_MPTR). The eval addresses are the plan's eval order walked
    from reversed_evals_mptr = 0x3000, whose base Encoding.lean pins; the ORDER is
    read from the port and not from an outside artifact, so this gate detects drift
    in the eval column and does not independently prove it.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: swapping the z_cur and z_next arms of
    the permutation-Z match reddens THIS GATE AND NOTHING ELSE; swapping the lookup
    accumulator's two slots reddens this gate and nothing else; returning rotation 0
    for the permutation-Z Last instead of meta.rotation_last reddens this gate and
    fourteen others (it changes the point-set partition, so almost everything moves).
    The gate is therefore a drift detector on the last row and a precise locator on
    the first two. -/
def queryFromPlan_allArms_ok : Bool :=
  let rows := (qsF.zip metaF.protocol.pcsQueries).map fun (q, s) =>
    srcTag s ++ "|" ++ ecPointKey q.comm ++ "|r" ++ toString q.rotation ++ "|" ++ wordKey q.eval
  rows ==
    ["advice 0|memory:0x5000|r0|mload(0x3020)",
     "advice 1|memory:0x5080|r1|mload(0x3040)",
     "advice 2|memory:0x5100|r-1|mload(0x3060)",
     "advice 3|memory:0x5180|r0|mload(0x3080)",
     "ci 0|memory:G1_IDENTITY_MPTR|r0|mload(0x3000)",
     "pz 0 cur|memory:0x6100|r0|mload(0x3140)",
     "pz 0 next|memory:0x6100|r1|mload(0x3160)",
     "pz 0 last|memory:0x6100|r-10|mload(0x3180)",
     "pz 1 cur|memory:0x6180|r0|mload(0x31a0)",
     "pz 1 next|memory:0x6180|r1|mload(0x31c0)",
     "lm 0|memory:0x6000|r0|mload(0x31e0)",
     "lh 0.0|memory:0x6200|r0|mload(0x3200)",
     "lh 0.1|memory:0x6280|r0|mload(0x3220)",
     "la 0.0|memory:0x6300|r0|mload(0x3240)",
     "la 0.1|memory:0x6300|r1|mload(0x3260)",
     "trash 0|memory:0x6400|r0|mload(0x3280)",
     "fixed 1|memory:0x4560|r0|mload(0x30a0)",
     "pc 0|memory:0x45e0|r0|mload(0x30c0)",
     "pc 1|memory:0x4660|r0|mload(0x30e0)",
     "pc 2|memory:0x46e0|r0|mload(0x3100)",
     "pc 3|memory:0x4760|r0|mload(0x3120)",
     "lin|memory:QUOTIENT_MPTR|r0|mload(QUOTIENT_EVAL_MPTR)"]
    && rows.length == 22
    && (metaF.protocol.pcsQueries.map (fun s => match s with
        | .advice _ => 1 | .committedInstance _ => 2 | .permutationZ _ _ => 3
        | .lookupMultiplicity _ => 4 | .lookupHelper _ _ => 5
        | .lookupAccumulator _ _ => 6 | .trash _ => 7 | .fixed _ => 8
        | .permutationCommon _ => 9 | .linearization => 10)).eraseDups.length == 10

/-- The panic arms of query_from_plan, one row per abort site. KZ:234, KZ:242 and
    KZ:279 are HashMap::get(...).expect; KZ:282 and KZ:284 are HashMap Index ([&k]),
    which panics on a missing key rather than returning None; KZ:251 is the Option
    expect on a permutation-Z Last with no eval, which is the shape of the FINAL
    permutation set (ENC:262-264); KZ:269 is the explicit unsupported-rotation panic.
    Each row removes exactly the entry that one arm reads, so the site is the claim.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: replacing the KZ:234 throw with a default
    Word reddens THIS GATE AND NOTHING ELSE, and replacing the KZ:269 catch-all throw
    with a return of zEval likewise reddens this gate and nothing else - the two runs
    stand for the other four sites, which are the same shape. FAILED TO REDDEN: a wrong LINE NUMBER inside a
    site string reddens only the gate that names that site - Fault.panic carries no
    payload, so the sites are pinned by text and not by behaviour. That is a limit of
    the whole Fault.panic idiom, not of this gate, and it is why the site strings are
    written out in full rather than built from a constant. -/
def queryFromPlan_panics_ok : Bool :=
  let noAdviceEval := { dataF with adviceEvals := [] }
  let noCiEval := { dataF with committedInstanceEvals := [] }
  let noFixedEval := { dataF with fixedEvals := [] }
  let noPermComm := { dataF with permutationComms := [] }
  let noPermEval := { dataF with permutationEvals := [] }
  let noLastEval : Data :=
    { dataF with permutationZEvals :=
        dataF.permutationZEvals.map (fun t => (t.1, t.2.1, (none : Option Word))) }
  let permCol0 := match metaF.protocol.pcsQueries.find? (fun s =>
      match s with | .permutationCommon _ => true | _ => false) with
    | some (.permutationCommon c) => c
    | _ => { index := 0, columnType := Any.fixed }
  panickedAt (queryFromPlan (adviceSrc 0 0) metaF noAdviceEval)
      "proofs/solidity-verifier/src/lowering/kzg/mod.rs:234"
    && panickedAt (queryFromPlan
        (PcsQuerySource.committedInstance { column := 0, rotation := 0 }) metaF noCiEval)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:242"
    && panickedAt (queryFromPlan
        (PcsQuerySource.fixed { column := 1, rotation := 0 }) metaF noFixedEval)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:279"
    && panickedAt (queryFromPlan (PcsQuerySource.permutationCommon permCol0)
        metaF noPermComm) "proofs/solidity-verifier/src/lowering/kzg/mod.rs:282"
    && panickedAt (queryFromPlan (PcsQuerySource.permutationCommon permCol0)
        metaF noPermEval) "proofs/solidity-verifier/src/lowering/kzg/mod.rs:284"
    && panickedAt (queryFromPlan (PcsQuerySource.permutationZ 0 PermutationZEval.last)
        metaF noLastEval) "proofs/solidity-verifier/src/lowering/kzg/mod.rs:251"
    && panickedAt (queryFromPlan (PcsQuerySource.lookupAccumulator 0 2) metaF dataF)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:269"
    && okFault (queryFromPlan (PcsQuerySource.lookupAccumulator 0 1) metaF dataF)
/-! ## The two assertions that sit on top of queries -/

/-- L-2, the identity pin at KZ:104-120, both arms. The assert fires when a query
    resolves to G1_IDENTITY_MPTR and its source is NOT a committed instance, because
    the MSM emitters drop identity commitments while keeping their evals, and that
    is sound only for the committed-instance column. Row 2 forces advice column 0
    onto the identity pointer, which is exactly the shape the assert exists to refuse;
    row 3 is the legal identity, the committed-instance query, which must NOT abort.
    Row 1 is the fixture, where the identity occurs once and legally.

    NON-VACUITY: rows 1 and 3 are true and row 2 is a panic, so neither an
    always-ok nor an always-panic implementation passes.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: dropping the identity check from queries
    reddens THIS GATE AND NOTHING ELSE; dropping the committed-instance exemption (the
    second conjunct) reddens this gate and fourteen others, because the fixture's
    committed-instance query then aborts every plan that uses it. -/
def queries_identityPin_ok : Bool :=
  okFault (queries metaF dataF)
    && panickedAt (queries (metaOnly [adviceSrc 0 0])
        { dataF with adviceComms := g1Identity :: dataF.adviceComms.drop 1 })
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:114"
    && okFault (queries (metaOnly [PcsQuerySource.committedInstance
        { column := 0, rotation := 0 }]) dataF)
    && ecPointBeq (unFault (queryFromPlan (PcsQuerySource.committedInstance
        { column := 0, rotation := 0 }) metaF dataF) (Query.new (kzgPt 0) 0 (kzgEv 0))).comm
        g1Identity

/-- I-6, the permutation-order guard at KZ:136-223, all four abort sites plus the
    early return. The guard re-plans the circuit with the z block reordered into the
    upstream (Cur, Next) then reversed-Last shape and refuses a plan whose point-set
    structure changes.

    Row 1 is the early return (no permutation-Z source in the plan). Row 2 is the
    contiguity assert: the z queries are at positions 0 and 2 with an advice query
    between them. Row 3 is the pass arm on the fixture. Row 4 hands the guard a
    generator order of NO queries at all, so the point-set lists differ and KZ:201
    fires. Row 5 hands it the fixture list plus one extra commitment that lands in an
    EXISTING point set, so the point-set lists agree and only the commitment count
    differs - KZ:207. Row 6 replaces the first query's commitment with a fresh one in
    the same set, so the lists and the count agree and only the per-commitment
    comparison fails - KZ:214.

    NON-VACUITY: three distinct sites plus two ok rows, so an implementation that
    always returns ok and one that always panics both fail.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: deleting the reverse on the Last block
    reddens NOTHING, and that is the honest result - for the fixture plan the two
    orderings produce identical intermediate sets, which is precisely the property the
    guard asserts, so a port that dropped the reorder cannot be caught by a plan that
    satisfies the guard. Rows 4-6 were built to reach the three structural asserts
    individually, and each does: removing the KZ:201 check reddens THIS GATE AND
    NOTHING ELSE, removing KZ:207 reddens this gate and nothing else, removing KZ:214
    reddens this gate and nothing else. The contiguity assert (KZ:152) is reached by
    row 2 and is not separately perturbable without also breaking rows 3-6. -/
def assertPermutationOrder_bothArms_ok : Bool :=
  let noZ := metaOnly [adviceSrc 0 0]
  let splitZ := metaOnly [PcsQuerySource.permutationZ 0 PermutationZEval.cur,
    adviceSrc 0 0, PcsQuerySource.permutationZ 0 PermutationZEval.next]
  let extraComm := qsF ++ [Query.new (kzgPt 0xdead) 0 (kzgEv 0x900)]
  let swappedComm := match qsF with
    | [] => []
    | q :: rest => Query.new (kzgPt 0xdead) q.rotation q.eval :: rest
  okFault (assertPermutationQueryOrderIsUpstreamEquivalent noZ dataF [])
    && panickedAt (assertPermutationQueryOrderIsUpstreamEquivalent splitZ dataF [])
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:152"
    && okFault (assertPermutationQueryOrderIsUpstreamEquivalent metaF dataF qsF)
    && panickedAt (assertPermutationQueryOrderIsUpstreamEquivalent metaF dataF [])
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:201"
    && panickedAt (assertPermutationQueryOrderIsUpstreamEquivalent metaF dataF extraComm)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:207"
    && panickedAt (assertPermutationQueryOrderIsUpstreamEquivalent metaF dataF swappedComm)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:214"

/-! ## construct_intermediate_sets_impl: hazards 1, 2, 3 and the anchor -/

/-- HAZARD 3, both arms of the duplicate-query assert at KZ:444-450. Two queries may
    share (commitment, rotation) legally - several columns can point at one slot - and
    the assert fires only when the evals CONFLICT. Row 1 is the silent collapse: one
    commitment entry, one eval, one point set. Row 2 is the abort. Row 3 is the
    non-duplicate control: the same commitment at two rotations coalesces into one
    entry with two evals, which is a different code path (KZ:451-452) and must not be
    confused with the duplicate path.

    NON-VACUITY: rows 1 and 3 succeed with different shapes and row 2 panics.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: making the conflicting arm silent
    (dropping the assert) reddens THIS GATE AND NOTHING ELSE, which is exactly the
    arm the assert exists for. FAILED TO REDDEN, and it is a real finding: making the
    duplicate arm PUSH a second (point_index, eval) pair instead of continuing
    reddens NOTHING in the file. The push is invisible because step 2 runs
    sort_unstable + dedup on the point indices and step 3 aligns evals by sorted
    position, so the duplicated pair collapses again two steps later. The observable
    content of KZ:449's continue is therefore only the eval-conflict check, and row 1
    of this gate pins the shape rather than the mechanism. -/
def duplicateQuery_bothArms_ok : Bool :=
  let agree := [Query.new (kzgPt 0x100) 5 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 5 (kzgEv 0x200)]
  let conflict := [Query.new (kzgPt 0x100) 5 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 5 (kzgEv 0x210)]
  let distinct := [Query.new (kzgPt 0x100) 5 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 6 (kzgEv 0x210)]
  let a := unFault (constructIntermediateSetsImpl agree) { commitments := [], pointSets := [] }
  let d := unFault (constructIntermediateSetsImpl distinct) { commitments := [], pointSets := [] }
  a.commitments.length == 1
    && (a.commitments.map (fun c => c.evals.length) == [1])
    && a.pointSets == [[5]]
    && panickedAt (constructIntermediateSetsImpl conflict)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:446"
    && d.commitments.length == 1 && (d.commitments.map (fun c => c.evals.length) == [2])
    && d.pointSets == [[5, 6]]

/-- HAZARD 2. EcPoint equality here is POINTER equality by construction: EcPoint is a
    newtype over Ptr (ENC:785-788) and Ptr is (Location, Value), so Lean's structural
    comparison of the two fields IS the Rust's derived PartialEq on the pointer. The
    rows state the four consequences a reviewer would ask about: two handles built
    from the same offset are equal; a memory handle and a calldata handle at the same
    offset are NOT; a symbolic handle and a concrete one at the same numeric offset
    are NOT; and every committed-instance column shares G1_IDENTITY_MPTR, which is
    the aliasing the doc at KZ:437-443 describes and the reason hazard 3 exists.

    This is the same hazard R-7 flagged in the VERIFIER, where CommitmentReference
    uses std::ptr::eq; the difference, said at constructIntermediateSetsImpl, is that
    the pointer here is a PLANNED memory address and not a Rust allocation.

    PERTURBATION RUN: comparing ecPointKey instead of the pointers reddens row 3 (both
    render as 0x100 under a location-blind key); comparing only the Value reddens rows
    2 and 3; comparing only the Location reddens row 1. -/
def ecPointEquality_isPointerEquality_ok : Bool :=
  ecPointBeq (kzgPt 0x100) (EcPoint.new (ptrMemory (valueFromNat 0x100)))
    && ! ecPointBeq (kzgPt 0x100) (EcPoint.new (ptrCalldata (valueFromNat 0x100)))
    && ! ecPointBeq (kzgPt 0x100) (EcPoint.new (ptrMemory (valueFromStr "X0")))
    && ecPointBeq g1Identity (EcPoint.new (ptrMemory (valueFromStr "G1_IDENTITY_MPTR")))
    && (dataF.committedInstanceComms.all (fun c => ecPointBeq c g1Identity))
    && (dataF.adviceComms.any fun c => ! ecPointBeq c g1Identity)
    && ! ecPointBeq (kzgPt 0x100) (kzgPt 0x101)
    && wordBeq (kzgEv 0x200) (Word.fromPtr (ptrMemory (valueFromNat 0x200)))
    && ! wordBeq (kzgEv 0x200) (kzgCalldataEv 0x200)

/-- HAZARD 1, THE TRAP ITSELF. KZ:460-467 numbers the point sets by INSERTION order
    while the BTreeMap iterates them in sorted-key order, and the two disagree as soon
    as the first commitment's index set is not the lexicographically smallest. This is
    the smallest case that shows it: commitment A is opened at rotations {5, 6} and so
    claims point indices {0, 1}, key [0, 1]; commitment B is opened at {7}, key [2];
    commitment C is opened at {5} alone, key [0], which sorts BEFORE [0, 1].

    Insertion numbering (the Rust): A = 0, B = 1, C = 2, so point_sets is
    [[5, 6], [7], [5]]. Sorted-key numbering (the wrong port): C = 0, A = 1, B = 2, so
    point_sets would be [[5], [5, 6], [7]]. The second row is the wrong answer and is
    asserted absent, which is what stops this gate from being a tautology about the
    first row.

    Every later use of the map is a lookup or a length except the one iteration at
    KZ:501, and that iteration writes point_sets[set_idx] by VALUE - traced in full at
    constructIntermediateSetsImpl - so the trap is only in the numbering and not in
    the visit order.

    PERTURBATION RUN: numbering the sets by their position in the sorted key list
    (enumerate over pointIdxSets instead of carrying the value) reddens this gate and
    anchorIntermediateSetsShape_ok; making the map insertion-ordered rather than
    key-sorted reddens btreeMapEntryOrInsert_ok and this gate. -/
def hazard1_insertionOrderOk_ok : Bool :=
  let qs := [Query.new (kzgPt 0x100) 5 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 6 (kzgEv 0x210),
    Query.new (kzgPt 0x110) 7 (kzgEv 0x220),
    Query.new (kzgPt 0x120) 5 (kzgEv 0x230)]
  let raw := unFault (constructIntermediateSetsImpl qs) { commitments := [], pointSets := [] }
  raw.pointSets == [[5, 6], [7], [5]]
    && raw.commitments.map (fun c => c.setIndex) == [0, 1, 2]
    && raw.pointSets != [[5], [5, 6], [7]]
    && raw.commitments.map (fun c => c.evals.length) == [2, 1, 1]
    && raw.commitments.length == 3

/-- THE ANCHOR. Hazards 1, 3 and 4 in one hand-made query list, and the shape the
    Phase 4 construct_intermediate_sets lemma will be stated against.

    The list: A = pt 0x100 opened at rotations 5 and 6; B = pt 0x110 opened at 7;
    C = pt 0x120 opened at 5, and then opened at 5 AGAIN with the same eval, which is
    hazard 3's legal duplicate and must collapse silently.

    Hazard 1: the insertion order of the three index sets is [0,1] (A, value 0),
    [2] (B, value 1), [0] (C, value 2), while the sorted key order is [0], [0,1], [2].
    So point_sets before sorting is [[5,6],[7],[5]] and NOT [[5],[5,6],[7]].
    Hazard 4: sets 1 and 2 both have cardinality 1, so sort_sets' tiebreak by original
    index decides between them, and it puts [7] before [5] - content order would put
    [5] first.
    The whole sorted shape, pinned below: point_sets = [[7],[5],[5,6]] with A in set 2,
    B in set 0 and C in set 1.

    This is the one gate worth more than all the small ones, so every component is
    pinned separately as well: the commitment list in first-seen order with its eval
    vectors, the set indices after remapping, and the point sets themselves.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: sorted-key numbering instead of insertion
    numbering reddens this gate and three others (hazard1_insertionOrderOk_ok,
    sortSets_remapTotality_ok and computations_blockOrder_ok) - point_sets becomes
    [[5],[7],[5,6]] after sorting and the set indices become 1, 2, 0. Keying sort_sets
    on the set CONTENTS reddens this gate and three others. Keying it on cardinality
    alone reddens nothing once the sort is stable - see sortSets_tiebreak_ok, whose
    note records that this same perturbation reddened four gates BEFORE the stability
    fix. Dropping the duplicate row reddens nothing here, and that is hazard 3's point:
    the legal duplicate does not change the shape. -/
def anchorIntermediateSetsShape_ok : Bool :=
  let qs := [Query.new (kzgPt 0x100) 5 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 6 (kzgEv 0x210),
    Query.new (kzgPt 0x110) 7 (kzgEv 0x220),
    Query.new (kzgPt 0x120) 5 (kzgEv 0x230),
    Query.new (kzgPt 0x120) 5 (kzgEv 0x230)]
  let raw := unFault (constructIntermediateSetsImpl qs) { commitments := [], pointSets := [] }
  let s := unFault (sortSets raw) { commitments := [], pointSets := [] }
  raw.pointSets == [[5, 6], [7], [5]]
    && s.pointSets == [[7], [5], [5, 6]]
    && (s.commitments.map entryKey
        == ["memory:0x0100/set2/mload(0x0200),mload(0x0210)",
            "memory:0x0110/set0/mload(0x0220)", "memory:0x0120/set1/mload(0x0230)"])
    && s.commitments.length == 3
    && (s.commitments.map (fun c => c.evals.length) == [2, 1, 1])
    && (s.commitments.all fun c => c.setIndex < s.pointSets.length)
    && (s.commitments.all fun c =>
          (s.pointSets.getD c.setIndex []).length == c.evals.length)

/-- rust: KZ:2021-2096 (intermediate_sets_partitions_by_rotation_set), the reference's
    own test, reproduced assertion for assertion. c0 at {0}, c1 and c2 at {0,1}, c3 at
    {0,1,-1}. The test checks the sorted cardinalities, the sorted CONTENT of each set
    (each set is re-sorted before comparison, deliberately, so the test does not couple
    to point_index_of order), the eval/point length agreement for every commitment, and
    the two named commitments' eval vectors.

    The pairs check at KZ:2085-2089 is reproduced as membership on the zipped list,
    which is what the Rust does with Vec::contains.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: neither of the two perturbations this
    gate was written to justify reddens IT. Aligning evals by insertion order reddens
    evalAlignment_sortedPosition_ok and nothing else, because every commitment in
    THIS fixture already has ascending point indices - the Rust test cannot see the
    bug, which is why the extra gate exists. Dropping the step-2 dedup reddens
    evalAlignment_sortedPosition_ok, intermediateSets_featureBranch_ok and
    augmentQueries_collapseToSingleSet_ok, and not this gate, for the same reason.
    What does redden this gate is renumbering the point-index map on a repeat
    (btreeMapEntryOrInsert's guard), which moves the set indices. -/
def constructIntermediateSets_partitions_ok : Bool :=
  let qs := [Query.new (kzgPt 0x100) 0 (kzgEv 0x200),
    Query.new (kzgPt 0x110) 0 (kzgEv 0x210), Query.new (kzgPt 0x110) 1 (kzgEv 0x230),
    Query.new (kzgPt 0x120) 0 (kzgEv 0x240), Query.new (kzgPt 0x120) 1 (kzgEv 0x260),
    Query.new (kzgPt 0x130) 0 (kzgEv 0x270), Query.new (kzgPt 0x130) 1 (kzgEv 0x290),
    Query.new (kzgPt 0x130) (-1) (kzgEv 0x2b0)]
  let raw := unFault (constructIntermediateSetsImpl qs) { commitments := [], pointSets := [] }
  let sorted := unFault (sortSets raw) { commitments := [], pointSets := [] }
  let sizes := insertionSortBy (fun a b => a < b) (raw.pointSets.map List.length)
  sizes == [1, 2, 3]
    && (sorted.pointSets.map List.length == [1, 2, 3])
    && (insertionSortBy (fun a b => a < b) (sorted.pointSets.getD 0 []) == [0])
    && (insertionSortBy (fun a b => a < b) (sorted.pointSets.getD 1 []) == [0, 1])
    && (insertionSortBy (fun a b => a < b) (sorted.pointSets.getD 2 []) == [(-1), 0, 1])
    && (sorted.commitments.all fun c =>
          c.evals.length == (sorted.pointSets.getD c.setIndex []).length)
    && ((sorted.commitments.filter (fun c => ecPointBeq c.comm (kzgPt 0x100))).map
          (fun c => c.evals.map wordKey) == [["mload(0x0200)"]])
    && ((sorted.commitments.filter (fun c => ecPointBeq c.comm (kzgPt 0x130))).all fun c =>
          let pts := sorted.pointSets.getD c.setIndex [];
          (pts.zip c.evals).any (fun p => p.1 == 0 && wordBeq p.2 (kzgEv 0x270))
            && (pts.zip c.evals).any (fun p => p.1 == 1 && wordBeq p.2 (kzgEv 0x290))
            && (pts.zip c.evals).any (fun p => p.1 == -1 && wordBeq p.2 (kzgEv 0x2b0)))
    && sorted.commitments.length == 4

/-- EVAL ALIGNMENT, KZ:479-484. Step 3 writes each eval at the POSITION ITS POINT
    INDEX HOLDS IN THE SORTED LIST, not at its own position in the commitment's
    insertion-ordered point-index vector. Those two differ exactly when a commitment
    first sees a rotation that ANOTHER commitment introduced later in value order -
    which is what this fixture does: B is opened at rotation 6 first (so rotation 6 is
    point index 0), then A is opened at 5 (index 1) and then at 6 again, so A's
    point-index vector is [1, 0] while its sorted key is [0, 1].

    The pinned answer is that A's eval vector comes out as [mload(0x0261),
    mload(0x0250)] - rotation 6's eval first, because the set's rotation list is
    [6, 5] - and NOT in the order the queries arrived. The last row states the
    alignment property the Rust relies on: for every commitment, evals[k] is the eval
    of the rotation at point_sets[set_index][k].

    PERTURBATION RUN: replacing sortedIndices.findIdx? with pointIndices.findIdx?
    (aligning by insertion position) reddens this gate and nothing else in the file -
    reported because it is the ONLY gate that catches it; the Rust test at KZ:2021
    cannot see it, because every commitment in that fixture already has ascending
    point indices. -/
def evalAlignment_sortedPosition_ok : Bool :=
  let qs := [Query.new (kzgPt 0x110) 6 (kzgEv 0x260),
    Query.new (kzgPt 0x100) 5 (kzgEv 0x250),
    Query.new (kzgPt 0x100) 6 (kzgEv 0x261)]
  let raw := unFault (constructIntermediateSetsImpl qs) { commitments := [], pointSets := [] }
  raw.pointSets == [[6], [6, 5]]
    && raw.commitments.map (fun c => c.setIndex) == [0, 1]
    && (raw.commitments.map entryKey
        == ["memory:0x0110/set0/mload(0x0260)",
            "memory:0x0100/set1/mload(0x0261),mload(0x0250)"])
    && (raw.commitments.all fun c =>
          c.evals.length == (raw.pointSets.getD c.setIndex []).length)
    && ((raw.commitments.filter (fun c => ecPointBeq c.comm (kzgPt 0x100))).all fun c =>
          ((raw.pointSets.getD c.setIndex []).zip c.evals).any
              (fun q => q.1 == 6 && wordBeq q.2 (kzgEv 0x261))
            && ((raw.pointSets.getD c.setIndex []).zip c.evals).any
              (fun q => q.1 == 5 && wordBeq q.2 (kzgEv 0x250)))

/-- rust: KZ:2098-2112 (intermediate_sets_dedups_commitments): two queries on one
    commitment at two rotations coalesce into ONE CommitmentEntry with two evals, one
    point set of two points.

    PERTURBATION RUN: matching commitments by eval instead of by comm reddens the
    length-1 assertions; dropping the point-index dedup reddens point_sets[0].len. -/
def constructIntermediateSets_dedups_ok : Bool :=
  let qs := [Query.new (kzgPt 0x100) 0 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 1 (kzgEv 0x220)]
  let r := unFault (sortSets (unFault (constructIntermediateSetsImpl qs)
    { commitments := [], pointSets := [] })) { commitments := [], pointSets := [] }
  r.commitments.length == 1
    && (r.commitments.headD { setIndex := 9, comm := kzgPt 0, evals := [] }).evals.length == 2
    && r.pointSets.length == 1 && (r.pointSets.headD []).length == 2
    && r.pointSets == [[0, 1]]/-! ## sort_sets: hazards 4 and 5, and the feature branch -/

/-- HAZARD 4. sort_sets keys on (cardinality, ORIGINAL index), and the doc at
    KZ:512-517 says the verifier relies on the order so that the first point set holds
    the fixed commitments opened at x. The equal-cardinality case is the only one where
    the second key component can matter at all, and this is that case: sets 1 and 2 of
    the anchor fixture both have cardinality 1, holding [7] and [5] respectively, and
    the original-index tiebreak keeps [7] first even though [5] is the smaller content.

    The last three rows pin the general shape: ascending cardinality, and the set_index
    remap applied to the commitments.

    WHAT THE PERTURBATION ACTUALLY SHOWED, AND A FINDING. Two runs of the same
    perturbation bracket the fix recorded at F6 in the header. WITH THE INHERITED
    insertionSortBy - whose doc claimed stability and did not have it, because
    inserting x after an equal y reverses runs of equal keys - dropping the second key
    component of lenIndexLt reddened FOUR gates: this one, anchorIntermediateSetsShape_ok,
    memoryRequirements_rolledTable_ok and computations_blockOrder_ok. AFTER making the
    sort stable, the same perturbation reddens NOTHING, which is the correct result:
    with a stable sort and an ascending input, (len, i) and (len,) are the same
    permutation, so hazard 4's tiebreak is a guard against an unstable sort that
    neither the Rust (sort_by_key is stable) nor the fixed port has. That is the
    honest answer to hazard 4 and it is only visible because the perturbation was run
    twice. What DOES redden in either state is keying on the set CONTENTS instead of
    on the original index: that reddens this gate, anchorIntermediateSetsShape_ok,
    memoryRequirements_rolledTable_ok and computations_blockOrder_ok, because [5] would
    then come before [7]. Swapping the remap direction reddens this gate and two others. -/
def sortSets_tiebreak_ok : Bool :=
  let e0 : CommitmentEntry := { setIndex := 0, comm := kzgPt 0x100, evals := [kzgEv 0x200, kzgEv 0x210] }
  let e1 : CommitmentEntry := { setIndex := 1, comm := kzgPt 0x110, evals := [kzgEv 0x220] }
  let e2 : CommitmentEntry := { setIndex := 2, comm := kzgPt 0x120, evals := [kzgEv 0x230] }
  let input : IntermediateSets := { commitments := [e0, e1, e2], pointSets := [[5, 6], [7], [5]] }
  let s := unFault (sortSets input) { commitments := [], pointSets := [] }
  s.pointSets == [[7], [5], [5, 6]]
    && s.commitments.map (fun c => c.setIndex) == [2, 0, 1]
    && (s.commitments.map entryKey
        == ["memory:0x0100/set2/mload(0x0200),mload(0x0210)",
            "memory:0x0110/set0/mload(0x0220)", "memory:0x0120/set1/mload(0x0230)"])
    && (s.pointSets.map List.length == [1, 1, 2])
    && (insertionSortBy (lenIndexLt [2, 1, 1]) (List.range 3) == [1, 2, 0])
    && (insertionSortBy (lenIndexLt [3, 1, 2]) (List.range 3) == [1, 2, 0])
    && (insertionSortBy (lenIndexLt [1, 1]) (List.range 2) == [0, 1])

/-- A one-entry CommitmentEntry with a caller-chosen set index, for hazard 5. -/
def badEntry (i : Nat) : CommitmentEntry :=
  { setIndex := i, comm := kzgPt 0x100, evals := [kzgEv 0x200] }

/-- HAZARD 5. KZ:533 reads remap[c.set_index] on a vec of length point_sets.len(), so
    an out-of-range set_index is a release-mode INDEX panic and not a wrap. The
    totality argument (restated at sortSets) is that every set_index is a value of the
    KZ:460 map, which are exactly 0..m-1 with m = point_sets.len(). Rows 1-2 check the
    argument on the fixture and on the anchor: every set_index is in range and every
    commitment's eval count matches its set's cardinality. Row 3 hands sortSets a
    hand-built IntermediateSets with set_index 5 against two point sets, which is the
    shape the argument rules out, and pins that the port panics at KZ:533 rather than
    silently pointing at set 0. Row 4 is the same input with a legal index, which must
    succeed - the non-vacuity pair for row 3.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: replacing listGetMut with
    (remap.getD c.setIndex 0) reddens THIS GATE AND NOTHING ELSE, which is the whole
    point of porting the panic rather than arguing it away. Swapping the remap
    direction (remap[new] = old) reddens this gate, anchorIntermediateSetsShape_ok and
    sortSets_tiebreak_ok. -/
def sortSets_remapTotality_ok : Bool :=
  let sets := unFault (intermediateSets metaF dataF) { commitments := [], pointSets := [] }
  let inRange := sets.commitments.all fun c => c.setIndex < sets.pointSets.length
  let anchor := [Query.new (kzgPt 0x100) 5 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 6 (kzgEv 0x210), Query.new (kzgPt 0x110) 7 (kzgEv 0x220),
    Query.new (kzgPt 0x120) 5 (kzgEv 0x230)]
  let as := unFault (sortSets (unFault (constructIntermediateSetsImpl anchor)
    { commitments := [], pointSets := [] })) { commitments := [], pointSets := [] }
  inRange && (sets.pointSets.length == 5)
    && (as.commitments.all fun c => c.setIndex < as.pointSets.length)
    && (as.commitments.all fun c =>
          (as.pointSets.getD c.setIndex []).length == c.evals.length)
    && panickedAt (sortSets
        { commitments := [badEntry 5], pointSets := [[0], [1]] } : Except Fault IntermediateSets)
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:533"
    && okFault (sortSets { commitments := [badEntry 1], pointSets := [[0], [1]] })

/-- HAZARD 7 / rule R8. KZ:547 switches on data.dummy_eval_words.is_empty(), and that
    is a RUNTIME test, not a cfg: the outer-fewer-point-sets feature decides in vk.rs
    whether the vector is ever filled, and it is FALSE under Features.solidity
    (BASELINE.md), so the RAW branch is the deployed one. Both branches are ported and
    both are gated here on the same circuit: the raw fixture has five point sets, and
    the same Data with the 33 dummy eval Words vk.rs would have allocated collapses
    them into ONE set of three rotations, because compute_dummy_queries pads every
    group out to the union {0, 1, -10}.

    The middle rows are the coupling the Rust's caller has to respect:
    augment_queries_with_dummies asserts the Word count exactly (KZ:377), so 32 or 34
    words abort and 33 does not - and num_dummy_queries on the RAW data is exactly the
    number that makes the assert pass, which is why vk.rs can call it before the
    augmented Data exists.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: always taking the augmented branch
    reddens this gate and five others (sortSets_remapTotality_ok,
    memoryRequirements_rolledTable_ok and the three computations gates, because every
    emitted block changes); always taking the raw branch reddens THIS GATE ALONE;
    dropping the length assert at KZ:377 reddens this gate alone; appending the
    dummies BEFORE the raw queries reddens this gate and
    augmentQueries_collapseToSingleSet_ok. -/
def intermediateSets_featureBranch_ok : Bool :=
  let raw := unFault (intermediateSets metaF dataF) { commitments := [], pointSets := [] }
  let nDummy := unFault (numDummyQueries metaF dataF) 0
  let withDummies : Data :=
    { dataF with dummyEvalWords := (List.range nDummy).map fun i => kzgEv (0x4000 + i * 0x20) }
  let aug := unFault (intermediateSets metaF withDummies) { commitments := [], pointSets := [] }
  dataF.dummyEvalWords.isEmpty
    && raw.pointSets.length == 5
    && nDummy == 33
    && aug.pointSets.length == 2
    && aug.pointSets.map List.length == [3, 4]
    && aug.pointSets.headD [] == [0, 1, -10]
    && aug.commitments.length == raw.commitments.length
    && panickedAt (augmentQueriesWithDummies qsF (List.range 32 |>.map fun i => kzgEv (0x4000 + i * 0x20)))
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:377"
    && panickedAt (augmentQueriesWithDummies qsF (List.range 34 |>.map fun i => kzgEv (0x4000 + i * 0x20)))
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:377"
    && okFault (augmentQueriesWithDummies qsF (List.range 33 |>.map fun i => kzgEv (0x4000 + i * 0x20)))

/-- rust: KZ:2118-2207, all FOUR of the reference's compute_dummy_queries tests,
    reproduced as the exact output vectors the Rust asserts - including the two empty
    cases, which are what stop the helper from being a "pad everything" function.

    Test 1 (KZ:2119): all singletons, so the union is empty and nothing is emitted.
    Test 2 (KZ:2131): two non-singleton groups sharing one rotation set, so nothing is
    missing. Test 3 (KZ:2144): {0,1} and {0,2} unify to {0,1,2} and each group is
    padded with the one it lacks, in group order then union order. Test 4 (KZ:2174):
    the midnight-proofs asymmetry - a singleton contributes nothing to the union but is
    still padded TO it, which is why group 0 gets two dummies here.

    The DummyQuery list is compared with the derived BEq (the Rust derives PartialEq
    and the two fields are usize and i32), which is the same comparison the Rust does.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: letting singletons into the union reddens
    this gate and intermediateSets_featureBranch_ok; emitting in union-major instead
    of group-major order reddens THIS GATE AND NOTHING ELSE, which is the direct
    evidence for the "insertion order of groups * insertion order of points" claim in
    the doc at KZ:320-321. FAILED TO REDDEN: dropping the contains-skip at KZ:336 was
    not run as a separate perturbation because it is the same code path as
    btreeMapEntryOrInsert's repeat guard, which was run (see
    btreeMapEntryOrInsert_ok) and reddened eleven gates without touching this one. -/
def computeDummyQueries_fourRustTests_ok : Bool :=
  let t1 := [Query.new (kzgPt 0x100) 0 (kzgEv 0x200), Query.new (kzgPt 0x110) 0 (kzgEv 0x220),
    Query.new (kzgPt 0x120) 5 (kzgEv 0x240)]
  let t2 := [Query.new (kzgPt 0x100) 0 (kzgEv 0x200), Query.new (kzgPt 0x100) 1 (kzgEv 0x210),
    Query.new (kzgPt 0x110) 0 (kzgEv 0x220), Query.new (kzgPt 0x110) 1 (kzgEv 0x230)]
  let t3 := [Query.new (kzgPt 0x100) 0 (kzgEv 0x200), Query.new (kzgPt 0x100) 1 (kzgEv 0x210),
    Query.new (kzgPt 0x110) 0 (kzgEv 0x220), Query.new (kzgPt 0x110) 2 (kzgEv 0x230)]
  let t4 := [Query.new (kzgPt 0x0f0) 0 (kzgEv 0x100), Query.new (kzgPt 0x100) 0 (kzgEv 0x200),
    Query.new (kzgPt 0x100) 1 (kzgEv 0x210), Query.new (kzgPt 0x110) 0 (kzgEv 0x220),
    Query.new (kzgPt 0x110) 2 (kzgEv 0x230)]
  computeDummyQueries t1 == []
    && computeDummyQueries t2 == []
    && computeDummyQueries t3 == [{ queryIndex := 0, rotation := 2 },
                                  { queryIndex := 2, rotation := 1 }]
    && computeDummyQueries t4 == [{ queryIndex := 0, rotation := 1 },
                                  { queryIndex := 0, rotation := 2 },
                                  { queryIndex := 1, rotation := 2 },
                                  { queryIndex := 3, rotation := 1 }]
    && computeDummyQueries [] == []
    && (computeDummyQueries qsF).length == 33

/-- rust: KZ:2209-2225 (augmented_queries_collapse_to_single_set): the raw list of
    test 3 plus two dummy Words yields six queries, and after the dummy padding the
    whole circuit has exactly ONE point set, of three rotations.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: appending the dummies BEFORE the raw
    queries reddens THIS GATE (the length-4 prefix row and the set shape) and
    intermediateSets_featureBranch_ok. Reordering the raw queries themselves is not
    what this gate is for; the first-seen-order rows are. -/
def augmentQueries_collapseToSingleSet_ok : Bool :=
  let raw := [Query.new (kzgPt 0x100) 0 (kzgEv 0x200), Query.new (kzgPt 0x100) 1 (kzgEv 0x210),
    Query.new (kzgPt 0x110) 0 (kzgEv 0x220), Query.new (kzgPt 0x110) 2 (kzgEv 0x230)]
  let words := [kzgEv 0x300, kzgEv 0x320]
  match augmentQueriesWithDummies raw words with
  | .error _ => false
  | .ok aug =>
      aug.length == 6
        && (match sortSets (unFault (constructIntermediateSetsImpl aug)
              { commitments := [], pointSets := [] }) with
            | .error _ => false
            | .ok s => s.pointSets.length == 1 && (s.pointSets.headD []).length == 3)
        && ((aug.take 4).zip raw).all fun p =>
            ecPointBeq p.1.comm p.2.comm && p.1.rotation == p.2.rotation
              && wordBeq p.1.eval p.2.eval
        && (aug.drop 4).all (fun q => ecPointBeq q.comm (kzgPt 0x100) || ecPointBeq q.comm (kzgPt 0x110))
        && (aug.drop 4).any (fun q => wordBeq q.eval (kzgEv 0x320))

/-! ## Hazard 6: the absorbed-to-precompile coverage boundary -/

/-- proof_absorbed_g1s on the fixture: all SEVENTEEN entries, with their labels and
    their handles, in the Rust's extend order (advice, lookup multiplicity, permutation
    product, per-lookup helper chunks, lookup accumulator, trashcan, quotient limbs,
    then f_com and pi). The order is the content of the item: it decides which missing
    point the error message at KZ:702 names first, so it is pinned and not just
    counted. The addresses come from Encoding.lean's dataNew_comms_ok plus memF's own
    seven overrides.

    Note what is NOT here, and why: the fixed and permutation-common commitments come
    from the VK and are never absorbed as user-controlled points, so hazard 6 does not
    apply to them - which is exactly why the count check against total_g1_count is a
    cross-module invariant and not a tautology.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: swapping the lookup_m_comms and
    lookup_z_comms blocks reddens THIS GATE AND NOTHING ELSE (labels and addresses
    both move); dropping the f_com and pi tail reddens this gate plus
    absorbedCoverage_countMismatch_ok and validateAbsorbedCoverage_fixture_ok. -/
def proofAbsorbedG1s_fixture_ok : Bool :=
  let a := proofAbsorbedG1s metaF dataF memF
  (a.map fun t => t.label ++ " " ++ ecPointKey t.point) ==
    ["advice[0] memory:0x5000", "advice[1] memory:0x5080", "advice[2] memory:0x5100",
     "advice[3] memory:0x5180", "lookup_multiplicity[0] memory:0x6000",
     "permutation_product[0] memory:0x6100", "permutation_product[1] memory:0x6180",
     "lookup_helper[0][0] memory:0x6200", "lookup_helper[0][1] memory:0x6280",
     "lookup_accumulator[0] memory:0x6300", "trashcan[0] memory:0x6400",
     "quotient_limb[0] memory:0x7000", "quotient_limb[1] memory:0x7080",
     "quotient_limb[2] memory:0x7100", "quotient_limb[3] memory:0x7180",
     "f_com memory:0x9000", "pi memory:0x9020"]
    && a.length == 17
    && a.length == proofLayoutF.totalG1Count
    && ((a.map fun t => ecPointKey t.point).eraseDups.length == 17)

/-- The three claims of precompile_validated_g1s that make hazard 6 true, each
    separated out: (1) the G1 identity is skipped, so no absorbed committed-instance
    point is claimed to reach a validating precompile - and none needs to, because the
    proof carries 128 zero bytes there and there is nothing to subgroup-check; (2) the
    synthetic linearization commitment is replaced by the four quotient limbs it
    expands into, so the absorbed quotient_limb entries are covered by NAME and by
    POINT; (3) f_com and pi are appended unconditionally.

    Row 4 is the negative that matters: the linearization handle itself
    (QUOTIENT_MPTR) must NOT appear in the validated list, because the final MSM never
    touches it. A port that pushed the linearization point instead of its limbs would
    leave all four quotient_limb entries reported missing.

    PERTURBATION RUN: removing the identity skip reddens rows 1 and 5; pushing the
    linearization point instead of expanding it reddens rows 2, 3 and 4 and
    validateAbsorbedCoverage_fixture_ok; dropping the f_com push reddens row 3. -/
def precompileValidated_identitySkip_ok : Bool :=
  let v := unFault (precompileValidatedG1s metaF dataF memF) []
  let absorbed := proofAbsorbedG1s metaF dataF memF
  let iSets := unFault (intermediateSets metaF dataF) { commitments := [], pointSets := [] }
  let setsOfF := (iSets : IntermediateSets)
  (setsOfF.commitments.any (fun c => ecPointBeq c.comm g1Identity))
    && (v.all fun t => ! ecPointBeq t.point g1Identity)
    && (absorbed.all fun t => ! ecPointBeq t.point g1Identity)
    && (v.filter (fun t => t.label.startsWith "quotient_limb")).length == 4
    && (v.filter (fun t => ecPointBeq t.point (linearizationComm dataF))).isEmpty
    && (v.any fun t => t.label == "f_com via final PCS G1MSM")
    && (v.any fun t => t.label == "pi via final pairing input")
    && (absorbed.all fun t => ecPointBeq t.point g1Identity
          || v.any fun c => ecPointBeq c.point t.point)

/-- rust: KZ:1953-1965 (absorbed_g1_coverage_accepts_later_precompile_input). The
    cover is by POINT and not by label, which is the whole point of the test: the two
    lists use different labels for the same handles and must still pass.

    PERTURBATION RUN: comparing labels instead of points reddens this gate and reddens
    validateG1Coverage_rejects_ok in the opposite direction. -/
def validateG1Coverage_accepts_ok : Bool :=
  let absorbed := [TrackedG1.new "advice[0]" (kzgPt 0x100), TrackedG1.new "pi" (kzgPt 0x200)]
  let inputs := [TrackedG1.new "advice[0] via final PCS G1MSM" (kzgPt 0x100),
    TrackedG1.new "pi via final pairing input" (kzgPt 0x200)]
  okStr (validateG1PrecompileCoverage absorbed inputs)
    && okStr (validateG1PrecompileCoverage [] inputs)
    && okStr (validateG1PrecompileCoverage absorbed (inputs ++ [TrackedG1.new "extra" (kzgPt 0x300)]))

/-- rust: KZ:1967-1978 (absorbed_g1_coverage_rejects_point_without_precompile_input),
    and stronger than the Rust: the reference asserts only that the message contains
    "advice[0]" and "EIP-2537 G1MSM/pairing precompile", and this pins the WHOLE
    string, including the count and the rendered pointer, because the message is a
    Result payload and so survives Fault.panic's loss of payload (the header's ONE
    GENUINE WIDENING note is about exactly this asymmetry).

    Row 3 is the missing.first() rule: with two uncovered points the message names the
    FIRST in absorbed order, which is why proof_absorbed_g1s's order is ported exactly.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: naming the LAST missing instead of the
    first reddens THIS GATE AND NOTHING ELSE; dropping the count from the message
    reddens this gate and nothing else; rendering the pointer through a location-aware
    key instead of printPtr reddens this gate and three others, because the Rust's
    Display for Ptr prints the value only (ENC:716-720). Note the pointer renders as
    0x0100 and not 0x100: printPtr goes through Filters.lean's hexFilter, which pads
    to an even nibble count, and that is the Rust's fmt_hex, not the {:#x} the emitter
    uses - the two formatters in this file are different and computations_hexFormatter_ok
    is what keeps them apart. -/
def validateG1Coverage_rejects_ok : Bool :=
  let absorbed := [TrackedG1.new "advice[0]" (kzgPt 0x100), TrackedG1.new "pi" (kzgPt 0x200)]
  let inputs := [TrackedG1.new "pi via final pairing input" (kzgPt 0x200)]
  errStrIs (validateG1PrecompileCoverage absorbed inputs)
    ("1 absorbed proof G1(s) are not consumed by a later EIP-2537 G1MSM/pairing "
      ++ "precompile; first missing: advice[0] at 0x0100")
    && errStrContains (validateG1PrecompileCoverage absorbed inputs) "advice[0]"
    && errStrContains (validateG1PrecompileCoverage absorbed inputs)
        "EIP-2537 G1MSM/pairing precompile"
    && errStrContains (validateG1PrecompileCoverage
        (absorbed ++ [TrackedG1.new "trashcan[0]" (kzgPt 0x300)]) inputs)
        "2 absorbed proof G1(s)"
    && errStrContains (validateG1PrecompileCoverage
        [TrackedG1.new "advice[0]" (kzgPt 0x100), TrackedG1.new "advice[1]" (kzgPt 0x110)]
        inputs) "first missing: advice[0]"

/-- The count check at KZ:1331-1336 (line numbers per the cite at KZ:731-736), which
    compares two INDEPENDENT derivations of the same number: proof_absorbed_g1s counts
    Data field lengths, total_g1_count counts proof section item counts. Row 1 breaks
    it by adding one pi to the layout, and pins the whole message. Row 2 is the
    fixture, which agrees at 17. Row 3 shows the two derivations can be moved
    independently: dropping one advice commitment from the Data changes the absorbed
    count and not the layout's.

    PERTURBATION RUN: comparing against commitmentG1Count instead of totalG1Count
    reddens row 2 (15 vs 17); dropping the f_com and pi terms from total_g1_count
    would reddened row 2 too, but that def is in Abi.lean and is not this package's to
    perturb - reported rather than run. -/
def absorbedCoverage_countMismatch_ok : Bool :=
  let brokenLayout := { proofLayoutF with pi := { proofLayoutF.pi with
      itemCount := proofLayoutF.pi.itemCount + 1 } }
  errStrIs (unFault (validateAbsorbedG1PrecompileCoverage metaF dataF memF brokenLayout)
      (.error "FAULT"))
    ("absorbed proof G1 count mismatch: generator tracked 17 point(s), "
      ++ "proof layout expects 18")
    && okStr (unFault (validateAbsorbedG1PrecompileCoverage metaF dataF memF proofLayoutF)
      (.error "FAULT"))
    && brokenLayout.totalG1Count == 18
    && proofLayoutF.totalG1Count == 17
    && ! okStr (unFault (validateAbsorbedG1PrecompileCoverage
        (metaOnly []) dataF memF proofLayoutF) (.error "FAULT"))

/-- HAZARD 6, THE ANSWER. validate_absorbed_g1_precompile_coverage RUN on the fixture,
    end to end, and it returns ok: every one of the seventeen absorbed proof G1 points
    reaches an EIP-2537 G1MSM or the pairing input. There is NO counterexample to PLAN
    9.5's points_subgroup_checked on the recorded profile, so the package does not stop.

    The rows say what the ok actually rests on, because a bare ok is weak evidence:
    row 2 pins that the count gate is what it looks like (17 == 17), row 3 pins that
    the identity appears exactly once among the DEDUPLICATED COMMITMENTS and not at all
    among the absorbed points - proof_absorbed_g1s never emits a committed-instance
    point, so KZ:661's identity skip is about the validated side only - and row 4 pins
    that the four quotient limbs are covered by the linearization expansion and not by
    a PCS query. Row 5 is the
    negative control: with one absorbed point removed from the validated list the same
    call errors, so the ok in row 1 is not vacuous.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: removing the identity skip from
    precompile_validated_g1s reddens NOTHING here, and that is stated rather than
    hidden: the cover is one-directional (absorbed must be a subset of validated), so
    dropping a validated entry can only make the check stricter, and on this fixture
    the identity is not in the absorbed list at all.
    precompileValidated_identitySkip_ok is what pins that arm. Removing the
    linearization expansion reddens this gate and two others; comparing by LABEL
    instead of by POINT reddens this gate and three others; comparing the count
    against commitmentG1Count instead of totalG1Count reddens this gate and
    absorbedCoverage_countMismatch_ok; dropping f_com and pi from the absorbed list
    reddens this gate and two others. -/
def validateAbsorbedCoverage_fixture_ok : Bool :=
  let res := validateAbsorbedG1PrecompileCoverage metaF dataF memF proofLayoutF
  let r := unFault res (.error "FAULT")
  okStr r
    && (proofAbsorbedG1s metaF dataF memF).length == proofLayoutF.totalG1Count
    && ((unFault (intermediateSets metaF dataF) { commitments := [], pointSets := [] }
        ).commitments.filter (fun c => ecPointBeq c.comm g1Identity)).length == 1
    && ((proofAbsorbedG1s metaF dataF memF).filter (fun t =>
          t.label.startsWith "quotient_limb[" && ! (t.label.contains "via"))).length == 4
    && ! okStr (validateG1PrecompileCoverage (proofAbsorbedG1s metaF dataF memF)
        ((unFault (precompileValidatedG1s metaF dataF memF) []).drop 1))
    && okFault res
/-! ## Set grouping, MSM sizing and the q_eval strategy -/

/-- The three arms of q_com_terms_for_set in ONE set: the identity contributes 0, the
    linearization commitment contributes linearization_term_count = num_quotients +
    simple_selector_cols.len() = 4 + 1 = 5, and anything else contributes 1. The sum
    is 6, and the four rows separate the arms so that a port which conflated any two
    of them is caught by a different row than the one it would otherwise fool.

    Row 6 pins linearization_term_count itself, and row 7 pins the difference between
    q_com_trace_terms (max over sets) and final_msm_shape (sum over all sets plus one
    for f_com), which is the pair most easily ported as the same function twice.

    PERTURBATION RUN: making the identity arm contribute 1 instead of 0 reddens rows
    1 and 3; using num_quotients alone for the linearization arm reddens rows 2, 6 and
    7; swapping max for sum in q_com_trace_terms reddens row 7 and
    memoryRequirements_rolledTable_ok. -/
def qComTermsForSet_threeArms_ok : Bool :=
  let idE : CommitmentEntry := { setIndex := 0, comm := g1Identity, evals := [kzgEv 0x200] }
  let linE : CommitmentEntry := { setIndex := 0, comm := linearizationComm dataF, evals := [kzgEv 0x210] }
  let adE : CommitmentEntry := { setIndex := 0, comm := kzgPt 0x100, evals := [kzgEv 0x220] }
  qComTermsForSet metaF dataF [idE] == 0
    && qComTermsForSet metaF dataF [linE] == 5
    && qComTermsForSet metaF dataF [adE] == 1
    && qComTermsForSet metaF dataF [idE, linE, adE] == 6
    && qComTermsForSet metaF dataF [] == 0
    && linearizationTermCount metaF == 5
    && metaF.numQuotients == 4 && metaF.simpleSelectorCols.length == 1
    && (finalMsmShape metaF dataF [[idE, linE, adE]]).terms == 7
    && (finalMsmShape metaF dataF [[idE, linE, adE]]).inputBytes == 7 * g1MsmPairBytes
    && qComTraceTerms metaF dataF [[idE, linE, adE], [adE]] == 6
    && qComTraceTerms metaF dataF [] == 0

/-- rust: KZ:1980-2018 (q_eval_roll_strategy_is_single_source_for_planning_and_emission),
    the reference's own test, reproduced exactly: the threshold is 4; four
    memory-backed two-eval commitments roll; making the LAST commitment's SECOND eval
    calldata-backed unrolls; popping that eval instead (ragged rows) also unrolls. The
    two discriminators are independent - a port that checked only the width would pass
    row 2 and fail rows 3 and 4, and one that checked only uniformity would pass row 3
    and fail row 4.

    The last three rows are the arms the Rust test does not exercise but the code has:
    the empty set (KZ:841-843), a three-commitment set below the threshold, and a set
    whose first row is empty.

    PERTURBATION RUN: dropping the location test from can_roll reddens row 3 only;
    dropping the length test reddens row 4 only; comparing against the threshold with
    <= instead of < reddens row 2 (four commitments would unroll); returning Rolled for
    the empty set reddens row 6. -/
def qEvalStrategy_matchesRustTest_ok : Bool :=
  let mk (i : Nat) (evs : List Word) : CommitmentEntry :=
    { setIndex := 0, comm := kzgPt (0x100 + i * 0x80), evals := evs }
  let rolled := [0, 1, 2, 3].map fun i =>
    mk i [kzgEv (0x200 + i * 0x40), kzgEv (0x220 + i * 0x40)]
  let calldataBacked := rolled.take 3 ++ [mk 3 [kzgEv 0x2c0, kzgCalldataEv 0x40]]
  let ragged := rolled.take 3 ++ [mk 3 [kzgEv 0x2c0]]
  let emptyRows := [0, 1, 2, 3].map fun i => mk i []
  qEvalRollThreshold == 4
    && qEvalStrategy rolled == QEvalStrategy.rolled
    && qEvalStrategy calldataBacked == QEvalStrategy.unrolled
    && qEvalStrategy ragged == QEvalStrategy.unrolled
    && qEvalStrategy [] == QEvalStrategy.unrolled
    && qEvalStrategy (rolled.take 3) == QEvalStrategy.unrolled
    && qEvalStrategy emptyRows == QEvalStrategy.rolled

/-- The n_sets == 0 arm of memory_requirements (KZ:868-870), which hands back
    PcsMemoryRequirements::default() - all seven fields zero. An empty query list is a
    legal if useless circuit shape, and the arm is a real early return rather than a
    fallthrough: without it the max over an empty by_set would still be 0 but the
    FinalMsmShape would be from_terms 1 and not from_terms 0, because final_msm_shape
    adds one for f_com unconditionally. That difference is the whole content of this
    gate: row 2 pins the default's final_msm.terms at 0 and row 3 pins that the same
    empty plan, once it has one point set, reports final_msm.terms == 2.

    PERTURBATION RUN: deleting the early return reddens row 1 (finalMsm.terms becomes
    1); returning default() for a NON-empty plan reddens memoryRequirements_rolledTable_ok. -/
def memoryRequirements_empty_ok : Bool :=
  let empty := metaOnly []
  match memoryRequirements empty dataF with
  | .error _ => false
  | .ok r =>
      r.finalMsm.terms == 0 && r.qComTraceMsm.terms == 0
        && r.rotPointsWords == 0 && r.qEvalSetWords == 0
        && r.qEvalSourceTableWords == 0 && r.x1PowersWords == 0 && r.qComWords == 0
        && (match memoryRequirements (metaOnly [adviceSrc 0 0]) dataF with
            | .error _ => false
            | .ok r2 => r2.finalMsm.terms == 2 && r2.rotPointsWords == 1
                && r2.qEvalSetWords == 1 && r2.x1PowersWords == 1)

/-- An eval-source-table staging line of Block 3 (KZ:1197-1201). Named apart so the
    takeWhile below does not have to carry a string literal with a paren in it. -/
def stageLine (l : String) : Bool := l.startsWith "mstore(0x8"

/-- THE COUPLING that makes q_eval_strategy a shared def and not two inlined copies:
    memory_requirements' q_eval_source_table_words is the max over the ROLLED sets of
    commitments.len() * rotations.len(), and Block 3 stages exactly that many
    mstore lines into the table at KZ:1193-1203. If the two disagreed the emitted Yul
    would write past its window. On the fixture the rolled set is set 0 with 13
    commitments and 1 rotation, so the table is 13 words and the staged block has 13
    mstore lines - and the loop bound in the emitted for is 0xd, the same 13.

    Row 4 is the other half: the planner's x1_powers_words (13) is the emitter's
    nb_x1_powers, which is what Block 2's loop bound 0xc (12 = 13 - 1) is derived from.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: dropping the rolled filter so the table
    size is the max over ALL sets reddens NOTHING - on this fixture the widest set is
    the rolled one, so the two readings coincide at 13, and that is reported here
    rather than hidden. It is also why rows 2 and 3 exist: row 3 counts the STAGED
    lines the emitter actually wrote, so a change to the emitter's stage loop reddens
    rows 2 and 3 together even when row 1 cannot see it. Changing the strategy
    threshold reddens this gate (the set stops being rolled and the staging
    disappears). Reading the rotations as Nat instead of Int reddens this gate too. -/
def memoryRequirements_rolledTable_ok : Bool :=
  let req := unFault (memoryRequirements metaF dataF) pcsMemoryRequirementsDefault
  let sets := unFault (intermediateSets metaF dataF) { commitments := [], pointSets := [] }
  let bySet := unFault (commitmentsBySet sets sets.pointSets.length) []
  let b3 := unFault (computations metaF dataF memF false false) []
  let block3set0 := b3.getD 2 []
  let staged := (((block3set0.drop 2).takeWhile stageLine)).length
  let rolledWidths := ((bySet.zip sets.pointSets).filterMap
    fun p => if qEvalStrategy p.1 == QEvalStrategy.rolled then some (p.1.length * p.2.length)
      else none)
  req.qEvalSourceTableWords == 13
    && rolledWidths.foldl max 0 == 13
    && staged == 13
    && req.x1PowersWords == 13
    && (b3.getD 1 []).any (fun l => l.contains "lt(i, 0xc)")
    && (bySet.map List.length).foldl max 0 == 13
    && req.qEvalSetWords == 8
    && req.rotPointsWords == 4

/-- The one place in the file where the SIGNEDNESS of a rotation changes an output:
    KZ:959-964 and KZ:875-878 both sort_unstable + dedup a Vec<i32>, and the fixture's
    distinct rotations are [-10, -1, 0, 1]. Under a Nat reading the same four values
    would order [0, 1, ...negatives last], so rotation 0 would land at index 0 and
    Block 1's first store would be at offset 0x0 instead of 0x40. The rot_points count
    is 4 either way - the header says so - so the ORDER is the only observable, and
    row 2 is what makes this gate about the order and not the count.

    Row 3 pins the same signedness in the other direction: the backward walk runs from
    -1 down to -10, so the LAST store in Block 1 is at offset 0x0 (rotation -10, index
    0) and the loop body executes ten mulmods.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: reading the rotation set as Nat instead
    of Int at KZ:875-878 (btreeSetFromList natCmp over Int.toNat) reddens THIS GATE and
    memoryRequirements_rolledTable_ok - the store order flips, so the first store moves
    from 0x40 to 0x0. Swapping intMaxOr and intMinOr at their call sites was not run
    separately; the two helpers are pinned at their own gate and the call sites are
    pinned by the store-order rows here. -/
def memoryRequirements_signedRotations_ok : Bool :=
  let req := unFault (memoryRequirements metaF dataF) pcsMemoryRequirementsDefault
  let b1 := (unFault (computations metaF dataF memF false false) []).getD 0 []
  let stores := b1.filter (fun l => l.startsWith "mstore(add(ROT_POINTS_MPTR, ")
  let fixtureRots := ((unFault (intermediateSets metaF dataF) { commitments := [], pointSets := [] }) : IntermediateSets).pointSets
  req.rotPointsWords == 4
    && (stores.headD "") == "mstore(add(ROT_POINTS_MPTR, 0x40), x_pow_of_omega)"
    && (stores.getD 1 "") == "mstore(add(ROT_POINTS_MPTR, 0x60), x_pow_of_omega)"
    && (stores.reverse.headD "") == "mstore(add(ROT_POINTS_MPTR, 0x0), x_pow_of_omega)"
    && (b1.filter (fun l => l.contains "omega_inv")).length == 11
    && (b1.filter (fun l => l.contains "mulmod(x_pow_of_omega, omega, r)")).length == 1
    && insertionSortBy (fun a b => a < b) (fixtureRots.flatten.eraseDups) == [(-10), (-1), 0, 1]

/-- static_working_memory_size is one constant read, so the constant cannot be wrong
    without the layout being wrong; what CAN be wrong is the comment around it, which
    claims an arithmetic (2 G1 = 8 words, 2 G2 = 16 words, 1 output = 25 words, rounded
    up to 32). This checks the arithmetic the comment claims and not just the constant,
    which is the only way a gate here can say anything at all.

    PERTURBATION RUN: this gate cannot be reddened by perturbing staticWorkingMemorySize
    alone - returning 33 would redden row 1 and nothing else, and that was run; the
    word-count rows are derived from g1Bytes and the G2 width and would only move if
    Layout.lean's widths moved, which is not this package's file to perturb. -/
def staticWorkingMemorySize_matchesDoc_ok : Bool :=
  staticWorkingMemorySize == 32
    && pcsStaticWorkingWords == 32
    && (2 * g1Bytes + 2 * (2 * g1Bytes) + wordBytes) / wordBytes == 25
    && 25 <= staticWorkingMemorySize
    && g1Bytes == 128 && wordBytes == 32

/-! ## computations: the six blocks -/

/-- The six-step structure the module doc at KZ:7-21 states and that PLAN section 6's
    construct_intermediate_sets lemma will be stated over. The block ORDER is the
    claim: rotation points, x1 powers, one block per point set, the optional q_com
    trace block, f_eval, the final MSM, the pairing inputs. Row 1 pins the eleven first
    lines with trace on and row 2 the ten with trace off, so a merged, split or
    reordered block reddens. Row 3 pins the block-count arithmetic itself:
    1 + 1 + n_sets + (trace ? 1 : 0) + 3.

    PERTURBATION RUN: pushing the trace block before Block 3 reddens row 1; emitting
    Block 3 as one merged block instead of one per set reddens rows 1-3; dropping the
    nb_x1_powers > 0 guard reddens row 2 for a circuit with a single-commitment-per-set
    plan (not this fixture - reported as a limit); swapping Blocks 5 and 6 reddens
    rows 1-2. -/
def computations_blockOrder_ok : Bool :=
  let tt := unFault (computations metaF dataF memF false true) []
  let ff := unFault (computations metaF dataF memF false false) []
  (tt.map (fun b => b.headD "")) ==
    ["// 4 distinct rotation(s)", "// pre-compute 13 x1 power(s)",
     "// q_eval_set[0]: 13 evaluation term(s), 12 commitment term(s) (rolled, m>=4)",
     "// q_eval_set[1]: 1 evaluation term(s), 1 commitment term(s)",
     "// q_eval_set[2]: 1 evaluation term(s), 1 commitment term(s)",
     "// q_eval_set[3]: 2 evaluation term(s), 2 commitment term(s)",
     "// q_eval_set[4]: 1 evaluation term(s), 1 commitment term(s)",
     "// materialize per-set q_com inputs for trace logging",
     "// f_eval via Horner over 5 reversed set(s)",
     "// build final_com and v (KZG single-opening proof, fused MSM)",
     "// Scale z*pi - vG before the final pairing check"]
    && (ff.map (fun b => b.headD "")) ==
      ["// 4 distinct rotation(s)", "// pre-compute 13 x1 power(s)",
       "// q_eval_set[0]: 13 evaluation term(s), 12 commitment term(s) (rolled, m>=4)",
       "// q_eval_set[1]: 1 evaluation term(s), 1 commitment term(s)",
       "// q_eval_set[2]: 1 evaluation term(s), 1 commitment term(s)",
       "// q_eval_set[3]: 2 evaluation term(s), 2 commitment term(s)",
       "// q_eval_set[4]: 1 evaluation term(s), 1 commitment term(s)",
       "// f_eval via Horner over 5 reversed set(s)",
       "// build final_com and v (KZG single-opening proof, fused MSM)",
       "// Scale z*pi - vG before the final pairing check"]
    && tt.length == 11 && ff.length == 10
    && tt.length == 1 + 1 + 5 + 1 + 3
    && ((ff.getD 8 []).filter (fun l => l.startsWith "v := addmod")).length == 5
    && (ff.getD 8 []).any (fun l => l == "let v := calldataload(Q_EVAL_CPTR)")
    -- KZ:1719 is 1..n_sets, exclusive: the f_eval term below supplies s == n_sets, so
    -- an inclusive range would fold q_evals[n_sets] twice. Perturbing the drop to
    -- (List.range (nSets + 1)).drop 1 reddens THIS ROW AND NOTHING ELSE in the file.
    && (ff.getD 8 []).any (fun l => l == "v := addmod(v, mulmod(mload(F_EVAL_MPTR), x4_pow_5, r), r)")
    && (ff.getD 9 []).reverse.headD "" == "mcopy(PAIRING_RHS_MPTR, 0x9200, 0x80)"
    && (ff.getD 8 []).reverse.headD "" == "mstore(V_MPTR, v)"
    && (ff.getD 7 []).reverse.headD "" == "mstore(F_EVAL_MPTR, f_eval)"

/-- Every {:#x} in the Rust is hashHex - "0x" plus minimal lowercase hex with NO
    even-width pad - and not Filters.lean's hexFilter, which pads to an even number of
    nibbles. The two differ from 0x100 upwards and the scratch addresses reach there:
    the fixture emits 0x100 (x1 power 8), 0x180 (x1 power 12 and the fourth quotient
    limb) and 0x1000-scale table addresses. Rows 1-3 pin the unpadded spellings that
    actually occur; row 4 pins the two places a padded formatter would have written
    0x00 and 0x0c0 instead of 0x0 and 0xc; row 5 asserts the absence of any padded
    four-nibble spelling anywhere in the emitted text.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: shadowing hashHex inside computations with
    a padded formatter ("0x" ++ hexFilter n) reddens THIS GATE and three others -
    memoryRequirements_rolledTable_ok, memoryRequirements_signedRotations_ok and
    computations_blockOrder_ok - because the fixture's scratch offsets reach 0x100 and
    above, where the two formatters disagree (0x100 versus 0x0100, 0x0 versus 0x00).
    Note that printPtr, used by the coverage error message, is the PADDED side: the
    file genuinely carries two formatters and the gates keep them apart. -/
def computations_hexFormatter_ok : Bool :=
  let ff := unFault (computations metaF dataF memF false false) []
  let all := ff.flatMap id
  (all.any fun l => l.contains "mload(add(X1_POWERS_MPTR, 0x100))")
    && (all.any fun l => l.contains "add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x180)")
    && (all.any fun l => l.contains "lt(i, 0xc)")
    && (all.any fun l => l == "mstore(add(ROT_POINTS_MPTR, 0x0), x_pow_of_omega)")
    && (all.all fun l => ! (l.contains "0x0100") && ! (l.contains "0x00,")
          && ! (l.contains "0x0c0"))
    && hashHex 256 == "0x100" && hashHex 0 == "0x0" && hashHex 12 == "0xc"
    && hashHex 3584 == "0xe00"

/-- All four combinations of the two bool parameters of computations, KZ:934-935.
    truncated_challenges is cfg!(feature = "truncated-challenges") at the call site in
    artifacts.rs:151-157 and is TRUE in the recorded profile; trace is a render option
    and defaults false. The two arms of the truncation switch declare DIFFERENT Yul
    variables (x4_pow_full only exists in the truncated arm), so a port that merged
    them would emit text that does not compile, and that is what rows 2 and 4 pin.
    Rows 1 and 2 pin Block 2's store arm; rows 3 and 5 pin Block 5's power walk; row 6
    pins the trace switch on both a block that only exists under trace (the q_com
    materialisation) and the rotation-serialisation lines inside Block 1, which are a
    SECOND trace-only region the first switch would miss.

    PERTURBATION RUN, AS ACTUALLY OBSERVED: dropping the b1Trace append reddens THIS
    GATE alone while leaving the block count correct, which is why the last rows check
    content and not only counts; swapping Blocks 5 and 6 reddens this gate and
    computations_blockOrder_ok; merging Block 3 into one block reddens this gate and
    computations_blockOrder_ok. Inverting the Block 2 switch alone (truncatedChallenges
    negated in the mstore arm and nowhere else) reddens THIS GATE AND NOTHING ELSE,
    and that is the evidence that the Block 2 and Block 5 switches are independent:
    the same inversion applied to the Block 5 x4-power walk reddens this gate through
    rows 5-8 instead. Dropping the nb_x1_powers > 0 guard was not run, because the
    fixture always has 13 powers and no gate here reaches a plan with none. -/
def computations_traceAndTruncationBranches_ok : Bool :=
  let bFF := unFault (computations metaF dataF memF false false) []
  let bTF := unFault (computations metaF dataF memF true false) []
  let bFT := unFault (computations metaF dataF memF false true) []
  let bTT := unFault (computations metaF dataF memF true true) []
  let has (bs : List (List String)) (i : Nat) (t : String) : Bool :=
    (bs.getD i []).any (fun l => l.contains t)
  has bFF 1 "mstore(p, acc)"
    && ! has bFF 1 "and(acc,"
    && has bTF 1 "mstore(p, and(acc, 0xffffffffffffffffffffffffffffffff))"
    && ! has bTF 1 "mstore(p, acc)"
    && (bFF.getD 8 []).any (fun l => l == "let x4_pow_0 := 1")
    && (bTF.getD 8 []).any (fun l => l == "let x4_pow_full := 1")
    && (bTF.getD 8 []).any (fun l => l.startsWith "let x4_pow_1 := and(x4_pow_full,")
    && (bFF.getD 8 []).any (fun l => l == "let x4_pow_1 := mulmod(x4_pow_0, x4, r)")
    && bFT.length == 11 && bTT.length == 11 && bFF.length == 10 && bTF.length == 10
    && (bFT.getD 7 []).headD "" == "// materialize per-set q_com inputs for trace logging"
    && (bFT.getD 0 []).any (fun l => l.startsWith "// trace serialized PCS point set 0 ")
    && ! (bFF.getD 0 []).any (fun l => l.contains "trace serialized PCS point set")
    && bTT.length == bFT.length


/-! ## The gate list -/

#eval btreeMapEntryOrInsert_ok -- expect true
#eval intMaxOr_minMaxOr_ok -- expect true
#eval query_new_argumentOrder_ok -- expect true
#eval queryFromPlan_allArms_ok -- expect true
#eval queryFromPlan_panics_ok -- expect true
#eval queries_identityPin_ok -- expect true
#eval assertPermutationOrder_bothArms_ok -- expect true
#eval duplicateQuery_bothArms_ok -- expect true
#eval ecPointEquality_isPointerEquality_ok -- expect true
#eval hazard1_insertionOrderOk_ok -- expect true
#eval anchorIntermediateSetsShape_ok -- expect true
#eval constructIntermediateSets_partitions_ok -- expect true
#eval evalAlignment_sortedPosition_ok -- expect true
#eval constructIntermediateSets_dedups_ok -- expect true
#eval sortSets_tiebreak_ok -- expect true
#eval sortSets_remapTotality_ok -- expect true
#eval intermediateSets_featureBranch_ok -- expect true
#eval computeDummyQueries_fourRustTests_ok -- expect true
#eval augmentQueries_collapseToSingleSet_ok -- expect true
#eval proofAbsorbedG1s_fixture_ok -- expect true
#eval precompileValidated_identitySkip_ok -- expect true
#eval validateG1Coverage_accepts_ok -- expect true
#eval validateG1Coverage_rejects_ok -- expect true
#eval absorbedCoverage_countMismatch_ok -- expect true
#eval validateAbsorbedCoverage_fixture_ok -- expect true
#eval qComTermsForSet_threeArms_ok -- expect true
#eval qEvalStrategy_matchesRustTest_ok -- expect true
#eval memoryRequirements_empty_ok -- expect true
#eval memoryRequirements_rolledTable_ok -- expect true
#eval memoryRequirements_signedRotations_ok -- expect true
#eval staticWorkingMemorySize_matchesDoc_ok -- expect true
#eval computations_blockOrder_ok -- expect true
#eval computations_hexFormatter_ok -- expect true
#eval computations_traceAndTruncationBranches_ok -- expect true

end Midfall.Generator.KzgKats
