-- |
-- Midfall.Generator.Protocol
--
-- The typed verifier protocol plan: a port of
-- proofs/solidity-verifier/src/lowering/protocol/mod.rs (1252 lines), every
-- top-level item, in source order (rule R1).
--
-- CITATION NOTATION. Two prefixes, each named with its file and line count
-- because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites that
-- silently pointed at the wrong file or at a declaration that does not exist:
--
-- * PM:  proofs/solidity-verifier/src/lowering/protocol/mod.rs (1252 lines) -
--   the file this module ports.
-- * LM:  proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines) - used
--   only for the trace block at LM:774-786, whose six constants are ported into
--   Midfall/Generator/Layout.lean (the Layout row) and re-exported here at
--   PM:177-180.
--
-- Rust paths under proofs/src/ (the verifier crate) are cited in full, never by
-- prefix: this file reaches them only through the already-ported accessors in
-- Midfall/Halo2/Exec/Circuit.lean, and those carry their own cites.
--
-- WHAT THIS FILE DOES NOT PORT, AND WHY.
--
-- * PM:942-1252, the #[cfg(test)] mod tests. Rule R8's convention in this repo
--   (see the Layout.lean header) is that test items are ported where a ported
--   test needs them. What is worth keeping from that module is its ASSERTIONS, so
--   each of its nine #[test] fns and its one proptest is mapped to a gate here:
--     expression_visitor_collects_queries (PM:969)      -> usedQuery_matchesRustTest_ok
--     plan_preserves_eval_and_pcs_order (PM:991)       -> fromConstraintSystem_streamOrder_ok
--                                                        and fromConstraintSystem_fixture_ok
--     plan_skips_non_committed_instance (PM:1035)      -> fromConstraintSystem_skipsNonCommitted_ok
--     plan_tracks_permutation_chunking (PM:1050)       -> fromConstraintSystem_fixture_ok, which
--                                                        has two permutation sets and pins the same
--                                                        3n-1 eval count exactly rather than as an
--                                                        inequality
--     lookup_identity_source_variable_chunks (PM:1082)  -> lookupIdentitySource_matchesRustTest_ok
--     plan_allows_challenge_phase_beyond_advice (PM:1104) - NOT reproduced: it needs
--        cs.challenge_usable_after(SecondPhase) and a second-phase advice column, and
--        the phase remapping it exercises is pinned instead by the fixture's
--        numUserAdvices / numUserChallenges / adviceIndices conjuncts
--     quotient_commitment_count_matches_feature (PM:1128) -> fromConstraintSystem_fixture_ok's
--        numQuotients == 4 conjunct, which is cs_degree - 1 under the recorded feature set
--     validation_rejects_simple_selector_eval (PM:1154) -> validate_rejectsSimpleSelectorEval_matchesRust_ok
--        plus validate_rejectsSimpleSelectorEval_readCheck_ok (see the finding recorded there:
--        the Rust assertion does not reach the check its name claims)
--     validation_rejects_absorbed_unopened_advice (PM:1163) -> validate_rejectsUnopenedAdvice_ok
--     proptest protocol_plan_invariants (PM:1180)       - NOT reproduced as a generator: it is
--        a random search over shapes this file cannot enumerate. Its five prop_asserts are the
--        validate invariants plus the pcs/evals off-by-one, all ported at their sites and
--        asserted concretely on the fixture.
-- * PM:11-19, the use statements. itertools::Itertools::collect_vec is the
--   identity here (Vec -> List). midnight_curves::Fq does not appear: nothing in
--   the ported scope inspects a field element, so fromConstraintSystem and
--   usedQuery are generic over the field type instead of specialised at Fq. That
--   is a widening, not a narrowing - every Rust call site is an instance of the
--   Lean one - and it is listed as a judgement call in the package report.
--
-- DECISIONS RECORDED RATHER THAN TAKEN SILENTLY (rules R5, R6, R8).
--
-- * usize is Nat, i32 is Int, u64 is Nat. The u64 of quotient_trace_ids and
--   pcs_query_trace_ids (PM:307, PM:309) is a trace topic number built as
--   base + index with base at most 41000, so the two readings cannot differ;
--   said again at the site.
-- * Vec is List, following Layout.lean and Models.lean. Every Vec operation used
--   here - iter, extend, push, map, filter, filter_map, enumerate, any, all,
--   sum, last, is_empty, contains, div_ceil - is order-preserving or
--   order-independent, so the two readings agree on everything observable.
-- * BTreeSet is a List kept ascending and duplicate-free by the comparator the
--   Rust Ord gives (btreeSetInsert / btreeSetFromList below), with the derived
--   field order ported exactly: QueryKey by (column, rotation) with rotation
--   SIGNED, CommonPoly by DECLARATION order. BTreeSet::contains is
--   order-independent, so it is ported as membership on the list and not as a
--   binary search; nothing observable depends on the difference. No HashMap
--   appears in this file at all, so R6's iteration-order argument is not needed.
-- * PM:348 reads crate::OUTER_SINGLE_H_COMMITMENT_ENABLED, a
--   cfg!(feature = "outer-single-h-commitment") const at lib.rs:76. Rule R8 says
--   a feature becomes an explicit branch, so fromConstraintSystem takes a
--   Features argument and both branches are written out rather than resolved at
--   compile time; Features.solidity (BASELINE.md) is the profile the call sites
--   and every gate pass, and under it the flag is false.
-- * Lean is order-sensitive and PM:642 calls the validate defined at PM:714, so
--   the seven members of the impl block sit in one mutual block. That keeps Rust
--   source order rather than moving validate earlier, which is what R1 asks for.
--   ProtocolPlan.remapping is the one item that moves: it is a let-bound closure
--   at PM:377-398 inside from_constraint_system, and Lean cannot forward- or
--   back-reference a let across a def, so it is hoisted above its caller.

import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Features
import Midfall.Generator.Layout

namespace Midfall.Generator
open Midfall Midfall.Halo2

/-! ## Port scaffolding for rules R5 and R6

Nothing here is a Rust item. These are the pieces the ported code needs in order
to honour R6 ("BTreeSet becomes a sorted list using the *same* Ord") without
inventing a set type, plus the two integer comparators every Ord below is stated
in terms of. -/

/-- Rust's derived Ord on usize. -/
def natCmp (a b : Nat) : Ordering :=
  if a < b then .lt else if a == b then .eq else .gt

/-- Rust's Ord on i32 - SIGNED, which is the entire reason this is separate from
    natCmp: QueryKey's derived Ord (PM:21-27) compares a field that is an i32,
    and under a Nat reading -1 would sort above every non-negative rotation
    instead of below it. queryKey_order_ok is what keeps that from being tidied. -/
def intCmp (a b : Int) : Ordering :=
  if a < b then .lt else if a == b then .eq else .gt

/-- Insert x into a list that is already ascending and duplicate-free under cmp,
    keeping it so. This is BTreeSet::insert: an existing key is left in place and
    nothing is appended (the Rust returns false there; the boolean is read
    nowhere in the ported scope), and a new key goes before the first larger
    one. btreeSetInsert_ok pins all three cases. -/
def btreeSetInsert {alpha : Type} (cmp : alpha → alpha → Ordering) (x : alpha)
    (xs : List alpha) : List alpha :=
  match xs with
  | [] => [x]
  | y :: ys => match cmp x y with
    | .lt => x :: y :: ys
    | .eq => y :: ys
    | .gt => y :: btreeSetInsert cmp x ys

/-- Iterator::collect::<BTreeSet<_>>(). A BTreeSet is a set, so the insertion
    order does not change the result and a plain left fold is the same function. -/
def btreeSetFromList {alpha : Type} (cmp : alpha → alpha → Ordering)
    (xs : List alpha) : List alpha :=
  xs.foldl (fun acc x => btreeSetInsert cmp x acc) []

/-- v[i] += 1 on a Vec<usize>, as PM:382 and PM:393 write it. Out of range is a
    Rust index panic, so it is a Fault.panic here (rule R4) and not a silent
    default; remapping states why neither site can reach it. -/
def bumpAt (xs : List Nat) (i : Nat) (site : String) : Except Fault (List Nat) :=
  if i < xs.length then
    Except.ok (xs.take i ++ (xs.getD i 0 + 1) :: xs.drop (i + 1))
  else
    Except.error (Fault.panic site)

/-- state[i] as a read, with the same panic discipline as bumpAt (PM:392). -/
def getAt (xs : List Nat) (i : Nat) (site : String) : Except Fault Nat :=
  if i < xs.length then Except.ok (xs.getD i 0) else Except.error (Fault.panic site)

/-! ## QueryKey (rust: PM:21-40) -/

/-- rust: PM:21-27 (struct QueryKey { column: usize, rotation: i32 })
    @formal-baseline. Field order is the Rust's, because #[derive(Ord)] compares
    in declaration order and that ordering is what BTreeSet<QueryKey> in
    UsedQueries (PM:186-190) inherits. -/
structure QueryKey where
  /-- rust: PM:24 (column: usize) - column index within its column kind. -/
  column : Nat
  /-- rust: PM:26 (rotation: i32) - Halo2 rotation relative to the current row. -/
  rotation : Int
  deriving BEq

/-- rust: PM:21 (#[derive(..., PartialOrd, Ord, ...)] on QueryKey), i.e. column
    first and rotation second, with rotation compared as a SIGNED i32. -/
def QueryKey.cmp (a b : QueryKey) : Ordering :=
  match natCmp a.column b.column with
  | .eq => intCmp a.rotation b.rotation
  | o => o

/-- rust: PM:31-33 (QueryKey::new). -/
def QueryKey.new (column : Nat) (rotation : Int) : QueryKey :=
  { column := column, rotation := rotation }

/-- rust: PM:37-39 (QueryKey::tuple), the historical ConstraintSystemMeta shape. -/
def QueryKey.tuple (self : QueryKey) : Nat × Int := (self.column, self.rotation)

/-! ## CommitmentRead (rust: PM:42-61) -/

/-- rust: PM:43-54 (enum CommitmentRead) @formal-baseline. Variant order is the
    declaration order. The Rust comment at PM:45-46 - "The commitment stream only
    needs kinds for sizing and transcript order. Column/query identity lives in
    the eval and PCS plans below." - is why no variant carries a payload. -/
inductive CommitmentRead
  | advice
  | lookupMultiplicity
  | permutationProduct
  | lookupHelper
  | lookupAccumulator
  | trash
  | quotient
  deriving BEq

/-- rust: PM:58-60 (CommitmentRead::is_quotient), the matches!(self,
    Self::Quotient) of PM:59. -/
def CommitmentRead.isQuotient (self : CommitmentRead) : Bool :=
  self == CommitmentRead.quotient

/-! ## PermutationZEval and EvalRead (rust: PM:63-95) -/

/-- rust: PM:64-72 (enum PermutationZEval) @formal-baseline. -/
inductive PermutationZEval
  /-- rust: PM:67 (Cur) - evaluation at x. -/
  | cur
  /-- rust: PM:69 (Next) - evaluation at omega * x. -/
  | next
  /-- rust: PM:71 (Last) - evaluation at the last usable rotation. -/
  | last
  deriving BEq

/-- rust: PM:74-95 (enum EvalRead) @formal-baseline. Variant and field order
    preserved. Column<Any> is the port's Column, whose columnType field already
    carries the Any (Exec/Circuit.lean's structural choice 2). -/
inductive EvalRead
  /-- rust: PM:78 - PCS-opened committed instance column. -/
  | committedInstance (q : QueryKey)
  /-- rust: PM:80 -/
  | advice (q : QueryKey)
  /-- rust: PM:82 - non-simple fixed polynomial query. -/
  | fixed (q : QueryKey)
  /-- rust: PM:84 - common permutation sigma polynomial query. -/
  | permutationCommon (column : Column)
  /-- rust: PM:86 -/
  | permutationZ (set : Nat) (kind : PermutationZEval)
  /-- rust: PM:88 -/
  | lookupMultiplicity (lookup : Nat)
  /-- rust: PM:90 -/
  | lookupHelper (lookup : Nat) (chunk : Nat)
  /-- rust: PM:92 -/
  | lookupAccumulator (lookup : Nat) (rotation : Int)
  /-- rust: PM:94 - trashcan accumulator query. -/
  | trash (index : Nat)
  deriving BEq

/-! ## PcsQuerySource (rust: PM:97-133) -/

/-- rust: PM:98-110 (enum PcsQuerySource) @formal-baseline. The variant order
    differs from EvalRead: CommittedInstance is second here and first there, and
    Linearization exists only here. That is not an accident to smooth over -
    from_constraint_system emits the two streams in their own orders (PM:436-521
    versus PM:528-580), and fromConstraintSystem_streamOrder_ok pins both. -/
inductive PcsQuerySource
  | advice (q : QueryKey)
  | committedInstance (q : QueryKey)
  | permutationZ (set : Nat) (kind : PermutationZEval)
  | lookupMultiplicity (lookup : Nat)
  | lookupHelper (lookup : Nat) (chunk : Nat)
  | lookupAccumulator (lookup : Nat) (rotation : Int)
  | trash (index : Nat)
  | fixed (q : QueryKey)
  | permutationCommon (column : Column)
  | linearization
  deriving BEq

/-- rust: PM:117-132 (PcsQuerySource::rotation). The Last arm returns the
    caller's rotation_last rather than a constant, which is why the signature
    takes it at all (PM:115-116: "circuit-dependent and is needed only for the
    permutation product's last-row opening"). Every other arm is a literal, and
    LookupAccumulator is the only variant that carries its own rotation. -/
def PcsQuerySource.rotation (self : PcsQuerySource) (rotationLast : Int) : Int :=
  match self with
  | .advice q => q.rotation
  | .committedInstance q => q.rotation
  | .fixed q => q.rotation
  | .permutationZ _ kind =>
      match kind with
      | .cur => 0
      | .next => 1
      | .last => rotationLast
  | .lookupMultiplicity _ => 0
  | .lookupHelper _ _ => 0
  | .trash _ => 0
  | .permutationCommon _ => 0
  | .linearization => 0
  | .lookupAccumulator _ rotation => rotation

/-! ## CommonPoly (rust: PM:135-146) -/

/-- rust: PM:136-146 (enum CommonPoly with #[derive(PartialOrd, Ord)])
    @formal-baseline. A derived Ord on a Rust enum is DECLARATION order, so
    Rotation _ < L0 < LLast < LBlind whatever the payload, and inside Rotation
    the i32 payload is compared signed. Note that this is the opposite of the
    order used_lagrange inserts them in, which is the trap. -/
inductive CommonPoly
  /-- rust: PM:139 (Rotation(i32)) - rotation point omega^rotation * x. -/
  | rotation (v : Int)
  /-- rust: PM:141 (L0) - first-row Lagrange basis evaluation. -/
  | l0
  /-- rust: PM:143 (LLast) - last-row Lagrange basis evaluation. -/
  | lLast
  /-- rust: PM:145 (LBlind) - blinding-row Lagrange basis evaluation. -/
  | lBlind
  deriving BEq

/-- rust: PM:136 (#[derive(..., PartialOrd, Ord)]) on CommonPoly, ported arm by
    arm rather than derived, so that the declaration-order claim is reviewable
    line by line. The arm ORDER inside this match is itself load-bearing and was
    got wrong on the first draft: a catch-all | .lLast, _ => .lt also matches
    (lLast, l0) and silently makes LLast sort below L0, which no amount of
    checking the Rotation arms would catch. commonPoly_order_ok is what pins it,
    and it is the reason the last three arms are split rather than collapsed. -/
def CommonPoly.cmp : CommonPoly → CommonPoly → Ordering
  | .rotation a, .rotation b => intCmp a b
  | .rotation _, _ => .lt
  | _, .rotation _ => .gt
  | .l0, .l0 => .eq
  | .l0, _ => .lt
  | .lLast, .lLast => .eq
  | .lLast, .lBlind => .lt
  | .lLast, _ => .gt
  | .lBlind, .lBlind => .eq
  | .lBlind, _ => .gt

/-! ## ProofReadPlan and QuotientIdentityPlan (rust: PM:148-175) -/

/-- rust: PM:149-155 (struct ProofReadPlan) @formal-baseline. -/
structure ProofReadPlan where
  /-- rust: PM:152 (commitments: Vec<CommitmentRead>) - G1 commitment reads in
      transcript order. -/
  commitments : List CommitmentRead
  /-- rust: PM:154 (evals: Vec<EvalRead>) - scalar evaluation reads in proof
      order. -/
  evals : List EvalRead
  deriving BEq

/-- The #[derive(Default)] of PM:149: two empty vectors. -/
def proofReadPlanDefault : ProofReadPlan := { commitments := [], evals := [] }

/-- rust: PM:158-168 (struct QuotientIdentityPlan) @formal-baseline. Field order
    preserved. -/
structure QuotientIdentityPlan where
  /-- rust: PM:161 (gates: usize) - gate polynomial identities. -/
  gates : Nat
  /-- rust: PM:163 (permutation: usize) -/
  permutation : Nat
  /-- rust: PM:165 (lookup: usize) -/
  lookup : Nat
  /-- rust: PM:167 (trash: usize) -/
  trash : Nat
  deriving BEq

/-- The #[derive(Default)] of PM:158: four zeros. -/
def quotientIdentityPlanDefault : QuotientIdentityPlan :=
  { gates := 0, permutation := 0, lookup := 0, trash := 0 }

/-- rust: PM:172-174 (QuotientIdentityPlan::total). Four usize additions. The
    reference profile is release (docs/REVIEW.md R-6; BASELINE.md "reference
    profile for the port: release"), where + wraps rather than panicking, so a
    wrapped sum and a Nat sum could in principle differ - and cannot here: each
    term is a count of constraints, permutation sets, lookup chunks or trashcans
    in a circuit that has to fit a transcript. Unreachability stated at the site
    per rule R5, not proved. -/
def QuotientIdentityPlan.total (self : QuotientIdentityPlan) : Nat :=
  self.gates + self.permutation + self.lookup + self.trash

/-- rust: PM:177-178 (pub(crate) const TRACE_QUOTIENT_IDENTITY_BASE: u64 =
    trace::QUOTIENT_IDENTITY_BASE) @formal-baseline. The value itself is ported
    in Layout.lean as Midfall.Generator.Trace.quotientIdentityBase (LM:784),
    because LM:774-786 is the Layout row of the module map; this is the re-export
    the protocol module uses at PM:610. -/
def traceQuotientIdentityBase : Nat := Midfall.Generator.Trace.quotientIdentityBase

/-- rust: PM:179-180 (pub(crate) const TRACE_PCS_QUERY_BASE: u64 =
    trace::PCS_QUERY_BASE) @formal-baseline; same note, LM:781, used at PM:613. -/
def tracePcsQueryBase : Nat := Midfall.Generator.Trace.pcsQueryBase

/-! ## UsedQueries and used_query (rust: PM:182-242)

Both are #[cfg(test)] in the reference. They are ported because
expression_visitor_collects_queries (PM:969-989) is one of the test assertions
this file reproduces as a gate, and that gate cannot be stated without them.
Marked TEST-ONLY at each site, which is the convention Layout.lean sets for the
six #[cfg(test)] items it ports. -/

/-- rust: PM:183-193 (struct UsedQueries), #[cfg(test)] so TEST-ONLY. Four
    BTreeSets, so four ascending duplicate-free lists: the first three under
    QueryKey.cmp (SIGNED rotation) and the last under natCmp.

    FORCED R2 DEVIATION, recorded: the Rust field is instance, which is a
    reserved word in Lean and cannot be a structure field name, so it is
    instance_ here. Nothing else in the record is renamed. -/
structure UsedQueries where
  /-- rust: PM:186 (fixed: BTreeSet<QueryKey>) -/
  fixed : List QueryKey
  /-- rust: PM:188 (advice: BTreeSet<QueryKey>) -/
  advice : List QueryKey
  /-- rust: PM:190 (instance: BTreeSet<QueryKey>) -/
  instance_ : List QueryKey
  /-- rust: PM:192 (challenges: BTreeSet<usize>) -/
  challenges : List Nat
  deriving BEq

/-- The #[derive(Default)] of PM:183: four empty sets. -/
def usedQueriesDefault : UsedQueries :=
  { fixed := [], advice := [], instance_ := [], challenges := [] }

/-- rust: PM:198-204 (UsedQueries::merge), a private fn in the #[cfg(test)]
    impl, so TEST-ONLY. BTreeSet::extend is a union, which for two ascending
    nub lists is btreeSetFromList over the concatenation. -/
def UsedQueries.merge (self other : UsedQueries) : UsedQueries :=
  { fixed := btreeSetFromList QueryKey.cmp (self.fixed ++ other.fixed)
    advice := btreeSetFromList QueryKey.cmp (self.advice ++ other.advice)
    instance_ := btreeSetFromList QueryKey.cmp (self.instance_ ++ other.instance_)
    challenges := btreeSetFromList natCmp (self.challenges ++ other.challenges) }

/-- rust: PM:213-242 (used_query), #[cfg(test)] so TEST-ONLY. The ten closures
    are handed to Expression.evaluate as the Callbacks record Exec/Circuit.lean
    builds for proofs/src/plonk/circuit.rs:907-918, in that parameter order, so
    the closure list can be checked against PM:214-241 line by line.

    The Rust takes &Expression<Fq>; the port is generic over the field type
    because nothing here inspects a field element and this tree has no concrete
    Fq (Midfall/Common/Curve.lean's header; docs/ecosystem.md). Every Rust call
    site is an instance of the generic one. -/
def usedQuery {F : Type} (expression : Expression F) : UsedQueries :=
  Expression.evaluate
    { constant := fun _ => usedQueriesDefault
      selectorColumn := fun _ => usedQueriesDefault
      fixedColumn := fun q =>
        { usedQueriesDefault with
          fixed := btreeSetInsert QueryKey.cmp
            (QueryKey.new q.columnIndex q.rotation.int) [] }
      adviceColumn := fun q =>
        { usedQueriesDefault with
          advice := btreeSetInsert QueryKey.cmp
            (QueryKey.new q.columnIndex q.rotation.int) [] }
      instanceColumn := fun q =>
        { usedQueriesDefault with
          instance_ := btreeSetInsert QueryKey.cmp
            (QueryKey.new q.columnIndex q.rotation.int) [] }
      challenge := fun ch =>
        { usedQueriesDefault with
          challenges := btreeSetInsert natCmp ch.index [] }
      negated := fun inner => inner
      sum := fun lhs rhs => lhs.merge rhs
      product := fun lhs rhs => lhs.merge rhs
      scaled := fun inner _ => inner }
    expression

/-! ## used_lagrange (rust: PM:244-260) -/

/-- rust: PM:245-260 (used_lagrange) @formal-baseline. Returns a
    BTreeSet<CommonPoly>, i.e. ascending under CommonPoly.cmp: with all three
    flags set that is [Rotation 0, L0, LLast, LBlind] - the rotation FIRST,
    because Rotation is the first declared variant, which is the opposite of the
    order the inserts happen in. usedLagrange_ok pins all eight combinations. -/
def usedLagrange (usesPermutation usesLookup usesTrash : Bool) : List CommonPoly :=
  let out0 : List CommonPoly := []
  let out1 :=
    if usesPermutation || usesLookup then
      btreeSetInsert CommonPoly.cmp CommonPoly.lBlind
        (btreeSetInsert CommonPoly.cmp CommonPoly.lLast
          (btreeSetInsert CommonPoly.cmp CommonPoly.l0 out0))
    else out0
  if usesTrash then btreeSetInsert CommonPoly.cmp (CommonPoly.rotation 0) out1 else out1

/-! ## ProtocolPlan (rust: PM:262-314) -/

/-- rust: PM:264-314 (struct ProtocolPlan) @formal-baseline. All twenty-four
    fields in source order (rule R1). The two BTreeSet fields are the sorted nub
    lists btreeSetInsert maintains; every Vec is a List. -/
structure ProtocolPlan where
  /-- rust: PM:267 (num_fixeds: usize) -/
  numFixeds : Nat
  /-- rust: PM:269 (permutation_columns: Vec<Column<Any>>) -/
  permutationColumns : List Column
  /-- rust: PM:271 (permutation_chunk_len: usize) -/
  permutationChunkLen : Nat
  /-- rust: PM:273 (lookup_chunks: Vec<usize>), one entry per lookup argument -/
  lookupChunks : List Nat
  /-- rust: PM:275 (num_lookups: usize) -/
  numLookups : Nat
  /-- rust: PM:277 (num_trashcans: usize) -/
  numTrashcans : Nat
  /-- rust: PM:279 (num_permutation_zs: usize) -/
  numPermutationZs : Nat
  /-- rust: PM:281 (num_quotients: usize) -/
  numQuotients : Nat
  /-- rust: PM:283 (advice_queries: Vec<QueryKey>) - upstream verifier order. -/
  adviceQueries : List QueryKey
  /-- rust: PM:285 (instance_queries: Vec<QueryKey>) -/
  instanceQueries : List QueryKey
  /-- rust: PM:287 (num_simple_selectors: usize) -/
  numSimpleSelectors : Nat
  /-- rust: PM:289 (simple_selector_cols: BTreeSet<usize>) -/
  simpleSelectorCols : List Nat
  /-- rust: PM:291 (num_committed_instances: usize) -/
  numCommittedInstances : Nat
  /-- rust: PM:293 (num_user_advices: Vec<usize>), per phase -/
  numUserAdvices : List Nat
  /-- rust: PM:295 (num_user_challenges: Vec<usize>), per phase -/
  numUserChallenges : List Nat
  /-- rust: PM:297 (advice_indices: Vec<usize>), CS order -> phase order. -/
  adviceIndices : List Nat
  /-- rust: PM:299 (challenge_indices: Vec<usize>) -/
  challengeIndices : List Nat
  /-- rust: PM:301 (rotation_last: i32) -/
  rotationLast : Int
  /-- rust: PM:303 (proof: ProofReadPlan) -/
  proof : ProofReadPlan
  /-- rust: PM:305 (pcs_queries: Vec<PcsQuerySource>) -/
  pcsQueries : List PcsQuerySource
  /-- rust: PM:307 (quotient_trace_ids: Vec<u64>) -/
  quotientTraceIds : List Nat
  /-- rust: PM:309 (pcs_query_trace_ids: Vec<u64>) -/
  pcsQueryTraceIds : List Nat
  /-- rust: PM:311 (common_polys: BTreeSet<CommonPoly>) -/
  commonPolys : List CommonPoly
  /-- rust: PM:313 (quotient: QuotientIdentityPlan) -/
  quotient : QuotientIdentityPlan
  deriving BEq

/-- The #[derive(Default)] of PM:264: every usize and i32 zero, every Vec and
    BTreeSet empty. The default is load-bearing, not decoration:
    lookup_identity_source_handles_variable_chunk_counts (PM:1086-1093) builds a
    plan with ..ProtocolPlan::default(). -/
def protocolPlanDefault : ProtocolPlan :=
  { numFixeds := 0
    permutationColumns := []
    permutationChunkLen := 0
    lookupChunks := []
    numLookups := 0
    numTrashcans := 0
    numPermutationZs := 0
    numQuotients := 0
    adviceQueries := []
    instanceQueries := []
    numSimpleSelectors := 0
    simpleSelectorCols := []
    numCommittedInstances := 0
    numUserAdvices := []
    numUserChallenges := []
    adviceIndices := []
    challengeIndices := []
    rotationLast := 0
    proof := proofReadPlanDefault
    pcsQueries := []
    quotientTraceIds := []
    pcsQueryTraceIds := []
    commonPolys := []
    quotient := quotientIdentityPlanDefault }

/-! ## impl ProtocolPlan (rust: PM:316-940)

Lean is order-sensitive and PM:642 calls the validate declared at PM:714, so the
seven members of the impl block are wrapped in one mutual block instead of
reordering them. ProtocolPlan.remapping is the one item that moves relative to
Rust source order: it is a let-bound closure at PM:377-398 inside
from_constraint_system, and Lean has no way to spell a closure that a later def
in the same file can reach, so it becomes a def above its caller. -/

/-- rust: PM:377-398, the remapping closure inside from_constraint_system. It
    captures num_phase, which becomes an explicit first argument.

    Three Rust sites that would abort, all unreachable, all stated rather than
    assumed away (rule R4):

    * nums[*p as usize] += 1 (PM:382) and state[*p as usize] read and written at
      PM:392-393 index a vector of length num_phase, and num_phase is
      max(advice phases, challenge phases) + 1 (PM:374-376), so every p drawn
      from either input is in range. bumpAt / getAt still carry the site, so a
      malformed phase vector faults rather than defaulting.
    * offsets.last().unwrap() (PM:386): offsets starts as vec![0] and is only
      ever pushed to, so it is never empty.

    nums.iter().take(num_phase - 1) (PM:385) is a usize subtraction that cannot
    underflow for the same reason num_phase >= 1. -/
def ProtocolPlan.remapping (numPhase : Nat) (phase : List Nat) :
    Except Fault (List Nat × List Nat) := do
  -- PM:381-383: fold(vec![0usize; num_phase], |mut nums, p| { nums[p] += 1; nums })
  let nums ← phase.foldlM
    (fun ns p => bumpAt ns p
      "proofs/solidity-verifier/src/lowering/protocol/mod.rs:382")
    (List.replicate numPhase 0)
  -- PM:385-388: running prefix sums of all but the last per-phase count, from 0
  let offsets ← (nums.take (numPhase - 1)).foldlM
    (fun offs n => do
      let last ← match offs.getLast? with
        | some l => Except.ok l
        | none => Except.error (Fault.panic
            "proofs/solidity-verifier/src/lowering/protocol/mod.rs:386")
      Except.ok (offs ++ [last + n]))
    [0]
  -- PM:389-396: scan over the phase vector with offsets as the mutable state,
  -- emitting each column's slot inside its phase and then consuming it
  let res ← phase.foldlM
    (fun st p => do
      let (acc, state) := st
      let i ← getAt state p
        "proofs/solidity-verifier/src/lowering/protocol/mod.rs:392"
      let state ← bumpAt state p
        "proofs/solidity-verifier/src/lowering/protocol/mod.rs:393"
      Except.ok (acc ++ [i], state))
    ([], offsets)
  Except.ok (nums, res.1)

mutual

/-- rust: PM:327-644 (ProtocolPlan::from_constraint_system) @formal-baseline.
    The bulk of the file: 318 Rust lines, and the reason this module exists.

    Five Rust sites need a word before they are read as code.

    * cs_degree - 2 (PM:334) and cs_degree.saturating_sub(1) (PM:351).
      ConstraintSystem::degree is at least 3 for every constraint system in
      existence, because permutation::Argument::required_degree is the constant 3
      (Exec/Circuit.lean's note on PermutationArgument.requiredDegree), so
      neither can underflow and Nat's saturating subtraction is exact. The
      div_ceil at PM:338 therefore also divides by at least 1, which is what makes
      divCeil's div-by-zero reading (Exec/Arith.lean:51-53) unreachable here.
    * num_fixeds - simple_selector_cols.len() (PM:463) cannot underflow either:
      simple_selector_cols is collected from 0..num_fixeds (PM:371-372), so its
      length is at most num_fixeds.
    * -(cs.blinding_factors() as i32 + 1) (PM:402) is exact because
      blinding_factors panics above i32::MAX at
      proofs/src/plonk/circuit.rs:2510 before the cast could truncate; the port
      threads that Except through.
    * assert_eq! at PM:461-475 is a real assert_eq!, not a debug_assert!, so it
      is a panic in the reference profile and becomes a Fault.panic at that site.
      Its message is the I-6 audit note about the native verifier sizing the
      fixed eval section COLUMN-based while this generator sizes it QUERY-based;
      the check is the point of the site and must not be relaxed.
    * PM:642 aborts through unwrap_or_else(|err| panic!("invalid protocol plan:
      {err}")), which is a Fault.panic at that site. The Rust panic payload
      carries the validate error string; Fault.panic carries only a site, so the
      message is dropped. Nothing in the ported scope reads a panic payload, and
      fromConstraintSystem_fixedEvalMismatch_panics_ok pins the site that is
      observable. -/
def ProtocolPlan.fromConstraintSystem {F : Type} (feat : Features)
    (cs : ConstraintSystem F) (nbCommittedInstances : Nat) :
    Except Fault ProtocolPlan := do
  -- PM:331-333
  let csDegree ← cs.degree
  let numFixeds := cs.numFixedColumns
  let permutationColumns := cs.permutation.getColumns.toList
  -- PM:334-339
  let permutationChunkLen := csDegree - 2
  let numPermutationZs :=
    if permutationColumns.isEmpty then 0
    else divCeil permutationColumns.length permutationChunkLen
  -- PM:341-346: chunk_by_degree(cs_degree).num_chunks() per lookup
  let lookupChunks ← mapExceptArray
    (fun l => do
      let chunked ← l.chunkByDegree csDegree
      Except.ok (LogupChunkedArgument.numChunks chunked))
    cs.lookups
  let lookupChunks := lookupChunks.toList
  let numLookups := lookupChunks.length
  -- PM:347-352
  let numTrashcans := cs.trashcans.size
  let numQuotients := if feat.outerSingleHCommitment then 1 else csDegree - 1
  -- PM:354-368: the three query vectors, (Column, Rotation) -> QueryKey
  let adviceQueries :=
    cs.adviceQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  let fixedQueries :=
    cs.fixedQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  let instanceQueries :=
    cs.instanceQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  -- PM:370-372: a range-filter, so already ascending and duplicate-free
  let numSimpleSelectors := cs.numSimpleSelectors
  let simpleSelectorCols :=
    (List.range numFixeds).filter (fun idx => cs.hasSimpleSelectorCol idx)
  -- PM:374-376: iter().max().unwrap_or(0), so an empty vector gives 0
  let maxAdvicePhase := cs.adviceColumnPhaseNats.toList.foldl (fun acc p => max acc p) 0
  let maxChallengePhase := cs.challengePhaseNats.toList.foldl (fun acc p => max acc p) 0
  let numPhase := max maxAdvicePhase maxChallengePhase + 1
  -- PM:399-400
  let (numUserAdvices, adviceIndices) ←
    ProtocolPlan.remapping numPhase cs.adviceColumnPhaseNats.toList
  let (numUserChallenges, challengeIndices) ←
    ProtocolPlan.remapping numPhase cs.challengePhaseNats.toList
  -- PM:402
  let blindingFactors ← cs.blindingFactors
  let rotationLast : Int := -((blindingFactors : Int) + 1)
  -- PM:403: ProofReadPlan::default(), filled by the extends below. The Rust
  -- mutates one binding; the port names each stage, in the same order.
  -- PM:408-431: the commitment stream, in transcript order
  let commitments :=
    List.replicate adviceIndices.length CommitmentRead.advice
      ++ List.replicate numLookups CommitmentRead.lookupMultiplicity
      ++ List.replicate numPermutationZs CommitmentRead.permutationProduct
      ++ (lookupChunks.map fun chunks =>
            List.replicate chunks CommitmentRead.lookupHelper
              ++ [CommitmentRead.lookupAccumulator]).flatten
      ++ List.replicate numTrashcans CommitmentRead.trash
      ++ List.replicate numQuotients CommitmentRead.quotient
  -- PM:436-442: only the COMMITTED instance columns are read from the proof
  let committedInstanceQueries :=
    instanceQueries.filter fun q => q.column < nbCommittedInstances
  let evalCommittedInstances := committedInstanceQueries.map EvalRead.committedInstance
  -- PM:443
  let evalAdvice := adviceQueries.map EvalRead.advice
  -- PM:444-475: the I-6 column-versus-query consistency assert. The Rust writes
  -- the same filter three times - once for the count at PM:457-460, once for the
  -- eval reads at PM:476-482 and once for the PCS queries at PM:567-573 - and the
  -- port computes it once into nonSimpleFixedQueryList and takes its length for
  -- the count. A filter is pure, so the sharing is unobservable.
  let nonSimpleFixedQueryList :=
    fixedQueries.filter fun q => !(q.column ∈ simpleSelectorCols)
  let nonSimpleFixedQueries := nonSimpleFixedQueryList.length
  unless nonSimpleFixedQueries == numFixeds - simpleSelectorCols.length do
    throw (Fault.panic
      "proofs/solidity-verifier/src/lowering/protocol/mod.rs:461")
  -- PM:476-482
  let evalFixed := nonSimpleFixedQueryList.map EvalRead.fixed
  -- PM:483-490
  let evalPermutationCommon := permutationColumns.map EvalRead.permutationCommon
  -- PM:491-506: Cur and Next for every set, Last for every set but the final one
  let evalPermutationZ :=
    (List.range numPermutationZs).map fun set =>
      [EvalRead.permutationZ set PermutationZEval.cur,
        EvalRead.permutationZ set PermutationZEval.next]
        ++ (if set + 1 != numPermutationZs
            then [EvalRead.permutationZ set PermutationZEval.last] else [])
  -- PM:507-520
  let evalLookup :=
    ((List.range numLookups).zip lookupChunks).map fun (lookup, chunks) =>
      [EvalRead.lookupMultiplicity lookup]
        ++ (List.range chunks).map (fun chunk => EvalRead.lookupHelper lookup chunk)
        ++ [EvalRead.lookupAccumulator lookup 0, EvalRead.lookupAccumulator lookup 1]
  -- PM:521
  let evalTrash := (List.range numTrashcans).map EvalRead.trash
  let evals :=
    evalCommittedInstances ++ evalAdvice ++ evalFixed ++ evalPermutationCommon
      ++ evalPermutationZ.flatten ++ evalLookup.flatten ++ evalTrash
  -- PM:527-580: the PCS multi-open schedule. Note the order difference from the
  -- eval stream: advice BEFORE committed instance here, the other way round
  -- above. That is the Rust, not a slip, and fromConstraintSystem_streamOrder_ok
  -- is what keeps it from being tidied away.
  let pcsAdvice := adviceQueries.map PcsQuerySource.advice
  let pcsCommittedInstances := committedInstanceQueries.map PcsQuerySource.committedInstance
  let pcsPermutationZ :=
    (List.range numPermutationZs).map fun set =>
      [PcsQuerySource.permutationZ set PermutationZEval.cur,
        PcsQuerySource.permutationZ set PermutationZEval.next]
        ++ (if set + 1 != numPermutationZs
            then [PcsQuerySource.permutationZ set PermutationZEval.last] else [])
  let pcsLookup :=
    ((List.range numLookups).zip lookupChunks).map fun (lookup, chunks) =>
      [PcsQuerySource.lookupMultiplicity lookup]
        ++ (List.range chunks).map (fun chunk => PcsQuerySource.lookupHelper lookup chunk)
        ++ [PcsQuerySource.lookupAccumulator lookup 0,
            PcsQuerySource.lookupAccumulator lookup 1]
  let pcsTrash := (List.range numTrashcans).map PcsQuerySource.trash
  let pcsFixed := nonSimpleFixedQueryList.map PcsQuerySource.fixed
  let pcsPermutationCommon := permutationColumns.map PcsQuerySource.permutationCommon
  let pcsQueries :=
    pcsAdvice ++ pcsCommittedInstances ++ pcsPermutationZ.flatten ++ pcsLookup.flatten
      ++ pcsTrash ++ pcsFixed ++ pcsPermutationCommon ++ [PcsQuerySource.linearization]
  -- PM:582-595: used_lagrange, then every planned PCS query's rotation point.
  -- BTreeSet::extend is a fold of inserts, and the seed is the Lagrange set.
  let commonPolys := pcsQueries.foldl
    (fun acc q =>
      btreeSetInsert CommonPoly.cmp (CommonPoly.rotation (q.rotation rotationLast)) acc)
    (usedLagrange (numPermutationZs != 0) (numLookups != 0) (numTrashcans != 0))
  -- PM:597-608
  let permutationIdentityCount :=
    if numPermutationZs == 0 then 0 else 2 + (numPermutationZs - 1) + numPermutationZs
  let lookupIdentityCount := (lookupChunks.map fun chunks => chunks + 2).foldl (fun a b => a + b) 0
  let quotient : QuotientIdentityPlan :=
    { gates := (cs.gates.map fun gate => gate.polynomials.size).foldl (fun a b => a + b) 0
      permutation := permutationIdentityCount
      lookup := lookupIdentityCount
      trash := numTrashcans }
  -- PM:609-614. idx as u64 is exact for any count a plan can hold and the bases
  -- are 2000 and 30000, so Nat and u64 cannot differ here (rule R5).
  let quotientTraceIds :=
    (List.range quotient.total).map (fun idx => traceQuotientIdentityBase + idx)
  let pcsQueryTraceIds :=
    (List.range pcsQueries.length).map (fun idx => tracePcsQueryBase + idx)
  -- PM:616-641
  let plan : ProtocolPlan :=
    { numFixeds := numFixeds
      permutationColumns := permutationColumns
      permutationChunkLen := permutationChunkLen
      lookupChunks := lookupChunks
      numLookups := numLookups
      numTrashcans := numTrashcans
      numPermutationZs := numPermutationZs
      numQuotients := numQuotients
      adviceQueries := adviceQueries
      instanceQueries := instanceQueries
      numSimpleSelectors := numSimpleSelectors
      simpleSelectorCols := simpleSelectorCols
      numCommittedInstances := nbCommittedInstances
      numUserAdvices := numUserAdvices
      numUserChallenges := numUserChallenges
      adviceIndices := adviceIndices
      challengeIndices := challengeIndices
      rotationLast := rotationLast
      proof := { commitments := commitments, evals := evals }
      pcsQueries := pcsQueries
      quotientTraceIds := quotientTraceIds
      pcsQueryTraceIds := pcsQueryTraceIds
      commonPolys := commonPolys
      quotient := quotient }
  -- PM:642
  match plan.validate with
  | Except.ok _ => Except.ok plan
  | Except.error _ => Except.error (Fault.panic
      "proofs/solidity-verifier/src/lowering/protocol/mod.rs:642")

/-- rust: PM:647-649 (ProtocolPlan::num_main_evals). -/
def ProtocolPlan.numMainEvals (self : ProtocolPlan) : Nat := self.proof.evals.length

/-- rust: PM:652-654 (ProtocolPlan::num_commitments), quotient limbs included. -/
def ProtocolPlan.numCommitments (self : ProtocolPlan) : Nat := self.proof.commitments.length

/-- rust: PM:657-663 (ProtocolPlan::num_non_quotient_commitments). -/
def ProtocolPlan.numNonQuotientCommitments (self : ProtocolPlan) : Nat :=
  (self.proof.commitments.filter fun commitment => ! commitment.isQuotient).length

/-- rust: PM:667-690 (ProtocolPlan::commitment_read_groups) @formal-baseline.
    The group sizes in the exact proof/transcript order.

    The debug_assert_eq! of PM:684-688 is compiled out in the reference profile
    (docs/REVIEW.md R-6; BASELINE.md "reference profile for the port: release"),
    so it is NOT enforced inside the definition; commitmentReadGroups_debugAssert_ok
    asserts the same equality from outside, which is the pattern Layout.lean sets
    for the seven debug_assert_eq! of MEM:97-103.

    num_user_advices.iter().filter(|&n| n != 0) (PM:669) drops empty phases, but
    the for &chunks in &self.lookup_chunks loop (PM:676-679) does NOT drop a
    zero-chunk lookup: it would push 0 and then 1. That asymmetry is the Rust and
    is preserved rather than tidied. -/
def ProtocolPlan.commitmentReadGroups (self : ProtocolPlan) : List Nat :=
  let groups0 := self.numUserAdvices.filter fun n => n != 0
  let groups1 := if self.numLookups != 0 then groups0 ++ [self.numLookups] else groups0
  let groups2 :=
    if self.numPermutationZs != 0 then groups1 ++ [self.numPermutationZs] else groups1
  let groups3 := groups2 ++ (self.lookupChunks.map fun chunks => [chunks, 1]).flatten
  let groups4 := if self.numTrashcans != 0 then groups3 ++ [self.numTrashcans] else groups3
  groups4 ++ [self.numQuotients]

/-- rust: PM:698-708 (ProtocolPlan::lookup_identity_source). The early return is
    kept (rule R3) by stopping at the first hit: the fold below carries the
    Option and never overwrites one, which is the same function as the loop with
    its return. The stride is chunks + 2 per lookup, not a constant - that is
    what the doc comment at PM:695-697 warns about, and what
    lookupIdentitySource_matchesRustTest_ok pins. -/
def ProtocolPlan.lookupIdentitySource (self : ProtocolPlan) (identityIndex : Nat) :
    Option (Nat × Nat) :=
  let (_, found) :=
    ((List.range self.lookupChunks.length).zip self.lookupChunks).foldl
      (fun st pair =>
        let (base, res) := st
        let (lookup, chunks) := pair
        let count := chunks + 2
        match res with
        | some r => (base + count, some r)
        | none =>
            if identityIndex < base + count
            then (base + count, some (lookup, identityIndex - base))
            else (base + count, none))
      (0, none)
  found

/-- rust: PM:714-939 (ProtocolPlan::validate) @formal-baseline. Twenty checks in
    source order, each returning the Rust's own format! string verbatim: the
    strings are observable (validation_rejects_simple_selector_eval_reads at
    PM:1155-1161 asserts err.contains("simple selector")), so they are part of
    the obligation and not commentary. -/
def ProtocolPlan.validate (self : ProtocolPlan) : Except String Unit := do
  -- PM:715-721
  if self.numSimpleSelectors != self.simpleSelectorCols.length then
    throw s!"simple selector count mismatch: count={self.numSimpleSelectors} cols={self.simpleSelectorCols.length}"
  -- PM:723-734
  let quotientCount := (self.proof.commitments.filter fun c => c.isQuotient).length
  if quotientCount != self.numQuotients then
    throw s!"quotient commitment count mismatch: plan={quotientCount} meta={self.numQuotients}"
  -- PM:736-742
  let groupedCommitments := self.commitmentReadGroups.foldl (fun a b => a + b) 0
  if groupedCommitments != self.proof.commitments.length then
    throw s!"commitment group schedule mismatch: groups={groupedCommitments} commitments={self.proof.commitments.length}"
  -- PM:744-755
  let nonQuotientCount := self.numNonQuotientCommitments
  let expectedNonQuotient :=
    self.adviceIndices.length + self.numLookups + self.numPermutationZs
      + (self.lookupChunks.foldl (fun a b => a + b) 0) + self.numLookups + self.numTrashcans
  if nonQuotientCount != expectedNonQuotient then
    throw s!"non-quotient commitment count mismatch: plan={nonQuotientCount} expected={expectedNonQuotient}"
  -- PM:757-764
  if self.proof.evals.any fun eval =>
      match eval with
      | .fixed q => q.column ∈ self.simpleSelectorCols
      | _ => false then
    throw "simple selector fixed column appears in proof eval reads"
  -- PM:766-781
  let expectedPermZEvals :=
    if self.numPermutationZs == 0 then 0 else 3 * self.numPermutationZs - 1
  let actualPermZEvals :=
    (self.proof.evals.filter fun eval =>
      match eval with
      | .permutationZ _ _ => true
      | _ => false).length
  if actualPermZEvals != expectedPermZEvals then
    throw s!"permutation z eval count mismatch: plan={actualPermZEvals} expected={expectedPermZEvals}"
  -- PM:783-801
  let expectedLookupEvals := (self.lookupChunks.foldl (fun a b => a + b) 0) + 3 * self.numLookups
  let actualLookupEvals :=
    (self.proof.evals.filter fun eval =>
      match eval with
      | .lookupMultiplicity _ => true
      | .lookupHelper _ _ => true
      | .lookupAccumulator _ _ => true
      | _ => false).length
  if actualLookupEvals != expectedLookupEvals then
    throw s!"lookup eval count mismatch: plan={actualLookupEvals} expected={expectedLookupEvals}"
  -- PM:803-805
  match self.pcsQueries.getLast? with
  | some (.linearization) => pure ()
  | _ => throw "PCS query schedule must end with linearization query"
  -- PM:807-821. The Rust loops over 0..advice_indices.len() and returns on the
  -- first column that is not opened, so the message names the smallest such
  -- column; filtering and taking the head reproduces that exactly.
  let openedAdviceCols :=
    btreeSetFromList natCmp (self.adviceQueries.map fun q => q.column)
  let unopened := (List.range self.adviceIndices.length).filter
    fun column => !(column ∈ openedAdviceCols)
  match unopened with
  | column :: _ =>
      throw s!"advice commitment column {column} is absorbed but never opened by PCS"
  | [] => pure ()
  -- PM:823-833
  let pcsLookupMultiplicities :=
    (self.pcsQueries.filter fun q =>
      match q with
      | .lookupMultiplicity _ => true
      | _ => false).length
  if pcsLookupMultiplicities != self.numLookups then
    throw s!"lookup multiplicity PCS coverage mismatch: pcs={pcsLookupMultiplicities} expected={self.numLookups}"
  -- PM:835-845
  let pcsLookupHelpers :=
    (self.pcsQueries.filter fun q =>
      match q with
      | .lookupHelper _ _ => true
      | _ => false).length
  let expectedLookupHelpers := self.lookupChunks.foldl (fun a b => a + b) 0
  if pcsLookupHelpers != expectedLookupHelpers then
    throw s!"lookup helper PCS coverage mismatch: pcs={pcsLookupHelpers} expected={expectedLookupHelpers}"
  -- PM:847-861
  let pcsLookupAccumulators :=
    btreeSetFromList natCmp (self.pcsQueries.filterMap fun q =>
      match q with
      | .lookupAccumulator lookup _ => some lookup
      | _ => none)
  if pcsLookupAccumulators.length != self.numLookups then
    throw s!"lookup accumulator PCS coverage mismatch: pcs={pcsLookupAccumulators.length} expected={self.numLookups}"
  -- PM:863-877
  let pcsPermutationSets :=
    btreeSetFromList natCmp (self.pcsQueries.filterMap fun q =>
      match q with
      | .permutationZ set _ => some set
      | _ => none)
  if pcsPermutationSets.length != self.numPermutationZs then
    throw s!"permutation product PCS coverage mismatch: pcs={pcsPermutationSets.length} expected={self.numPermutationZs}"
  -- PM:879-889
  let pcsTrash :=
    (self.pcsQueries.filter fun q =>
      match q with
      | .trash _ => true
      | _ => false).length
  if pcsTrash != self.numTrashcans then
    throw s!"trashcan PCS coverage mismatch: pcs={pcsTrash} expected={self.numTrashcans}"
  -- PM:891-897
  if self.quotientTraceIds.length != self.quotient.total then
    throw s!"quotient trace id count mismatch: ids={self.quotientTraceIds.length} identities={self.quotient.total}"
  -- PM:898-905
  let lookupIdentityCount :=
    (self.lookupChunks.map fun chunks => chunks + 2).foldl (fun a b => a + b) 0
  if self.quotient.lookup != lookupIdentityCount then
    throw s!"lookup quotient identity count mismatch: plan={self.quotient.lookup} expected={lookupIdentityCount}"
  -- PM:906-912
  if self.pcsQueryTraceIds.length != self.pcsQueries.length then
    throw s!"PCS trace id count mismatch: ids={self.pcsQueryTraceIds.length} queries={self.pcsQueries.length}"
  -- PM:913-915
  if self.quotientTraceIds.any fun id => id ∈ self.pcsQueryTraceIds then
    throw "quotient and PCS trace id spaces overlap"
  -- PM:917-923
  let pcsWithoutLinearization := self.pcsQueries.length - 1
  let proofQueryEvals := self.proof.evals.length
  if pcsWithoutLinearization != proofQueryEvals then
    throw s!"PCS/proof eval query mismatch before linearization: pcs={pcsWithoutLinearization} evals={proofQueryEvals}"
  -- PM:925-936
  let committedInstanceReads := self.proof.evals.filterMap fun eval =>
    match eval with
    | .committedInstance q => some q
    | _ => none
  for q in committedInstanceReads do
    if q.column >= self.numCommittedInstances then
      throw s!"non-committed instance column {q.column} is read from proof"
  -- PM:938
  Except.ok ()

end

end Midfall.Generator

/-! # Known-answer tests for the ported protocol plan

Every gate names the wrong implementation it rules out, in the sense
docs/REVIEW.md R-38 states at the end of its entry and R-41 turns into a rule: a
gate's stated scope must be justified by a perturbation inside that scope.

The expected sides come in two kinds, and the kinds are not equally strong.

The strongest are the assertions of PM:942-1252, the reference's own
#[cfg(test)] mod tests, which this file does not control:
expression_visitor_collects_queries (PM:969-989),
plan_preserves_eval_and_pcs_order_for_basic_cs (PM:991-1033),
plan_skips_non_committed_instance_eval_reads (PM:1035-1048),
lookup_identity_source_handles_variable_chunk_counts (PM:1082-1102),
validation_rejects_simple_selector_eval_reads (PM:1154-1161) and
validation_rejects_absorbed_unopened_advice_commitments (PM:1163-1178). Gates
built on those are evidence, not transcription - and one of them,
validate_rejectsSimpleSelectorEval_matchesRust_ok below, records that a Rust
assertion does not test what its name claims.

The second kind is arithmetic derived here from the ported definitions - the
fixture plan's counts, orders and rotation set. Those are checked against the
port, not against an outside source, and each says so. -/

namespace Midfall.Generator.ProtocolKats

open Midfall Midfall.Halo2 Midfall.Generator

/-- Reading an Except String as "it succeeded at all". Named apart from
    Exec/Circuit.lean's okNat / panicSite, which are already taken in the
    Midfall.Halo2 namespace this file opens. -/
def validateOk {alpha : Type} (e : Except String alpha) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

/-- Reading an Except String as "it failed with a message containing this
    substring", which is exactly what the reference's own tests assert
    (err.contains("simple selector"), PM:1160). -/
def errContains {alpha : Type} (e : Except String alpha) (want : String) : Bool :=
  match e with
  | .error m => m.contains want
  | .ok _ => false

/-- Reading an Except Fault as "it failed at exactly this panic site". -/
def panickedAtSite {alpha : Type} (e : Except Fault alpha) (site : String) : Bool :=
  match e with
  | .error (Fault.panic s) => s == site
  | _ => false

/-! ## The fixture constraint system

Four advice columns (so the phase remapping has a non-trivial nums), two
instance columns (column 0 committed, column 1 not, BOTH at Rotation::cur() so a
filter that tested the rotation instead of the column would keep both and differ),
a simple selector on fixed column 0 with the only real fixed query on column 1,
four permutation columns, one lookup with five parallel inputs (two chunks), one
empty trashcan, and two gate polynomials.

minimumDegree := some 5 is what makes the expectations hand-computable. Without
it the lookup's own degree_batched_argument would raise the system degree, and
the degree would then feed back into chunk_by_degree; with it,
degree_without_lookup is 5 and degree_batched_argument 5 is also 5, so
cs_degree = 5 exactly. That gives permutation_chunk_len = 3, four permutation
columns and so num_permutation_zs = 2 - the smallest case that exercises the
"Last for every set except the final one" rule, which is R-30's lesson that a
dimension of size one cannot distinguish "one" from "all". -/

def colA (i : Nat) : Column := { index := i, columnType := Any.advice { phase := { val := 0 } } }
def colF (i : Nat) : Column := { index := i, columnType := Any.fixed }
def colI (i : Nat) : Column := { index := i, columnType := Any.instance }

def eA (i : Nat) (r : Rotation) : Expression (Fr 17) :=
  Expression.advice { index := some i, columnIndex := i, rotation := r, phase := { val := 0 } }
def eF (i : Nat) (r : Rotation) : Expression (Fr 17) :=
  Expression.fixed { index := some i, columnIndex := i, rotation := r }

def fixtureCs : ConstraintSystem (Fr 17) :=
  { (ConstraintSystem.default : ConstraintSystem (Fr 17)) with
    numFixedColumns := 2
    numAdviceColumns := 4
    numInstanceColumns := 2
    numSelectors := 1
    selectorFlags := #[{ isSimple := true, colIdx := some 0 }]
    adviceColumnPhase := #[{ val := 0 }, { val := 0 }, { val := 0 }, { val := 0 }]
    challengePhase := #[]
    numAdviceQueries := #[1, 1, 1, 1]
    minimumDegree := some 5
    gates := #[
      { name := "fixture", constraintNames := #["c0", "c1"],
        polys := #[Expression.product (eA 0 Rotation.cur) (eA 1 Rotation.cur),
          eF 1 Rotation.cur],
        queriedSelectors := #[], queriedCells := #[] }]
    adviceQueries := #[(colA 0, Rotation.cur), (colA 1, Rotation.next),
      (colA 2, Rotation.prev), (colA 3, Rotation.cur)]
    instanceQueries := #[(colI 0, Rotation.cur), (colI 1, Rotation.cur)]
    fixedQueries := #[(colF 1, Rotation.cur)]
    permutation := { columns := #[colA 0, colA 1, colA 2, colA 3] }
    lookups := #[
      { name := "lk", selector := Expression.constant 0,
        inputExpressions := #[#[eA 0 Rotation.cur], #[eA 0 Rotation.cur],
          #[eA 0 Rotation.cur], #[eA 0 Rotation.cur], #[eA 0 Rotation.cur]],
        tableExpressions := #[eF 1 Rotation.cur] }]
    trashcans := #[
      { name := "tr", selector := Expression.constant 1,
        constraintExpressions := #[] }] }

/-- The fixture plan, built once and read by the gates below. If construction
    fails it degrades to protocolPlanDefault, which makes every gate that reads
    it fail loudly rather than quietly. -/
def fixturePlan : ProtocolPlan :=
  match ProtocolPlan.fromConstraintSystem Features.solidity fixtureCs 1 with
  | .ok plan => plan
  | .error _ => protocolPlanDefault

/-! ## The BTreeSet model (hazards 1, 2 and 3) -/

/-- HAZARD 1 - QueryKey's derived Ord compares rotation as a SIGNED i32. PM:21
    derives Ord on the struct, so the order is column then rotation, and rotation
    is an i32. A model that reused Nat's ordering would put -1 above 5. This
    collects the keys the reference's own visitor test touches - advice at
    Rotation::next() = 1, fixed at Rotation::prev() = -1 (PM:985-986) - plus a
    deliberate same-column negative/positive pair and a duplicate.

    PERTURBATION CHECKED: replacing intCmp with natCmp in QueryKey.cmp is a
    one-token edit and reddens this gate, because (0,-1) moves past (0,5).
    Swapping the two comparators - ordering by rotation first - reddens it too,
    since (1,-5) would then precede (0,-1). -/
def queryKey_order_ok : Bool :=
  btreeSetFromList QueryKey.cmp
    [QueryKey.new 1 (-5), QueryKey.new 0 5, QueryKey.new 0 (-1),
      QueryKey.new 0 5, QueryKey.new 0 0, QueryKey.new 1 0]
  ==
    [QueryKey.new 0 (-1), QueryKey.new 0 0, QueryKey.new 0 5,
      QueryKey.new 1 (-5), QueryKey.new 1 0]

/-- HAZARD 2 - CommonPoly's derived Ord is DECLARATION order, so
    Rotation _ < L0 < LLast < LBlind whatever the payload, and inside Rotation
    the payload is a signed i32 (PM:136-146). Three inputs: the plain Lagrange
    triple, a mixed set with a negative rotation that must sort below L0, and a
    duplicate.

    PERTURBATION CHECKED, and this gate earned its keep: the first draft of
    CommonPoly.cmp collapsed the LLast row to | .lLast, _ => .lt, which also
    matches (lLast, l0) and put LLast BELOW L0 - the plain Lagrange triple came
    out as [LLast, L0, LBlind]. That is a one-token arm-order error the Rotation
    arms cannot see, and the FIRST conjunct here is what went red until the arms
    were split. Two perturbations were run against the fixed comparator: making
    the | .l0, _ => .lt arm return .gt reddens the first conjunct and leaves the
    other two green, and reverting the LLast arms to a single catch-all reddens
    this gate plus usedLagrange_ok and fromConstraintSystem_fixture_ok. -/
def commonPoly_order_ok : Bool :=
  btreeSetFromList CommonPoly.cmp
    [CommonPoly.lBlind, CommonPoly.l0, CommonPoly.lLast]
  == [CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && btreeSetFromList CommonPoly.cmp
      [CommonPoly.l0, CommonPoly.rotation (-1), CommonPoly.lBlind,
        CommonPoly.rotation 3, CommonPoly.lLast, CommonPoly.rotation 0]
  ==
    [CommonPoly.rotation (-1), CommonPoly.rotation 0, CommonPoly.rotation 3,
      CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && btreeSetFromList CommonPoly.cmp
      [CommonPoly.rotation 2, CommonPoly.rotation 2, CommonPoly.l0]
  == [CommonPoly.rotation 2, CommonPoly.l0]

/-- HAZARD 3 - the sorted-nub helper itself. btreeSetInsert is what every
    BTreeSet::insert in the file becomes, so if it is wrong both BTreeSet fields
    of ProtocolPlan and all four of UsedQueries are wrong together. This pins the
    three cases the Rust distinguishes - below, equal (no change, no duplicate),
    above - on a list that is already sorted, and pins btreeSetFromList against a
    permutation of the same multiset, which is the property the set reading
    depends on and the Vec reading does not have.

    PERTURBATION CHECKED: making the .eq arm append (so an existing key is
    inserted again) reddens the second and fourth conjuncts; swapping .lt and .gt
    reddens the first and third. -/
def btreeSetInsert_ok : Bool :=
  btreeSetInsert natCmp 0 [1, 3] == [0, 1, 3]
    && btreeSetInsert natCmp 3 [1, 3, 5] == [1, 3, 5]
    && btreeSetInsert natCmp 4 [1, 3, 5] == [1, 3, 4, 5]
    && btreeSetFromList natCmp [4, 1, 4, 7, 1, 4] == [1, 4, 7]
    && btreeSetFromList natCmp [7, 4, 1] == btreeSetFromList natCmp [1, 4, 7]
    && btreeSetFromList intCmp [(-2 : Int), 0, (-1), 0] == [-2, -1, 0]

/-! ## The small ported items -/

/-- used_lagrange for all eight boolean triples (PM:245-260). The rows that
    discriminate are (false,false,true), where ONLY Rotation 0 is present - a
    port that gated the rotation insert on the other two flags reddens it - and
    the three rows with Rotation 0 plus the Lagrange triple, where the sorted
    order puts the rotation FIRST even though the Rust inserts it last. -/
def usedLagrange_ok : Bool :=
  usedLagrange false false false == []
    && usedLagrange true false false
      == [CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && usedLagrange false true false
      == [CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && usedLagrange false false true == [CommonPoly.rotation 0]
    && usedLagrange true true false
      == [CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && usedLagrange true false true
      == [CommonPoly.rotation 0, CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && usedLagrange false true true
      == [CommonPoly.rotation 0, CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && usedLagrange true true true
      == [CommonPoly.rotation 0, CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]

/-- PcsQuerySource::rotation (PM:117-132), every arm, including the Last case
    with a NEGATIVE rotation_last - the only realistic input, since PM:402 makes
    it -(blinding_factors + 1). A port that returned 0 for Last, or that ignored
    the argument, changes common_polys and so the generated verifier's Lagrange
    set, without changing any count.

    PERTURBATION CHECKED, each one run: returning 0 in the .last arm reddens the
    sixth and seventh conjuncts; returning 1 for LookupMultiplicity reddens the
    eighth; and making the lookupAccumulator arm ignore its payload reddens the
    tenth. -/
def pcsQuerySource_rotation_ok : Bool :=
  (PcsQuerySource.advice (QueryKey.new 3 (-2))).rotation (-7) == -2
    && (PcsQuerySource.committedInstance (QueryKey.new 0 4)).rotation (-7) == 4
    && (PcsQuerySource.fixed (QueryKey.new 1 (-1))).rotation (-7) == -1
    && (PcsQuerySource.permutationZ 0 PermutationZEval.cur).rotation (-7) == 0
    && (PcsQuerySource.permutationZ 0 PermutationZEval.next).rotation (-7) == 1
    && (PcsQuerySource.permutationZ 0 PermutationZEval.last).rotation (-7) == -7
    && (PcsQuerySource.permutationZ 2 PermutationZEval.last).rotation (-10) == -10
    && (PcsQuerySource.lookupMultiplicity 0).rotation (-7) == 0
    && (PcsQuerySource.lookupHelper 0 1).rotation (-7) == 0
    && (PcsQuerySource.lookupAccumulator 0 1).rotation (-7) == 1
    && (PcsQuerySource.lookupAccumulator 0 0).rotation (-7) == 0
    && (PcsQuerySource.trash 0).rotation (-7) == 0
    && (PcsQuerySource.permutationCommon (colF 0)).rotation (-7) == 0
    && PcsQuerySource.linearization.rotation (-7) == 0

/-- CommitmentRead::is_quotient (PM:58-60): exactly one of the seven variants.
    Rules out the matches! being written against the wrong variant, and rules out
    Trash - the neighbour in declaration order - being swept in, which would
    change num_non_quotient_commitments and the quotient-count check together. -/
def isQuotient_ok : Bool :=
  ! CommitmentRead.advice.isQuotient
    && ! CommitmentRead.lookupMultiplicity.isQuotient
    && ! CommitmentRead.permutationProduct.isQuotient
    && ! CommitmentRead.lookupHelper.isQuotient
    && ! CommitmentRead.lookupAccumulator.isQuotient
    && ! CommitmentRead.trash.isQuotient
    && CommitmentRead.quotient.isQuotient

/-- QuotientIdentityPlan::total (PM:172-174) is a plain four-way sum. The
    all-zero row matters because protocolPlanDefault must give 0 -
    lookup_identity_source_handles_variable_chunk_counts (PM:1086-1093) builds a
    plan with ..QuotientIdentityPlan::default(). Dropping any one of the four
    terms reddens the second or third conjunct. -/
def quotientTotal_ok : Bool :=
  quotientIdentityPlanDefault.total == 0
    && ({ gates := 1, permutation := 2, lookup := 3, trash := 4 } :
        QuotientIdentityPlan).total == 10
    && ({ gates := 0, permutation := 5, lookup := 4, trash := 1 } :
        QuotientIdentityPlan).total == 10

/-- The reference's own test PM:1082-1102, transcribed. lookup_chunks = [1,4,2]
    gives strides 3, 6, 4 and so bases 0, 3, 9; the seven probes land in each
    lookup's first slot, its last slot, and one past the end of the whole
    schedule. A constant stride - the bug the doc comment at PM:695-697 warns
    about - reddens the (3, (1,0)) and (9, (2,0)) rows. Dropping the guard that
    keeps the FIRST hit, so the fold becomes "last one wins", reddens the (0,0)
    row: probe 0 then also satisfies 0 < 3 + 6 for the second lookup and comes
    back (1, 0) after the saturating Nat subtraction. Both perturbations were
    run. -/
def lookupIdentitySource_matchesRustTest_ok : Bool :=
  let plan : ProtocolPlan :=
    { protocolPlanDefault with
      lookupChunks := [1, 4, 2]
      quotient := { quotientIdentityPlanDefault with lookup := 13 } }
  plan.lookupIdentitySource 0 == some (0, 0)
    && plan.lookupIdentitySource 2 == some (0, 2)
    && plan.lookupIdentitySource 3 == some (1, 0)
    && plan.lookupIdentitySource 8 == some (1, 5)
    && plan.lookupIdentitySource 9 == some (2, 0)
    && plan.lookupIdentitySource 12 == some (2, 3)
    && plan.lookupIdentitySource 13 == none

/-- The reference's own test PM:969-989, transcribed: the expression
    advice(next) + fixed(prev) * instance(cur) + challenge must report advice
    (0, 1), fixed (0, -1), instance (0, 0) and challenge index 0 - the four
    contains! assertions at PM:985-988, stated as exact sets rather than
    membership so a closure that inserted into the wrong field is caught. All
    three column indices are 0 because each column kind has its own counter,
    which is exactly what makes a mix-up between the three closures invisible to
    a membership assertion and visible to an equality one.

    PERTURBATION CHECKED: swapping the adviceColumn and fixedColumn closures
    reddens the first two conjuncts; making the challenge closure insert 1
    reddens the fourth; and making merge return its left argument unchanged
    reddens the second, third and fourth - not the first, because advice is the
    left spine of the expression, which is exactly why all four fields are
    asserted rather than only the interesting one. -/
def usedQuery_matchesRustTest_ok : Bool :=
  let expr : Expression (Fr 17) :=
    Expression.sum
      (Expression.sum
        (eA 0 Rotation.next)
        (Expression.product (eF 0 Rotation.prev)
          (Expression.instance { index := some 0, columnIndex := 0, rotation := Rotation.cur })))
      (Expression.challenge { index := 0, phase := { val := 0 } })
  let used := usedQuery expr
  used.advice == [QueryKey.new 0 1]
    && used.fixed == [QueryKey.new 0 (-1)]
    && used.instance_ == [QueryKey.new 0 0]
    && used.challenges == [0]

/-- The two trace re-exports must be the Layout row's values and not copies that
    can drift: PM:178 re-exports trace::QUOTIENT_IDENTITY_BASE (LM:784) and
    PM:180 re-exports trace::PCS_QUERY_BASE (LM:781). The literals are the ones
    the reference's own layout test pins at LM:877 and LM:880. -/
def traceReexports_ok : Bool :=
  traceQuotientIdentityBase == Midfall.Generator.Trace.quotientIdentityBase
    && tracePcsQueryBase == Midfall.Generator.Trace.pcsQueryBase
    && traceQuotientIdentityBase == 30000
    && tracePcsQueryBase == 2000

/-! ## from_constraint_system on the fixture -/

/-- THE FIXTURE PLAN IS THE HAND-COMPUTED ONE. Every number below was derived
    from PM:331-614 before the port was run, and the port agrees; the derivation
    is written out so a reviewer can redo it without executing anything.

    * cs_degree = 5: minimumDegree 5 beats the permutation's constant 3, the
      degree-2 gate product and the trash's 2, and degree_batched_argument 5 is
      also 5. So permutation_chunk_len = 5 - 2 = 3 and
      num_permutation_zs = div_ceil 4 3 = 2, and num_quotients = 5 - 1 = 4 under
      the recorded feature set (outerSingleHCommitment = false).
    * lookup_chunks = [2]: nb_parallel_lookups_per_chunk 5 is
      (next_power_of_two(4) + 1) - 1 = 4 divided by lookup_degree 1, and
      div_ceil 5 4 = 2.
    * rotation_last = -10: blinding_factors is max(3, max num_advice_queries 1)
      = 3, +1 trashcan = 4, +2 lookup chunks = 6, +1+1+1 = 9.
    * 15 commitments = 4 advice + 1 multiplicity + 2 products + (2 helpers + 1
      accumulator) + 1 trash + 4 quotients.
    * 21 evals, 22 PCS queries - the extra one is Linearization, which is what
      PM:917-923 requires.
    * quotient = {gates: 2, permutation: 2 + (2-1) + 2 = 5, lookup: 2 + 2 = 4,
      trash: 1}, total 12, so the trace ids run 30000..30011 and 2000..2021.
    * common_polys is the seven-element set whose four rotations -10, -1, 0, 1
      sort BELOW the three Lagrange bases.

    PERTURBATION CHECKED, both run: dropping the set + 1 != numPermutationZs
    guard so the final set also emits Last makes the plan fail validate, so
    fixturePlan degrades to protocolPlanDefault and this gate goes red on almost
    every conjunct; and setting num_quotients to csDegree instead of csDegree - 1
    reddens the numQuotients, commitment-count and trace-id conjuncts for the
    same reason. That degradation is the design: a plan that cannot be built can
    never look like a plan that was built wrong. -/
def fromConstraintSystem_fixture_ok : Bool :=
  fixturePlan.numFixeds == 2
    && fixturePlan.permutationChunkLen == 3
    && fixturePlan.numPermutationZs == 2
    && fixturePlan.lookupChunks == [2]
    && fixturePlan.numLookups == 1
    && fixturePlan.numTrashcans == 1
    && fixturePlan.numQuotients == 4
    && fixturePlan.numSimpleSelectors == 1
    && fixturePlan.simpleSelectorCols == [0]
    && fixturePlan.numCommittedInstances == 1
    && fixturePlan.numUserAdvices == [4]
    && fixturePlan.numUserChallenges == [0]
    && fixturePlan.adviceIndices == [0, 1, 2, 3]
    && fixturePlan.challengeIndices == []
    && fixturePlan.rotationLast == -10
    && fixturePlan.adviceQueries ==
      [QueryKey.new 0 0, QueryKey.new 1 1, QueryKey.new 2 (-1), QueryKey.new 3 0]
    && fixturePlan.instanceQueries == [QueryKey.new 0 0, QueryKey.new 1 0]
    && fixturePlan.proof.commitments.length == 15
    && fixturePlan.proof.evals.length == 21
    && fixturePlan.pcsQueries.length == 22
    && fixturePlan.numMainEvals == 21
    && fixturePlan.numCommitments == 15
    && fixturePlan.numNonQuotientCommitments == 11
    && fixturePlan.commitmentReadGroups == [4, 1, 2, 2, 1, 1, 4]
    && fixturePlan.quotient == { gates := 2, permutation := 5, lookup := 4, trash := 1 }
    && fixturePlan.quotient.total == 12
    && fixturePlan.quotientTraceIds == (List.range 12).map (fun i => 30000 + i)
    && fixturePlan.pcsQueryTraceIds == (List.range 22).map (fun i => 2000 + i)
    && fixturePlan.commonPolys ==
      [CommonPoly.rotation (-10), CommonPoly.rotation (-1), CommonPoly.rotation 0,
        CommonPoly.rotation 1, CommonPoly.l0, CommonPoly.lLast, CommonPoly.lBlind]
    && validateOk fixturePlan.validate

/-- THE TWO STREAMS ARE IN DIFFERENT ORDERS, AND BOTH ARE PINNED ELEMENT BY
    ELEMENT. The eval stream opens the committed instance BEFORE advice
    (PM:436-443); the PCS stream opens advice BEFORE the committed instance
    (PM:528-535). A port that used one order for both - the obvious tidy-up, and
    invisible to every count in validate because the counts are the same - would
    emit a proof whose scalar stream is read in the wrong order. This is also
    where the reference's own plan_preserves_eval_and_pcs_order_for_basic_cs
    (PM:996-1031) lives; the fixture is richer so the permutation, lookup and
    trash interleavings are pinned too.

    PERTURBATION CHECKED: swapping evalCommittedInstances and evalAdvice reddens
    the first conjunct and leaves every length gate green - which is the point. -/
def fromConstraintSystem_streamOrder_ok : Bool :=
  fixturePlan.proof.evals ==
    [EvalRead.committedInstance (QueryKey.new 0 0),
      EvalRead.advice (QueryKey.new 0 0),
      EvalRead.advice (QueryKey.new 1 1),
      EvalRead.advice (QueryKey.new 2 (-1)),
      EvalRead.advice (QueryKey.new 3 0),
      EvalRead.fixed (QueryKey.new 1 0),
      EvalRead.permutationCommon (colA 0),
      EvalRead.permutationCommon (colA 1),
      EvalRead.permutationCommon (colA 2),
      EvalRead.permutationCommon (colA 3),
      EvalRead.permutationZ 0 PermutationZEval.cur,
      EvalRead.permutationZ 0 PermutationZEval.next,
      EvalRead.permutationZ 0 PermutationZEval.last,
      EvalRead.permutationZ 1 PermutationZEval.cur,
      EvalRead.permutationZ 1 PermutationZEval.next,
      EvalRead.lookupMultiplicity 0,
      EvalRead.lookupHelper 0 0,
      EvalRead.lookupHelper 0 1,
      EvalRead.lookupAccumulator 0 0,
      EvalRead.lookupAccumulator 0 1,
      EvalRead.trash 0]
    && fixturePlan.pcsQueries.take 6 ==
      [PcsQuerySource.advice (QueryKey.new 0 0),
        PcsQuerySource.advice (QueryKey.new 1 1),
        PcsQuerySource.advice (QueryKey.new 2 (-1)),
        PcsQuerySource.advice (QueryKey.new 3 0),
        PcsQuerySource.committedInstance (QueryKey.new 0 0),
        PcsQuerySource.permutationZ 0 PermutationZEval.cur]
    && fixturePlan.pcsQueries.drop 16 ==
      [PcsQuerySource.fixed (QueryKey.new 1 0),
        PcsQuerySource.permutationCommon (colA 0),
        PcsQuerySource.permutationCommon (colA 1),
        PcsQuerySource.permutationCommon (colA 2),
        PcsQuerySource.permutationCommon (colA 3),
        PcsQuerySource.linearization]
    && fixturePlan.pcsQueries.getLast? == some PcsQuerySource.linearization

/-- The reference's own test PM:1035-1048: with nb_committed_instances = 0 no
    CommittedInstance appears in either stream, even though the constraint system
    still has two instance queries. Both fixture instance queries are at
    Rotation::cur(), so a filter written against the ROTATION instead of the
    column - q.rotation < nb_committed_instances, the same shape of mistake -
    would keep BOTH reads at nb_committed_instances = 1 and is caught by
    fromConstraintSystem_streamOrder_ok. It is NOT caught here: at
    nb_committed_instances = 0 both filters keep nothing, so this gate is the
    absence check only and the other gate supplies the presence check. Verified:
    replacing q.column with q.rotation in the filter reddens
    fromConstraintSystem_fixture_ok and fromConstraintSystem_streamOrder_ok and
    leaves this one green. -/
def fromConstraintSystem_skipsNonCommitted_ok : Bool :=
  match ProtocolPlan.fromConstraintSystem Features.solidity fixtureCs 0 with
  | .ok plan =>
    ! plan.proof.evals.any (fun e => match e with
      | .committedInstance _ => true
      | _ => false)
      && ! plan.pcsQueries.any (fun q => match q with
        | .committedInstance _ => true
        | _ => false)
      && plan.proof.evals.length == 20
      && plan.pcsQueries.length == 21
      && validateOk plan.validate
  | .error _ => false

/-- The reference's own test PM:1154-1161, transcribed. Its simple_cs has one
    fixed column and NO simple selectors, so the plan starts at
    num_simple_selectors = 0 with an empty column set; the test inserts column 0
    into that set, pushes a Fixed read on column 0, and expects an error
    containing "simple selector". The fixture is reset to that shape here -
    numSimpleSelectors := 0, simpleSelectorCols := [0] - rather than reusing its
    own one-selector state.

    AND THE FINDING: that Rust test does not reach the check its name claims. In
    the reference's simple_cs there are no simple selectors, so inserting column
    0 makes num_simple_selectors (0) disagree with simple_selector_cols.len()
    (1), and validate's FIRST check fires with "simple selector count mismatch" -
    which contains "simple selector", so the assertion passes without ever
    evaluating the eval-read check at PM:757-764. The next gate is the one that
    actually exercises that check. Recorded rather than quietly improved, because
    R11 asks for the divergence to be said out loud. -/
def validate_rejectsSimpleSelectorEval_matchesRust_ok : Bool :=
  let plan : ProtocolPlan :=
    { fixturePlan with
      numSimpleSelectors := 0
      simpleSelectorCols := [0]
      proof := { fixturePlan.proof with
        evals := fixturePlan.proof.evals ++ [EvalRead.fixed (QueryKey.new 0 0)] } }
  errContains plan.validate "simple selector"
    && match plan.validate with
       | .error m => m == "simple selector count mismatch: count=0 cols=1"
       | .ok _ => false

/-- The check the reference test misses: make num_simple_selectors agree with the
    column set so the first check passes, and the eval-read check at PM:757-764 is
    the one that fires - the fixture's own Fixed read is on column 1, which the
    widened set now contains. The message is a literal with no numbers, so
    asserting the whole string is strictly stronger than the Rust's contains, and
    it is a different string from the one the gate above pins. -/
def validate_rejectsSimpleSelectorEval_readCheck_ok : Bool :=
  let plan : ProtocolPlan :=
    { fixturePlan with
      numSimpleSelectors := 2
      simpleSelectorCols := [0, 1] }
  match plan.validate with
  | .error m =>
    m == "simple selector fixed column appears in proof eval reads"
  | .ok _ => false

/-- The reference's own test PM:1163-1178: an advice column that is absorbed as
    a commitment but never opened by PCS is rejected with "absorbed but never
    opened by PCS". The Rust reaches it by retaining column 1 out of all three
    vectors; the same is done here, and the point is that the untouched plan
    validates (fromConstraintSystem_fixture_ok) while this one does not. -/
def validate_rejectsUnopenedAdvice_ok : Bool :=
  let adviceQueries := fixturePlan.adviceQueries.filter fun q => q.column != 1
  let evals := fixturePlan.proof.evals.filter fun e =>
    match e with
    | .advice q => q.column != 1
    | _ => true
  let pcsQueries := fixturePlan.pcsQueries.filter fun q =>
    match q with
    | .advice q => q.column != 1
    | _ => true
  let plan : ProtocolPlan :=
    { fixturePlan with
      adviceQueries := adviceQueries
      proof := { fixturePlan.proof with evals := evals }
      pcsQueries := pcsQueries }
  errContains plan.validate "absorbed but never opened by PCS"
    && errContains plan.validate "advice commitment column 1"

/-- The I-6 column-versus-query assert at PM:461-475 fires as a PANIC, not as a
    validate error, and it is the only place in the file where a malformed
    constraint system is refused before a plan exists. The fixture has one fixed
    column (index 1) queried once and one simple selector (index 0), so
    1 == 2 - 1 holds; querying column 1 twice breaks the equality (2 non-simple
    queries against 1 non-simple column) and must abort at exactly that site
    rather than defaulting. Rules out the assert being ported as a silent filter,
    which is the shape this check would take if it were written to pass. -/
def fromConstraintSystem_fixedEvalMismatch_panics_ok : Bool :=
  let cs : ConstraintSystem (Fr 17) :=
    { fixtureCs with
      fixedQueries := #[(colF 1, Rotation.cur), (colF 1, Rotation.next)] }
  panickedAtSite (ProtocolPlan.fromConstraintSystem Features.solidity cs 1)
    "proofs/solidity-verifier/src/lowering/protocol/mod.rs:461"

/-- The debug_assert_eq! of PM:684-688, compiled out in the reference profile
    and asserted here instead: the commitment groups must cover the commitment
    plan exactly. Rules out a group being dropped from commitmentReadGroups -
    which validate's third check would also catch, so this gate is the one that
    says WHY the third check passes rather than leaning on it. The first three
    conjuncts are there because the equality alone is satisfied by
    protocolPlanDefault - 0 == 0 - so a plan that failed to build would let this
    gate pass vacuously; pinning the concrete groups and lengths closes that, and
    dropping the trailing 1 from each lookup group reddens it. -/
def commitmentReadGroups_debugAssert_ok : Bool :=
  fixturePlan.numQuotients == 4
    && fixturePlan.commitmentReadGroups == [4, 1, 2, 2, 1, 1, 4]
    && fixturePlan.proof.commitments.length == 15
    && (fixturePlan.commitmentReadGroups.foldl (fun a b => a + b) 0)
      == fixturePlan.proof.commitments.length

#eval queryKey_order_ok -- expect true
#eval commonPoly_order_ok -- expect true
#eval btreeSetInsert_ok -- expect true
#eval usedLagrange_ok -- expect true
#eval pcsQuerySource_rotation_ok -- expect true
#eval isQuotient_ok -- expect true
#eval quotientTotal_ok -- expect true
#eval lookupIdentitySource_matchesRustTest_ok -- expect true
#eval usedQuery_matchesRustTest_ok -- expect true
#eval traceReexports_ok -- expect true
#eval fromConstraintSystem_fixture_ok -- expect true
#eval fromConstraintSystem_streamOrder_ok -- expect true
#eval fromConstraintSystem_skipsNonCommitted_ok -- expect true
#eval validate_rejectsSimpleSelectorEval_matchesRust_ok -- expect true
#eval validate_rejectsSimpleSelectorEval_readCheck_ok -- expect true
#eval validate_rejectsUnopenedAdvice_ok -- expect true
#eval fromConstraintSystem_fixedEvalMismatch_panics_ok -- expect true
#eval commitmentReadGroups_debugAssert_ok -- expect true

end Midfall.Generator.ProtocolKats
