-- |
-- Midfall.Halo2.Exec.Kzg.Utils
--
-- The multi-open bookkeeping (rust: proofs/src/poly/kzg/utils.rs): group the
-- verifier queries by commitment and by point set, and lay their evaluations
-- out in the order the KZG combination expects. multi_prepare is the direct
-- consumer, and the order this returns is part of the proof layout, so it is
-- as load-bearing as the arithmetic.
--
-- Two Rust collections need care under rule R6:
--
--   * point_index_map is a HashMap, but everything taken from it is
--     entry(p).or_insert(len), i.e. a point's index is the order of its first
--     occurrence. The inverse map built at :69 is iterated once and every
--     index is distinct there, so its iteration order is unobservable and
--     rule R6's HashMap condition holds. Modelled as a list in first-
--     occurrence order, which is what the behaviour actually is.
--   * point_idx_sets is a BTreeMap keyed by BTreeSet<usize>: keys deduplicate,
--     and a key's indices iterate ascending. Modelled as a list of
--     (ascending index list, set index) in insertion order. The BTreeMap
--     ordering is only used at :125, where each set writes into its own slot,
--     so what matters is the ascending order inside a slot - which the sorted
--     key gives.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Query

namespace Midfall.Halo2

-- rust: proofs/src/poly/kzg/utils.rs:11-18 (struct CommitmentData). Field
-- order is the Rust order (rule R1).
structure CommitmentData (eval com : Type) where
  commitmentLabel : CommitmentLabel
  commitment : com
  setIndex : Nat
  pointIndices : Array Nat
  evals : Array eval

-- rust: proofs/src/poly/kzg/utils.rs:20-30 (CommitmentData::new): set_index
-- starts at 0 and both vectors are empty; the caller pushes the first point
-- index separately, and the port keeps that split rather than folding it in.
def CommitmentData.new {eval com : Type} (commitment : com)
    (commitmentLabel : CommitmentLabel) : CommitmentData eval com :=
  { commitmentLabel, commitment, setIndex := 0, pointIndices := #[], evals := #[] }

-- rust: proofs/src/poly/kzg/utils.rs:32-35 (type IntermediateSets): the
-- commitment data and the point sets, as a pair.
abbrev IntermediateSets (F C : Type) : Type :=
  Array (CommitmentData F (CommitmentReference F C)) × Array (Array F)

-- Replace the i-th element of a list. Port scaffolding for the Rust's
-- in-place mutation of commitment_map[pos]; out of range leaves the list
-- alone, which is unreachable because every index comes from findIdx?.
def listReplaceAt {α : Type} (xs : List α) (i : Nat) (v : α) : List α :=
  go xs i v
where
  go : List α → Nat → α → List α
    | [], _, _ => []
    | _ :: rest, 0, v => v :: rest
    | x :: rest, i + 1, v => x :: go rest i v

-- The head of a list dropped to an index, as an Option: the safe reading of
-- the Rust's commitment_map[pos] indexing.
def listAt {α : Type} (xs : List α) (i : Nat) : Option α :=
  (xs.drop i).head?


/-- Ascending insertion sort on Nat: the BTreeSet ordering the Rust key gives.
    Lean v4.35.0 core has no List.qsort, and these lists are the point indices
    of a single commitment, i.e. tiny. -/
def natSort : List Nat -> List Nat
  | [] => []
  | x :: xs => insert x (natSort xs)
where
  insert : Nat -> List Nat -> List Nat
    | x, [] => [x]
    | x, y :: ys => if x <= y then x :: y :: ys else y :: insert x ys

/-- Array update that ignores an out-of-range index. The Rust indexes
    evals[point_index_in_set] directly (utils.rs:118); the index comes from a
    findIdx? over the set the vector was sized from, so it is in range, and the
    fallback only keeps the port total (rule R10). -/
def arraySetD {α : Type} (a : Array α) (i : Nat) (v : α) : Array α :=
  if h : i < a.size then
    a.set i v
  else
    a

/-- Array of n copies of v (rust: vec![F::default(); n]). -/
def arrayReplicate {α : Type} (n : Nat) (v : α) : Array α :=
  (List.replicate n v).toArray

-- Shorthand for the commitment record at the instantiated types.
abbrev CD (F C : Type) : Type := CommitmentData F (CommitmentReference F C)

/-- rust: proofs/src/poly/kzg/utils.rs:37-133 (construct_intermediate_sets).

    THE GROUPING RELATION IS A PARAMETER, and that is the point of the
    signature. The Rust groups with comm == query.get_commitment(), i.e.
    PartialEq on CommitmentReference, whose OnePiece arm is std::ptr::eq
    (query.rs:125): grouping is by *allocation*, not by value. Lean has no
    addresses, so D-P61 (docs/design.md:2183-2196, card REF.1) gave one-piece
    commitments a `CommitSlot` and `Exec/Kzg/MultiOpen` instantiates this with
    `kzgCommitBeq`, which compares the slot (and, for Linear, the points and
    scalars with the labels ignored). That is the Rust relation; value equality
    is the old pre-D-P61 reading and is kept only as the falsifier below. The
    fixture's six identity fixed-column commitments are the case that
    distinguishes them: `fixtureShape_groups_ok` pins the slot reading and
    `fixtureShape_old_rejects_ok` pins the value reading's rejection.

    Panic sites, all of them .unwrap() on a lookup the construction just
    populated: :96 (point index), :103 (commitment to set), :107 (set index),
    :112 (position of the point in its set), and the :104 assert that a set is
    non-empty. :118 indexes evals at the position just found. None is
    reachable for a query set built by multi_prepare; each is a Fault.panic so
    a malformed caller cannot silently shift the point sets.

    The one Rust error, Error::DuplicatedQuery at :58 (same commitment queried
    twice at the same point), is reported as Error::opening: the only caller
    collapses every poly::Error to Error::Opening (plonk/verifier.rs:651), and
    poly::Error belongs to Exec/Poly, not here. -/
def constructIntermediateSets {F C : Type} [Field F] [BEq F]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (queries : Array (VerifierQuery F C)) : Except Fault (IntermediateSets F C) := do
  let (points, cmap0) ← pass1 queries.toList [] []
  let (commitSets, sets) := pass2 cmap0 [] []
  let cmap1 := cmap0.map fun cd =>
    { cd with evals := arrayReplicate cd.pointIndices.size (0 : F) }
  let cmap2 ← pass3 queries.toList points sets commitSets cmap1
  let pointSets := (sets.map fun (set, _) =>
    (set.filterMap (fun i => listAt points i)).toArray).toArray
  return (cmap2.toArray, pointSets)
where
  pass1 : List (VerifierQuery F C) → List F → List (CD F C) →
      Except Fault (List F × List (CD F C))
    | [], pts, cms => .ok (pts, cms)
    | q :: rest, pts, cms => do
        let (pidx, ptsNext) := match pts.findIdx? (fun p => p == q.point) with
          | some i => (i, pts)
          | none => (pts.length, pts ++ [q.point])
        match cms.findIdx? (fun cd => eqC cd.commitment q.commitment) with
        | some pos =>
          match listAt cms pos with
          | none => .error (Fault.panic "proofs/src/poly/kzg/utils.rs:55")
          | some cd =>
            if cd.pointIndices.toList.contains pidx then
              .error (Fault.error Error.opening)
            else
              pass1 rest ptsNext
                (listReplaceAt cms pos
                  { cd with pointIndices := cd.pointIndices.push pidx })
        | none =>
          let tmp := CommitmentData.new q.commitment q.commitmentLabel
          pass1 rest ptsNext (cms ++ [{ tmp with pointIndices := #[pidx] }])

  pass2 : List (CD F C) → List (List Nat × Nat) →
      List (CommitmentReference F C × List Nat) →
      List (CommitmentReference F C × List Nat) × List (List Nat × Nat)
    | [], sets, csm => (csm.reverse, sets)
    | cd :: rest, sets, csm =>
        let set := natSort cd.pointIndices.toList
        let found := sets.findIdx? (fun s => s.1 == set)
        let idx := match found with | some i => i | none => sets.length
        let setsNext := match found with
          | some _ => sets
          | none => sets ++ [(set, idx)]
        pass2 rest setsNext ((cd.commitment, set) :: csm)

  pass3 : List (VerifierQuery F C) → List F → List (List Nat × Nat) →
      List (CommitmentReference F C × List Nat) → List (CD F C) →
      Except Fault (List (CD F C))
    | [], _, _, _, cms => .ok cms
    | q :: rest, pts, sets, csm, cms => do
      match pts.findIdx? (fun p => p == q.point) with
      | none => .error (Fault.panic "proofs/src/poly/kzg/utils.rs:96")
      | some pidx =>
        match csm.find? (fun e => eqC e.1 q.commitment) with
        | none => .error (Fault.panic "proofs/src/poly/kzg/utils.rs:103")
        | some (_, set) =>
          if set.isEmpty then
            .error (Fault.panic "proofs/src/poly/kzg/utils.rs:104")
          else
            match sets.find? (fun e => e.1 == set) with
            | none => .error (Fault.panic "proofs/src/poly/kzg/utils.rs:107")
            | some (set', sidx) =>
              match set'.findIdx? (fun i => i == pidx) with
              | none => .error (Fault.panic "proofs/src/poly/kzg/utils.rs:112")
              | some inSet =>
                  let cmsNext := cms.map fun cd =>
                    if eqC cd.commitment q.commitment then
                      { cd with setIndex := sidx,
                                evals := arraySetD cd.evals inSet q.eval }
                    else cd
                  pass3 rest pts sets csm cmsNext


/-- rust: proofs/src/poly/kzg/utils.rs:135-187 (compute_dummy_queries).
    Reached only under the fewer-point-sets feature (poly/kzg/mod.rs:334), so
    rule R8 makes it a branch of multi_prepare rather than always-on.

    The doc comment is a contract: group by key, take the union of every point
    set with more than one point, and return the missing (first index, point)
    pairs that make all such sets identical. Single-point sets are deliberately
    left alone - most selectors are opened at one point and padding them would
    grow the proof. Output order is insertion order, which is what keeps prover
    and verifier in sync; the port preserves it exactly.

    Grouping again uses PartialEq on the key, i.e. the same allocation-vs-value
    question as construct_intermediate_sets (R-7): the caller passes
    q.commitment.clone(), so this is CommitmentReference equality too.

    Panic sites: :158 panics outright on a duplicate (key, point) pair - the
    Rust does not return an error here, it aborts - and :166 asserts a group is
    non-empty (unreachable: groups are created with one element). -/
def computeDummyQueries {K P : Type} [BEq P] (eqK : K → K → Bool) (pairs : List (K × P)) :
    Except Fault (List (Nat × P)) := do
  let groups ← groupPass pairs [] 0
  let union ← unionPass groups []
  return groups.flatMap fun (idx, existing) =>
    (union.filter fun p => !existing.contains p) |>.map fun p => (idx, p)
where
  groupPass : List (K × P) → List (Nat × List P) → Nat →
      Except Fault (List (Nat × List P))
    | [], gs, _ => .ok gs
    | (key, point) :: rest, gs, i =>
      -- rust: groups.iter_mut().find(|(idx, _)| pairs[*idx].0 == *key): the
      -- comparison reads the key back out of the *original* slice at the
      -- group's first index, not a stored copy. Kept that way (rule R1).
      match gs.findIdx? fun g =>
            match listAt pairs g.1 with
            | some (k, _) => eqK k key
            | none => false with
      | some gi =>
        match listAt gs gi with
        | none => .error (Fault.panic "proofs/src/poly/kzg/utils.rs:156")
        | some (gidx, pts) =>
          if pts.contains point then
            .error (Fault.panic "proofs/src/poly/kzg/utils.rs:158")
          else
            groupPass rest (listReplaceAt gs gi (gidx, pts ++ [point])) (i + 1)
      | none => groupPass rest (gs ++ [(i, [point])]) (i + 1)

  unionPass : List (Nat × List P) → List P → Except Fault (List P)
    | [], acc => .ok acc
    | (_, pts) :: rest, acc =>
      if pts.isEmpty then
        .error (Fault.panic "proofs/src/poly/kzg/utils.rs:166")
      else if pts.length == 1 then
        unionPass rest acc
      else
        unionPass rest
          (pts.foldl (fun a p => if a.contains p then a else a ++ [p]) acc)

-- ## Known-answer checks
--
-- Hand-computed over Fr 17 with C := Nat, so the grouping relation is plain
-- value equality on Nats. The point of these is the *ordering* contract:
-- point indices by first occurrence, set indices by first occurrence, and
-- each set's points ascending.

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The KAT commitment type is `Nat`, and the natural reading of "commitment 5" is
    "the 5th allocation", so the slot is `.anon com`: slot equality then coincides
    with the value equality these KATs were written against, and their expected
    point-set layout is unchanged by D-P61. -/
def vq17 (point : Fr 17) (com : Nat) (eval : Fr 17) : VerifierQuery (Fr 17) Nat :=
  { point, commitmentLabel := .noLabel, commitment := .onePiece (.anon com) com, eval }

def eqNatRef : CommitmentReference (Fr 17) Nat → CommitmentReference (Fr 17) Nat → Bool
  | .onePiece s _, .onePiece t _ => s == t
  | .linear p1 s1 _, .linear p2 s2 _ => p1 == p2 && s1 == s2
  | _, _ => false

/-- THE OLD RELATION, kept as the falsifier below: value equality on one-piece
    commitments, which is what the port did before D-P61. -/
def eqNatRefOld : CommitmentReference (Fr 17) Nat → CommitmentReference (Fr 17) Nat → Bool
  | .onePiece _ x, .onePiece _ y => x == y
  | .linear p1 s1 _, .linear p2 s2 _ => p1 == p2 && s1 == s2
  | _, _ => false

/-- Three queries: commitment 5 opened at points 1 and 3, commitment 7 opened
    at point 1. Expected: points in first-occurrence order [1, 3]; set 0 is
    {0, 1} (commitment 5) and set 1 is {0} (commitment 7); evals laid out by
    position inside the set, so [2, 4] and [6]; point sets [[1, 3], [1]]. -/
def cisKats_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRef
      (#[vq17 1 5 2, vq17 3 5 4, vq17 1 7 6]) with
  | .error _ => false
  | .ok (cms, pointSets) =>
      match cms.toList with
      | [c0, c1] =>
          c0.pointIndices.toList == [0, 1] && c0.setIndex == 0 &&
          (c0.evals.map ZMod.val).toList == [2, 4] &&
          c1.pointIndices.toList == [0] && c1.setIndex == 1 &&
          (c1.evals.map ZMod.val).toList == [6] &&
          (pointSets.map fun ps => (ps.map ZMod.val).toList).toList ==
            [[1, 3], [1]]
      | _ => false

/-- The same commitment opened twice at the same point is the one error this
    function can produce (utils.rs:58). -/
def cisDupKats_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRef
      (#[vq17 1 5 2, vq17 1 5 3]) with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- Groups {5: [1,3], 7: [1]}; the union of the non-singleton sets is [1, 3],
    so the only dummy is (first index of group 7, 3) = (2, 3). -/
def dummyKats_ok : Bool :=
  match computeDummyQueries (K := Nat) (P := Nat) (fun a b => a == b)
      [(5, 1), (5, 3), (7, 1)] with
  | .ok ds => ds == [(2, 3)]
  | .error _ => false

/-- A repeated (key, point) pair is a hard panic in the Rust (:158). -/
def dummyPanicKats_ok : Bool :=
  match computeDummyQueries (K := Nat) (P := Nat) (fun a b => a == b)
      [(5, 1), (5, 1)] with
  | .error (Fault.panic "proofs/src/poly/kzg/utils.rs:158") => true
  | _ => false
/-- **REF.1 / D-P61 - THE WITNESS.** The shape of fixtures/conformance/poseidon: the
    committed instance is the identity (instances.json c000..00), fixed columns
    8, 10, 11, 12 and 16 are the identity (vk.json), all six are opened at x
    (rotation 0) and none is a simple selector. Point 5 stands for x. Six DISTINCT
    allocations that happen to hold the SAME point: the tree's own
    CommitmentReference.beq must keep them apart, and does - six entries, one
    point set, each eval in its own entry. -/
def fixtureShape_groups_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) CommitmentReference.beq
      (#[ VerifierQuery.new 5 (.instance_ 0) (.instance_ 0 0) 0 1,
          VerifierQuery.new 5 (.fixed 8)  (.fixed 8)  0 2,
          VerifierQuery.new 5 (.fixed 10) (.fixed 10) 0 3,
          VerifierQuery.new 5 (.fixed 11) (.fixed 11) 0 4,
          VerifierQuery.new 5 (.fixed 12) (.fixed 12) 0 5,
          VerifierQuery.new 5 (.fixed 16) (.fixed 16) 0 6 ]) with
  | .ok (cms, pointSets) =>
      cms.size == 6 && pointSets.size == 1 &&
        (cms.toList.map fun cd => (cd.evals.map ZMod.val).toList)
          == [[1], [2], [3], [4], [5], [6]] &&
        cms.toList.all fun cd => cd.setIndex == 0 && cd.pointIndices.toList == [0]
  | .error _ => false

/-- **REF.1 / D-P61 - THE FALSIFIER.** The SAME input under the pre-D-P61 relation -
    value equality on one-piece commitments, with the value relation otherwise kept
    intact - returns Error.opening. This is the failure that stopped the reference
    gate: the real key's six identity commitments at x merged into one entry and the
    second opening of "the same polynomial at the same point" was rejected. If this
    KAT ever reads false, the old relation has been reinstated somewhere. -/
def fixtureShape_old_rejects_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) eqNatRefOld
      (#[ VerifierQuery.new 5 (.instance_ 0) (.instance_ 0 0) 0 1,
          VerifierQuery.new 5 (.fixed 8)  (.fixed 8)  0 2,
          VerifierQuery.new 5 (.fixed 10) (.fixed 10) 0 3,
          VerifierQuery.new 5 (.fixed 11) (.fixed 11) 0 4,
          VerifierQuery.new 5 (.fixed 12) (.fixed 12) 0 5,
          VerifierQuery.new 5 (.fixed 16) (.fixed 16) 0 6 ]) with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- A GENUINE duplicate - the SAME allocation at the SAME point - is still
    Error::DuplicatedQuery, collapsed to Error.opening (utils.rs:58,
    plonk/verifier.rs:651). The repair does not loosen the check the check was for. -/
def duplicate_still_rejects_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) CommitmentReference.beq
      (#[ VerifierQuery.new 5 (.fixed 8) (.fixed 8) 0 2,
          VerifierQuery.new 5 (.fixed 8) (.fixed 8) 0 3 ]) with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- ... even when the two VALUES differ: the reference never looks at them, so a
    repeated slot is rejected whatever the pointee claims. -/
def duplicate_slot_distinct_values_rejects_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) CommitmentReference.beq
      (#[ VerifierQuery.new 5 (.fixed 8) (.fixed 8) 7 2,
          VerifierQuery.new 5 (.fixed 8) (.fixed 8) 9 3 ]) with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- One allocation opened at TWO points is ONE entry with two point indices (the
    advice column queried at x and at omega x), whatever the labels say - and a
    different allocation at the same point is a different entry in the same set. -/
def oneSlotTwoPoints_ok : Bool :=
  match constructIntermediateSets (F := Fr 17) (C := Nat) CommitmentReference.beq
      (#[ VerifierQuery.new 5 .noLabel (.permProduct 0 0) 11 2,
          VerifierQuery.new 6 .noLabel (.permProduct 0 0) 11 3,
          VerifierQuery.new 5 .noLabel (.permProduct 0 1) 11 4 ]) with
  | .ok (cms, pointSets) =>
      cms.size == 2 && pointSets.size == 2 &&
        (cms.toList.map fun cd => cd.pointIndices.toList) == [[0, 1], [0]] &&
        (cms.toList.map fun cd => (cd.evals.map ZMod.val).toList) == [[2, 3], [4]]
  | .error _ => false

end Kats

#eval Midfall.Halo2.cisKats_ok        -- expect true
#eval Midfall.Halo2.cisDupKats_ok    -- expect true
#eval Midfall.Halo2.dummyKats_ok     -- expect true
#eval Midfall.Halo2.dummyPanicKats_ok -- expect true
#eval Midfall.Halo2.fixtureShape_groups_ok -- expect true
#eval Midfall.Halo2.fixtureShape_old_rejects_ok -- expect true
#eval Midfall.Halo2.duplicate_still_rejects_ok -- expect true
#eval Midfall.Halo2.duplicate_slot_distinct_values_rejects_ok -- expect true
#eval Midfall.Halo2.oneSlotTwoPoints_ok -- expect true

end Midfall.Halo2
