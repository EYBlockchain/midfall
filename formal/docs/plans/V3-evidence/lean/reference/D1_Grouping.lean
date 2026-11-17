/-
  D1 - THE GROUPING REPAIR (R-7 / E-1 / A-1), as a PATCHED COPY of
    formal/Midfall/Halo2/Exec/Query.lean                 (the types)
    formal/Midfall/Halo2/Exec/Kzg/Utils.lean:34-195      (constructIntermediateSets, VERBATIM)
    formal/Midfall/Halo2/Exec/Kzg/MultiOpen.lean:42-48   (kzgCommitBeq)
  It imports ONLY what those files import below Query (Error, Curve), so the declarations
  live in the tree's own namespace `Midfall.Halo2` without clashing with the built olean.
  Everything marked  -- PATCH  is new or changed; everything else is the tree's text.
-/
import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Error

set_option autoImplicit false

namespace Midfall.Halo2

/-- rust: proofs/src/poly/query.rs:12-25 (enum CommitmentLabel). UNCHANGED. -/
inductive CommitmentLabel where
  | advice (i : Nat)
  | instance_ (i : Nat)
  | fixed (i : Nat)
  | permutation (i : Nat)
  | custom (s : String)
  | noLabel
  deriving BEq

-- PATCH (new). THE ALLOCATION a `&'com CS::Commitment` points into.
/-- One constructor per place the reference verifier takes a `&CS::Commitment` when it builds a
    `VerifierQuery` (the only producers of `CommitmentReference::OnePiece`):

      advice      plonk/verifier.rs:605        &advice_commitments[column.index()]      (per proof)
      instance_   plonk/verifier.rs:616        &committed_instances[column.index()]     (per proof)
      permProduct permutation/verifier.rs:161,167,177
                                               &self.coms.permutation_product_commitments[i]
      lookupM     logup/verifier.rs:183        &self.committed.multiplicities           (per lookup)
      lookupHelper logup/verifier.rs:192       an element of self.committed.helper_polys
      lookupAcc   logup/verifier.rs:199,205    &self.committed.accumulator
      trash       trash/verifier.rs:70         &self.committed.trash_commitment         (per trashcan)
      fixed       plonk/verifier.rs:640        &vk.fixed_commitments[column.index()]
      sigma       permutation/verifier.rs:192  an element of vkey.commitments
      anon        test and KAT queries only: a fresh allocation, numbered by the caller

    `std::ptr::eq` on two such references is true exactly when the two slots are equal: each slot
    names one element of one live `Vec` (or one struct field) of a non-zero-sized type, distinct
    elements have distinct addresses, and every vector is alive for the whole of `multi_prepare`
    (the query vector borrows them), so no address is reused. -/
inductive CommitSlot where
  | advice (proof col : Nat)
  | instance_ (proof col : Nat)
  | permProduct (proof set : Nat)
  | lookupM (proof lookup : Nat)
  | lookupHelper (proof lookup j : Nat)
  | lookupAcc (proof lookup : Nat)
  | trash (proof idx : Nat)
  | fixed (col : Nat)
  | sigma (i : Nat)
  | anon (n : Nat)
  deriving BEq, DecidableEq, Repr

/-- rust: proofs/src/poly/query.rs:72-101 (enum CommitmentReference).
    PATCH: `onePiece` carries the allocation next to the value: a Rust `&T` is an address AND a
    pointee, and `PartialEq` (query.rs:117-133) reads the ADDRESS for `OnePiece`. -/
inductive CommitmentReference (F C : Type) where
  | onePiece (slot : CommitSlot) (com : C)                                       -- PATCH
  | linear (points : Array C) (scalars : Array F) (labels : Array CommitmentLabel)

/-- rust: proofs/src/poly/query.rs:117-133 (impl PartialEq for CommitmentReference).
    PATCH: `OnePiece` is `std::ptr::eq`, i.e. slot equality; the VALUE is not read. `Linear` is
    unchanged: `Vec<&Commitment> == Vec<&Commitment>` goes through `PartialEq for &T`, which
    dereferences, so points compare by value, scalars by value, labels are ignored. -/
def CommitmentReference.beq {F C : Type} [BEq F] [BEq C]
    (a b : CommitmentReference F C) : Bool :=
  match a, b with
  | .onePiece s _, .onePiece t _ => s == t                                       -- PATCH
  | .linear p1 s1 _, .linear p2 s2 _ => p1 == p2 && s1 == s2
  | _, _ => false

/-- rust: proofs/src/poly/query.rs:135-164 (as_terms). PATCH: the extra binder only. -/
def CommitmentReference.asTerms {F C : Type} [One F]
    (cr : CommitmentReference F C) : Except Fault (Array (F × C)) :=
  match cr with
  | .onePiece _ com => .ok #[(1, com)]                                            -- PATCH
  | .linear points scalars _ =>
      if points.size != scalars.size then
        .error (Fault.panic "proofs/src/poly/query.rs:151")
      else
        .ok ((List.zip points.toList scalars.toList).map (fun (p, s) => (s, p))).toArray

structure VerifierQuery (F C : Type) where
  point : F
  commitmentLabel : CommitmentLabel
  commitment : CommitmentReference F C
  eval : F

/-- rust: proofs/src/poly/query.rs:179-195 (VerifierQuery::new). PATCH: takes the slot. -/
def VerifierQuery.new {F C : Type} (point : F) (commitmentLabel : CommitmentLabel)
    (slot : CommitSlot) (commitment : C) (eval : F) : VerifierQuery F C :=           -- PATCH
  { point, commitmentLabel, commitment := .onePiece slot commitment, eval }

/-! ### Exec/Kzg/Utils.lean:34-195, VERBATIM (no patch: the relation is already a parameter) -/

structure CommitmentData (eval com : Type) where
  commitmentLabel : CommitmentLabel
  commitment : com
  setIndex : Nat
  pointIndices : Array Nat
  evals : Array eval

def CommitmentData.new {eval com : Type} (commitment : com)
    (commitmentLabel : CommitmentLabel) : CommitmentData eval com :=
  { commitmentLabel, commitment, setIndex := 0, pointIndices := #[], evals := #[] }

abbrev IntermediateSets (F C : Type) : Type :=
  Array (CommitmentData F (CommitmentReference F C)) × Array (Array F)

def listReplaceAt {α : Type} (xs : List α) (i : Nat) (v : α) : List α :=
  go xs i v
where
  go : List α → Nat → α → List α
    | [], _, _ => []
    | _ :: rest, 0, v => v :: rest
    | x :: rest, i + 1, v => x :: go rest i v

def listAt {α : Type} (xs : List α) (i : Nat) : Option α :=
  (xs.drop i).head?

def natSort : List Nat -> List Nat
  | [] => []
  | x :: xs => insert x (natSort xs)
where
  insert : Nat -> List Nat -> List Nat
    | x, [] => [x]
    | x, y :: ys => if x <= y then x :: y :: ys else y :: insert x ys

def arraySetD {α : Type} (a : Array α) (i : Nat) (v : α) : Array α :=
  if h : i < a.size then
    a.set i v
  else
    a

def arrayReplicate {α : Type} (n : Nat) (v : α) : Array α :=
  (List.replicate n v).toArray

abbrev CD (F C : Type) : Type := CommitmentData F (CommitmentReference F C)

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

/-! ### Exec/Kzg/MultiOpen.lean:38-48, PATCHED -/

def decideBool {α : Type} {a b : α} (d : Decidable (a = b)) : Bool :=
  match d with | .isTrue _ => true | .isFalse _ => false

section KzgBeq
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- rust: proofs/src/poly/query.rs:117-133. The commitment comparison `multi_prepare` groups by.
    PATCH (R-7 CLOSED): the `OnePiece` arm is `std::ptr::eq`, modelled as equality of the
    allocation slot; the group VALUE is not consulted, so two distinct allocations holding the
    same point stay apart exactly as in the reference. The `Linear` arm is unchanged (value
    equality on points and scalars, labels ignored, lengths compared explicitly because
    `List.zip` truncates). -/
def kzgCommitBeq : CommitmentReference (Fr p) G₁ → CommitmentReference (Fr p) G₁ → Bool
  | .onePiece s _, .onePiece t _ => s == t                                       -- PATCH
  | .linear p1 s1 _, .linear p2 s2 _ =>
      p1.size == p2.size && s1.size == s2.size &&
      (List.zip p1.toList p2.toList).all (fun (x, y) => decideBool (P.decEqG₁ x y)) &&
      (List.zip s1.toList s2.toList).all (fun (x, y) => x == y)
  | _, _ => false

-- the call site (MultiOpen.lean:257-259) is textually UNCHANGED:
--   constructIntermediateSets (F := Fr p) (C := G₁) (kzgCommitBeq (G₂ := G₂) (Gₜ := Gₜ)) queries
example (queries : Array (VerifierQuery (Fr p) G₁)) : Except Fault (IntermediateSets (Fr p) G₁) :=
  constructIntermediateSets (F := Fr p) (C := G₁) (kzgCommitBeq (G₂ := G₂) (Gₜ := Gₜ)) queries
end KzgBeq

/-! ### KATs (the falsifier and the witness) -/
section Kats
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- C := Nat stands for a group element; 0 is "the identity". -/
def refBeq : CommitmentReference (Fr 17) Nat → CommitmentReference (Fr 17) Nat → Bool :=
  CommitmentReference.beq

/-- THE OLD RELATION, kept for the falsifier: value equality on one-piece commitments. -/
def refBeqOld : CommitmentReference (Fr 17) Nat → CommitmentReference (Fr 17) Nat → Bool
  | .onePiece _ x, .onePiece _ y => x == y
  | .linear p1 s1 _, .linear p2 s2 _ => p1 == p2 && s1 == s2
  | _, _ => false

/-- The shape of formal/fixtures/conformance/poseidon: the committed instance is the identity
    (instances.json "c000..00"), fixed columns 8, 10, 11, 12, 16 are the identity (vk.json), all six
    are opened at x (rotation 0) and none is a simple selector. Point 5 stands for x. -/
def fixtureShape : Array (VerifierQuery (Fr 17) Nat) :=
  #[ VerifierQuery.new 5 (.instance_ 0) (.instance_ 0 0) 0 1,
     VerifierQuery.new 5 (.fixed 8)  (.fixed 8)  0 2,
     VerifierQuery.new 5 (.fixed 10) (.fixed 10) 0 3,
     VerifierQuery.new 5 (.fixed 11) (.fixed 11) 0 4,
     VerifierQuery.new 5 (.fixed 12) (.fixed 12) 0 5,
     VerifierQuery.new 5 (.fixed 16) (.fixed 16) 0 6 ]

/-- WITNESS: six entries, one point set, every eval in its own entry. -/
def fixtureShape_groups_ok : Bool :=
  match constructIntermediateSets refBeq fixtureShape with
  | .ok (cms, pointSets) =>
      cms.size == 6 && pointSets.size == 1 &&
      (cms.toList.map fun cd => (cd.evals.map ZMod.val).toList) == [[1], [2], [3], [4], [5], [6]] &&
      cms.toList.all (fun cd => cd.setIndex == 0 && cd.pointIndices.toList == [0])
  | .error _ => false

/-- FALSIFIER: the relation in the tree today returns Error.opening on the same input. -/
def fixtureShape_old_rejects_ok : Bool :=
  match constructIntermediateSets refBeqOld fixtureShape with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- A GENUINE duplicate - the SAME allocation at the SAME point - is still Error::DuplicatedQuery,
    collapsed to Error.opening (utils.rs:58, plonk/verifier.rs:651). -/
def duplicate_still_rejects_ok : Bool :=
  match constructIntermediateSets refBeq
      #[ VerifierQuery.new 5 (.fixed 8) (.fixed 8) 0 2,
         VerifierQuery.new 5 (.fixed 8) (.fixed 8) 0 3 ] with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- ... even when the two VALUES differ: the reference never looks at them. -/
def duplicate_slot_distinct_values_rejects_ok : Bool :=
  match constructIntermediateSets refBeq
      #[ VerifierQuery.new 5 (.fixed 8) (.fixed 8) 7 2,
         VerifierQuery.new 5 (.fixed 8) (.fixed 8) 9 3 ] with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- One allocation at two points is ONE entry with two point indices (advice column queried at x
    and at omega x), whatever the labels say. -/
def oneSlotTwoPoints_ok : Bool :=
  match constructIntermediateSets refBeq
      #[ VerifierQuery.new 5 .noLabel (.permProduct 0 0) 11 2,
         VerifierQuery.new 6 .noLabel (.permProduct 0 0) 11 3,
         VerifierQuery.new 5 .noLabel (.permProduct 0 1) 11 4 ] with
  | .ok (cms, pointSets) =>
      cms.size == 2 && pointSets.size == 2 &&
      (cms.toList.map fun cd => cd.pointIndices.toList) == [[0, 1], [0]] &&
      (cms.toList.map fun cd => (cd.evals.map ZMod.val).toList) == [[2, 3], [4]]
  | .error _ => false

/-- The existing Utils KAT (cisKats_ok), re-run with slots 5 and 7 for commitments 5 and 7. -/
def cisKats_ok : Bool :=
  match constructIntermediateSets refBeq
      #[ VerifierQuery.new 1 .noLabel (.anon 5) 5 2, VerifierQuery.new 3 .noLabel (.anon 5) 5 4,
         VerifierQuery.new 1 .noLabel (.anon 7) 7 6 ] with
  | .error _ => false
  | .ok (cms, pointSets) =>
      match cms.toList with
      | [c0, c1] =>
          c0.pointIndices.toList == [0, 1] && c0.setIndex == 0 &&
          (c0.evals.map ZMod.val).toList == [2, 4] &&
          c1.pointIndices.toList == [0] && c1.setIndex == 1 &&
          (c1.evals.map ZMod.val).toList == [6] &&
          (pointSets.map fun ps => (ps.map ZMod.val).toList).toList == [[1, 3], [1]]
      | _ => false

end Kats

#eval Midfall.Halo2.fixtureShape_groups_ok                     -- expect true
#eval Midfall.Halo2.fixtureShape_old_rejects_ok                -- expect true
#eval Midfall.Halo2.duplicate_still_rejects_ok                 -- expect true
#eval Midfall.Halo2.duplicate_slot_distinct_values_rejects_ok  -- expect true
#eval Midfall.Halo2.oneSlotTwoPoints_ok                        -- expect true
#eval Midfall.Halo2.cisKats_ok                                 -- expect true

end Midfall.Halo2
