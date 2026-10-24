-- |
-- Midfall.Halo2.Exec.Linearization
--
-- The linearization polynomial's commitment query (rust:
-- proofs/src/plonk/linearization/verifier.rs, one 59-line function). This is the
-- last verifier leaf before Exec/Verifier: it turns the partially evaluated
-- identities into the VerifierQuery that the multi-open argument checks opens
-- to expected_eval at x.
--
-- The one thing that is easy to get silently wrong is the BTreeMap. Rust groups
-- the identity multiples in a BTreeMap<Option<usize>, F>, and then iterates it
-- - so the MSM's term order is the map's KEY ORDER, not insertion order:
-- Option<usize> orders None before Some, and Some ascending. That matters
-- because the resulting point/scalar/label vectors are what construct_intermediate
--_sets later groups by commitment, and because the Rust derives the whole
-- linearization MSM from it. Rule R6 says port the derived Ord exactly, so the
-- grouping below keeps a list sorted by that same order and adds into it.
--
-- Also easy to miss: the y powers are accumulated while walking expressions in
-- REVERSE (verifier.rs:75), so the LAST identity gets y^0 and the first gets
-- y^m. Reversing that is invisible on a one-identity circuit and wrong in general.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.VerifyingKey

namespace Midfall.Halo2

/-- The derived Ord on Option<usize> that BTreeMap uses: None < Some _ and Some
    ascending. Written out rather than trusted (rule R6). -/
def optionNatLt : Option Nat → Option Nat → Bool
  | none, some _ => true
  | some a, some b => a < b
  | _, _ => false

/-- Insert-or-add into the sorted association list, i.e
    `*grouped_points.entry(col).or_insert(F::ZERO) += y_pow * eval`
    (verifier.rs:76). -/
def groupedAdd {F : Type} [Ring F] (acc : List (Option Nat × F))
    (key : Option Nat) (v : F) : List (Option Nat × F) :=
  go acc
where
  go : List (Option Nat × F) → List (Option Nat × F)
    | [] => [(key, v)]
    | (k, e) :: rest =>
      if k == key then (k, e + v) :: rest
      else if optionNatLt key k then (key, v) :: (k, e) :: rest
      else (k, e) :: go rest

/-- rust: linearization/verifier.rs:45-104 (compute_linearization_commitment).

    Panic sites kept as Fault.panic:
    * verifier.rs:84 `vk.fixed_commitments[col_idx]` - an identity naming a
      simple-selector column beyond the VK's fixed commitments. The Rust indexes
      directly; the port checks, because a malformed-but-parseable VK can reach
      it (the same class as R-14).
    * the two length asserts inside VerifierQuery.newLinear (query.rs:217, :222).
      Points, scalars and labels are built in lockstep here so they cannot
      disagree, but the check is kept rather than dropped so a future edit that
      desynchronises them fails loudly.

    The Rust takes &VerifyingKey and reads vk.cs.num_simple_selectors() (only as
      a capacity hint) and vk.fixed_commitments; the port takes the whole vk so
      the reads that matter are visible in the signature. -/
def computeLinearizationCommitment {F G₁ : Type} [Field F] [BEq F]
    (expressions : Array (Option Nat × F)) (vk : VerifyingKey F G₁) (x : F)
    (y : F) (xn : F) (splittingFactor : F)
    (quotientLimbCommitments : Array G₁) : Except Fault (VerifierQuery F G₁) := do
  -- verifier.rs:84 reached through a bad col_idx (checked up front so the
  -- error is reported at the Rust site rather than as a Lean index failure).
  if expressions.toList.any (fun e =>
       match e.1 with | some ci => ci ≥ vk.fixedCommitments.size | none => false) then
    throw (Fault.panic "proofs/src/plonk/linearization/verifier.rs:84")
  -- verifier.rs:63-70: the quotient limbs first, each scaled by
  -- (1 - xn) * splitting_factor^i. splitting_pow starts at ONE - xn, so the
  -- FIRST limb already carries the vanishing factor.
  let limbStep : F := 1 - xn
  let limbPairs :=
    (List.range quotientLimbCommitments.size).foldl
      (init := (([] : List F), limbStep))
      (fun (acc : List F × F) _ => ((acc.1 ++ [acc.2]), acc.2 * splittingFactor))
  let limbScalars := limbPairs.1
  -- verifier.rs:73-78: group by selector column, walking expressions in
  -- REVERSE so the last identity gets y^0 and the first gets y^m.
  let groupedPairs :=
    expressions.toList.reverse.foldl (init := (([] : List (Option Nat × F)), (1 : F)))
      (fun st e =>
        ((groupedAdd st.1 e.1 (st.2 * e.2)), st.2 * y))
  let grouped := groupedPairs.1;
  -- verifier.rs:80-94: emit in BTreeMap key order. The None bucket - fully
  -- evaluated identities - folds into the expected evaluation instead of a
  -- point, and note the sign: expected_eval -= eval.
  let step (st : List G₁ × List F × List CommitmentLabel × F)
      (entry : Option Nat × F) : Except Fault (List G₁ × List F × List CommitmentLabel × F) := do
    match entry with
    | (some colIdx, eval) =>
        match vk.fixedCommitments[colIdx]? with
        | none => .error (Fault.panic "proofs/src/plonk/linearization/verifier.rs:84")
        | some com =>
          .ok (st.1 ++ [com], st.2.1 ++ [eval], st.2.2.1 ++ [CommitmentLabel.fixed colIdx],
               st.2.2.2)
    | (none, eval) => .ok (st.1, st.2.1, st.2.2.1, st.2.2.2 - eval)
  let (pts, scals, labs, expectedEval) ←
    grouped.foldlM
      (init := (quotientLimbCommitments.toList, limbScalars,
                 List.replicate quotientLimbCommitments.size CommitmentLabel.noLabel,
                 (0 : F)))
      step
  VerifierQuery.newLinear x (CommitmentLabel.custom "linearization_poly")
    pts.toArray scals.toArray labs.toArray expectedEval

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

-- Hand-computed over Fr 17. expressions = [(Some 0, 3), (None, 5)], y = 2,
-- xn = 4, splitting_factor = 7, one quotient limb, two fixed commitments.
--  limbStep = 1 - 4 = -3 = 14, so limb scalars = [14] and labels = [NoLabel].
--  reversed walk: (None,5) at y^0 -> bucket None = 5; (Some 0,3) at y^1 = 2 ->
--  bucket Some 0 = 2*3 = 6. Key order puts None first, so expected_eval =
--  0 - 5 = 12 and the only point appended is fixedCommitments[0] with scalar 6.
--  Result: points [limb0, com0], scalars [14, 6], labels [NoLabel, Fixed 0],
--  expected 12, commitment label Custom "linearization_poly", point x.
def linearizationKats_ok : Bool :=
  match EvaluationDomain.new (F := Fr 17) fc17 3 2 with
  | .error _ => false
  | .ok dom =>
      let vk : VerifyingKey (Fr 17) Nat :=
        { domain := dom, fixedCommitments := #[9, 10], permutation := ⟨#[]⟩,
          cs := ConstraintSystem.default (F := Fr 17), csDegree := 3,
          transcriptRepr := 7 };
      match computeLinearizationCommitment (F := Fr 17) (G₁ := Nat)
          (#[((some 0 : Option Nat), 3), ((none : Option Nat), 5)]) vk 1 2 4 7 #[3] with
      | .error _ => false
      | .ok q =>
          q.point == 1 && q.eval == 12 &&
          q.commitmentLabel == CommitmentLabel.custom "linearization_poly" &&
          match q.commitment with
          | .linear ps ss ls =>
              ps.toList == [3, 9] && (ss.map ZMod.val).toList == [14, 6] &&
              ls.toList == [CommitmentLabel.noLabel, CommitmentLabel.fixed 0]
          | .onePiece _ => false

-- an identity naming a column the VK does not have is the verifier.rs:84 panic.
def linearizationPanicKats_ok : Bool :=
  match EvaluationDomain.new (F := Fr 17) fc17 3 2 with
  | .error _ => false
  | .ok dom =>
      let vk : VerifyingKey (Fr 17) Nat :=
        { domain := dom, fixedCommitments := #[9], permutation := ⟨#[]⟩,
          cs := ConstraintSystem.default (F := Fr 17), csDegree := 3,
          transcriptRepr := 7 };
      match computeLinearizationCommitment (F := Fr 17) (G₁ := Nat)
          (#[((some 4 : Option Nat), (1 : Fr 17))]) vk 1 2 4 7 #[] with
      | .error (Fault.panic "proofs/src/plonk/linearization/verifier.rs:84") => true
      | _ => false

end Kats

#eval Midfall.Halo2.linearizationKats_ok        -- expect true
#eval Midfall.Halo2.linearizationPanicKats_ok  -- expect true

end Midfall.Halo2
