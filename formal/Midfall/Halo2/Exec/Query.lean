-- |
-- Midfall.Halo2.Exec.Query
--
-- The query vocabulary of the polynomial commitment scheme
-- (rust: proofs/src/poly/query.rs): CommitmentLabel, CommitmentReference and
-- VerifierQuery. This is the shape multi_prepare consumes, so it sits below
-- Exec/Kzg rather than inside it: MSMKZG stores a CommitmentLabel per term and
-- DualMSM.split returns them.
--
-- Not ported: ProverQuery and PolynomialPointer (poly/query.rs:31-70) - prover
-- code, out of scope by plan Section 1.

import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

/-- rust: proofs/src/poly/query.rs:12-25 (enum CommitmentLabel). Variant order
    is the source order (rule R1). The Rust derives Clone, Debug,
    PartialEq, Eq, Hash; the port needs only equality, which an inductive has.
    Instance is spelled instance_ because instance is a Lean keyword. -/
inductive CommitmentLabel where
  /-- Advice column commitment (column index). -/
  | advice (i : Nat)
  /-- Instance column commitment (column index). -/
  | instance_ (i : Nat)
  /-- Fixed column commitment (column index). -/
  | fixed (i : Nat)
  /-- Permutation verifying-key commitment (index). -/
  | permutation (i : Nat)
  /-- User-defined label. -/
  | custom (s : String)
  /-- No label. -/
  | noLabel
  deriving BEq

/-- rust: proofs/src/poly/query.rs:27-38 (impl Display for CommitmentLabel).
    The strings are what the verifier trace prints, so they are part of the
    conformance surface, not cosmetics. -/
def CommitmentLabel.text : CommitmentLabel → String
  | .advice i => "advice_" ++ toString i
  | .instance_ i => "instance_" ++ toString i
  | .fixed i => "fixed_" ++ toString i
  | .permutation i => "vk_perm_" ++ toString i
  | .custom s => s
  | .noLabel => "-"


/-- **THE ALLOCATION** a `&CS::Commitment` points into (D-P61, card REF.1).
    One constructor per place the reference verifier takes such a reference when it
    builds a `VerifierQuery::OnePiece` - the only producers of a one-piece
    commitment:

      advice        plonk/verifier.rs:605        &advice_commitments[column.index()]
      instance_     plonk/verifier.rs:616        &committed_instances[column.index()]
      permProduct   permutation/verifier.rs:161, :167, :177
                                                 &self.coms.permutation_product_commitments[i]
      lookupM       logup/verifier.rs:183        &self.committed.multiplicities
      lookupHelper  logup/verifier.rs:192        an element of self.committed.helper_polys
      lookupAcc     logup/verifier.rs:199, :205  &self.committed.accumulator
      trash         trash/verifier.rs:70         &self.committed.trash_commitment
      fixed         plonk/verifier.rs:640        &vk.fixed_commitments[column.index()]
      sigma         permutation/verifier.rs:192  an element of vkey.commitments
      anon          a fresh allocation the caller numbers itself: the KATs, and the
                    shape model of Spec/Degrees.lean, whose linearization term is one
                    shape and not a bag of its terms.

    WHY THIS EXISTS. `std::ptr::eq` on two such references is true exactly when the
    two slots are equal: each slot names one element of one live `Vec` (or one struct
    field) of a non-zero-sized type, distinct elements have distinct addresses, and
    every vector is alive for the whole of `multi_prepare` because the query vector
    borrows them, so no address is reused. Comparing one-piece commitments by VALUE
    instead (what the port did before D-P61) merges allocations that happen to hold
    the same point: on the poseidon fixture the six identity fixed-column
    commitments opened at x collapse into one entry, and `constructIntermediateSets`
    reports the second opening of "the same polynomial at the same point" as
    `Error::DuplicatedQuery`, which the caller renders as `Error.opening`
    (utils.rs:55-58, plonk/verifier.rs:651). The reference ACCEPTS that proof.
    REVIEW-V3 RV-03/RV-04; the witness and the falsifier are the KATs at the foot of
    Exec/Kzg/Utils.lean. -/
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

/-- rust: proofs/src/poly/query.rs:72-101
    (enum CommitmentReference). The Rust holds `&CS::Commitment` references;
    Lean has no lifetimes, so the port owns the commitments (rule R6 takes
    Vec -> Array, and a `&T` becomes a `T`). That is only safe because nothing
    in the verifier mutates a commitment through the reference.

    D-P61 (card REF.1) adds the ADDRESS the reference carried: a Rust `&T` is an
    address AND a pointee, and `PartialEq` (query.rs:117-133) reads the address for
    `OnePiece`. See `CommitSlot` above for why that is observable. -/
inductive CommitmentReference (F C : Type) where
  /-- A single commitment, together with the allocation it was taken from. -/
  | onePiece (slot : CommitSlot) (com : C)
  /-- A linear combination: points, scalars, and a label per term. -/
  | linear (points : Array C) (scalars : Array F) (labels : Array CommitmentLabel)

/-- rust: proofs/src/poly/query.rs:117-133 (impl PartialEq for
    CommitmentReference). READ THIS BEFORE USING IT AS A DEDUPLICATION KEY.
    The Rust compares OnePiece variants with std::ptr::eq - *address*, not
    value - and for Linear it compares points and scalars but explicitly
    ignores the labels. D-P61 (card REF.1) DECIDED the question this comment used
    to leave open: Rust relies on IDENTITY, so the OnePiece arm compares the
    allocation slot and never looks at the value. Two distinct allocations holding
    the same point compare unequal here, exactly as in Rust. The label-blindness is
    ported exactly: two Linears with different labels are equal. -/
def CommitmentReference.beq {F C : Type} [BEq F] [BEq C]
    (a b : CommitmentReference F C) : Bool :=
  match a, b with
  | .onePiece s _, .onePiece t _ => s == t
  | .linear p1 s1 _, .linear p2 s2 _ => p1 == p2 && s1 == s2
  | _, _ => false

/-- rust: proofs/src/poly/query.rs:135-164 (CommitmentReference::as_terms).
    OnePiece gives [(1, com)]; Linear zips points with scalars. Panic site:
    `assert_eq!(points.len(), scalars.len())` at :151. The labels are dropped
    by the Rust return type, which is why the Linear arm ignores them. -/
def CommitmentReference.asTerms {F C : Type} [One F]
    (cr : CommitmentReference F C) : Except Fault (Array (F × C)) :=
  match cr with
  | .onePiece _ com => .ok #[(1, com)]
  | .linear points scalars _ =>
      if points.size != scalars.size then
        .error (Fault.panic "proofs/src/poly/query.rs:151")
      else
        .ok ((List.zip points.toList scalars.toList).map (fun (p, s) => (s, p))).toArray

/-- rust: proofs/src/poly/query.rs:166-177 (struct VerifierQuery). Field order
    is the Rust order (rule R1). `commitment_label` is a per-query label,
    distinct from the per-term labels inside a Linear commitment. -/
structure VerifierQuery (F C : Type) where
  /-- Point at which the polynomial is queried. -/
  point : F
  /-- Optional label identifying the commitment in this query. -/
  commitmentLabel : CommitmentLabel
  /-- Commitment to the polynomial. -/
  commitment : CommitmentReference F C
  /-- Evaluation of the polynomial at the query point. -/
  eval : F

/-- rust: proofs/src/poly/query.rs:179-195 (VerifierQuery::new): a one-piece
    commitment. D-P61 (card REF.1) adds `slot`: the caller names the ALLOCATION the
    Rust reference points into, next to the value it points at. -/
def VerifierQuery.new {F C : Type} (point : F) (commitmentLabel : CommitmentLabel)
    (slot : CommitSlot) (commitment : C) (eval : F) : VerifierQuery F C :=
  { point, commitmentLabel, commitment := .onePiece slot commitment, eval }

/-- rust: proofs/src/poly/query.rs:197-233 (VerifierQuery::new_linear).
    Two panic sites, :217 and :222, both length agreement between points,
    scalars and base_labels. The Rust doc comment spells the panic out. -/
def VerifierQuery.newLinear {F C : Type} (point : F) (commitmentLabel : CommitmentLabel)
    (points : Array C) (scalars : Array F) (baseLabels : Array CommitmentLabel)
    (eval : F) : Except Fault (VerifierQuery F C) := do
  unless points.size == scalars.size do
    throw (Fault.panic "proofs/src/poly/query.rs:217")
  unless points.size == baseLabels.size do
    throw (Fault.panic "proofs/src/poly/query.rs:222")
  return { point, commitmentLabel,
            commitment := .linear points scalars baseLabels, eval }

/-- rust: proofs/src/poly/query.rs:235-251 (impl Query<F> for VerifierQuery).
    The four accessors are the trait methods; under rule R9 the Query trait
    itself needs no record because every verifier call site already knows it
    has a VerifierQuery (the only other instance, ProverQuery, is prover code
    and out of scope by plan Section 1). -/
def VerifierQuery.getPoint {F C : Type} (q : VerifierQuery F C) : F := q.point
def VerifierQuery.getEval {F C : Type} (q : VerifierQuery F C) : F := q.eval
def VerifierQuery.getCommitment {F C : Type} (q : VerifierQuery F C)
    : CommitmentReference F C := q.commitment
def VerifierQuery.getCommitmentLabel {F C : Type} (q : VerifierQuery F C)
    : CommitmentLabel := q.commitmentLabel

end Midfall.Halo2
