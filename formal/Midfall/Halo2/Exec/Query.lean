-- |
-- Midfall.Halo2.Exec.Query
--
-- Commitment labels (rust: proofs/src/poly/query.rs:10-38). Only the label
-- enum and its Display form are here: VerifierQuery, CommitmentReference and
-- the Query trait land with Exec/Pcs, which is where the verifier reaches
-- them. They are separated because MSMKZG already stores a label per term.

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

end Midfall.Halo2
