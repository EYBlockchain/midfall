-- |
-- Midfall.Halo2.Exec.Pcs
--
-- The polynomial-commitment-scheme interface (rust:
-- proofs/src/poly/commitment.rs, 129 lines). Rule R9 names this trait
-- explicitly - PolynomialCommitmentScheme and Guard become structures of
-- functions - so the records are here even though there is exactly one
-- instantiation, KZG. The difference from trait MSM (deliberately not a
-- record, see Exec/Kzg/Msm.lean) is that the Rust calls multi_prepare through
-- the trait: plonk/verifier.rs:651 is CS::multi_prepare(...), generic in CS, so
-- Exec/Verifier must be written against the record to mirror it, and the
-- instantiation is the seam where CS := KZGCommitmentScheme<E>.
--
-- Of the trait's six methods only multi_prepare is verifier-reachable; the
-- other five are prover code, out of scope by plan Section 1.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Common.Codec
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Transcript
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Kzg.MultiOpen

namespace Midfall.Halo2

/-- rust: proofs/src/poly/commitment.rs:77-80 (trait Guard, the verify method).
    The guard is the value multi_prepare returns - a DualMSM - and params are
    the verifier parameters, so the record is a function between them. The
    Rust returns Result<(), poly::Error>; the port returns Except Fault, and
    docs/REVIEW.md R-8 records that the poly::Error variant is flattened here.
    Instantiated at DualMSM.verify (Exec/Kzg/Msm.lean). -/
structure Guard (G P : Type) where
  verify : G → P → Except Fault Unit

/-- rust: proofs/src/poly/commitment.rs:82-93 (Guard::batch_verify, the DEFAULT
    method). It asserts the two iterators agree in length (:88, a panic site),
    zips - which truncates, though the assert makes that unreachable - and
    short-circuits on the first error via try_for_each. The port keeps all of
    that: foldlM over the zip stops at the first error exactly like
    try_for_each. -/
def Guard.batchVerify {G P : Type} (g : Guard G P) (guards : Array G)
    (params : Array P) : Except Fault Unit := do
  unless guards.size == params.size do
    throw (Fault.panic "proofs/src/poly/commitment.rs:88")
  ((List.zip guards.toList params.toList).foldlM
    (init := ()) fun _ (guard, p) => g.verify guard p)

/-- rust: proofs/src/poly/commitment.rs:16-74 (trait
    PolynomialCommitmentScheme), the verifier-reachable projection. The
    associated types collapse to concrete ones under the KZG instantiation:
    Commitment = E::G1, VerifierParameters = ParamsVerifierKZG,
    VerificationGuard = DualMSM. -/
structure Pcs (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ] where
  /-- rust: commitment.rs:65-73 (multi_prepare), implemented for KZG at
      poly/kzg/mod.rs:321-574 and ported as Midfall.Halo2.multiPrepare. -/
  multiPrepare : Array (VerifierQuery (Fr p) G₁) →
                 TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)

/-- The KZG instantiation of the record (rule R9: instantiated with KZG plus
    Keccak). The four arguments are the configuration the Rust reads off the
    type and the environment: the point codec, the field constants (D-P1),
    the cargo features (R8) and the fewer-point-sets runtime switch. -/
def Pcs.kzg {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) : Pcs p G₁ G₂ Gₜ where
  multiPrepare := fun queries =>
    Midfall.Halo2.multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
      fewerPointSetsRuntime queries

/-- The Guard record at the KZG instantiation: DualMSM against
    ParamsVerifierKZG. rust: poly/kzg/msm.rs:223-234 (impl Guard for DualMSM). -/
def Pcs.kzgGuard {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ] :
    Guard (DualMSM (Fr p) G₁ G₂ Gₜ) (ParamsVerifierKZG G₁ G₂) where
  verify := fun g params => DualMSM.verify g params

/-! rust: proofs/src/poly/commitment.rs:18-19 (type Parameters), :38 (gen_params),
    :44 (commit), :48-51 (commit_lagrange), :54-61 (multi_open) - NOT
    verifier-reachable: all five are the prover half of the trait (plan
    Section 1 puts prover code out of scope). Evidence: gen_params and the two
    commit methods are called from plonk/keygen.rs and plonk/prover.rs;
    multi_open from plonk/prover.rs only. get_verifier_params (:41) is reached
    from ParamsKZG::verifier_params (poly/kzg/params.rs:313), which the port
    already has as ParamsVerifierKZG.ofParams. -/

/-! rust: proofs/src/poly/commitment.rs:96-129 (trait Params: max_k,
    g_monomial_size, downsize, downsize_from_circuit) - NOT verifier-reachable.
    The trait is implemented by ParamsKZG (the prover SRS), not by
    ParamsVerifierKZG, which has no Params impl (poly/kzg/params.rs:280-307).
    max_k is used by keygen to validate the SRS, i.e. exactly the keygen path
    plan Section 1 excludes: the VK is imported from Rust. -/

end Midfall.Halo2
