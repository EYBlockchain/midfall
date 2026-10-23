-- |
-- Midfall.Halo2.Exec.Types
--
-- Placeholder declarations for the rest of the L0 interface (plan Section 9.2).
-- Each names a type the faithful port fills in during Phase 2; declaring them
-- now is what lets Statements.lean be written, frozen and hash-checked against
-- the final names and arities.

import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

/-- rust: proofs/src/plonk/mod.rs VerifyingKey {domain, fixed_commitments,
    permutation, cs, cs_degree, transcript_repr}. Filled in by Phase 2. -/
structure VerifyingKey (Fr G₁ : Type) where

/-- rust: proofs/src/poly/kzg/msm.rs DualMSM. The check is
    e(left, sG2) * e(right, -G2) = 1 (plan Section 9.2). -/
structure DualMSM (Fr G₁ G₂ : Type) where

/-- rust: proofs/src/poly/kzg/params.rs ParamsVerifierKZG -/
structure ParamsVerifierKZG (G₁ G₂ : Type) where

/-- rust: proofs/src/transcript/mod.rs CircuitTranscript<Keccak256> -/
structure Transcript where

/-- The transcript state monad with the verifier failure type (plan 9.2). -/
abbrev TranscriptM := StateT Transcript (Except Fault)

/-- A decoded verifier message: an absorbed G1 point or a squeezed scalar. -/
inductive Msg (Fr G₁ : Type) where
  | g1 (P : G₁)
  | fr (s : Fr)

end Midfall.Halo2
