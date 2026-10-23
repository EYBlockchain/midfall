-- |
-- Midfall.Halo2.Exec.Permutation
--
-- rust: proofs/src/plonk/permutation/* (verifier path only, plan Section 4).
-- Placeholder shapes for Phase 2; the copy-constraint structure is what the
-- Section 9.3 relation quantifies over.

import Midfall.Halo2.Exec.Circuit

namespace Midfall.Halo2

/-- A cell of the trace: (column, row). -/
structure Cell where
  column : Column
  row : Nat

/-- rust: proofs/src/plonk/permutation/keygen.rs Assembly, verifier view. The
    sigma polynomials are given as their cycle decomposition here, because that
    is the form the relation quantifies over (plan 9.3 perm.cycles). -/
structure PermutationAssembly {F : Type} (cs : ConstraintSystem F) (k : Nat) where
  /-- Equivalence classes of cells under the copy constraints: each cycle is a
      list of cells that must carry equal values. -/
  cycles : Array (Array Cell)
  /-- sigma mappings, as the verifier reads them from the VK commitments. -/
  sigmaCommitments : Array Column

end Midfall.Halo2
