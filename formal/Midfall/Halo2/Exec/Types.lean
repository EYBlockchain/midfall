-- |
-- Midfall.Halo2.Exec.Types
--
-- Placeholder declarations for the rest of the L0 interface (plan Section 9.2).
-- Each names a type the faithful port fills in during Phase 2; declaring them
-- now is what lets Statements.lean be written, frozen and hash-checked against
-- the final names and arities.

import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

/-- A decoded verifier message: an absorbed G1 point or a squeezed scalar. -/
inductive Msg (Fr G₁ : Type) where
  | g1 (P : G₁)
  | fr (s : Fr)

end Midfall.Halo2
