-- |
-- Midfall.Halo2.Exec.Circuit
--
-- The verifier-visible subset of the constraint system (plan Section 4 module
-- map: plonk/circuit.rs verifier subset). Placeholders now, filled by Phase 2;
-- the shapes are what the Section 9.3 relation and the Section 9.5 lowering
-- hypotheses are stated against.

import Midfall.Common.Curve

namespace Midfall.Halo2

/-- rust: proofs/src/plonk/circuit.rs Rotation -/
inductive Rotation where
  | cur | next | prev | value (v : Int)

/-- rust: proofs/src/plonk/circuit.rs Any -/
inductive Any where
  | advice | fixed | instance

/-- rust: proofs/src/plonk/circuit.rs Column<C>. Rust carries the kind in the
    type; the port keeps it as a field because the verifier reads kinds at
    runtime (committed-instance columns are distinguished by index < n). -/
structure Column where
  kind : Any
  index : Nat

/-- rust: proofs/src/plonk/circuit.rs Expression<F> -/
inductive Expression (F : Type) where
  | constant (c : F)
  | selector (s : Column)
  | fixed (c : Column) (r : Rotation)
  | advice (c : Column) (r : Rotation)
  | instance (c : Column) (r : Rotation)
  | challenge (c : Nat)
  | negated (e : Expression F)
  | sum (a b : Expression F)
  | product (a b : Expression F)
  | scaled (a : Expression F) (s : F)

/-- rust: proofs/src/plonk/circuit.rs Gate -/
structure Gate (F : Type) where
  name : String
  polys : Array (Expression F)
  queriedSelectors : Array Column

/-- rust: proofs/src/plonk/circuit.rs ConstraintSystem, verifier-reachable
    fields (source lines 1678-1727). Field order follows the Rust struct so the
    port can be checked line by line. -/
structure ConstraintSystem (F : Type) where
  gates : Array (Gate F)
  adviceQueries : Array (Column × Rotation)
  fixedQueries : Array (Column × Rotation)
  instanceQueries : Array (Column × Rotation)
  numAdviceColumns : Nat
  numFixedColumns : Nat
  numInstanceColumns : Nat
  numChallenges : Nat
  lookups : Array (Nat × Nat)
  trashcans : Array (String × Array (Expression F))

end Midfall.Halo2
