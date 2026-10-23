-- |
-- Midfall.Halo2.Exec.Error
--
-- Faithful port of the verifier-visible error taxonomy
-- (proofs/src/plonk/error.rs). The column payload types are declared here as
-- the placeholders Phase 2 will replace; keeping them inside this module means
-- `Error` and `Fault` are the concrete types the plan names.

namespace Midfall.Halo2

/-- rust: proofs/src/plonk/circuit.rs Column<Any> -/
structure ColumnAny where

/-- rust: proofs/src/plonk/circuit.rs TableColumn -/
structure TableColumn where

/-- rust: proofs/src/plonk/error.rs:33 (Error::Transcript(io::Error)). The Rust
    side carries an io::Error; the verifier can only observe a handful of kinds
    through the Keccak transcript, so the port keeps a closed taxonomy
    (plan Section 4 module map: Transcript(io::Error) -> transcript (k : IoErrorKind)). -/
inductive IoErrorKind where
  | unexpectedEof
  | other

/-- rust: proofs/src/plonk/error.rs:99-108 (TableError) -/
inductive TableError where
  | columnNotAssigned (col : TableColumn)
  | unevenColumnLengths (a : TableColumn × Nat) (b : TableColumn × Nat)
  | usedColumn (col : TableColumn)
  | overwriteDefault (col : TableColumn) (default : String) (val : String)

/-- rust: proofs/src/plonk/error.rs:7-45 (Error). All variants, in source order
    (port rule R1). Variants only the prover can reach are kept: the port is
    line-faithful, and pruning them would make the error classes diverge from
    the reference. -/
inductive Error where
  | synthesis (msg : String)
  | invalidInstances
  | constraintSystemFailure
  | boundsFailure
  | opening
  | transcript (k : IoErrorKind)
  | notEnoughRowsAvailable (current_k : Nat)
  | instanceTooLarge
  | notEnoughColumnsForConstants
  | columnNotInPermutation (col : ColumnAny)
  | tableError (e : TableError)
  | srsError (srs_k circuit_k : Nat)

/-- A verifier failure: a typed error, or a panic site (port rule R4). -/
inductive Fault where
  | error (e : Error)
  | panic (site : String)

end Midfall.Halo2
