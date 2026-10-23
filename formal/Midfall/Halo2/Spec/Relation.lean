-- |
-- Midfall.Halo2.Spec.Relation
--
-- The NP relation the verifier is sound and complete for (plan Section 9.3).
-- Row-level evaluation helpers are placeholders until Phase 4; writing them now
-- fixes the five conjuncts of `Satisfies` - and so the statements of S1 and S6 -
-- in their final shape.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Permutation

namespace Midfall.Halo2.Spec

open Midfall Midfall.Halo2

variable {p : Nat} [Fact (Nat.Prime p)]

/-- Everything the mathematical verifier needs about a circuit: the constraint
    system, the domain size, the fixed columns as values (not commitments), the
    permutation structure, and `transcript_repr` as given by Rust (keygen is out
    of scope per plan Section 1). -/
structure CircuitIndex (Fr : Type) where
  cs : ConstraintSystem Fr
  k : Nat
  fixed : Nat -> Nat -> Fr
  perm : PermutationAssembly cs k
  repr : Fr

/-- Rows the identities are checked on: the domain minus the blinding factors
    (rust: ConstraintSystem::blinding_factors). -/
def CircuitIndex.usable (idx : CircuitIndex (Fr p)) : Array Nat := sorry

/-- A witness: one column of values per advice column, over the whole domain. -/
structure Witness (idx : CircuitIndex (Fr p)) where
  advice : Nat -> Nat -> Fr p

/-- Evaluate one expression at one row. -/
def evalRow (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx)
    (e : Expression (Fr p)) (i : Nat) : Fr p := sorry

/-- The value a cell carries, for the copy-constraint conjunct. -/
def cell (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx)
    (c : Cell) : Fr p := sorry

/-- The tuple of values a lookup input or table row takes. -/
def rowTuple (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx)
    (side : Nat) (i : Nat) : Array (Fr p) := sorry

/-- Design-assessment F3, turned into a hypothesis of the relation: the
    committed-instance column's commitment is the identity, which is what makes
    the verifier's identity-pinned MSM omission sound. -/
def CommittedInstanceZero (idx : CircuitIndex (Fr p)) : Prop := True

/-- The relation. Five conjuncts, in the plan's order: committed-instance
    identity, gate vanishing on usable rows, permutation copy constraints,
    lookup containment, and trashcan constraints under their selector. -/
structure Satisfies (idx : CircuitIndex (Fr p)) (inst : Array (Fr p))
    (w : Witness idx) : Prop where
  committedInstanceZero : CommittedInstanceZero idx
  gatesVanish : ∀ g ∈ idx.cs.gates, ∀ p' ∈ g.polys,
    ∀ i ∈ idx.usable, evalRow idx inst w p' i = 0
  permutes : ∀ c ∈ idx.perm.cycles, ∀ a ∈ c,
    ∀ b ∈ c, cell idx inst w a = cell idx inst w b
  lookupsContained : ∀ L ∈ idx.cs.lookups,
    ∀ i ∈ idx.usable, ∃ j ∈ idx.usable,
      rowTuple idx inst w L.1 i = rowTuple idx inst w L.2 j
  trashcansHold : ∀ T ∈ idx.cs.trashcans,
    ∀ i ∈ idx.usable,
      evalRow idx inst w T.2.1 i = 1 → ∀ c ∈ T.2.2,
        evalRow idx inst w c i = 0

/-- The relation as a set of (instances, witness) pairs, as S1 and S6 state it. -/
def Rel (idx : CircuitIndex (Fr p)) : Set (Array (Fr p) × Witness idx) :=
  { q | Satisfies idx q.1 q.2 }

end Midfall.Halo2.Spec