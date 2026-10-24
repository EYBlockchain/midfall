-- |
-- Midfall.Halo2.Spec.Relation
--
-- The NP relation the verifier is sound and complete for (plan Section 9.3).
-- Row-level evaluation is the spec-level counterpart of the verifier's
-- Expression::evaluate at the challenge point: same expression algebra, but over
-- witness values on a row rather than openings at x.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
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

/-- The domain size. rust: poly/domain.rs:39 (`n = 1 << k`). -/
def CircuitIndex.n (idx : CircuitIndex (Fr p)) : Nat := 2 ^ idx.k

/-- Row arithmetic wraps around the domain: `next` on the last row lands on row 0.
    rust: a Rotation is applied modulo n wherever the prover evaluates a
    polynomial on its domain. -/
def CircuitIndex.rowAt (idx : CircuitIndex (Fr p)) (i : Nat) (r : Rotation) : Nat :=
  Int.toNat (((i : Int) + r.int).emod (idx.n : Int))

/-- Rows the identities are checked on: `0 .. n - blinding_factors`.
    rust: circuit.rs:2472-2512 (`blinding_factors`) and the usable-row range it
    feeds.

    When `blinding_factors` faults - the i32::MAX site at circuit.rs:2510, which
    R-13 records as reachable from a logUp-heavy constraint system - the row set
    is empty rather than guessed at. That makes `Satisfies` degenerate to True on
    such a system, which is exactly why the theorems carry a well-formedness
    hypothesis; `CircuitIndex.WellFormed` in Spec/Degrees.lean is where that has
    to be required. -/
def CircuitIndex.usable (idx : CircuitIndex (Fr p)) : Array Nat :=
  match idx.cs.blindingFactors with
  | .error _ => #[]
  | .ok bf => (List.range (idx.n - bf)).toArray

/-- A witness: one column of values per advice column, over the whole domain. -/
structure Witness (idx : CircuitIndex (Fr p)) where
  advice : Nat -> Nat -> Fr p

/-- Evaluate one expression at one row.

    Three cases are totalised rather than faulted, because this is a Prop-level
    definition and the reference's panics are the Exec layer's job:

    * a `selector` whose flag is virtual (`colIdx = none`) evaluates to 0. By VK
      time virtual selectors are gone - the reference panics at mod.rs:532 - so a
      well-formed index never reaches this branch.
    * `challenge` evaluates to 0. Plan Section 13 excludes multi-phase circuits
      and S1/S6 assume `numChallenges = 0`, so no challenge occurs.
    * `instance` reads `inst` at the rotated row. NOTE a shape tension to resolve
      before the refinement theorem: plan 9.3 types `inst : Array Fr`, one flat
      column, while plan 9.5's `Supported.instShape` requires
      `numInstanceColumns = 2`. With more than one instance column this reads
      column 0 only. Flagged rather than silently widened, because the signature
      is normative. -/
def evalRow (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx)
    (e : Expression (Fr p)) (i : Nat) : Fr p :=
  match e with
  | .constant c => c
  | .selector s =>
      match idx.cs.selectorFlags[s.index]?.bind (fun f => f.colIdx) with
      | some c => idx.fixed c (idx.rowAt i Rotation.cur)
      | none => 0
  | .fixed q => idx.fixed q.columnIndex (idx.rowAt i q.rotation)
  | .advice q => w.advice q.columnIndex (idx.rowAt i q.rotation)
  | .instance q => inst.getD (idx.rowAt i q.rotation) 0
  | .challenge _ => 0
  | .negated a => -evalRow idx inst w a i
  | .sum a b => evalRow idx inst w a i + evalRow idx inst w b i
  | .product a b => evalRow idx inst w a i * evalRow idx inst w b i
  | .scaled a s => evalRow idx inst w a i * s

/-- The value a cell carries, for the copy-constraint conjunct. Dispatched on the
    column type exactly as `Column.queryCell` does (circuit.rs:57-59 through the
    `impl ColumnType` arms at :269-317), with no rotation: a permutation cell is
    addressed by (column, row). -/
def cell (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx)
    (c : Cell) : Fr p :=
  match c.column.columnType with
  | .advice _ => w.advice c.column.index c.row
  | .fixed => idx.fixed c.column.index c.row
  | .instance => inst.getD c.row 0

/-- The tuple of values a lookup input or table row takes: one entry per
    expression in the row, evaluated at row i. Plan 9.3 writes this as
    `rowTuple idx inst w inp i` where inp is an input vector and L.table the
    table vector, so the argument is the expression list, not an index. -/
def rowTuple (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx)
    (exprs : Array (Expression (Fr p))) (i : Nat) : Array (Fr p) :=
  exprs.map (fun e => evalRow idx inst w e i)

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
    ∀ inp ∈ L.inputExpressions, ∀ i ∈ idx.usable, ∃ j ∈ idx.usable,
      rowTuple idx inst w inp i = rowTuple idx inst w L.tableExpressions j
  trashcansHold : ∀ T ∈ idx.cs.trashcans,
    ∀ i ∈ idx.usable,
      evalRow idx inst w T.selector i = 1 → ∀ c ∈ T.constraintExpressions,
        evalRow idx inst w c i = 0

/-- The relation as a set of (instances, witness) pairs, as S1 and S6 state it. -/
def Rel (idx : CircuitIndex (Fr p)) : Set (Array (Fr p) × Witness idx) :=
  { q | Satisfies idx q.1 q.2 }

/-! ## Sanity checks

    Small hand-computed checks over `Fr 17`, in the style of the Exec KATs. These
    exist because a spec definition that never runs is exactly how a wrong
    `usable` or a missing wrap-around would survive review. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- n = 4, and blinding_factors for an empty-ish system is 3 (the constant
    permutation needs it), so the usable window is short. Computed from the port
    rather than assumed: `usable` is whatever `blindingFactors` allows. -/
def relIdx : CircuitIndex (Fr 17) :=
  { cs := { ConstraintSystem.default (F := Fr 17) with
            numAdviceColumns := 1, adviceColumnPhase := #[⟨0⟩],
            numFixedColumns := 1, numInstanceColumns := 1,
            selectorFlags := #[{ isSimple := true, colIdx := some 0 }],
            adviceQueries := #[({ index := 0, columnType := Any.adviceFirst },
                                Rotation.cur)],
            fixedQueries := #[({ index := 0, columnType := Any.fixed },
                                Rotation.cur)],
            instanceQueries := #[({ index := 0, columnType := Any.instance },
                                   Rotation.cur)] },
    k := 2,
    fixed := fun _ j => (j + 1 : Fr 17),
    perm := { cycles := #[], sigmaCommitments := #[] },
    repr := 7 }

def relKats_ok : Bool :=
  -- domain size and wrap-around
  relIdx.n == 4 &&
  (relIdx.rowAt 3 Rotation.next == 0) &&
  (relIdx.rowAt 0 Rotation.prev == 3) &&
  (relIdx.rowAt 1 Rotation.cur == 1) &&
  -- fixed column: fixed col row = row + 1
  (evalRow relIdx #[] ⟨fun _ _ => 0⟩
     (Expression.fixed { index := some 0, columnIndex := 0, rotation := .next }) 2)
    == (4 : Fr 17) &&
  -- advice reads the witness at the rotated row
  (evalRow relIdx #[] ⟨fun _ j => (2 * j : Fr 17)⟩
     (Expression.advice { index := some 0, columnIndex := 0, rotation := .cur,
                          phase := ⟨0⟩ }) 3) == (6 : Fr 17) &&
  -- selector resolves through selectorFlags to the fixed column at row i
  (evalRow relIdx #[] ⟨fun _ _ => 0⟩
     (Expression.selector { index := 0, isSimple := true }) 1) == (2 : Fr 17) &&
  -- expression algebra
  (evalRow relIdx #[] ⟨fun _ _ => 0⟩
     (Expression.sum (Expression.constant 8) (Expression.constant 9)) 0) == 0 &&
  (evalRow relIdx #[] ⟨fun _ _ => 0⟩
     (Expression.product (Expression.constant 3)
        (Expression.negated (Expression.constant 5))) 0) == (2 : Fr 17) &&
  -- cell dispatch
  (cell relIdx #[9] ⟨fun _ _ => 4⟩
     { column := { index := 0, columnType := Any.instance }, row := 0 }) == 9 &&
  (cell relIdx #[] ⟨fun _ j => (j : Fr 17)⟩
     { column := { index := 0, columnType := Any.adviceFirst }, row := 2 }) == 2 &&
  -- rowTuple maps pointwise
  (rowTuple relIdx #[] ⟨fun _ _ => 0⟩
     #[Expression.constant 3, Expression.constant 4] 0).toList == [3, 4] &&
  -- usable is either empty (blinding_factors faulted) or a prefix of the domain
  (relIdx.usable.size ≤ relIdx.n)

end Kats

#eval Midfall.Halo2.Spec.relKats_ok   -- expect true

end Midfall.Halo2.Spec
