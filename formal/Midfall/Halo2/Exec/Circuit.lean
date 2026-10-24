-- |
-- Midfall.Halo2.Exec.Circuit
--
-- Faithful port of the verifier-visible subset of `proofs/src/plonk/circuit.rs`
-- (2745 lines) (plan Section 4 module map, row
-- `plonk/circuit.rs (verifier subset) -> Exec/Circuit`:
-- Column/Any/Phase/Challenge/Selector/queries/Expression (Constant, Selector,
-- Fixed, Advice, Instance, Challenge, Negated, Sum, Product, Scaled)/Gate/
-- ConstraintSystem fields 1678-1727, `degree`, `blinding_factors`, `evaluate`
-- (a virtual selector panics)).
--
-- Port rules applied (plan Section 4): R1 provenance on every def *and* on every
-- skip, statements in source order, no improvements; R2 snake_case ->
-- lowerCamelCase, type names kept; R3 `?` becomes a left-arrow bind in `Except`
-- and iterator chains are mirrored (`zip` truncates; `enumerate`, `map`,
-- `unzip`, `flat_map`, `filter_map` and `max` keep Rust semantics, including
-- that `max` on an empty iterator is `None`); R4 `unwrap`, `expect`, `panic!`,
-- `assert!` and out-of-bounds slicing become
-- `.error (Fault.panic "<path>:<line>")`; R5 `Nat`/`Int` with wrapping emulated
-- only where it can actually occur; R6 `Vec` -> `Array`, `HashMap` only where its
-- iteration order cannot be observed (argued at `generalColumnAnnotations`);
-- R7 `invert` returns `Option` (nothing in this file inverts); R8 both branches
-- of every `#[cfg(feature)]` (this file has exactly one, `circuit-params`,
-- recorded at its site); R9 traits become records of functions; R10 computable,
-- never `partial`, and no proofs here.
--
-- REACHABILITY. The set grepped is the one the task names: plonk/verifier.rs,
-- plonk/{permutation,logup,trash,linearization}/verifier.rs, plonk/mod.rs,
-- poly/** and proofs/solidity-verifier/src, plus plonk/{permutation,logup,trash}.rs
-- because those host the `impl` blocks the verifier files call. Ported because
-- reachable, with the site that reaches each:
--   Expression::evaluate        plonk/mod.rs:530 (`partially_evaluate_identities`,
--                               the gate loop), plonk/trash.rs:68,
--                               plonk/logup.rs:419, and the generator's own
--                               visitor solidity-verifier/src/lowering/
--                               quotient_numerator/yul_emit.rs:1024
--   Expression::degree          plonk/logup.rs:230, :246, :264, plonk/trash.rs:32
--   Expression::contains_simple_selector and the Neg/Add/Sub/Mul impls
--                               plonk/circuit.rs:2204-2235 (`replace_selectors`),
--                               reached from `directly_convert_selectors_to_fixed`
--                               at plonk/mod.rs:189, i.e. `read_from_cs`
--   ConstraintSystem::degree    plonk/mod.rs:175, :233, solidity-verifier
--                               src/lowering/quotient.rs:1430
--   ConstraintSystem::blinding_factors
--                               plonk/verifier.rs:443, plonk/mod.rs:509,
--                               plonk/permutation/verifier.rs:150,
--                               solidity-verifier/src/lowering/protocol/mod.rs:402
--   ConstraintSystem::phases    plonk/verifier.rs:112
--   ConstraintSystem::has_simple_selector_col
--                               plonk/verifier.rs:409, :635, protocol/mod.rs:372
--   ConstraintSystem::num_simple_selectors
--                               plonk/verifier.rs:400,
--                               plonk/linearization/verifier.rs:58
--   ConstraintSystem::get_any_query_index
--                               plonk/permutation.rs:246-272
--   ConstraintSystem::{advice,instance,fixed}_queries, ::gates, ::lookups,
--   ::trashcans, ::permutation, ::num_*, ::advice_column_phase, ::challenge_phase
--                               plonk/verifier.rs:62, :109, :110, :115, :128,
--                               :331, :381, :408, :600, :610; plonk/mod.rs:188,
--                               :527, :556, :572, :592; solidity-verifier
--                               src/lowering/protocol/mod.rs:332-400
--   the three argument structs  plonk/verifier.rs:179, :188, :196, plonk/mod.rs:
--                               556, :572, :592, and their degree helpers through
--                               `cs.degree()` / `cs.blinding_factors()`
--   Selector::is_simple/index   plonk/mod.rs:545, solidity-verifier
--                               src/lowering/diagnostics.rs:112,
--                               quotient_numerator/yul_emit.rs:218
--   Gate::{name,polynomials,constraint_name,queried_selectors}
--                               plonk/mod.rs:529, :543, solidity-verifier
--                               src/lowering/{diagnostics.rs:110, :125, :130,
--                               quotient.rs:824, protocol/mod.rs:604}
-- NOT verifier-reachable, so skipped with evidence at each site: the gate and
-- lookup *construction* API (`create_gate`, `lookup*`, `selector`,
-- `complex_selector`, `*_column`, `challenge_usable_after`, `enable_*`,
-- `set_minimum_degree`, `annotate_*`), `VirtualCells`' methods, `query_cells`,
-- `evaluate_lazy`, `identifier`/`write_identifier`, `complexity`, `square`,
-- `minimum_rows`, `general_column_annotations`, `constants()`, `pinned` and
-- `PinnedConstraintSystem`, and the `Circuit`/`Assignment`/`FloorPlanner` traits.
--
-- THREE STRUCTURAL CHOICES, each forced, each recorded because it changes how
-- the file has to be read.
--
-- 1. DECLARATION ORDER. Rust declares `Column<C>` (circuit.rs:34) before the
--    kinds it is generic over (`Phase` :103, `Advice` :159, `Any` :206) because
--    the kind is a type parameter. Lean has no forward references, so the kinds
--    come first and `Column` follows. Everything else keeps source order.
-- 2. `COLUMN` CARRIES ITS KIND AS A VALUE. Rust's `Column<C: ColumnType>` puts
--    the kind in the type; the verifier reads kinds at runtime (an instance
--    column is one with `index < nb_committed_instances`, plonk/verifier.rs:357),
--    so the port keeps `columnType : Any` as a field. That is what the
--    placeholder had, and it is why `Any.advice` has to carry a `Phase`:
--    `query_advice_index` deduplicates `(Column<Advice>, Rotation)` pairs by
--    equality (circuit.rs:2026-2028) and two advice columns with the same index
--    in different phases are *different* queries in Rust. A payload-free
--    `Any.advice` would silently merge them.
-- 3. THE ARGUMENT STRUCTS LIVE HERE. `permutation::Argument`,
--    `logup::BatchedArgument` and `trash::Argument` are declared in
--    plonk/{permutation,logup,trash}.rs, which the plan assigns to
--    Exec/{Permutation,Logup,Trash}, but `ConstraintSystem` names all three as
--    field types and `Exec/Permutation.lean` already imports this module - so
--    declaring them there would be an import cycle. They are ported here, with
--    provenance pointing at their real files, and only the fields and methods
--    `ConstraintSystem` and the verifier path need.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

/-- rust: proofs/src/poly/mod.rs:509 (`pub struct Rotation(pub i32)`) and its
    `cur`/`next`/`prev` constructors at :511-526. The plan's module map assigns
    `Rotation` to this row (the placeholder had it here), `Exec/Domain.lean`
    extends it with `Rotation.int`, and `Exec/Poly.lean` records the same
    representational caveat; `deriving BEq` is new and needed, because the
    query-index lookups below compare `(Column, Rotation)` pairs, which is the
    `==` on the Rust tuple at circuit.rs:2012, :2027 and :2043.

    THE HAZARD, inherited from the placeholder rather than introduced:
    `Rotation.cur` and `Rotation.value 0` are two inhabitants in Lean and one
    `i32` in Rust, so a Rust `rotation == Rotation::cur()` must be read as
    `rotation.int == 0`, never as structural equality. A query pushed as
    `(col, Rotation::cur())` and looked up as `Rotation(0)` deduplicates in Rust
    and does *not* deduplicate here. Pinned by a KAT below; it cannot bite the
    verifier itself, because every rotation on the verify path is built by
    `query_*`/`create_gate` and looked up by `get_*_query_index` through the same
    constructor, but it can bite a hand-written `ConstraintSystem`, which is
    exactly what the conformance exporter will feed us. -/
inductive Rotation where
  | cur | next | prev | value (v : Int)
  deriving BEq

/-! ### Phases (rust: proofs/src/plonk/circuit.rs:100-157) -/

/-- rust: proofs/src/plonk/circuit.rs:103-127 (`sealed::Phase(pub(super) u8)`,
    its `prev`, and `impl SealedPhase for Phase`).

    The Rust is a `u8`; the port uses `Nat` (rule R5) and records why no
    wrapping can occur: the only inhabitants Rust ever builds are 0, 1 and 2,
    from `FirstPhase`/`SecondPhase`/`ThirdPhase` (:129-157), and
    `ConstraintSystem::advice_column_in` refuses a phase whose predecessor has no
    advice column (:2370-2388 + `assert_phase_exists` :2423-2433), so the counter
    cannot walk up to 255 without a phase-0..254 chain of `Column<Advice>`.
    `Phase.prev` is Rust's `checked_sub(1)` exactly: phase 0 has no predecessor. -/
structure Phase where
  /-- rust: circuit.rs:103 (`pub(super) u8`) -/
  val : Nat
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:106-110 (`Phase::prev`). -/
def Phase.prev (p : Phase) : Option Phase :=
  if p.val = 0 then none else some { val := p.val - 1 }

/-- rust: proofs/src/plonk/circuit.rs:103 (`#[derive(..., Ord, PartialOrd, ...)]`
    on `Phase`). Reached by `ConstraintSystem::phases` (:2435-2441, `iter().max()`)
    and by `Any`'s `Ord` (:250). -/
def Phase.cmp (a b : Phase) : Ordering :=
  if a.val < b.val then .lt else if a.val == b.val then .eq else .gt

/-- rust: proofs/src/plonk/circuit.rs:119-127 (`pub trait SealedPhase` with
    `to_sealed`) plus :129-157 (`FirstPhase`, `SecondPhase`, `ThirdPhase`, each
    an empty struct whose `to_sealed` returns `Phase(0)`, `Phase(1)`,
    `Phase(2)`). Rule R9: a trait of functions becomes a record of functions -
    here a closed sum of three cases, because the three "types" carry no data and
    the trait has one method with no default. The `pub trait Phase: SealedPhase`
    at :124 and its blanket impl at :126 are the sealing device that keeps
    `Phase(3)` unconstructable from outside the module; Lean has no module
    visibility to seal, so the closed sum is what enforces it. -/
inductive PhaseKind where
  | first | second | third

/-- rust: proofs/src/plonk/circuit.rs:132-157 (the three `to_sealed` impls). -/
def PhaseKind.toSealed : PhaseKind → Phase
  | .first => { val := 0 }
  | .second => { val := 1 }
  | .third => { val := 2 }

/-- rust: proofs/src/plonk/circuit.rs:159-196 (`struct Advice { phase:
    sealed::Phase }`, `Default`, `new`, `phase()`). `Advice.default` is the
    `FirstPhase` default at :164-170; `Advice.new` is :174-176.

    `Advice::phase()` returns the raw `u8` and the field is a `Phase`, so the
    Rust accessor and the Rust field have *different* Lean names here: the
    projection `Advice.phase` already occupies the name `phase`. FORCED R2
    DEVIATION: the accessor is `Advice.phaseNat`. The same collision recurs at
    `AdviceQuery` and `Challenge` and is resolved the same way. -/
structure Advice where
  /-- rust: circuit.rs:161 (`pub(crate) phase: sealed::Phase`) -/
  phase : Phase
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:164-170 (`impl Default for Advice`). -/
def Advice.default : Advice := { phase := PhaseKind.first.toSealed }

/-- rust: proofs/src/plonk/circuit.rs:174-176 (`Advice::new<P: Phase>`). -/
def Advice.new (pk : PhaseKind) : Advice := { phase := pk.toSealed }

/-- rust: proofs/src/plonk/circuit.rs:181-183 (`Advice::phase`). -/
def Advice.phaseNat (a : Advice) : Nat := a.phase.val

/-! rust: proofs/src/plonk/circuit.rs:186-196 (`impl Debug for Advice`) - not
    ported, and not only because `Debug` is a formatting trait: the impl *hides*
    the phase when it is `FirstPhase`, so the rendered string is a partial
    function of the value. It is reached from `format!("{:?}", ..)` only, and the
    only verifier-reachable `{:?}` on a constraint system is
    `PinnedConstraintSystem` at plonk/mod.rs:272, which feeds `transcript_repr` -
    that is docs/REVIEW.md R-1, owned by Exec/VerifyingKey, and the plan takes
    `transcript_repr` as given (Section 1). Nothing in the reachable set formats
    an `Advice` directly. -/

/-- rust: proofs/src/plonk/circuit.rs:206-214 (`enum Any { Advice(Advice),
    Fixed, Instance }`). The Rust unit structs `Fixed` (:198-199) and
    `Instance` (:202-203) carry no fields, so they become nullary constructors
    here rather than separate types; `impl ColumnType` for them (:279-296) is the
    corresponding arms of `Column.queryCell`.

    `Any::Advice` carries the `Advice`, which is what makes the phase visible to
    the query deduplication - see structural choice 2 in this file's header. -/
inductive Any where
  | advice (a : Advice)
  | fixed
  | instance
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:216-226 (`Any::advice()` and
    `Any::advice_in::<P>()`). Both collide with the `Any.advice` constructor, so
    the port names them `Any.adviceFirst` and `Any.adviceIn`. FORCED R2
    DEVIATION, recorded: the Rust has a *unit fn* and a *variant* sharing a name
    (distinguished by case, `advice` vs `Advice`), which Lean cannot express.
    Neither is verifier-reachable: `Any::advice()` is used by keygen and by
    `dev`, and `advice_in` has no call site in the reachable set. -/
def Any.adviceFirst : Any := .advice Advice.default

/-- rust: proofs/src/plonk/circuit.rs:223-226 (`Any::advice_in`). -/
def Any.adviceIn (pk : PhaseKind) : Any := .advice (Advice.new pk)

/-! rust: proofs/src/plonk/circuit.rs:228-243 (`impl Debug for Any`) - not
    ported; same reason as `Advice`'s `Debug` above. -/
/-- rust: proofs/src/plonk/circuit.rs:245-262 (`impl Ord for Any`), with the
    `#[derive(Ord)]` on `sealed::Phase` (:103) that it delegates to for the
    advice/advice case.

    The Rust comment is a warning worth keeping verbatim: "This ordering is
    consensus-critical! The layouters rely on deterministic column orderings."
    Across kinds the order is Instance < Advice < Fixed; within `Advice` it is
    the phase; `Fixed` and `Instance` compare equal to themselves, which is what
    lets `Column`'s `Ord` fall through to the index. The nine arms are ported
    one for one rather than derived, because a derived `Ord` on the inductive
    would order by *declaration* position (Advice < Fixed < Instance) - the
    opposite of what the Rust pins. -/
def Any.cmp : Any → Any → Ordering
  | .instance, .instance => .eq
  | .fixed, .fixed => .eq
  | .advice a, .advice b => Phase.cmp a.phase b.phase
  | .instance, .advice _ => .lt
  | .advice _, .fixed => .lt
  | .instance, .fixed => .lt
  | .fixed, .instance => .gt
  | .fixed, .advice _ => .gt
  | .advice _, .instance => .gt

/-- rust: proofs/src/plonk/circuit.rs:263-267 (`impl PartialOrd for Any`):
    `Some(self.cmp(other))`, so it carries no behaviour of its own. -/
def Any.partialCmp (a b : Any) : Ordering := Any.cmp a b

/-! rust: proofs/src/plonk/circuit.rs:26-31 (`trait ColumnType`) - not ported as
    a record, which is what rule R9 would normally do. The trait carries exactly
    one function, `query_cell`, and its four impls (:269-317) are a case split on
    the kind; because this port stores the kind as a *value* in `Column` (choice 2
    above), that case split lands in `Column.queryCell` and there is nothing left
    for a record to carry. The trait's supertraits are structural facts about the
    Rust types, not behaviour: `'static`/`Sized`/`Copy` have no Lean counterpart,
    `Debug` is not ported (see the two `Debug` skips above), and `Into<Any>` is
    the six `From` impls at :320-363, which collapse together with the generic
    parameter - `Column<Advice>`, `Column<Fixed>` and `Column<Instance>` are all
    `Column` here, and the three `TryFrom` impls at :365-405 (whose `Err` strings
    are "Cannot convert into Column<Advice>" and friends) become the match arms of
    `ConstraintSystem.queryAnyIndex` and `getAnyQueryIndex`, where the Rust's
    `.unwrap()` on them can never fire because the arm was chosen by the same
    test. -/

/-- rust: proofs/src/plonk/circuit.rs:34-39 (`struct Column<C: ColumnType> {
    index: usize, column_type: C }`), field order preserved (rule R1).

    `Column::index()` (:47-49) and `Column::column_type()` (:52-54) are the Lean
    projections: the Rust returns `usize` and `&C` and the port returns `Nat` and
    `Any` by value, which is unobservable because nothing mutates a column.
    `Column::new` (:41-45) is `#[cfg(test)]` in the reference, so it is not part
    of the port at all. -/
structure Column where
  /-- rust: circuit.rs:36 (`index: usize`) -/
  index : Nat
  /-- rust: circuit.rs:37 (`column_type: C`) -/
  columnType : Any
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:82-92 (`impl Ord for Column`). The Rust
    converts the kind to `Any` first; here the kind already *is* an `Any`, so the
    conversion is the identity and only the two-step ordering survives. -/
def Column.cmp (a b : Column) : Ordering :=
  match Any.cmp a.columnType b.columnType with
  | .eq => if a.index < b.index then .lt else if a.index == b.index then .eq else .gt
  | o => o

/-- rust: proofs/src/plonk/circuit.rs:94-101 (`impl PartialOrd for Column`). -/
def Column.partialCmp (a b : Column) : Ordering := Column.cmp a b

/-- rust: proofs/src/plonk/circuit.rs:463-464 (`struct Selector(pub(crate)
    usize, bool)`), tuple field order preserved: `.0` is the index and `.1` is
    the "simple" flag. That order matters and is easy to get backwards - the Rust
    writes `Selector(index, true)` in `ConstraintSystem::selector` (:2267-2272)
    and `Selector(index, false)` in `complex_selector` (:2276-2281), and
    `directly_convert_selectors_to_fixed` mutates `s.0`, the *index*, at :2197.

    `Selector::index()` (:479-481) and `is_simple()` (:474-476) are the
    projections. `Selector::enable` (:468-470) is witness assignment (it calls
    `Region::enable_selector`), so it is prover-only. -/
structure Selector where
  /-- rust: circuit.rs:464 (`.0: usize`) -/
  index : Nat
  /-- rust: circuit.rs:464 (`.1: bool`) -/
  isSimple : Bool
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:490-495 (`struct FixedQuery { index:
    Option<usize>, column_index: usize, rotation: Rotation }`), field order
    preserved. The three accessors at :502-513 are the projections.

    `index` is the position of this query in `ConstraintSystem::fixed_queries`,
    filled in by `query_cells`/`query_fixed` and *read* by the verifier: the
    closure at plonk/mod.rs:533 is `fixed_evals[query.index.unwrap()]`, so an
    unfilled (`none`) query is a panic on the verify path, not a default. -/
structure FixedQuery where
  /-- rust: circuit.rs:492 (`index: Option<usize>`) -/
  index : Option Nat
  /-- rust: circuit.rs:493 (`column_index: usize`) -/
  columnIndex : Nat
  /-- rust: circuit.rs:494 (`rotation: Rotation`) -/
  rotation : Rotation
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:517-525 (`struct AdviceQuery`), field
    order preserved (`index`, `column_index`, `rotation`, `phase`). Note the
    Rust `pub` on `index` and `pub(crate)` on the rest - visibility, not data.
    `phase()` (:541-543) returns the raw `u8`, so it collides with the projection
    and becomes `AdviceQuery.phaseNat` (the same forced deviation as
    `Advice.phaseNat`). -/
structure AdviceQuery where
  /-- rust: circuit.rs:519 (`index: Option<usize>`) -/
  index : Option Nat
  /-- rust: circuit.rs:520 (`column_index: usize`) -/
  columnIndex : Nat
  /-- rust: circuit.rs:521 (`rotation: Rotation`) -/
  rotation : Rotation
  /-- rust: circuit.rs:523 (`phase: sealed::Phase`) -/
  phase : Phase
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:541-543 (`AdviceQuery::phase`). -/
def AdviceQuery.phaseNat (q : AdviceQuery) : Nat := q.phase.val

/-- rust: proofs/src/plonk/circuit.rs:547-553 (`struct InstanceQuery`), field
    order preserved; the accessors at :559-565 are the projections. -/
structure InstanceQuery where
  /-- rust: circuit.rs:549 (`index: Option<usize>`) -/
  index : Option Nat
  /-- rust: circuit.rs:550 (`column_index: usize`) -/
  columnIndex : Nat
  /-- rust: circuit.rs:551 (`rotation: Rotation`) -/
  rotation : Rotation
  deriving BEq

/-! rust: proofs/src/plonk/circuit.rs:580-599 (`struct TableColumn { inner:
    Column<Fixed> }` and its `inner()`) - NOT ported, for two independent
    reasons. (1) It is not verifier-reachable: grepping the reachable set for
    `TableColumn` returns nothing outside circuit.rs, because the type only ever
    appears in the lookup-*construction* API (`lookup_table_column` :2284-2288,
    `annotate_lookup_column` :2291-2303, `batched_lookup`'s `table_map`
    :1915-1955); by the time the verifier looks at `cs.lookups` the tables have
    been flattened into `logup::BatchedArgument` table *expressions*. (2) The
    name is already taken: `Midfall.Halo2.TableColumn` is declared in
    Exec/Error.lean as the payload of `Error::table_error` (plonk/error.rs:99-108),
    and Error cannot import Circuit - `Fault` lives in Error and every panicking
    def here needs it - so the two cannot be unified in either direction.
    Exec/Error.lean's header says its column payload types are "placeholders
    Phase 2 will replace"; they cannot be, and that is a plan-level consequence of
    the import direction rather than a local choice (raised in this package's
    report). Until it is settled, `TableColumn` means the empty stub in
    Exec/Error.lean and this module introduces no second one. The Rust security
    note on the field ("This inner column MUST NOT be exposed in the public API,
    or else chip developers can load lookup tables into their circuits without
    default-value-filling the columns, which can cause soundness bugs", :583-588)
    travels with whatever ends up owning the type. -/

/-- rust: proofs/src/plonk/circuit.rs:601-605 (`struct Challenge { index:
    usize, phase: sealed::Phase }`), field order preserved. `index()` (:609-611)
    is the projection; `phase()` (:614-616) returns the raw `u8` and so becomes
    `Challenge.phaseNat` (forced deviation, as above). -/
structure Challenge where
  /-- rust: circuit.rs:603 (`index: usize`) -/
  index : Nat
  /-- rust: circuit.rs:604 (`phase: sealed::Phase`) -/
  phase : Phase
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:614-616 (`Challenge::phase`). -/
def Challenge.phaseNat (c : Challenge) : Nat := c.phase.val

/-! rust: proofs/src/plonk/circuit.rs:626-822 (`trait Assignment`, `trait
    FloorPlanner`, `trait Circuit`) - NOT verifier-reachable, so nothing to port.
    Evidence: `Assignment` is the witness-assignment callback interface
    (implemented by `SingleChipLayouter` and `MockProver`); `FloorPlanner`'s only
    method `synthesize` (:765) is called from `Circuit::synthesize` in the prover
    and keygen; `trait Circuit` (:776-821) is consumed by `VerifyingKey::read`
    and `from_bytes` (plonk/mod.rs:123, :202) as a *type parameter only* - the
    verifier never calls a method on it - and plan Section 1 puts circuit
    synthesis and keygen out of scope.

    THE FILE'S ONLY `#[cfg(feature)]`, recorded for rule R8: :784, :794 and :804
    gate `type Params: Default`, `fn params()` and `fn configure_with_params()`
    on `feature = "circuit-params"`. Both branches would be the same Lean code (a
    field and two methods on a trait that is not ported), and neither is reachable:
    the verifier uses `ConcreteCircuit` only through `Circuit::configure` inside
    `VerifyingKey::read`. The remaining `#[cfg]`s in the file are `#[cfg(test)]`
    at :41 (`Column::new`) and :2702 (`mod tests`). -/
/-- rust: proofs/src/plonk/circuit.rs:824-849 (`enum Expression<F>`), variant
    order preserved (rule R1). The Rust boxes every recursive payload
    (`Box<Expression<F>>` at :841-848); Lean has no heap/stack distinction to
    make, so the boxes disappear and nothing else changes - the tree shape, and
    hence `degree`, is identical. `deriving BEq` is needed because the operator
    impls below compare against `Constant(ZERO)` and `Constant(ONE)` exactly as
    Rust's `==` does (:1341, :1344, :1378, :1381, :1416-1421). -/
inductive Expression (F : Type) where
  | constant (c : F)
  | selector (s : Selector)
  | fixed (q : FixedQuery)
  | advice (q : AdviceQuery)
  | instance (q : InstanceQuery)
  | challenge (c : Challenge)
  | negated (e : Expression F)
  | sum (a b : Expression F)
  | product (a b : Expression F)
  | scaled (a : Expression F) (s : F)
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:57-59 (`Column::query_cell`) dispatched
    through the `impl ColumnType` arms at :269-317. Declared here rather than next
    to `Column` because Lean cannot forward-reference `Expression`, which the Rust
    can (choice 1 above).

    Every arm builds the query with `index := none`, which is what the Rust does
    (`index: None` at :271, :281, :290, :299): the query index is filled in later,
    by `query_cells` (:852-899) or by `VirtualCells::query_*` (:2633-2672), and an
    expression that reaches the verifier with `none` still in it panics at
    plonk/mod.rs:533. -/
def Column.queryCell {F : Type} (c : Column) (at' : Rotation) : Expression F :=
  match c.columnType with
  | .advice a =>
      Expression.advice { index := none, columnIndex := c.index, rotation := at', phase := a.phase }
  | .fixed => Expression.fixed { index := none, columnIndex := c.index, rotation := at' }
  | .instance => Expression.instance { index := none, columnIndex := c.index, rotation := at' }

/-- rust: proofs/src/plonk/circuit.rs:62-64 (`Column::cur`). -/
def Column.cur {F : Type} (c : Column) : Expression F := c.queryCell Rotation.cur

/-- rust: proofs/src/plonk/circuit.rs:67-69 (`Column::next`). -/
def Column.next {F : Type} (c : Column) : Expression F := c.queryCell Rotation.next

/-- rust: proofs/src/plonk/circuit.rs:72-74 (`Column::prev`). -/
def Column.prev {F : Type} (c : Column) : Expression F := c.queryCell Rotation.prev

/-- rust: proofs/src/plonk/circuit.rs:77-79 (`Column::rot(rotation: i32)`),
    which is `query_cell(Rotation(rotation))`: the raw tuple constructor, so
    `rot 0` is `Rotation.value 0` and *not* `Rotation.cur` (see the hazard note on
    `Rotation`). -/
def Column.rot {F : Type} (c : Column) (rotation : Int) : Expression F :=
  c.queryCell (Rotation.value rotation)

/-- rust: proofs/src/plonk/circuit.rs:484-486 (`Selector::expr`). -/
def Selector.expr {F : Type} (s : Selector) : Expression F := Expression.selector s

/-- rust: proofs/src/plonk/circuit.rs:619-621 (`Challenge::expr`). -/
def Challenge.expr {F : Type} (c : Challenge) : Expression F := Expression.challenge c

/-- rust: proofs/src/plonk/circuit.rs:907-918 (`Expression::evaluate`'s ten
    closure parameters) as a structure of functions (rule R9). The Rust takes
    `&impl Fn(..) -> T` for each; a Lean record of functions is the same object,
    and the field order is the parameter order so a call site can be checked
    against the Rust argument list line by line.

    The ten closures are the ten variants, in variant order, followed by the four
    recursive cases - which is exactly how the Rust is written, and it is why
    `evaluate` can be the *only* traversal this port needs: `contains_simple_selector`
    (:1243-1257) and `replace_selectors` (:2204-2235) are both defined in terms of
    it, and the verifier's gate loop (plonk/mod.rs:530) is a tenth instantiation
    of the same record. -/
structure Expression.Callbacks (F T : Type) where
  /-- rust: circuit.rs:908 (`constant: &impl Fn(F) -> T`) -/
  constant : F → T
  /-- rust: circuit.rs:909 (`selector_column: &impl Fn(Selector) -> T`) -/
  selectorColumn : Selector → T
  /-- rust: circuit.rs:910 (`fixed_column: &impl Fn(FixedQuery) -> T`) -/
  fixedColumn : FixedQuery → T
  /-- rust: circuit.rs:911 (`advice_column: &impl Fn(AdviceQuery) -> T`) -/
  adviceColumn : AdviceQuery → T
  /-- rust: circuit.rs:912 (`instance_column: &impl Fn(InstanceQuery) -> T`) -/
  instanceColumn : InstanceQuery → T
  /-- rust: circuit.rs:913 (`challenge: &impl Fn(Challenge) -> T`) -/
  challenge : Challenge → T
  /-- rust: circuit.rs:914 (`negated: &impl Fn(T) -> T`) -/
  negated : T → T
  /-- rust: circuit.rs:915 (`sum: &impl Fn(T, T) -> T`) -/
  sum : T → T → T
  /-- rust: circuit.rs:916 (`product: &impl Fn(T, T) -> T`) -/
  product : T → T → T
  /-- rust: circuit.rs:917 (`scaled: &impl Fn(T, F) -> T`) -/
  scaled : T → F → T

/-- rust: proofs/src/plonk/circuit.rs:907-1014 (`Expression::evaluate`). The
    recursion is spelled out four times in the Rust (once per recursive variant,
    each re-passing all ten closures); the port passes the record, which is the
    same traversal with the same order: `a` before `b`, and the combining closure
    applied after both. -/
def Expression.evaluate {F T : Type} (cb : Expression.Callbacks F T) : Expression F → T
  | .constant c => cb.constant c
  | .selector s => cb.selectorColumn s
  | .fixed q => cb.fixedColumn q
  | .advice q => cb.adviceColumn q
  | .instance q => cb.instanceColumn q
  | .challenge c => cb.challenge c
  | .negated a => cb.negated (Expression.evaluate cb a)
  | .sum a b => cb.sum (Expression.evaluate cb a) (Expression.evaluate cb b)
  | .product a b => cb.product (Expression.evaluate cb a) (Expression.evaluate cb b)
  | .scaled a f => cb.scaled (Expression.evaluate cb a) f

/-- rust: proofs/src/plonk/circuit.rs:1206-1220 (`Expression::degree`).
    `Constant` and `Challenge` are degree 0, every leaf query is 1, `Sum` takes the
    max and `Product` the sum - and `Negated`/`Scaled` pass through, which is what
    makes a scaled product cost the same as the product. -/
def Expression.degree {F : Type} : Expression F → Nat
  | .constant _ => 0
  | .selector _ => 1
  | .fixed _ => 1
  | .advice _ => 1
  | .instance _ => 1
  | .challenge _ => 0
  | .negated p => Expression.degree p
  | .sum a b => max (Expression.degree a) (Expression.degree b)
  | .product a b => Expression.degree a + Expression.degree b
  | .scaled p _ => Expression.degree p

/-- rust: proofs/src/plonk/circuit.rs:1243-1257 (`Expression::contains_simple_selector`),
    which is `evaluate` with `T = Bool`. The closure list is ported in order; note
    that `product` is `a || b` and not `a && b`, i.e. the question really is "does
    *any* leaf carry a simple selector", and that the `Selector` arm is the only
    one that can answer true - a selector that has already been converted to a
    fixed column is invisible to this test. -/
def Expression.containsSimpleSelector {F : Type} [BEq F] (e : Expression F) : Bool :=
  Expression.evaluate
    { constant := fun _ => false
      selectorColumn := fun s => s.isSimple
      fixedColumn := fun _ => false
      adviceColumn := fun _ => false
      instanceColumn := fun _ => false
      challenge := fun _ => false
      negated := fun a => a
      sum := fun a b => a || b
      product := fun a b => a || b
      scaled := fun a _ => a }
    e

/-- rust: proofs/src/plonk/circuit.rs:1322-1334 (`impl Neg for Expression` and
    the `&Expression` overload). Infallible: unlike `Add`/`Sub`/`Mul` below, `Neg`
    performs no check and no simplification. -/
def Expression.neg {F : Type} (e : Expression F) : Expression F := Expression.negated e

/-- rust: proofs/src/plonk/circuit.rs:1336-1350 (`impl Add for Expression`),
    plus the three reference overloads at :1352-1371, which only clone.

    Three behaviours a "tidy" port would lose, all kept:
    * the panic at :1340 when *either* side contains a simple selector;
    * the `Constant(ZERO)` short-circuit at :1341-1346, which returns the other
      operand *unchanged* rather than building a `Sum`;
    * the order of those two: the panic is checked first, so `0 + s` for a simple
      selector `s` panics instead of returning `s`. -/
def Expression.add {F : Type} [Zero F] [BEq F] (a b : Expression F) :
    Except Fault (Expression F) := do
  if a.containsSimpleSelector || b.containsSimpleSelector then
    throw (Fault.panic "proofs/src/plonk/circuit.rs:1340")
  if a == Expression.constant 0 then return b
  if b == Expression.constant 0 then return a
  return Expression.sum a b

/-- rust: proofs/src/plonk/circuit.rs:1373-1387 (`impl Sub for Expression`) and
    the overloads at :1389-1408. Note the asymmetry with `Add`: when the left side
    is zero the Rust returns `-rhs` (a `Negated` node), not a negated copy of the
    simplification, so `0 - x` is `Negated(x)` while `x + 0` is `x`. -/
def Expression.sub {F : Type} [Zero F] [BEq F] (a b : Expression F) :
    Except Fault (Expression F) := do
  if a.containsSimpleSelector || b.containsSimpleSelector then
    throw (Fault.panic "proofs/src/plonk/circuit.rs:1377")
  if a == Expression.constant 0 then return Expression.neg b
  if b == Expression.constant 0 then return a
  return Expression.sum a (Expression.neg b)

/-- rust: proofs/src/plonk/circuit.rs:1410-1427 (`impl Mul for Expression`) and
    the overloads at :1429-1448. The guard here is `&&`, not `||`: multiplying a
    simple selector by *one* selector-carrying expression is legal (that is how a
    gate is enabled), while multiplying two of them is the panic at :1414. Then
    three short-circuits, in this order: zero, `Constant(ONE)` left, `Constant(ONE)`
    right. -/
def Expression.mul {F : Type} [Zero F] [One F] [BEq F] (a b : Expression F) :
    Except Fault (Expression F) := do
  if a.containsSimpleSelector && b.containsSimpleSelector then
    throw (Fault.panic "proofs/src/plonk/circuit.rs:1414")
  if a == Expression.constant 0 || b == Expression.constant 0 then
    return Expression.constant 0
  if a == Expression.constant 1 then return b
  if b == Expression.constant 1 then return a
  return Expression.product a b

/-- rust: proofs/src/plonk/circuit.rs:1450-1462 (`impl Mul<F> for Expression`
    and the `&Expression` overload). No checks and no short-circuits: `x * 0` is a
    `Scaled` node here even though `x * Constant(0)` would collapse to
    `Constant(0)` in `mul` above, and that difference is observable through
    `degree`. -/
def Expression.scaledMul {F : Type} (a : Expression F) (s : F) : Expression F :=
  Expression.scaled a s

/-! rust: proofs/src/plonk/circuit.rs:852-899 (`Expression::query_cells`) - NOT
    verifier-reachable, so no body. Evidence: grepping the reachable set for
    `query_cells` returns nothing; its only callers are `create_gate`'s map at
    circuit.rs:2145 and the two lookup builders at :1935, :1941, :1990 and :1996,
    all of which run while the constraint system is being *built*. It is the fn
    that turns a `none` query index into a real one by calling
    `query_*_index` on the meta, i.e. it is the mutation the verifier's read-only
    view of a `ConstraintSystem` assumes has already happened. Recorded because
    it is the reason `Expression.evaluate` can panic at plonk/mod.rs:533: an
    expression that never went through `query_cells` still has `index := none`. -/

/-! rust: proofs/src/plonk/circuit.rs:1017-1128 (`Expression::evaluate_lazy`) -
    NOT verifier-reachable: grepping the reachable set for `evaluate_lazy` returns
    nothing, and its only caller in the crate is plonk/evaluation.rs (the prover's
    numerator evaluator). Skipped rather than ported for the same reason the
    prover's `Polynomial` was: putting it in L0 would import prover code. Worth
    noting for whoever does port it, because it is *not* equivalent to `evaluate`:
    the `Product` arm (:1085-1112) first swaps its operands so the cheaper one is
    evaluated first (`a.complexity() <= b.complexity()`), short-circuits to the
    zero value if that one comes back zero, and so can skip a subterm entirely.
    Two consequences: the result depends on `complexity` (a heuristic) rather than
    only on the tree, and the `T: PartialEq` bound means the zero value is a
    *parameter*, so a caller passing the wrong `zero` silently prunes. -/

/-! rust: proofs/src/plonk/circuit.rs:1141-1204 (`write_identifier` and
    `identifier`) - NOT verifier-reachable: grepping the reachable set for
    `identifier()` returns nothing. `identifier` is used by `dev` and by the
    prover's cache keys. Recorded because it is a second string-rendering surface
    with the same R-1 problem as `Debug`: the `Constant` and `Scaled` arms print
    the field element with `{scalar:?}`, so the bytes depend on the field's
    `Debug` impl, and `Rotation` is printed as a raw `i32` (`fixed[3][-1]`). -/

/-! rust: proofs/src/plonk/circuit.rs:1222-1236 (`Expression::complexity`) - NOT
    verifier-reachable: grepping the reachable set for `complexity` returns
    nothing; its only caller is `evaluate_lazy` (skipped immediately above). The
    constants are worth recording anyway, because they are a cost model that no
    test pins: `Negated` +5, `Sum` +15, `Product` +30, `Scaled` +30, leaves 1,
    `Constant`/`Challenge` 0. -/

/-! rust: proofs/src/plonk/circuit.rs:1238-1241 (`Expression::square`) - NOT
    verifier-reachable. The five `square()` hits in the reachable set
    (plonk/permutation.rs:213, poly/domain.rs:61, :73, :82, poly/kzg/params.rs:121)
    are all `Field::square` on a scalar, not `Expression::square`; the only
    caller of the latter is plonk/evaluation.rs. Ported note: `square(self) =
    self.clone() * self` goes through `Mul`, so squaring an expression that
    contains a simple selector hits the "two expressions containing simple
    selectors" panic at :1414 - a surprising way to fail. -/

/-! rust: proofs/src/plonk/circuit.rs:1259-1314 (`impl Debug for Expression`) -
    not ported. `Debug` is a formatting trait and the only verifier-reachable
    formatting of a constraint system is `PinnedConstraintSystem`'s `Debug` at
    plonk/mod.rs:272, which feeds `transcript_repr`; that is docs/REVIEW.md R-1
    (owner: Exec/VerifyingKey) and the plan takes `transcript_repr` as given
    (Section 1). Recorded because the impl is not a faithful rendering of the
    enum: the `Fixed`/`Advice`/`Instance` arms deliberately "skip the enum
    variant and print the query struct directly to maintain backwards
    compatibility" (:1264), print the index under the name `query_index`, and
    hide an advice query's phase when it is `FirstPhase` (:1287-1289) - so two
    expressions that differ only by a first-phase annotation render identically. -/

/-! rust: proofs/src/plonk/circuit.rs:1316-1320 (`impl From<u64> for Expression`)
    and :1464-1475 (`impl Sum`, `impl Product`) - NOT verifier-reachable.
    `From::from` is the `Expression::from(1)` sugar used by circuit.rs's own
    `#[cfg(test)] mod tests` (:2702-2745, the only place in the crate that
    exercises `iter().sum()` and `iter().product()` on expressions) and by
    circuit-construction code in solidity-verifier/src/test.rs. The two iterator
    folds are `reduce(op).unwrap_or(Constant(0))` and
    `reduce(op).unwrap_or(Constant(1))`, i.e. left-associated and using the
    operator impls above, so they inherit their panics and their
    short-circuits; `sum` of an empty iterator is `Constant(ZERO)`, not an error.
    Rule R5 note for whoever ports `From<u64>`: `F::from(value)` for a `Field` is
    the canonical reduction of the `u64` mod p, which over `Fr p` is
    `Nat.cast`. -/

/-- rust: proofs/src/plonk/circuit.rs:1478-1492 (`struct VirtualCell { column:
    Column<Any>, rotation: Rotation }`), field order preserved, plus the
    `From<(Col, Rotation)>` impl at :1484-1492 (which only widens the kind, a
    no-op here because `Column` already stores an `Any`). -/
structure VirtualCell where
  /-- rust: circuit.rs:1479 (`column: Column<Any>`) -/
  column : Column
  /-- rust: circuit.rs:1480 (`rotation: Rotation`) -/
  rotation : Rotation
  deriving BEq

/-- rust: proofs/src/plonk/circuit.rs:1497-1501 (`struct Constraint<F> { name:
    String, poly: Expression<F> }`), field order preserved. The three `From`
    impls at :1503-1527 (`From<Expression>` with an empty name,
    `From<(S, Expression)>`, and `From<Expression> for Vec<Constraint>`) are
    gate-construction sugar reached only through `create_gate`, so they are not
    ported; the empty-name default they encode is what
    solidity-verifier/src/lowering/quotient_listing/mod.rs:742 tests for with
    `if constraint_name.is_empty()`. -/
structure Constraint (F : Type) where
  /-- rust: circuit.rs:1498 (`name: String`) -/
  name : String
  /-- rust: circuit.rs:1499 (`poly: Expression<F>`) -/
  poly : Expression F

/-- rust: proofs/src/plonk/circuit.rs:1530-1535 (`enum SelectorType {
    Multiplicative(Selector), Additive(Selector), None }`), variant order
    preserved. This is the discriminator that decides whether a gate is multiplied
    by a selector, routed through a trash argument, or left alone - see
    `VirtualCells.apply_selector_to_constraints` at :2678-2700. -/
inductive SelectorType where
  | multiplicative (s : Selector)
  | additive (s : Selector)
  | none

/-- rust: proofs/src/plonk/circuit.rs:1571-1575 (`struct Constraints<F> {
    selector: SelectorType, constraints: Vec<Constraint<F>> }`), field order
    preserved. The three constructors at :1583-1616 (`with_selector`,
    `with_additive_selector`, `without_selector`) are the user-facing gate-building
    API and are not verifier-reachable (their only callers are `create_gate`
    closures: solidity-verifier/src/test.rs:255, :511, :559, :5401, :5418 and
    plonk/circuit.rs's own `mod tests`), so they are skipped.

    The doc comment on `with_additive_selector` (:1591-1600) is the clearest
    statement in the file of what a trash argument *is* - "the enforced constraint
    will have the form `(sum_i r^i constraints[i]) - (1 - selector) * trash`,
    where `r` is a Fiat-Shamir challenge and `trash` is an unrestricted column" -
    and it is the shape plan 9.3's `T.selector` / `T.constraints` conjunct and
    `Exec/Trash` have to reproduce. -/
structure Constraints (F : Type) where
  /-- rust: circuit.rs:1572 (`selector: SelectorType`) -/
  selector : SelectorType
  /-- rust: circuit.rs:1573 (`constraints: Vec<Constraint<F>>`) -/
  constraints : Array (Constraint F)

/-- rust: proofs/src/plonk/circuit.rs:1618-1627 (`struct Gate<F>`), field order
    preserved: `name`, `constraint_names`, `polys`, `queried_selectors`,
    `queried_cells`. The placeholder had only three of the five; `constraint_names`
    is not decoration - `Gate::constraint_name` below is reached from the
    generator's diagnostics (solidity-verifier/src/lowering/diagnostics.rs:130),
    and `queried_cells` is what `Gate::queried_cells` (:1651-1653) returns.

    The Rust doc on `queried_selectors` (:1623-1624) explains why selectors are
    tracked separately from cells: "so that we can use them to trigger debug
    checks on gates". The verifier reads them at plonk/mod.rs:543 to pick the
    simple selector that multiplies each identity, so the *order* inside the
    array is observable and is preserved. -/
structure Gate (F : Type) where
  /-- rust: circuit.rs:1620 (`name: String`) -/
  name : String
  /-- rust: circuit.rs:1621 (`constraint_names: Vec<String>`) -/
  constraintNames : Array String
  /-- rust: circuit.rs:1622 (`polys: Vec<Expression<F>>`) -/
  polys : Array (Expression F)
  /-- rust: circuit.rs:1626 (`queried_selectors: Vec<Selector>`) -/
  queriedSelectors : Array Selector
  /-- rust: circuit.rs:1627 (`queried_cells: Vec<VirtualCell>`) -/
  queriedCells : Array VirtualCell

/-! rust: proofs/src/plonk/circuit.rs:1631-1633 (`Gate::name`) - the projection of
    the `name` field, so no separate def. -/

/-- rust: proofs/src/plonk/circuit.rs:1636-1638 (`Gate::constraint_name`).
    `self.constraint_names[constraint_index]` is a slice index, so an out-of-range
    index is a panic (rule R4) rather than a default; the generator walks
    `0..gate.polynomials().len()` (diagnostics.rs:125) and the two arrays are kept
    the same length by `create_gate`'s `unzip` at :2141-2147, so the panic is a
    malformed-`Gate` case rather than a normal one. -/
def Gate.constraintName {F : Type} (g : Gate F) (constraintIndex : Nat) :
    Except Fault String :=
  match g.constraintNames[constraintIndex]? with
  | some s => .ok s
  | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:1637")

/-- rust: proofs/src/plonk/circuit.rs:1641-1643 (`Gate::polynomials`, returning
    `&[Expression<F>]`). Named apart from the field so the accessor and the field
    keep their Rust distinction. -/
def Gate.polynomials {F : Type} (g : Gate F) : Array (Expression F) := g.polys

/-! rust: proofs/src/plonk/circuit.rs:1646-1648 (`Gate::queried_selectors`) and
    :1651-1653 (`Gate::queried_cells`) - both are the projections of the
    same-named fields, so neither needs a def. -/

/-- rust: proofs/src/plonk/circuit.rs:1656-1675 (`struct SelectorFlag(bool,
    Option<usize>)` and its two accessors), tuple field order preserved: `.0` is
    the "simple" flag and `.1` the fixed-column index once the selector has been
    converted. `is_simple()` (:1662-1664) and `col_idx()` (:1670-1672) are the
    projections.

    The pair is what makes `has_simple_selector_col` and `num_simple_selectors`
    answer different questions: a *complex* selector that was converted to a fixed
    column has `isSimple = false` and a `col_idx`, and it counts as neither. -/
structure SelectorFlag where
  /-- rust: circuit.rs:1657 (`.0: bool`) -/
  isSimple : Bool
  /-- rust: circuit.rs:1657 (`.1: Option<usize>`) -/
  colIdx : Option Nat
  deriving BEq

/-! ### The three argument structs

`ConstraintSystem` names one type from each of plonk/permutation.rs,
plonk/logup.rs and plonk/trash.rs as a field type, and `degree` /
`blinding_factors` call into all three, so they are ported here (structural
choice 3 in this file's header). Only what the verifier path and the constraint
system need is ported; the evaluated/committed halves of those modules belong to
Exec/{Permutation,Logup,Trash}. -/

/-- rust: proofs/src/plonk/permutation.rs:33-36 (`struct Argument { columns:
    Vec<Column<Any>> }`). The whole struct is one field: the permutation
    argument's *data* in the constraint system is just the list of
    equality-enabled columns, in the order `enable_equality` pushed them
    (circuit.rs:1886-1894 + permutation.rs:81-86). The sigma polynomials and
    their commitments live in `permutation::VerifyingKey` (plonk/mod.rs:185),
    not here. -/
structure PermutationArgument where
  /-- rust: permutation.rs:35 (`columns: Vec<Column<Any>>`) -/
  columns : Array Column
  deriving BEq

/-- rust: proofs/src/plonk/permutation.rs:39-41 (`Argument::new`) - the empty
    column list, which is also what `ConstraintSystem::default` needs. -/
def PermutationArgument.new : PermutationArgument := { columns := #[] }

/-- rust: proofs/src/plonk/permutation.rs:46-80 (`Argument::required_degree`).
    Reached from `ConstraintSystem::degree` (circuit.rs:2445). The body is a
    long comment and a constant: "There are constraints of degree 3 regardless of
    the number of columns involved" (:78-79), because the argument always
    contains the degree-3 `l_last * (z'^2 - z')` constraint. So the field
    `columns` does *not* affect the required degree, which is what makes
    `degree >= 3` hold for every constraint system in existence - including the
    empty one, and including one with no permutation columns at all. -/
def PermutationArgument.requiredDegree (_ : PermutationArgument) : Nat := 3

/-- rust: proofs/src/plonk/permutation.rs:88-90 (`Argument::get_columns`).
    Reachable at solidity-verifier/src/lowering/protocol/mod.rs:333. -/
def PermutationArgument.getColumns (p : PermutationArgument) : Array Column := p.columns

/-! rust: proofs/src/plonk/permutation.rs:81-86 (`Argument::add_column`) - NOT
    verifier-reachable: its only caller is `ConstraintSystem::enable_equality`
    (circuit.rs:1893), which runs while the constraint system is built. Recorded
    because it deduplicates with `contains` *before* pushing, so the column order
    is first-occurrence order and a repeated `enable_equality` on the same column
    does not add a second permutation column. -/

/-- Port scaffolding for the two logup degree helpers: the Rust
    `.flat_map(..).map(|e| e.degree()).max()` over a nested vector, kept as an
    `Option` because `unwrap_or(1)` fires only when the iterator is *empty*, not
    when every degree is 0 - and the difference is a division-by-zero panic at
    logup.rs:237. Lean's `max` over an empty fold would silently give 0 instead of
    `None`, which is exactly the bug this avoids. -/
def maxDegreeNested {F : Type} : Array (Array (Expression F)) → Option Nat :=
  Array.foldl (fun inner acc =>
      Array.foldl (fun a e => match a with
        | none => some (Expression.degree e)
        | some m => some (max m (Expression.degree e)))
        inner acc)
    none

/-- Port scaffolding, as `maxDegreeNested` but over a flat vector (logup.rs:264,
    trash.rs:32). -/
def maxDegreeFlat {F : Type} : Array (Expression F) → Option Nat :=
  Array.foldl (fun acc e => match acc with
    | none => some (Expression.degree e)
    | some m => some (max m (Expression.degree e)))
    none

/-- rust: `usize::next_power_of_two` (std), used by plonk/logup.rs:224 and
    :268. The std fn maps 0 and 1 to 1 and otherwise rounds up to the next power
    of two; it panics if the result would overflow, which needs an input above
    `2^63` and so cannot happen for a constraint degree (rule R5). -/
def nextPowerOfTwo (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

/-- Port scaffolding for `chunkByDegree` and `numChunks`: Rust's
    `slice::chunks(n)`, which **panics when `n == 0`** rather than looping
    forever. Lean has no `List.chunksOf` in this dependency set at all, so the
    splitting is written out; the fuel is `size / n + 1`, which is an upper bound
    on the number of chunks once `n >= 1`, and it only keeps the definition
    structurally terminating (rule R10). -/
def rustChunks {α : Type} (n : Nat) (site : String) (xs : Array α) :
    Except Fault (Array (Array α)) :=
  if n = 0 then .error (Fault.panic site) else .ok (go (xs.size / n + 1) n xs #[])
where
  go : Nat → Nat → Array α → Array (Array α) → Array (Array α)
    | 0, _, _, acc => acc
    | fuel + 1, n, xs, acc =>
        if xs.size = 0 then acc else go fuel n (xs.drop n) (acc.push (xs.take n))

/-- rust: proofs/src/plonk/logup.rs:171-176 (`struct BatchedArgument<F> { name,
    selector, input_expressions, table_expressions }`), field order preserved.
    This is the `cs.lookups` element type (circuit.rs:1710).

    `input_expressions` is the transposed layout the constructor documents at
    logup.rs:286-291: `[parallel_lookup][lookup_width]`, i.e. the outer index is
    the *width* dimension after `BatchedArgument::new` transposes the caller's
    `[(inputs, table)]` map. Getting that transpose wrong is silent: the same
    expressions are present, grouped differently, and only `num_chunks` and the
    helper-polynomial degree notice. -/
structure LogupBatchedArgument (F : Type) where
  /-- rust: logup.rs:172 (`name: String`) -/
  name : String
  /-- rust: logup.rs:173 (`selector: Expression<F>`) -/
  selector : Expression F
  /-- rust: logup.rs:174 (`input_expressions: Vec<Vec<Expression<F>>>`) -/
  inputExpressions : Array (Array (Expression F))
  /-- rust: logup.rs:175 (`table_expressions: Vec<Expression<F>>`) -/
  tableExpressions : Array (Expression F)

/-- rust: proofs/src/plonk/logup.rs:223-238 (`nb_parallel_lookups_per_chunk`).
    Reached from `degree_batched_argument` (:241) and `num_chunks` (:316), hence
    through `ConstraintSystem::degree` and `ConstraintSystem::blinding_factors`
    into the verifier.

    Two panic sites, both easy to miss and both reachable from a malformed-but-
    accepted constraint system:
    * `:237` `(max_degree - 1) / lookup_degree` is a **division by zero** when
      every input expression has degree 0, i.e. when a lookup's inputs are all
      constants or challenges. `unwrap_or(1)` does *not* protect this: the
      iterator is non-empty, so `max()` is `Some(0)`.
    * `:224` `cs_degree - 1` is a `usize` subtraction. In the reference
      (release) profile it wraps to `2^64 - 1` when `cs_degree == 0` and then
      `next_power_of_two` panics with a capacity overflow; in debug it panics
      immediately. Neither is reachable, because `ConstraintSystem::degree` ends
      in `.unwrap_or(1)` and takes `max` with the permutation's constant 3, so
      `cs_degree >= 3` always. The port uses saturating `Nat` subtraction and
      says so here rather than emulating the wrap (rule R5). -/
def LogupBatchedArgument.nbParallelLookupsPerChunk {F : Type}
    (L : LogupBatchedArgument F) (csDegree : Nat) : Except Fault Nat := do
  -- logup.rs:224
  let maxDegree := nextPowerOfTwo (csDegree - 1) + 1
  -- logup.rs:226-232
  let lookupDegree := (maxDegreeNested L.inputExpressions).getD 1
  -- logup.rs:237
  if lookupDegree = 0 then
    throw (Fault.panic "proofs/src/plonk/logup.rs:237")
  return (maxDegree - 1) / lookupDegree

/-- rust: proofs/src/plonk/logup.rs:241-270 (`degree_batched_argument`). Reached
    from `ConstraintSystem::degree` (circuit.rs:2462).

    The rounding at :266-269 is the subtle part and it is *not* a plain
    `next_power_of_two`: the Rust rounds `max(helper, accumulator) - 1` up to a
    power of two and adds 1 back, i.e. it picks the smallest degree `d > 1` such
    that `d - 1` is a power of two, so that a chunked helper still has degree
    exactly `cs_degree`. The accumulator term is `2 + selector.degree() +
    table_degree` (:265-267), which is why a degree-1 selector can push the whole
    system to degree 4 even when the helper constraint only needs 3. -/
def LogupBatchedArgument.degreeBatchedArgument {F : Type}
    (L : LogupBatchedArgument F) (csDegree : Nat) : Except Fault Nat := do
  let lookupDegree := (maxDegreeNested L.inputExpressions).getD 1
  let nb ← L.nbParallelLookupsPerChunk csDegree
  let helperConstraintDegree := nb * lookupDegree + 1
  let tableDegree := (maxDegreeFlat L.tableExpressions).getD 1
  let accumulatorConstraintDegree := 2 + L.selector.degree + tableDegree
  return nextPowerOfTwo (max helperConstraintDegree accumulatorConstraintDegree - 1) + 1

/-- rust: proofs/src/plonk/logup.rs:316-319 (`num_chunks`). Reached from
    `ConstraintSystem::blinding_factors` (circuit.rs:2496), which the verifier
    calls at plonk/verifier.rs:443, and from solidity-verifier
    src/lowering/protocol/mod.rs:344.

    A third panic site joins the two in `nbParallelLookupsPerChunk`:
    `.chunks(nb)` at :318 panics when `nb == 0`, which happens whenever
    `lookup_degree > max_degree - 1` - e.g. a degree-3 input expression in a
    system whose degree-without-lookup is 3 gives `nb = (3 - 1) / 3 = 0`. So a
    circuit whose lookup inputs are as steep as the system's own degree makes the
    *verifier* abort while it is computing blinding factors, before it has looked
    at the proof at all. -/
def LogupBatchedArgument.numChunks {F : Type}
    (L : LogupBatchedArgument F) (csDegree : Nat) : Except Fault Nat := do
  let nb ← L.nbParallelLookupsPerChunk csDegree
  if nb = 0 then
    throw (Fault.panic "proofs/src/plonk/logup.rs:318")
  return divCeil L.inputExpressions.size nb

/-- rust: proofs/src/plonk/logup.rs:189-199 (`struct ChunkedArgument<F>`), field
    order preserved. Produced by `chunk_by_degree` and consumed by the verifier at
    plonk/verifier.rs:188 and plonk/mod.rs:572 (`.chunk_by_degree(vk.cs_degree)`). -/
structure LogupChunkedArgument (F : Type) where
  /-- rust: logup.rs:194 (`name: String`) -/
  name : String
  /-- rust: logup.rs:195 (`selector: Expression<F>`) -/
  selector : Expression F
  /-- rust: logup.rs:197 (`input_expression_chunks: Vec<Vec<Vec<Expression<F>>>>`) -/
  inputExpressionChunks : Array (Array (Array (Expression F)))
  /-- rust: logup.rs:198 (`table_expressions: Vec<Expression<F>>`) -/
  tableExpressions : Array (Expression F)

/-- rust: proofs/src/plonk/logup.rs:326-338 (`chunk_by_degree`). The clone-only
    sibling of `num_chunks`, with the same `chunks(0)` panic at :329. -/
def LogupBatchedArgument.chunkByDegree {F : Type}
    (L : LogupBatchedArgument F) (csDegree : Nat) : Except Fault (LogupChunkedArgument F) := do
  let nb ← L.nbParallelLookupsPerChunk csDegree
  let chunks ← rustChunks nb "proofs/src/plonk/logup.rs:329" L.inputExpressions
  return { name := L.name, selector := L.selector,
            inputExpressionChunks := chunks, tableExpressions := L.tableExpressions }

/-- rust: proofs/src/plonk/logup.rs:352-354 (`ChunkedArgument::num_chunks`) - the
    length of the pre-split chunks. Note there are two `num_chunks` in the Rust
    with *different* signatures: this one takes no argument because the splitting
    already happened, and the one on `BatchedArgument` takes `cs_degree`. -/
def LogupChunkedArgument.numChunks {F : Type} (c : LogupChunkedArgument F) : Nat :=
  c.inputExpressionChunks.size

/-! rust: proofs/src/plonk/logup.rs:277-311 (`BatchedArgument::new`) and
    :341-349, :356-368, :371-379 (the `selector_expression` /
    `table_expressions` / `input_expression_chunks` accessors) - the constructor is
    NOT verifier-reachable (its only callers are circuit.rs:1940 and :2000, inside
    `batched_lookup` and `batch_lookup_any`) and the accessors are the projections
    of the same-named fields in the port.

    Recorded for the construction port, because `new` has two sharp edges:
    `input_expressions[0].len()` at :291 is an **index panic on an empty table
    map**, so `lookup(.., None, vec![])` aborts rather than producing a vacuous
    argument; and the `assert_eq!(width.len(), nb_parallel_lookups)` at :296 makes
    a ragged map panic too. The transpose it performs is the reason
    `LogupBatchedArgument.inputExpressions` is indexed the way it is, and a
    `ChunkedArgument` built by hand with the wrong nesting reproduces no Rust
    panic - it just computes different degrees. -/

/-- rust: proofs/src/plonk/trash.rs:10-16 (`struct Argument<F> { name,
    selector, constraint_expressions }`), field order preserved. This is the
    `cs.trashcans` element type (circuit.rs:1716).

    The placeholder in this file had trashcans as a bare
    `(String, Expression, Array Expression)` tuple, which carried the same data
    but no names; plan 9.3 states the conjunct against `T.selector` and
    `T.constraints`, so the field names now matter and the Rust names win under
    rule R2 (`constraint_expressions`, not `constraints`). -/
structure TrashArgument (F : Type) where
  /-- rust: trash.rs:12 (`name: String`) -/
  name : String
  /-- rust: trash.rs:13 (`selector: Expression<F>`) -/
  selector : Expression F
  /-- rust: trash.rs:14 (`constraint_expressions: Vec<Expression<F>>`) -/
  constraintExpressions : Array (Expression F)

/-- rust: proofs/src/plonk/trash.rs:31-34 (`Argument::required_degree`). Reached
    from `ConstraintSystem::degree` (circuit.rs:2446). `max(2, ..)` because the
    `(1 - q) * trash` term is always degree 2, and `unwrap_or(0)` - not 1 - for
    an argument with no constraints, so an empty trashcan still contributes 2. -/
def TrashArgument.requiredDegree {F : Type} (t : TrashArgument F) : Nat :=
  max 2 ((maxDegreeFlat t.constraintExpressions).getD 0)

/-! rust: proofs/src/plonk/trash.rs:19-27 (`Argument::new`) and :37-48
    (`name()`, `selector()`, `constraint_expressions()`) - the constructor is not
    verifier-reachable (its only caller is circuit.rs:2696, inside
    `VirtualCells::apply_selector_to_constraints`) and the three accessors are
    the projections of the same-named fields here. -/

/-! ### ConstraintSystem -/

/-- rust: proofs/src/plonk/circuit.rs:1677-1727 (`struct ConstraintSystem<F>`),
    all twenty fields in source order (rule R1) - the plan names this range
    explicitly, and Section 9.3 states the relation against these fields.

    Three notes on the shapes:
    * `adviceQueries`, `instanceQueries` and `fixedQueries` are
      `Vec<(Column<Advice>, Rotation)>` etc. in Rust, where the kind is in the
      type. Here they are `Array (Column × Rotation)` and the kind lives in
      the `Column` (choice 2 above), which is what lets `getAnyQueryIndex` dispatch
      on `column.columnType` the way the Rust dispatches on `column.column_type()`.
    * `numAdviceQueries` is a *private* Rust field (no `pub(crate)`, :1699) and is
      the only field the placeholder omitted. It is load-bearing: it is what
      `blinding_factors` reads (`num_advice_queries.iter().max()`, :2474), and it
      is bumped by `query_advice_index` (:2057) rather than derived from
      `adviceQueries`, so it can disagree with it in a hand-built system.
    * `generalColumnAnnotations` is a `HashMap` in Rust. Rule R6 allows a
      `HashMap` only where iteration order cannot be observed, and here it can:
      nothing in the reachable set reads it at all (grep for
      `general_column_annotations` outside circuit.rs returns nothing), so the
      port stores an insertion-ordered `Array` and the choice is unobservable.
      The two writers (`annotate_lookup_column` :2291-2303 and
      `annotate_lookup_any_column` :2305-2319) are construction, and both
      `insert`, i.e. they overwrite an existing key in place rather than appending -
      a detail that only matters if the map is ever rendered. -/
structure ConstraintSystem (F : Type) where
  /-- rust: circuit.rs:1678 (`num_fixed_columns: usize`) -/
  numFixedColumns : Nat
  /-- rust: circuit.rs:1679 (`num_advice_columns: usize`) -/
  numAdviceColumns : Nat
  /-- rust: circuit.rs:1680 (`num_instance_columns: usize`) -/
  numInstanceColumns : Nat
  /-- rust: circuit.rs:1681 (`num_selectors: usize`) -/
  numSelectors : Nat
  /-- rust: circuit.rs:1682 (`selector_flags: Vec<SelectorFlag>`) -/
  selectorFlags : Array SelectorFlag
  /-- rust: circuit.rs:1683 (`num_challenges: usize`) -/
  numChallenges : Nat
  /-- rust: circuit.rs:1686 (`unblinded_advice_columns: Vec<usize>`) -/
  unblindedAdviceColumns : Array Nat
  /-- rust: circuit.rs:1690 (`advice_column_phase: Vec<sealed::Phase>`) -/
  adviceColumnPhase : Array Phase
  /-- rust: circuit.rs:1692 (`challenge_phase: Vec<sealed::Phase>`) -/
  challengePhase : Array Phase
  /-- rust: circuit.rs:1694 (`gates: Vec<Gate<F>>`) -/
  gates : Array (Gate F)
  /-- rust: circuit.rs:1695 (`advice_queries: Vec<(Column<Advice>, Rotation)>`) -/
  adviceQueries : Array (Column × Rotation)
  /-- rust: circuit.rs:1699 (`num_advice_queries: Vec<usize>`, private) -/
  numAdviceQueries : Array Nat
  /-- rust: circuit.rs:1700 (`instance_queries: Vec<(Column<Instance>, Rotation)>`) -/
  instanceQueries : Array (Column × Rotation)
  /-- rust: circuit.rs:1701 (`fixed_queries: Vec<(Column<Fixed>, Rotation)>`) -/
  fixedQueries : Array (Column × Rotation)
  /-- rust: circuit.rs:1704 (`permutation: permutation::Argument`) -/
  permutation : PermutationArgument
  /-- rust: circuit.rs:1708 (`lookups: Vec<logup::BatchedArgument<F>>`) -/
  lookups : Array (LogupBatchedArgument F)
  /-- rust: circuit.rs:1716 (`trashcans: Vec<trash::Argument<F>>`) -/
  trashcans : Array (TrashArgument F)
  /-- rust: circuit.rs:1720 (`general_column_annotations:
      HashMap<metadata::Column, String>`) -/
  generalColumnAnnotations : Array (Column × String)
  /-- rust: circuit.rs:1724 (`constants: Vec<Column<Fixed>>`) -/
  constants : Array Column
  /-- rust: circuit.rs:1726 (`minimum_degree: Option<usize>`) -/
  minimumDegree : Option Nat

/-! rust: proofs/src/plonk/circuit.rs:1730-1806 (`PinnedConstraintSystem`,
    `impl Debug for PinnedConstraintSystem` and `PinnedGates`) - NOT ported.
    `ConstraintSystem::pinned` (:1852-1876) is reached from plonk/mod.rs:272, where
    its `Debug` rendering is hashed into `vk.transcript_repr`, but plan Section 1
    takes `transcript_repr` as given and docs/REVIEW.md R-1 assigns the byte-exact
    `{:?}` question to Exec/VerifyingKey; duplicating it here would put a second,
    unverified copy of the same formatting in the tree. Recorded because the pin
    set is *not* the whole struct: `pinned()` omits `selector_flags`,
    `unblinded_advice_columns`, `num_advice_queries`,
    `general_column_annotations` and `constants` is included even though the
    verifier never reads it, so two constraint systems that differ only in those
    fields hash to the same `transcript_repr`. `PinnedGates` (:1798-1806) in
    addition drops each gate's `constraint_names` and `queried_selectors` from the
    hash, keeping only `polys`. -/

/-- rust: proofs/src/plonk/circuit.rs:1808-1833 (`impl Default for
    ConstraintSystem`). Every field is the empty value; the Rust literal lists
    them in a different order than the struct declares them (`fixed_queries`
    before `advice_queries` at :1820-1821), which is why the struct order above
    is the one the port follows. Named `default` rather than `empty` to keep R2. -/
def ConstraintSystem.default {F : Type} : ConstraintSystem F :=
  { numFixedColumns := 0
    numAdviceColumns := 0
    numInstanceColumns := 0
    numSelectors := 0
    selectorFlags := #[]
    numChallenges := 0
    unblindedAdviceColumns := #[]
    adviceColumnPhase := #[]
    challengePhase := #[]
    gates := #[]
    adviceQueries := #[]
    numAdviceQueries := #[]
    instanceQueries := #[]
    fixedQueries := #[]
    permutation := PermutationArgument.new
    lookups := #[]
    trashcans := #[]
    generalColumnAnnotations := #[]
    constants := #[]
    minimumDegree := none }

/-! ### impl ConstraintSystem (rust: proofs/src/plonk/circuit.rs:1835-2607) -/

/-- rust: proofs/src/plonk/circuit.rs:1838-1843 (`has_simple_selector_col`).
    Reachable at plonk/verifier.rs:409 and :635 and at solidity-verifier
    src/lowering/protocol/mod.rs:372: it is how the verifier knows that a fixed
    column is really a converted selector whose evaluation is 1 and is therefore
    *not* read from the proof.

    The Rust is `any(f.is_simple() && f.col_idx() == Some(col_idx))`, i.e. both
    halves must hold on the *same* flag; a complex selector that was converted to
    this column does not count. -/
def ConstraintSystem.hasSimpleSelectorCol {F : Type} (cs : ConstraintSystem F)
    (colIdx : Nat) : Bool :=
  cs.selectorFlags.toList.any (fun f => f.isSimple && f.colIdx == some colIdx)

/-- rust: proofs/src/plonk/circuit.rs:1845-1847 (`num_simple_selectors`).
    Reachable at plonk/verifier.rs:400 (it is subtracted from
    `num_fixed_columns` to decide how many fixed evaluations to read) and at
    plonk/linearization/verifier.rs:58 (the size of the linearization MSM).

    `filter(..).count()`, not `len()` of anything: only the *simple* flags count,
    so a complex selector converted to a fixed column is still read from the
    transcript. -/
def ConstraintSystem.numSimpleSelectors {F : Type} (cs : ConstraintSystem F) : Nat :=
  (cs.selectorFlags.filter (fun f => f.isSimple)).size

/-! rust: proofs/src/plonk/circuit.rs:1852-1876 (`pinned`), :1878-1883
    (`enable_constant`), :1886-1894 (`enable_equality`), :1899-1913 (`lookup`),
    :1915-1955 (`batched_lookup`), :1957-1971 (`lookup_any`) and :1973-2007
    (`batch_lookup_any`) - NOT verifier-reachable, so no bodies. Evidence: grepping
    the reachable set for `enable_constant`, `batched_lookup`, `batch_lookup_any`
    and `lookup_any` returns nothing; `enable_equality` appears only as a
    `&mut self` mutation inside circuit.rs itself; the four lookup builders are
    called from circuit-construction closures in solidity-verifier/src/test.rs:549
    and src/lowering/protocol/mod.rs (inside its `mod tests`), never from a
    verify path - the verifier only ever *reads* `cs.lookups`.

    Two things those builders do that the port has to respect when it ever builds
    a `ConstraintSystem` by hand, both from `batched_lookup` (:1915-1955):
    * every input expression is checked with `assert!(!input.contains_simple_selector(),
      "expression containing simple selector supplied to lookup argument")` at
      :1927-1930, and the *table* expression the same way at :1984-1992 - except
      that `batch_lookup_any` uses an `if .. panic!` for the table (:1991-1993)
      and an `assert!` for the inputs, so the two paths differ in message only.
    * the table side of a `lookup` is re-queried through
      `cells.query_fixed(table.inner(), Rotation::cur())` at :1925, which is what
      puts a lookup table column into `fixed_queries` - and therefore into the
      evaluation vector the verifier reads. -/

/-- rust: proofs/src/plonk/circuit.rs:2009-2022 (`query_fixed_index`). The Rust
    takes `&mut self` and returns `usize`; the port threads the system through
    explicitly and returns the pair, which is the same observable behaviour
    (rule R3). Cannot fail: a miss appends. -/
def ConstraintSystem.queryFixedIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : ConstraintSystem F × Nat :=
  match cs.fixedQueries.toList.findIdx? (fun q => q == (column, at')) with
  | some i => (cs, i)
  | none => ({ cs with fixedQueries := cs.fixedQueries.push (column, at') },
      cs.fixedQueries.size)

/-- rust: proofs/src/plonk/circuit.rs:2024-2038 (`query_advice_index`).

    Panic site kept: `:2033` `self.num_advice_queries[column.index] += 1` is a
    `Vec` index, so an advice column whose index was never allocated (a
    `ConstraintSystem` built by hand with `numAdviceQueries` shorter than
    `numAdviceColumns`) aborts here rather than growing the counter. -/
def ConstraintSystem.queryAdviceIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : Except Fault (ConstraintSystem F × Nat) := do
  match cs.adviceQueries.toList.findIdx? (fun q => q == (column, at')) with
  | some i => .ok (cs, i)
  | none =>
      unless column.index < cs.numAdviceQueries.size do
        throw (Fault.panic "proofs/src/plonk/circuit.rs:2035")
      let bumped := (cs.numAdviceQueries.toList.take column.index ++
          ((cs.numAdviceQueries.getD column.index 0) + 1) ::
            cs.numAdviceQueries.toList.drop (column.index + 1)).toArray
      .ok ({ cs with adviceQueries := cs.adviceQueries.push (column, at'),
                       numAdviceQueries := bumped }, cs.adviceQueries.size)

/-- rust: proofs/src/plonk/circuit.rs:2040-2053 (`query_instance_index`). -/
def ConstraintSystem.queryInstanceIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : ConstraintSystem F × Nat :=
  match cs.instanceQueries.toList.findIdx? (fun q => q == (column, at')) with
  | some i => (cs, i)
  | none => ({ cs with instanceQueries := cs.instanceQueries.push (column, at') },
      cs.instanceQueries.size)

/-- rust: proofs/src/plonk/circuit.rs:2055-2065 (`query_any_index`). The three
    `Column::<T>::try_from(column).unwrap()` calls at :2058, :2060 and :2062 are
    *not* panic sites in the port: the arm was selected by testing the same
    `column_type` the conversion tests, so the `Err("Cannot convert into
    Column<Advice>")` branch is unreachable by construction. In Rust the same is
    true, but nothing checks it. -/
def ConstraintSystem.queryAnyIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : Except Fault (ConstraintSystem F × Nat) :=
  match column.columnType with
  | .advice _ => cs.queryAdviceIndex column at'
  | .fixed => .ok (cs.queryFixedIndex column at')
  | .instance => .ok (cs.queryInstanceIndex column at')

/-- rust: proofs/src/plonk/circuit.rs:2067-2075 (`get_advice_query_index`).
    The `panic!("get_advice_query_index called for non-existent query")` at :2074
    is a real, reachable abort: this is a *lookup* in a read-only view, and the
    caller (plonk/permutation.rs:246-272 through `get_any_query_index`) assumes
    the query was registered during keygen. -/
def ConstraintSystem.getAdviceQueryIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : Except Fault Nat :=
  match cs.adviceQueries.toList.findIdx? (fun q => q == (column, at')) with
  | some i => .ok i
  | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2074")

/-- rust: proofs/src/plonk/circuit.rs:2077-2085 (`get_fixed_query_index), panic
    at :2084. -/
def ConstraintSystem.getFixedQueryIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : Except Fault Nat :=
  match cs.fixedQueries.toList.findIdx? (fun q => q == (column, at')) with
  | some i => .ok i
  | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2084")

/-- rust: proofs/src/plonk/circuit.rs:2087-2095 (`get_instance_query_index),
    panic at :2094. -/
def ConstraintSystem.getInstanceQueryIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : Except Fault Nat :=
  match cs.instanceQueries.toList.findIdx? (fun q => q == (column, at')) with
  | some i => .ok i
  | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2094")

/-- rust: proofs/src/plonk/circuit.rs:2097-2109 (`get_any_query_index). The
    verifier-reachable one of the four: plonk/permutation.rs:246, :249, :252,
    :266, :269 and :272 call it with `Rotation::cur()` to index
    `advice_evals`/`fixed_evals`/`instance_evals` while building the permutation
    identity. Same `try_from(..).unwrap()` remark as `queryAnyIndex`. -/
def ConstraintSystem.getAnyQueryIndex {F : Type} (cs : ConstraintSystem F)
    (column : Column) (at' : Rotation) : Except Fault Nat :=
  match column.columnType with
  | .advice _ => cs.getAdviceQueryIndex column at'
  | .fixed => cs.getFixedQueryIndex column at'
  | .instance => cs.getInstanceQueryIndex column at'

/-- Port scaffolding: `Array.mapM` over `Except Fault`, which Lean will not
    synthesise a `Traverse` instance for at these types. Left-to-right, and the
    first error wins - the same order Rust's `for .. { }` loops with an
    `assert!` inside produce. -/
def mapExceptArray {α β : Type} (f : α → Except Fault β) (xs : Array α) :
    Except Fault (Array β) :=
  go xs.toList #[]
where
  go : List α → Array β → Except Fault (Array β)
    | [], acc => .ok acc
    | x :: rest, acc => do
        let y ← f x
        go rest (acc.push y)

/-- rust: proofs/src/plonk/circuit.rs:2206-2235 (`fn replace_selectors`), the
    private helper nested inside `replace_selectors_with_fixed`; rule R1 keeps
    private helpers, so it is a def here. Declared before its caller because Lean
    needs the callee first (the Rust order is :2160 then :2204).

    It is `Expression::evaluate` with `T = Except Fault (Expression F)`, i.e. the
    four arithmetic closures are the *operator impls* - `-a`, `a + b`, `a * b`,
    `a * f` at :2225-2228 - so every panic and every short-circuit of `Add`/`Sub`/
    `Mul` fires again here, on the VK construction path. That is not a curiosity:
    a gate whose polynomial multiplies two simple-selector-carrying expressions
    survives `create_gate` (which only builds the tree) and aborts inside
    `read_from_cs`.

    Two panic sites of its own:
    * `:2216` `assert!(!selector.is_simple())` when `must_be_nonsimple`, i.e. a
      simple selector still present in a lookup or trash expression.
    * `:2219` `selector_replacements[selector.0]`, a slice index: a selector whose
      index is past the end of the replacement vector aborts. The vector is built
      with one entry per `num_selectors`, so a `Gate` naming a selector that was
      never allocated reaches it. -/
def replaceSelectors {F : Type} [Field F] [BEq F] (expr : Expression F)
    (selectorReplacements : Array (Expression F)) (mustBeNonsimple : Bool) :
    Except Fault (Expression F) :=
  Expression.evaluate
    { constant := fun c => .ok (Expression.constant c)
      selectorColumn := fun s => do
        if mustBeNonsimple && s.isSimple then
          throw (Fault.panic "proofs/src/plonk/circuit.rs:2216")
        match selectorReplacements[s.index]? with
        | some e => .ok e
        | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2219")
      fixedColumn := fun q => .ok (Expression.fixed q)
      adviceColumn := fun q => .ok (Expression.advice q)
      instanceColumn := fun q => .ok (Expression.instance q)
      challenge := fun c => .ok (Expression.challenge c)
      negated := fun a => match a with
        | .ok x => .ok (Expression.neg x)
        | .error e => .error e
      sum := fun a b => match a with
        | .error e => .error e
        | .ok x => match b with
            | .error e => .error e
            | .ok y => Expression.add x y
      product := fun a b => match a with
        | .error e => .error e
        | .ok x => match b with
            | .error e => .error e
            | .ok y => Expression.mul x y
      scaled := fun a f => match a with
        | .ok x => .ok (Expression.scaledMul x f)
        | .error e => .error e }
    expr

/-- rust: proofs/src/plonk/circuit.rs:2204-2265 (`replace_selectors_with_fixed`).
    The four passes are in the Rust's order and each keeps the Rust's
    `must_be_nonsimple` flag: gates with `false` (:2237-2239), the lookup inputs
    and tables with `true` (:2243-2252, one chained iterator - inputs first, then
    tables), the lookup *selector* fields with `true` (:2255-2257), and the trash
    selectors and constraint expressions with `true` (:2259-2264).

    The asymmetry is the point: gate polynomials may keep a simple selector (it
    becomes the fixed column that the linearization groups by), while lookup and
    trash expressions may not, because those arguments already consume the
    selector multiplicatively/additively elsewhere. -/
def ConstraintSystem.replaceSelectorsWithFixed {F : Type} [Field F] [BEq F]
    (cs : ConstraintSystem F) (selectorReplacements : Array (Expression F)) :
    Except Fault (ConstraintSystem F) := do
  let gates ← mapExceptArray (fun g => do
      let polys ← mapExceptArray (fun e => replaceSelectors e selectorReplacements false) g.polys
      return { g with polys := polys }) cs.gates
  let lookups ← mapExceptArray (fun l => do
      let inputs ← mapExceptArray
        (fun inner => mapExceptArray (fun e => replaceSelectors e selectorReplacements true) inner)
        l.inputExpressions
      let tables ← mapExceptArray
        (fun e => replaceSelectors e selectorReplacements true) l.tableExpressions
      let sel ← replaceSelectors l.selector selectorReplacements true
      return { l with selector := sel, inputExpressions := inputs, tableExpressions := tables })
      cs.lookups
  let trashcans ← mapExceptArray (fun t => do
      let sel ← replaceSelectors t.selector selectorReplacements true
      let cs' ← mapExceptArray
        (fun e => replaceSelectors e selectorReplacements true) t.constraintExpressions
      return { t with selector := sel, constraintExpressions := cs' }) cs.trashcans
  return { cs with gates := gates, lookups := lookups, trashcans := trashcans }

/-- rust: proofs/src/plonk/circuit.rs:2160-2202 (`directly_convert_selectors_to_fixed`).
    Reachable at plonk/mod.rs:189, inside `VerifyingKey::read_from_cs`, with
    `fake_selectors = vec![vec![]; cs.num_selectors]` (:188) - so on the VK path
    every selector poly is the *empty* vector and only the column allocation, the
    flag update and the index shift are observable.

    Panic sites: `:2166` `assert_eq!(selectors.len(), self.num_selectors)`;
    `:2176`/`:2177` index `selector_flags[idx]`, which is a `Vec` index (the
    flags vector is only grown by `selector()`/`complex_selector()`, so a
    `num_selectors` that outran it aborts); and everything `replaceSelectors` can
    raise.

    THREE BEHAVIOURS A TIDY PORT WOULD LOSE:
    * `nr_fixed_columns` is read at :2168 *before* the loop allocates new columns,
      and the shift at :2197 is by that pre-loop value. So a gate's
      `queried_selectors` indices move by the number of fixed columns the system
      had on entry, not by the number of selectors converted.
    * the shift is applied to **every** entry of `queried_selectors`, including
      complex selectors' - the comment at :2192-2194 says "simple, multiplicative
      selectors" but the loop does not filter.
    * `s.0 += nr_fixed_columns` is a `usize` addition: it wraps in the reference
      (release) profile rather than panicking. Not emulated (rule R5): the index
      would have to exceed `2^64`. -/
def ConstraintSystem.directlyConvertSelectorsToFixed {F : Type} [Field F] [BEq F]
    (cs : ConstraintSystem F) (selectors : Array (Array Bool)) :
    Except Fault (ConstraintSystem F × Array (Array F)) := do
  unless selectors.size == cs.numSelectors do
    throw (Fault.panic "proofs/src/plonk/circuit.rs:2166")
  let nrFixedColumns := cs.numFixedColumns
  let (cs, polys, repls) ← go cs #[] #[] selectors.toList 0
  let cs ← cs.replaceSelectorsWithFixed repls
  let gates := cs.gates.map fun g =>
    { g with queriedSelectors := g.queriedSelectors.map fun s =>
        { s with index := s.index + nrFixedColumns } }
  return ({ cs with gates := gates, numSelectors := 0 }, polys)
where
  go : ConstraintSystem F → Array (Array F) → Array (Expression F) → List (Array Bool) →
      Nat → Except Fault (ConstraintSystem F × Array (Array F) × Array (Expression F))
    | cs, polys, repls, [], _ => .ok (cs, polys, repls)
    | cs, polys, repls, selector :: rest, idx => do
        -- circuit.rs:2173-2174
        let poly : Array F := selector.map fun b => if b then 1 else 0
        -- circuit.rs:2175 (`self.fixed_column()`, :2321-2328)
        let column : Column := { index := cs.numFixedColumns, columnType := Any.fixed }
        let cs := { cs with numFixedColumns := cs.numFixedColumns + 1 }
        -- circuit.rs:2176-2178
        match cs.selectorFlags[idx]? with
        | none => throw (Fault.panic "proofs/src/plonk/circuit.rs:2176")
        | some f =>
            let flags := if f.isSimple then
              (cs.selectorFlags.toList.take idx ++
                  ({ isSimple := true, colIdx := some column.index } ::
                    cs.selectorFlags.toList.drop (idx + 1))).toArray
            else cs.selectorFlags
            -- circuit.rs:2179-2184
            let cs2 := { cs with selectorFlags := flags }
            let (cs3, qi) := cs2.queryFixedIndex column Rotation.cur
            let fq : FixedQuery := { index := some qi, columnIndex := column.index, rotation := Rotation.cur }
            let expr : Expression F := Expression.fixed fq
            go cs3 (polys.push poly) (repls.push expr) rest (idx + 1)

/-! rust: proofs/src/plonk/circuit.rs:2114-2120 (`set_minimum_degree`),
    :2124-2156 (`create_gate`), :2267-2272 (`selector`), :2276-2281
    (`complex_selector`), :2284-2288 (`lookup_table_column`), :2291-2303
    (`annotate_lookup_column`), :2305-2319 (`annotate_lookup_any_column`),
    :2321-2328 (`fixed_column`), :2331-2333 (`unblinded_advice_column`),
    :2336-2338 (`advice_column`), :2345-2368 (`unblinded_advice_column_in`),
    :2370-2388 (`advice_column_in`), :2390-2396 (`instance_column`),
    :2404-2416 (`challenge_usable_after`) and :2423-2433
    (`assert_phase_exists`) - the allocation and gate-construction half of the
    impl, NOT verifier-reachable, so no bodies. Evidence: every one of them is a
    `&mut self` mutation whose callers live in `Circuit::configure` closures
    (solidity-verifier/src/test.rs:255-560, src/lowering/protocol/mod.rs:959-1113
    and plonk/keygen.rs); the verifier's only contact with the same data is
    through the read accessors below. `set_minimum_degree` has zero call sites in
    the reachable set, `create_gate`'s are all construction, and
    `assert_phase_exists` is reached only from the three `*_in` allocators.

    Recorded anyway because two of them decide things the verifier *reads*:
    * `create_gate` panics on an empty constraint list at :2132-2135 ("Gates must
      contain at least one constraint"), so a `Gate` with `polys = #[]` cannot
      come from the reference - but solidity-verifier/src/lowering/diagnostics.rs:238
      still defends against it (`filter(|gate| gate.polynomials().is_empty())`).
    * `advice_column_in` and `challenge_usable_after` are what make
      `adviceColumnPhase` / `challengePhase` non-decreasing and gap-free, which is
      what `phases()` below assumes when it renders `0..=max_phase`.
    * `unblinded_advice_column_in` (:2345-2368) pushes the index into
      `unblindedAdviceColumns` *before* incrementing `numAdviceColumns`; the plain
      `advice_column_in` does not push at all. Nothing on the verify path reads
      `unblindedAdviceColumns`, so the port keeps the field but not the writers. -/

/-- rust: proofs/src/plonk/circuit.rs:2435-2441 (`phases`). Reachable at
    plonk/verifier.rs:112 - it is the loop the whole multi-phase challenge schedule
    runs on.

    `max_phase` is `advice_column_phase.iter().max().map(|p| p.0).unwrap_or_default()`
    and the iterator is `0..=max_phase`, so **an empty constraint system still
    yields exactly one phase (0)**, not zero. That is easy to get wrong and it is
    observable: with zero advice columns the verifier would otherwise skip the
    phase loop entirely and never squeeze the challenges it does have. The port
    reproduces it with `foldl max 0` (which is `unwrap_or_default` on an empty
    vector) and `List.range (m + 1)` (which is `0..=m`). -/
def ConstraintSystem.phases {F : Type} (cs : ConstraintSystem F) : List Phase :=
  let maxPhase := cs.adviceColumnPhase.foldl (fun acc p => max acc p.val) 0
  (List.range (maxPhase + 1)).map fun i => { val := i }

/-- rust: proofs/src/plonk/circuit.rs:2443-2456 (`degree`). Reachable at
    plonk/mod.rs:175 (it sizes the evaluation domain: `EvaluationDomain::new(
    cs.degree() as u32, k)`) and :233 (`cs_degree`, a `VerifyingKey` field the
    verifier passes to `chunk_by_degree`).

    The Rust builds a four-element array of `Option<usize>` - the permutation's
    required degree, the *max* over trashcans, the *max* over every gate
    polynomial degree, and `minimum_degree` - drops the `None`s and takes the
    max, with `unwrap_or(1)`. Because the permutation's contribution is the
    constant 3 (permutation.rs:79), `degree` is at least 3 for every constraint
    system, and the `unwrap_or(1)` can never be observed. Then each batched lookup
    is asked what degree it would push the system to and the answer is the max of
    the two. Note that `degree` is *not* idempotent w.r.t. lookups:
    `degree_batched_argument` is computed against `degree_without_lookup`, so a
    lookup can raise the degree but the raised degree is never fed back into the
    chunking. -/
def ConstraintSystem.degree {F : Type} (cs : ConstraintSystem F) : Except Fault Nat := do
  -- circuit.rs:2445-2456: four Option<usize> candidates, filter_map, max, unwrap_or(1)
  let perm := some cs.permutation.requiredDegree
  let trash := cs.trashcans.foldl (fun acc t => match acc with
      | none => some (TrashArgument.requiredDegree t)
      | some m => some (max m (TrashArgument.requiredDegree t))) none
  let gateDeg := cs.gates.foldl (fun acc g =>
      g.polys.foldl (fun a e => match a with
        | none => some (Expression.degree e)
        | some m => some (max m (Expression.degree e))) acc) none
  let candidates := [perm, trash, gateDeg, cs.minimumDegree].filterMap id
  let dwl := match candidates with
    | [] => 1
    | _ :: _ => candidates.foldl (fun a d => max a d) 0
  -- circuit.rs:2458-2465: each batched lookup is asked against degree_without_lookup
  let lookupDegrees ← mapExceptArray (fun l => l.degreeBatchedArgument dwl) cs.lookups
  let degree := match lookupDegrees.toList with
    | [] => dwl
    | _ :: _ => lookupDegrees.foldl (fun a d => max a d) dwl
  -- circuit.rs:2467
  return max dwl degree

/-- rust: proofs/src/plonk/circuit.rs:2472-2512 (`blinding_factors`). Reachable
    at plonk/verifier.rs:443, plonk/mod.rs:509, plonk/permutation/verifier.rs:150
    and solidity-verifier src/lowering/protocol/mod.rs:402.

    The arithmetic is a running `let factors = factors + ..` chain and every step
    is kept, in order: max over `num_advice_queries` (`unwrap_or(&1)`, so an empty
    counter vector gives 1 but a vector of zeros gives 0 - the same distinction as
    in the logup helpers), then `max(3, .)`, then one per trash argument, then one
    per lookup *chunk* (which is why a lookup whose inputs are steeper than the
    system's degree aborts here - see `LogupBatchedArgument.numChunks`), then
    +1 for the multi-open at x_3, +1 "as a slight defense against off-by-one
    errors", +1 "as a security margin for opening the linearization polynomial".
    Three separate +1s, not a `+3`.

    THE ONE THAT MATTERS FOR THE VERIFIER, and it is docs/REVIEW.md R-9: the
    result is checked against `i32::MAX` at :2509-2511 and panics above it, but
    nothing bounds it from *below* in the callers. plonk/verifier.rs:444 and
    plonk/permutation/verifier.rs:152 both build
    `Rotation(-((blinding_factors + 1) as i32))` from it, so the value flows
    straight into a rotation that `l_i_range` and `rotate_omega` turn into a field
    power. The `as i32` cast is a silent truncation for a `usize` above
    `2^31` - unreachable *because* of the panic at :2510, which is the only thing
    in the file that makes it unreachable. -/
def ConstraintSystem.blindingFactors {F : Type} (cs : ConstraintSystem F) :
    Except Fault Nat := do
  -- circuit.rs:2474 (`num_advice_queries.iter().max().unwrap_or(&1)`)
  let maxQueries := cs.numAdviceQueries.toList.foldl (fun acc q => match acc with
      | none => some q
      | some m => some (max m q)) none
  let f0 := maxQueries.getD 1
  -- circuit.rs:2479
  let f1 := max 3 f0
  -- circuit.rs:2483
  let f2 := f1 + cs.trashcans.size
  -- circuit.rs:2490-2496 (note: `self.degree()` is recomputed per lookup in Rust)
  let deg ← cs.degree
  let chunkCounts ← mapExceptArray (fun l => l.numChunks deg) cs.lookups
  let f3 := f2 + chunkCounts.foldl (fun a c => a + c) 0
  -- circuit.rs:2499, :2505, :2508
  let f4 := f3 + 1 + 1 + 1
  -- circuit.rs:2509-2511
  if f4 > 2147483647 then
    throw (Fault.panic "proofs/src/plonk/circuit.rs:2510")
  return f4

/-! rust: proofs/src/plonk/circuit.rs:2517-2524 (`minimum_rows`) - NOT
    verifier-reachable: grepping the reachable set for `minimum_rows` returns
    nothing; its callers are plonk/prover.rs and plonk/keygen.rs, which size the
    blinding region. It is `blinding_factors() + 3` (one row for
    `l_{-(m+1)}`, one for `l_0`, one to have a row at all), so the verifier can
    recompute it from what it already has if it ever needs it. -/

/-! rust: proofs/src/plonk/circuit.rs:2528-2606 - the fifteen read accessors
    (`num_fixed_columns`, `num_advice_columns`, `num_instance_columns`,
    `num_selectors`, `num_challenges`, `gates`, `advice_queries`,
    `instance_queries`, `fixed_queries`, `permutation`, `lookups`, `trashcans`,
    `constants`, `general_column_annotations`, and the two phase getters). All but
    the phase getters are the projections of the identically named fields; the
    Rust returns `&T` where the port returns `T`, which is unobservable because
    every `&mut self` mutation in the impl runs before the VK is built.

    TWO EXCEPTIONS, both forced and both named differently from their field:
    * `advice_column_phase()` (:2553-2556) and `challenge_phase()` (:2558-2561)
      return `Vec<u8>` - the *unwrapped* phase - while the fields hold
      `Vec<sealed::Phase>`. The projection already owns the name, so the accessors
      are `adviceColumnPhaseNats` and `challengePhaseNats`. Both are reachable:
      plonk/verifier.rs:115 and :128 zip over the *fields*, while
      solidity-verifier src/lowering/protocol/mod.rs:374 and :399-400 call the
      methods, so the port needs both shapes.
    * `constants()` (:2603-2606) is NOT ported: grepping the reachable set for
      `.constants` and `constants()` returns nothing. The field is kept because
      it is a struct field in the plan's 1678-1727 range and because
      `PinnedConstraintSystem` includes it (so it is part of whatever hashes
      `transcript_repr`, which is R-1's problem, not this module's). -/

/-- rust: proofs/src/plonk/circuit.rs:2553-2556 (`advice_column_phase`). -/
def ConstraintSystem.adviceColumnPhaseNats {F : Type} (cs : ConstraintSystem F) : Array Nat :=
  cs.adviceColumnPhase.map (fun p => p.val)

/-- rust: proofs/src/plonk/circuit.rs:2558-2561 (`challenge_phase`). -/
def ConstraintSystem.challengePhaseNats {F : Type} (cs : ConstraintSystem F) : Array Nat :=
  cs.challengePhase.map (fun p => p.val)

/-- rust: proofs/src/plonk/circuit.rs:2610-2615 (`struct VirtualCells<'a, F> {
    meta: &'a mut ConstraintSystem<F>, queried_selectors: Vec<Selector>,
    queried_cells: Vec<VirtualCell> }`), field order preserved except for the
    first: `meta` is a mutable borrow of the constraint system, and Lean has no
    borrow - the port's `ConstraintSystem` is a value, so the "same" `meta` cannot
    be shared by reference. It is therefore dropped from the record and the two
    accumulated vectors are what remains. This is the one place in the port where
    a Rust field is *absent* rather than re-typed, and it is why the methods below
    are skipped rather than ported: they are `&mut self` on both the cells and the
    meta at once. -/
structure VirtualCells where
  /-- rust: circuit.rs:2612 (`queried_selectors: Vec<Selector>`) -/
  queriedSelectors : Array Selector
  /-- rust: circuit.rs:2613 (`queried_cells: Vec<VirtualCell>`) -/
  queriedCells : Array VirtualCell

/-- rust: proofs/src/plonk/circuit.rs:2618-2625 (`VirtualCells::new`) - the two
    empty vectors; the `meta` argument is the dropped borrow. -/
def VirtualCells.new : VirtualCells := { queriedSelectors := #[], queriedCells := #[] }

/-! rust: proofs/src/plonk/circuit.rs:2627-2700 (`query_selector`, `query_fixed`,
    `query_advice`, `query_instance`, `query_any`, `query_challenge` and
    `apply_selector_to_constraints`) - NOT verifier-reachable, so no bodies.
    Evidence: grepping the reachable set for `VirtualCells`, `query_selector`,
    `query_any`, `query_any_index` and `apply_selector_to_constraints` returns
    nothing; `query_fixed`/`query_advice`/`query_instance`/`query_challenge` occur
    only inside `create_gate` closures in circuit-construction code
    (solidity-verifier/src/test.rs:260-560, :5420 and
    src/lowering/protocol/mod.rs:962-1113, the latter inside its own test
    module). They are the API a chip author calls while *building* the system.

    Two of them are worth describing for whoever ports keygen, because they are
    the only place the query index is filled in on the happy path:
    * `query_fixed` (:2633-2641) pushes `(column, at)` into `queried_cells` *and*
      calls `meta.query_fixed_index`, storing the returned index into the
      `FixedQuery`. So a gate built through `VirtualCells` has `index := some i`
      from the start, while one built by `Column::query_cell` has `index := none`
      until `query_cells` fills it (circuit.rs:861-869).
    * `apply_selector_to_constraints` (:2678-2700) is where an `Additive` selector
      turns into a trash argument: it pushes
      `trash::Argument::new(names.join("&"), q, polys)` onto `meta.trashcans` and
      returns `vec![]`, i.e. the gate itself gets *no* polynomial from those
      constraints. The `&`-joined name is the only place that separator is
      produced, and `Constraints::with_additive_selector` is its only entry point. -/

/-- Port scaffolding for `Expression.verifierCallbacks`: the two Rust panics that
    live on one line - `evals[query.index.unwrap()]` - as one site, since the
    reference reports the same file:line for both only by accident of formatting
    and the port's `Fault.panic` carries a single string. -/
def queryEvalsAt {F : Type} (evals : Array F) (index : Option Nat) (site : String) :
    Except Fault F :=
  match index with
  | none => .error (Fault.panic site)
  | some i => match evals[i]? with
      | some v => .ok v
      | none => .error (Fault.panic site)

/-- rust: proofs/src/plonk/mod.rs:530-541, the closure list handed to
    `poly.evaluate(..)` inside `partially_evaluate_identities` - the verifier's
    gate loop. The identical ten closures are repeated at plonk/trash.rs:63-77
    (`Evaluated::expressions`) and plonk/logup.rs:415-429
    (`ChunkedArgument`/`Evaluated::expressions`), so this one def is the shared
    meaning of "evaluate an expression at x" for the whole verifier, and it is
    what the plan's module map means by `evaluate` "(a virtual selector panics)".

    THE PANIC THE PLAN CALLS OUT: the `selector_column` closure is
    `&|_| panic!("virtual selectors are removed during optimization")`
    (plonk/mod.rs:532). It is not defensive - `directly_convert_selectors_to_fixed`
    (plonk/mod.rs:189) is supposed to have replaced every `Expression::Selector`
    with a `Fixed` query before a VK exists, so reaching this arm means the VK was
    built without that pass. The port keeps it as `Fault.panic` at that line.

    The other four are the silent ones. `query.index.unwrap()` (:533, :534, :535)
    aborts on an expression whose query index was never filled, and the slice
    index on the same line aborts when the index is past the evaluation vector -
    which is exactly what happens to a `fixed_evals` that the transcript filled
    short. `challenges[challenge.index()]` (:536) is the third.

    Rule R3 note: Rust evaluates the left subterm, then the right, then combines,
    and a panic aborts immediately, so the *first* error in left-to-right order is
    the one observed. The `sum` and `product` closures below reproduce that by
    matching on `a` before `b`; a symmetric `match a, b` with the arms in the other
    order would report the wrong panic site. -/
def Expression.verifierCallbacks {F : Type} [Field F]
    (adviceEvals fixedEvals instanceEvals challenges : Array F) :
    Expression.Callbacks F (Except Fault F) :=
  { constant := fun c => .ok c
    selectorColumn := fun _ => .error (Fault.panic "proofs/src/plonk/mod.rs:532")
    fixedColumn := fun q => queryEvalsAt fixedEvals q.index "proofs/src/plonk/mod.rs:533"
    adviceColumn := fun q => queryEvalsAt adviceEvals q.index "proofs/src/plonk/mod.rs:534"
    instanceColumn := fun q => queryEvalsAt instanceEvals q.index "proofs/src/plonk/mod.rs:535"
    challenge := fun c => match challenges[c.index]? with
      | some v => .ok v
      | none => .error (Fault.panic "proofs/src/plonk/mod.rs:536")
    negated := fun a => match a with
      | .ok x => .ok (-x)
      | .error e => .error e
    sum := fun a b => match a with
      | .error e => .error e
      | .ok x => match b with
          | .error e => .error e
          | .ok y => .ok (x + y)
    product := fun a b => match a with
      | .error e => .error e
      | .ok x => match b with
          | .error e => .error e
          | .ok y => .ok (x * y)
    scaled := fun a f => match a with
      | .ok x => .ok (x * f)
      | .error e => .error e }


/-! ## Known-answer checks

Executable booleans, not proofs, in the style of `Exec/Arith` and
`Exec/Domain`: hand-computed values over `ZMod 17`, small enough to check on
paper. They pin the four things this module claims - that the ordering and
deduplication rules are the Rust ones, that the degree and blinding-factor
arithmetic matches a hand calculation, that every documented panic really fires
at its documented line, and that the verifier's `evaluate` instantiation is the
one plonk/mod.rs:530 describes. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A `Fr 17` value as a `Nat`, so the checks compare through `BEq Nat` rather
    than depending on a `BEq` for `Except` or `Fault` (which the Rust has no
    counterpart for either). -/
def fr17c (x : Fr 17) : Nat := x.val

/-- The panic site carried by an `Except Fault`, or the empty string. -/
def panicSite {α : Type} (x : Except Fault α) : String :=
  match x with
  | .error (Fault.panic s) => s
  | _ => ""

/-- The value of a successful `Except Fault Nat`, with a sentinel so a panic can
    never match an expected number. -/
def okNat (x : Except Fault Nat) : Nat :=
  match x with
  | .ok v => v
  | .error _ => 999

/-- As `okNat` for a field element. -/
def okFr (x : Except Fault (Fr 17)) : Nat :=
  match x with
  | .ok v => v.val
  | .error _ => 999

/-- A first-phase advice query at column 0, current row, index 0 - the shape a
    converted VK carries. -/
def aq0 : AdviceQuery :=
  { index := some 0, columnIndex := 0, rotation := Rotation.cur, phase := { val := 0 } }

/-- The same query at index 1, so the evaluation vectors can be told apart. -/
def aq1 : AdviceQuery :=
  { index := some 1, columnIndex := 0, rotation := Rotation.cur, phase := { val := 0 } }

/-- An advice query whose index was never filled - `Column::queryCell` output. -/
def aqNone : AdviceQuery :=
  { index := none, columnIndex := 0, rotation := Rotation.cur, phase := { val := 0 } }

/-- A fixed query at column 0, current row, index 0. -/
def fq0 : FixedQuery :=
  { index := some 0, columnIndex := 0, rotation := Rotation.cur }

/-- A fixed query whose index is past the end of the evaluation vector. -/
def fqOob : FixedQuery :=
  { index := some 5, columnIndex := 0, rotation := Rotation.cur }

/-- A simple selector with index 0 (circuit.rs:2267-2272 output). -/
def selSimple : Selector := { index := 0, isSimple := true }

/-- A complex selector with index 0 (circuit.rs:2276-2281 output). -/
def selComplex : Selector := { index := 0, isSimple := false }

def colFixed : Column := { index := 0, columnType := Any.fixed }

def colAdvice : Column := { index := 0, columnType := Any.advice Advice.default }

def eAdvice : Expression (Fr 17) := Expression.advice aq0

def eAdvice1 : Expression (Fr 17) := Expression.advice aq1

def eAdviceNone : Expression (Fr 17) := Expression.advice aqNone

def eFixed : Expression (Fr 17) := Expression.fixed fq0

def eFixedOob : Expression (Fr 17) := Expression.fixed fqOob

def eInst : Expression (Fr 17) := Expression.instance { index := some 0, columnIndex := 0, rotation := Rotation.cur }

def eInstOob : Expression (Fr 17) := Expression.instance { index := some 4, columnIndex := 0, rotation := Rotation.cur }

def eChallenge : Expression (Fr 17) := Expression.challenge { index := 0, phase := { val := 0 } }

def eChallengeOob : Expression (Fr 17) := Expression.challenge { index := 3, phase := { val := 0 } }

def eSel : Expression (Fr 17) := Expression.selector selSimple

def eSelComplex : Expression (Fr 17) := Expression.selector selComplex

def eConst3 : Expression (Fr 17) := Expression.constant 3

def eConst0 : Expression (Fr 17) := Expression.constant 0

def eProd2 : Expression (Fr 17) := Expression.product eAdvice eAdvice

def eProd3 : Expression (Fr 17) := Expression.product eProd2 eAdvice

def eProd4 : Expression (Fr 17) := Expression.product eProd3 eAdvice

/-- Columns, kinds and the consensus-critical ordering (circuit.rs:245-262 and
    :82-92): `Instance < Advice < Fixed` across kinds, advice ordered by phase,
    and within a kind `Column` falls through to the index. The last three lines
    are the `Rotation` hazard: `cur` and `value 0` are the same rotation but not
    the same term, so `cur` and `rot 0` build different expressions and a
    hand-built system can fail to deduplicate a query. -/
def columnAny_kats_ok : Bool :=
  Phase.prev { val := 0 } == none &&
    Phase.prev { val := 2 } == some { val := 1 } &&
    PhaseKind.toSealed PhaseKind.third == { val := 2 } &&
    Advice.phaseNat Advice.default == 0 &&
    Advice.phaseNat (Advice.new PhaseKind.second) == 1 &&
    Any.cmp Any.instance Any.fixed == .lt &&
    Any.cmp Any.fixed Any.instance == .gt &&
    Any.cmp (Any.advice Advice.default) Any.fixed == .lt &&
    Any.cmp (Any.advice { phase := { val := 0 } }) (Any.advice { phase := { val := 2 } }) == .lt &&
    Any.cmp (Any.advice { phase := { val := 1 } }) (Any.advice { phase := { val := 1 } }) == .eq &&
    Any.cmp Any.instance Any.instance == .eq &&
    Column.cmp { index := 3, columnType := Any.fixed } { index := 1, columnType := Any.fixed } == .gt &&
    Column.cmp { index := 0, columnType := Any.instance }
      { index := 9, columnType := Any.advice Advice.default } == .lt &&
    Column.queryCell (F := Fr 17) { index := 2, columnType := Any.fixed } Rotation.next ==
      (Expression.fixed { index := none, columnIndex := 2, rotation := Rotation.next } :
        Expression (Fr 17)) &&
    Column.queryCell (F := Fr 17) colAdvice Rotation.cur == (eAdviceNone : Expression (Fr 17)) &&
    Column.cur (F := Fr 17) colFixed != Column.rot (F := Fr 17) colFixed 0 &&
    (Rotation.cur == Rotation.value 0) == false

/-- `Expression::degree` (circuit.rs:1206-1220) and the operator impls
    (:1336-1462), panics and short-circuits included. The last block is the
    behaviour a reviewer should notice: the `Mul` zero short-circuit *lowers* the
    degree, so `0 * (a*b)` has degree 0 where the unsimplified product has 2, and
    `ConstraintSystem::degree` reads the simplified tree. -/
def expression_kats_ok : Bool :=
  (Expression.constant (F := Fr 17) 0).degree == 0 &&
    eChallenge.degree == 0 &&
    eAdvice.degree == 1 &&
    eProd2.degree == 2 &&
    (Expression.sum (F := Fr 17) eProd2 eConst3).degree == 2 &&
    (Expression.scaled (F := Fr 17) eProd2 3).degree == 2 &&
    (Expression.negated (F := Fr 17) eAdvice).degree == 1 &&
    eSel.containsSimpleSelector &&
    !eSelComplex.containsSimpleSelector &&
    (Expression.product (F := Fr 17) eSel eAdvice).containsSimpleSelector &&
    !(Expression.sum (F := Fr 17) eFixed eAdvice).containsSimpleSelector &&
    okFr (do let e ← Expression.add (F := Fr 17) eConst0 eAdvice
             Expression.evaluate (F := Fr 17) (Expression.verifierCallbacks (F := Fr 17) #[0] #[0] #[0] #[0]) e) == 0 &&
    (match Expression.add (F := Fr 17) eConst0 eAdvice with
      | .ok e => e == eAdvice
      | .error _ => false) &&
    (match Expression.sub (F := Fr 17) eConst0 eAdvice with
      | .ok e => e == Expression.negated eAdvice
      | .error _ => false) &&
    (match Expression.mul (F := Fr 17) (Expression.constant 1) eAdvice with
      | .ok e => e == eAdvice
      | .error _ => false) &&
    panicSite (Expression.add (F := Fr 17) eSel eAdvice) == "proofs/src/plonk/circuit.rs:1340" &&
    panicSite (Expression.sub (F := Fr 17) eAdvice eSel) == "proofs/src/plonk/circuit.rs:1377" &&
    panicSite (Expression.mul (F := Fr 17) eSel eSel) == "proofs/src/plonk/circuit.rs:1414" &&
    (match Expression.mul (F := Fr 17) eSel eAdvice with
      | .ok e => e.degree == 2
      | .error _ => false) &&
    (match Expression.mul (F := Fr 17) eConst0 eProd2 with
      | .ok e => e.degree == 0 && e == eConst0
      | .error _ => false) &&
    (Expression.scaledMul (F := Fr 17) eConst0 0) == Expression.scaled eConst0 0

/-- Fixtures for the checks below, one record literal per line so the layout is
    unambiguous. -/
def csEmpty : ConstraintSystem (Fr 17) := ConstraintSystem.default (F := Fr 17)

def gateProd2 : Gate (Fr 17) := { name := "g", constraintNames := #["c"], polys := #[eProd2], queriedSelectors := #[], queriedCells := #[] }

def gateProd4 : Gate (Fr 17) := { name := "g", constraintNames := #["c"], polys := #[eProd4], queriedSelectors := #[], queriedCells := #[] }

def gateSel : Gate (Fr 17) := { name := "g", constraintNames := #["c"], polys := #[Expression.product eSel eAdvice], queriedSelectors := #[selSimple], queriedCells := #[] }

def trashDeg4 : TrashArgument (Fr 17) := { name := "t", selector := eConst3, constraintExpressions := #[eProd4] }

def trashEmpty : TrashArgument (Fr 17) := { name := "t", selector := eConst3, constraintExpressions := #[] }

def lookupDeg1 : LogupBatchedArgument (Fr 17) := { name := "l", selector := eConst3, inputExpressions := #[#[eAdvice]], tableExpressions := #[eFixed] }

def lookupDeg3 : LogupBatchedArgument (Fr 17) := { name := "l", selector := eConst3, inputExpressions := #[#[eProd3]], tableExpressions := #[eFixed] }

def lookupDeg0 : LogupBatchedArgument (Fr 17) := { name := "l", selector := eConst3, inputExpressions := #[#[eConst0]], tableExpressions := #[eFixed] }

def lookupSelSimple : LogupBatchedArgument (Fr 17) := { name := "l", selector := eSel, inputExpressions := #[#[eAdvice]], tableExpressions := #[eFixed] }

def csWithGate2 : ConstraintSystem (Fr 17) := { csEmpty with gates := #[gateProd2] }

def csWithGate4 : ConstraintSystem (Fr 17) := { csEmpty with gates := #[gateProd4] }

def csWithMin7 : ConstraintSystem (Fr 17) := { csEmpty with minimumDegree := some 7 }

def csWithTrash4 : ConstraintSystem (Fr 17) := { csEmpty with trashcans := #[trashDeg4] }

def csWithTrashEmpty : ConstraintSystem (Fr 17) := { csEmpty with trashcans := #[trashEmpty] }

def csWithLookup1 : ConstraintSystem (Fr 17) := { csEmpty with lookups := #[lookupDeg1] }

def csWithLookup3 : ConstraintSystem (Fr 17) := { csEmpty with lookups := #[lookupDeg3] }

def csWithLookup0 : ConstraintSystem (Fr 17) := { csEmpty with lookups := #[lookupDeg0] }

def csWithPhases : ConstraintSystem (Fr 17) := { csEmpty with adviceColumnPhase := #[{ val := 0 }, { val := 1 }] }

def csWithFlags : ConstraintSystem (Fr 17) := { csEmpty with selectorFlags := #[{ isSimple := true, colIdx := some 4 }, { isSimple := false, colIdx := some 5 }] }

def csWithFixedQuery : ConstraintSystem (Fr 17) := { csEmpty with fixedQueries := #[(colFixed, Rotation.cur)] }

def csWithAdviceQuery : ConstraintSystem (Fr 17) := { csEmpty with adviceQueries := #[(colAdvice, Rotation.cur)], numAdviceQueries := #[1] }

def csConvertible : ConstraintSystem (Fr 17) := { csEmpty with numSelectors := 1, selectorFlags := #[{ isSimple := true, colIdx := none }], gates := #[gateSel] }

def csConvertibleShift2 : ConstraintSystem (Fr 17) := { csConvertible with numFixedColumns := 2 }

def csConvertibleLookupSimple : ConstraintSystem (Fr 17) := { csConvertible with gates := #[], lookups := #[lookupSelSimple] }

def csConvertibleNoFlags : ConstraintSystem (Fr 17) := { csConvertible with selectorFlags := #[] }

def gateSel5 : Gate (Fr 17) := { name := "g", constraintNames := #["c"], polys := #[Expression.selector { index := 5, isSimple := false }], queriedSelectors := #[], queriedCells := #[] }

def csConvertibleBadSel : ConstraintSystem (Fr 17) := { csEmpty with numSelectors := 1, selectorFlags := #[{ isSimple := false, colIdx := none }], gates := #[gateSel5] }

/-- A system whose advice-query counter vector is shorter than its advice columns,
    which is what makes the index at circuit.rs:2035 abort. -/
def csWithShortCounters : ConstraintSystem (Fr 17) := { csEmpty with numAdviceQueries := #[] }

/-- The gate polynomial after conversion: the simple selector is replaced by the
    fixed column allocated for it, query index 0. -/
def eFixedRepl : Expression (Fr 17) := Expression.fixed { index := some 0, columnIndex := 0, rotation := Rotation.cur }

/-- As `eFixedRepl` but for the `numFixedColumns := 2` case, where the new column
    is index 2 and the gate's selector index shifts by 2. -/
def eFixedRepl2 : Expression (Fr 17) := Expression.fixed { index := some 0, columnIndex := 2, rotation := Rotation.cur }

def polysAt (cs : ConstraintSystem (Fr 17)) (i : Nat) : Array (Expression (Fr 17)) :=
  match cs.gates[i]? with
  | some g => g.polys
  | none => #[]

def selsAt (cs : ConstraintSystem (Fr 17)) (i : Nat) : Array Selector :=
  match cs.gates[i]? with
  | some g => g.queriedSelectors
  | none => #[]

/-- `ConstraintSystem::degree` (circuit.rs:2443-2456) and `blinding_factors`
    (:2472-2512), against a hand calculation.

    * empty system: the permutation's constant 3 dominates, so degree 3;
      `num_advice_queries` is empty so the `unwrap_or(&1)` gives 1, `max(3,1) = 3`,
      no trashcans, no lookups, then three separate `+ 1`s: 6.
    * a degree-2 gate does not move it (3 still dominates); a degree-4 gate does.
    * `minimumDegree := some 7` raises it to 7 - that is what the field is for.
    * a trash argument whose constraint has degree 4 raises it to 4; one with no
      constraints contributes `max(2, 0) = 2` and so does not.
    * a lookup with a degree-1 input and a fixed-column table:
      `max_degree = next_power_of_two(3-1) + 1 = 3`, `nb = (3-1)/1 = 2`,
      helper `= 2*1+1 = 3`, accumulator `= 2 + 0 + 1 = 3`, so
      `degree_batched_argument = next_power_of_two(2) + 1 = 3` and the system stays
      at 3; `num_chunks = ceil(1/2) = 1`, so blinding factors are 3 + 0 + 1 + 3 = 7.
    * a lookup whose input has degree 3 in a system of degree 3 gives
      `nb = (3-1)/3 = 0`, and `chunks(0)` aborts at logup.rs:318 - the verifier
      dies before it reads a single proof byte.
    * a lookup whose input is a constant gives `lookup_degree = 0` and the
      division at logup.rs:237 aborts. -/
def csDegree_kats_ok : Bool :=
  okNat csEmpty.degree == 3 && okNat csEmpty.blindingFactors == 6 &&
    okNat csWithGate2.degree == 3 &&
    okNat csWithGate4.degree == 4 &&
    okNat csWithMin7.degree == 7 &&
    trashDeg4.requiredDegree == 4 && okNat csWithTrash4.degree == 4 &&
    trashEmpty.requiredDegree == 2 && okNat csWithTrashEmpty.degree == 3 &&
    okNat (lookupDeg1.nbParallelLookupsPerChunk 3) == 2 &&
    okNat (lookupDeg1.numChunks 3) == 1 &&
    okNat (lookupDeg1.degreeBatchedArgument 3) == 3 &&
    okNat csWithLookup1.degree == 3 &&
    okNat csWithLookup1.blindingFactors == 7 &&
    (match lookupDeg1.chunkByDegree 3 with
      | .ok c => c.numChunks == 1 && c.inputExpressionChunks == #[#[#[eAdvice]]]
      | .error _ => false) &&
    okNat (lookupDeg3.nbParallelLookupsPerChunk 3) == 0 &&
    panicSite (lookupDeg3.numChunks 3) == "proofs/src/plonk/logup.rs:318" &&
    panicSite csWithLookup3.blindingFactors == "proofs/src/plonk/logup.rs:318" &&
    panicSite (lookupDeg0.nbParallelLookupsPerChunk 3) == "proofs/src/plonk/logup.rs:237" &&
    nextPowerOfTwo 0 == 1 && nextPowerOfTwo 1 == 1 && nextPowerOfTwo 3 == 4 &&
      nextPowerOfTwo 4 == 4 && nextPowerOfTwo 5 == 8 && nextPowerOfTwo 17 == 32 &&
      nextPowerOfTwo 16 == 16 &&
    (match rustChunks 2 "" (#[1, 2, 3, 4, 5] : Array Nat) with
      | .ok c => c == #[#[1, 2], #[3, 4], #[5]]
      | .error _ => false) &&
    panicSite (rustChunks 0 "site" (#[1] : Array Nat)) == "site"

/-- The read accessors and the query-index helpers (circuit.rs:1838-1847,
    :2009-2109, :2435-2441, :2553-2561).

    `phases` on an empty system is one phase, not none: the Rust renders
    `0..=max_phase` with `unwrap_or_default()`, so the verifier's phase loop always
    runs even for a circuit with no advice columns at all. The `queryFixedIndex`
    block also shows the `Rotation` hazard biting a real deduplication: asking for
    `(col, Rotation.value 0)` after `(col, Rotation.cur)` appends a second query
    here, where Rust would have returned the first. The advice counter is
    *per column*, not per query: a second distinct query on column 0 bumps
    `numAdviceQueries[0]` from 1 to 2 rather than appending a third entry, which is
    what `blinding_factors` then reads as "this column is opened twice". -/
def csAccessors_kats_ok : Bool :=
  csEmpty.phases == [{ val := 0 }] &&
    csWithPhases.phases == [{ val := 0 }, { val := 1 }] &&
    ConstraintSystem.adviceColumnPhaseNats csWithPhases == #[0, 1] &&
    csWithFlags.hasSimpleSelectorCol 4 && !csWithFlags.hasSimpleSelectorCol 5 &&
      !csWithFlags.hasSimpleSelectorCol 6 && csWithFlags.numSimpleSelectors == 1 &&
    okNat (csWithFixedQuery.getFixedQueryIndex colFixed Rotation.cur) == 0 &&
    panicSite (csWithFixedQuery.getFixedQueryIndex colFixed Rotation.next) ==
      "proofs/src/plonk/circuit.rs:2084" &&
    (csWithFixedQuery.queryFixedIndex colFixed Rotation.cur).2 == 0 &&
    ((csWithFixedQuery.queryFixedIndex colFixed Rotation.cur).1.fixedQueries.size) == 1 &&
    (csWithFixedQuery.queryFixedIndex colFixed (Rotation.value 0)).2 == 1 &&
    okNat (csWithAdviceQuery.getAnyQueryIndex colAdvice Rotation.cur) == 0 &&
    (match csWithAdviceQuery.queryAdviceIndex colAdvice Rotation.cur with
      | .ok (_, i) => i == 0
      | .error _ => false) &&
    (match csWithAdviceQuery.queryAdviceIndex colAdvice Rotation.next with
      | .ok (cs', i) => i == 1 && cs'.numAdviceQueries == #[2]
      | .error _ => false) &&
    panicSite (csEmpty.getAnyQueryIndex colAdvice Rotation.cur) ==
      "proofs/src/plonk/circuit.rs:2074" &&
    panicSite (csEmpty.getInstanceQueryIndex colAdvice Rotation.cur) ==
      "proofs/src/plonk/circuit.rs:2094" &&
    panicSite (csWithShortCounters.queryAdviceIndex colAdvice Rotation.next) ==
      "proofs/src/plonk/circuit.rs:2035"

/-- `directly_convert_selectors_to_fixed` (circuit.rs:2160-2202) and
    `replace_selectors` (:2206-2235) on a one-gate system.

    The first block is the happy path with `nr_fixed_columns = 0`: a new fixed
    column 0 is allocated, the flag records it, the gate's selector becomes that
    fixed query, `num_selectors` drops to 0 and the queried-selector index does
    not move. The second is the same system with two fixed columns already
    allocated, where the new column is index 2 and the gate's selector index
    shifts by 2 - the shift the Rust comment describes but applies to *every*
    queried selector, not only the simple ones. The last four lines are the four
    panic paths: the length assert, the missing flag, the simple selector in a
    lookup, and a selector index past the replacement vector. -/
def convertSelectors_kats_ok : Bool :=
  (match csConvertible.directlyConvertSelectorsToFixed #[#[true, false]] with
    | .error _ => false
    | .ok (cs', polys) => polys == #[#[1, 0]] && cs'.numFixedColumns == 1 &&
        cs'.numSelectors == 0 && cs'.selectorFlags == #[{ isSimple := true, colIdx := some 0 }] &&
        cs'.fixedQueries == #[(colFixed, Rotation.cur)] &&
        polysAt cs' 0 == #[Expression.product eFixedRepl eAdvice] &&
        selsAt cs' 0 == #[{ index := 0, isSimple := true }]) &&
  (match csConvertibleShift2.directlyConvertSelectorsToFixed #[#[]] with
    | .error _ => false
    | .ok (cs', polys) => polys == #[#[]] && cs'.numFixedColumns == 3 &&
        cs'.selectorFlags == #[{ isSimple := true, colIdx := some 2 }] &&
        polysAt cs' 0 == #[Expression.product eFixedRepl2 eAdvice] &&
        selsAt cs' 0 == #[{ index := 2, isSimple := true }]) &&
  panicSite (csConvertible.directlyConvertSelectorsToFixed #[]) ==
    "proofs/src/plonk/circuit.rs:2166" &&
  panicSite (csConvertibleNoFlags.directlyConvertSelectorsToFixed #[#[]]) ==
    "proofs/src/plonk/circuit.rs:2176" &&
  panicSite (csConvertibleLookupSimple.directlyConvertSelectorsToFixed #[#[]]) ==
    "proofs/src/plonk/circuit.rs:2216" &&
  panicSite (csConvertibleBadSel.directlyConvertSelectorsToFixed #[#[]]) ==
    "proofs/src/plonk/circuit.rs:2219"

/-- The verifier's instantiation of `Expression::evaluate` (plonk/mod.rs:530-541,
    repeated at trash.rs:63-77 and logup.rs:415-429) over four evaluation vectors
    `(advice, fixed, instance, challenges) = ([3, 5], [7], [11], [13])`.

    Every arm is exercised, including all six panic paths: the virtual selector
    (the plan's named case), an unfilled query index, an index past the end of an
    evaluation vector, and a challenge index past the challenge vector. The last
    two lines pin the left-to-right error order that rule R3 requires. -/
def verifierEvaluate_kats_ok : Bool :=
  let cb := Expression.verifierCallbacks (F := Fr 17) #[3, 5] #[7] #[11] #[13]
  okFr (Expression.evaluate cb eAdvice1) == 5 &&
    okFr (Expression.evaluate cb eConst3) == 3 &&
    okFr (Expression.evaluate cb eFixed) == 7 &&
    okFr (Expression.evaluate cb eInst) == 11 &&
    okFr (Expression.evaluate cb eChallenge) == 13 &&
    okFr (Expression.evaluate cb (Expression.sum eAdvice1 eConst3)) == 8 &&
    okFr (Expression.evaluate cb (Expression.product eAdvice1 eChallenge)) == 14 &&
    okFr (Expression.evaluate cb (Expression.scaled eAdvice1 3)) == 15 &&
    okFr (Expression.evaluate cb (Expression.negated eConst3)) == 14 &&
    panicSite (Expression.evaluate cb eSel) == "proofs/src/plonk/mod.rs:532" &&
    panicSite (Expression.evaluate cb eAdviceNone) == "proofs/src/plonk/mod.rs:534" &&
    panicSite (Expression.evaluate cb eFixedOob) == "proofs/src/plonk/mod.rs:533" &&
    panicSite (Expression.evaluate cb eInstOob) == "proofs/src/plonk/mod.rs:535" &&
    panicSite (Expression.evaluate cb eChallengeOob) == "proofs/src/plonk/mod.rs:536" &&
    panicSite (Expression.evaluate cb (Expression.sum eSel eAdviceNone)) ==
      "proofs/src/plonk/mod.rs:532" &&
    panicSite (Expression.evaluate cb (Expression.product eAdviceNone eSel)) ==
      "proofs/src/plonk/mod.rs:534"

end Kats

#eval columnAny_kats_ok   -- expect true
#eval expression_kats_ok   -- expect true
#eval csDegree_kats_ok   -- expect true
#eval csAccessors_kats_ok   -- expect true
#eval convertSelectors_kats_ok   -- expect true
#eval verifierEvaluate_kats_ok   -- expect true

end Midfall.Halo2
