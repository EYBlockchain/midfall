-- |
-- Midfall.Halo2.Exec.Circuit
--
-- The verifier-visible subset of the constraint system (plan Section 4 module
-- map, row plonk/circuit.rs): the column and query vocabulary, Expression with
-- its degree and the ten-closure evaluate, Gate, and ConstraintSystem with all
-- twenty fields in source order plus degree and blinding_factors.
--
-- Why the logUp and trash argument records live HERE rather than in
-- Exec/Logup.lean and Exec/Trash.lean: in Rust, circuit.rs refers to
-- logup::BatchedArgument and trash::Argument while logup.rs and trash.rs refer
-- to Expression - the modules are mutually recursive. Lean modules are not, so
-- the data goes in the lower module and the verifier-path functions
-- (read_committed, evaluate, the permutation grand product) land in
-- Exec/Logup and Exec/Trash later. The namespaces are the ones the plan names,
-- so nothing downstream can tell the difference.
--
-- Expression carries the Rust query structs rather than the placeholder's bare
-- (Column, Rotation) pairs, because the verifier reads column_index and
-- rotation off them separately and AdviceQuery carries a Phase the pair lacks.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

-- rust: circuit.rs:509 (pub struct Rotation(pub i32)) and :511-527 (cur,
-- next, prev). A closed inductive, with Exec/Domain supplying Rotation.int to
-- recover the integer. Not isomorphic: cur and (value 0) are two inhabitants
-- of one Rust value, so Rust's rotation == Rotation::cur() must port as
-- rotation.int == 0, never structurally.
inductive Rotation where
  | cur | next | prev | value (v : Int)

-- rust: circuit.rs:52-70 (enum Any). Instance is spelled instance_ because
-- instance is a Lean keyword.
inductive Any where
  | advice | fixed | instance_

-- rust: circuit.rs:72-80 (struct Column<C>). Rust carries the kind in the
-- type; the port keeps it as a field because the verifier reads kinds at
-- runtime (committed-instance columns are distinguished by index < n).
structure Column where
  kind : Any
  index : Nat

-- rust: circuit.rs:103 (sealed::Phase(pub(super) u8)). The sealing is a Rust
-- visibility device; u8 -> Nat per rule R5.
structure Phase where
  index : Nat

-- rust: circuit.rs:464 (struct Selector(usize, bool)). The bool says whether
-- this is a *simple* selector, backed by its own fixed column. A virtual
-- (non-simple) selector cannot be read by the verifier - the caller's
-- selector_column closure panics on it, which is the plan's flagged site.
structure Selector where
  idx : Nat
  simple : Bool

-- rust: circuit.rs:466-489 (Selector::is_simple, ::index).
def Selector.isSimple (s : Selector) : Bool := s.simple
def Selector.index' (s : Selector) : Nat := s.idx

-- rust: circuit.rs:1655-1674 (struct SelectorFlag(bool, Option<usize>)).
structure SelectorFlag where
  simple : Bool
  colIdx : Option Nat

def SelectorFlag.isSimple (f : SelectorFlag) : Bool := f.simple

-- rust: circuit.rs:491-496 (struct FixedQuery). Field order is the Rust order;
-- index is Option because a query is only numbered once the CS has collected it.
structure FixedQuery where
  index : Option Nat
  columnIndex : Nat
  rotation : Rotation

-- rust: circuit.rs:518-525 (struct AdviceQuery).
structure AdviceQuery where
  index : Option Nat
  columnIndex : Nat
  rotation : Rotation
  phase : Phase

-- rust: circuit.rs:548-554 (struct InstanceQuery).
structure InstanceQuery where
  index : Option Nat
  columnIndex : Nat
  rotation : Rotation

-- rust: circuit.rs:602-605 (struct Challenge).
structure Challenge where
  idx : Nat
  phase : Phase

def Challenge.index' (c : Challenge) : Nat := c.idx

-- rust: circuit.rs:1479-1482 (struct VirtualCell).
structure VirtualCell where
  column : Column
  rotation : Rotation

-- rust: circuit.rs:820-860 (enum Expression<F>). Ten variants in source order.
inductive Expression (F : Type) where
  | constant (c : F)
  | selector (s : Selector)
  | fixed (q : FixedQuery)
  | advice (q : AdviceQuery)
  | instance_ (q : InstanceQuery)
  | challenge (c : Challenge)
  | negated (e : Expression F)
  | sum (a b : Expression F)
  | product (a b : Expression F)
  | scaled (a : Expression F) (s : F)

-- rust: circuit.rs:1206-1220 (Expression::degree). Constants and challenges are
-- degree 0, every column query degree 1, Negated passes through, Sum takes the
-- max and Product the sum.
def Expression.degree {F : Type} : Expression F → Nat
  | .constant _ => 0
  | .selector _ => 1
  | .fixed _ => 1
  | .advice _ => 1
  | .instance_ _ => 1
  | .challenge _ => 0
  | .negated a => a.degree
  | .sum a b => max a.degree b.degree
  | .product a b => a.degree + b.degree
  | .scaled a _ => a.degree

-- rust: circuit.rs:907-1013 (Expression::evaluate). Ten closures, one per
-- constructor: rule R9 in its purest form, since the Rust is generic in ten
-- impl Fn. The virtual-selector panic the plan flags is NOT here - it lives in
-- the caller's selector_column closure (plonk/verifier.rs, evaluation.rs), so
-- Exec/Verifier owns that site; evaluate only dispatches.
def Expression.evaluate {F T : Type}
    (constant : F → T) (selectorColumn : Selector → T) (fixedColumn : FixedQuery → T)
    (adviceColumn : AdviceQuery → T) (instanceColumn : InstanceQuery → T)
    (challenge : Challenge → T) (negated : T → T) (sum : T → T → T)
    (product : T → T → T) (scaled : T → F → T) : Expression F → T
  | .constant s => constant s
  | .selector q => selectorColumn q
  | .fixed q => fixedColumn q
  | .advice q => adviceColumn q
  | .instance_ q => instanceColumn q
  | .challenge v => challenge v
  | .negated a =>
      negated (a.evaluate constant selectorColumn fixedColumn adviceColumn
        instanceColumn challenge negated sum product scaled)
  | .sum a b =>
      sum (a.evaluate constant selectorColumn fixedColumn adviceColumn
            instanceColumn challenge negated sum product scaled)
          (b.evaluate constant selectorColumn fixedColumn adviceColumn
            instanceColumn challenge negated sum product scaled)
  | .product a b =>
      product (a.evaluate constant selectorColumn fixedColumn adviceColumn
               instanceColumn challenge negated sum product scaled)
          (b.evaluate constant selectorColumn fixedColumn adviceColumn
            instanceColumn challenge negated sum product scaled)
  | .scaled a f =>
      scaled (a.evaluate constant selectorColumn fixedColumn adviceColumn
              instanceColumn challenge negated sum product scaled) f

-- rust: std usize::next_power_of_two (logup.rs:225, :265). Smallest 2^k >= n;
-- Rust gives 1 for both 0 and 1.
def nextPowerOfTwo (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

namespace Logup

-- rust: plonk/logup.rs:171-176 (struct BatchedArgument). inputExpressions is
-- [parallel_lookup][lookup_width], the unzip of the table_map the Rust new
-- takes (logup.rs:243-252).
structure BatchedArgument (F : Type) where
  name : String
  selector : Midfall.Halo2.Expression F
  inputExpressions : Array (Array (Midfall.Halo2.Expression F))
  tableExpressions : Array (Midfall.Halo2.Expression F)

open Midfall.Halo2 in
-- rust: logup.rs:224-239 (nb_parallel_lookups_per_chunk). max_degree =
-- (cs_degree - 1).next_power_of_two() + 1; lookup_degree is the max over the
-- flattened input degrees with unwrap_or(1); the result is the floor of
-- (max_degree - 1) / lookup_degree.
def BatchedArgument.nbParallelLookupsPerChunk {F : Type}
    (a : BatchedArgument F) (csDegree : Nat) : Nat :=
  let maxDegree := nextPowerOfTwo (csDegree - 1) + 1
  let flat := a.inputExpressions.flatMap (fun es => es.map (fun x => x.degree))
  let lookupDegree := if flat.foldl (init := 0) max = 0 then 1
                       else flat.foldl (init := 0) max
  (maxDegree - 1) / lookupDegree

-- rust: logup.rs:241-270 (degree_batched_argument). Helper constraint degree is
-- 1 + lookup_degree * nb; the accumulator constraint is
-- 2 + selector.degree + table_degree; the max is rounded so (x - 1) is a power
-- of two, which is what makes the chunked helper degrees equal cs.degree() and
-- therefore what makes Supported.hLimbs (assessment F7) true at all.
def BatchedArgument.degreeBatchedArgument {F : Type}
    (a : BatchedArgument F) (csDegree : Nat) : Nat :=
  let iflat := a.inputExpressions.flatMap (fun es => es.map (fun x => x.degree))
  let lookupDegree := if iflat.foldl (init := 0) max = 0 then 1
                       else iflat.foldl (init := 0) max
  let helper := a.nbParallelLookupsPerChunk csDegree * lookupDegree + 1
  let tflat := a.tableExpressions.map (fun x => x.degree)
  let tableDegree := if tflat.foldl (init := 0) max = 0 then 1
                      else tflat.foldl (init := 0) max
  let accumulator := 2 + a.selector.degree + tableDegree
  nextPowerOfTwo (max helper accumulator - 1) + 1

-- rust: logup.rs:316-319 (num_chunks): input_expressions.chunks(nb).count().
-- chunks(0) panics, which needs nb = 0, i.e. an input expression of degree at
-- least max_degree - 1 - a caller error, not a proof outcome. The port returns
-- 1 there and records the divergence rather than emulating the panic.
def BatchedArgument.numChunks {F : Type}
    (a : BatchedArgument F) (csDegree : Nat) : Nat :=
  let nb := a.nbParallelLookupsPerChunk csDegree
  if nb = 0 then 1 else divCeil a.inputExpressions.size nb

end Logup

namespace Trash

-- rust: plonk/trash.rs:11-15 (struct Argument).
structure Argument (F : Type) where
  name : String
  selector : Midfall.Halo2.Expression F
  constraintExpressions : Array (Midfall.Halo2.Expression F)

open Midfall.Halo2 in
-- rust: trash.rs:31-34 (required_degree): max 2 over the constraint degrees,
-- the 2 coming from (1 - q) * trash. An empty list gives 0, so the result is 2.
def Argument.requiredDegree {F : Type} (a : Argument F) : Nat :=
  max 2 ((a.constraintExpressions.map (fun x => x.degree)).foldl (init := 0) max)

end Trash

-- rust: plonk/permutation.rs:33-36 (struct Argument) - the *circuit*
-- permutation argument (its column list), not the VK's sigma commitments,
-- which Exec/Permutation models as PermutationAssembly.
structure PermutationArgument where
  columns : Array Column

-- rust: permutation.rs:46-78 (required_degree). Constant 3: there are degree-3
-- constraints regardless of how many columns participate.
def PermutationArgument.requiredDegree (_ : PermutationArgument) : Nat := 3

-- rust: circuit.rs:1619-1626 (struct Gate), field order as in the Rust.
structure Gate (F : Type) where
  name : String
  constraintNames : Array String
  polys : Array (Expression F)
  queriedSelectors : Array Selector
  queriedCells : Array VirtualCell

-- rust: circuit.rs:1641-1650 (polynomials, name, constraint_name,
-- queried_selectors).
def Gate.polynomials {F : Type} (g : Gate F) : Array (Expression F) := g.polys
def Gate.constraintName {F : Type} (g : Gate F) (i : Nat) : Option String :=
  g.constraintNames[i]?

-- rust: circuit.rs:1678-1727 (struct ConstraintSystem). All twenty fields in
-- source order (rule R1). general_column_annotations is a HashMap in Rust;
-- rule R6 allows that only where iteration order is unobservable, and it is:
-- read at circuit.rs:2568 and by plonk/dev/failure.rs:511,522 only, never on
-- the verifier path. It is carried as an ordered list regardless.
structure ConstraintSystem (F : Type) where
  numFixedColumns : Nat
  numAdviceColumns : Nat
  numInstanceColumns : Nat
  numSelectors : Nat
  selectorFlags : Array SelectorFlag
  numChallenges : Nat
  unblindedAdviceColumns : Array Nat
  adviceColumnPhase : Array Phase
  challengePhase : Array Phase
  gates : Array (Gate F)
  adviceQueries : Array AdviceQuery
  numAdviceQueries : Array Nat
  instanceQueries : Array InstanceQuery
  fixedQueries : Array FixedQuery
  permutation : PermutationArgument
  lookups : Array (Logup.BatchedArgument F)
  trashcans : Array (Trash.Argument F)
  generalColumnAnnotations : Array (Nat × String)
  constants : Array Column
  minimumDegree : Option Nat

-- rust: circuit.rs:2443-2468 (degree). Max over permutation, trash, gate
-- polynomial degrees and minimum_degree, defaulting to 1 when all are absent;
-- then the logUp batched degrees fold in. The unwrap_or(1) at :2456 is why
-- cs_degree >= 1 everywhere downstream, which Exec/Domain relies on for the
-- (j - 1) subtraction at domain.rs:39.
def ConstraintSystem.degree {F : Type} (cs : ConstraintSystem F) : Nat :=
  let gateDegrees := (cs.gates.flatMap (fun g => g.polys.map (fun x => x.degree))).foldl (init := 0) max
  let trashDegrees :=
    (cs.trashcans.map (fun a => a.requiredDegree)).foldl (init := 0) max
  let raw : Nat := max (max cs.permutation.requiredDegree trashDegrees) gateDegrees
  let raw := match cs.minimumDegree with
    | some d => max raw d
    | none => raw
  let withoutLookup : Nat := if raw = 0 then 1 else raw
  let withLookup := (cs.lookups.map (fun l => l.degreeBatchedArgument withoutLookup)).foldl (init := withoutLookup) max
  max withoutLookup withLookup

-- rust: circuit.rs:2472-2512 (blinding_factors). The exact chain matters: it
-- decides how many rows are unusable, hence the range of i the verifier checks
-- identities over and the l_i_range windows at verifier.rs:444. Steps: max
-- over num_advice_queries (unwrap_or(&1)), max with 3 for the permutation, +1
-- per trashcan, + the SUM of the logUp chunk counts, then +1 for multiopen at
-- x_3, +1 as an off-by-one defence and +1 for the linearization opening. The
-- i32::MAX check at :2511 is a real panic site, omitted here because Nat does
-- not overflow; Phase 4 should state it as a bound on the caller.
def ConstraintSystem.blindingFactors {F : Type}
    (cs : ConstraintSystem F) : Nat :=
  let d := cs.degree
  let amax := cs.numAdviceQueries.foldl (init := 0) max
  let factors := if amax = 0 then 1 else amax
  let factors := max 3 factors
  let factors := factors + cs.trashcans.size
  let factors := factors +
    (cs.lookups.map (fun l => l.numChunks d)).foldl (init := 0) (· + ·)
  let factors := factors + 1
  let factors := factors + 1
  factors + 1


-- ## Known-answer checks
--
-- Hand-computed over Fr 17. The point is the degree and blinding-factor chains,
-- since both decide the proof layout: degree fixes the quotient limb count
-- (Supported.hLimbs) and blinding_factors fixes how many rows the verifier
-- checks identities over.

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def nextPowerOfTwo_kats_ok : Bool :=
  [nextPowerOfTwo 0, nextPowerOfTwo 1, nextPowerOfTwo 2, nextPowerOfTwo 3,
   nextPowerOfTwo 5, nextPowerOfTwo 8, nextPowerOfTwo 9, nextPowerOfTwo 16] ==
    [1, 1, 2, 4, 8, 8, 16, 16]

def adv (i : Nat) : Expression (Fr 17) :=
  .advice { index := some i, columnIndex := i, rotation := .cur,
            phase := ⟨0⟩ }

def degree_kats_ok : Bool :=
  ((adv 0).degree == 1 &&
   (Expression.constant (2 : Fr 17)).degree == 0 &&
   (Expression.challenge (F := Fr 17) ⟨0, ⟨0⟩⟩).degree == 0 &&
   (Expression.product (adv 0) (adv 1)).degree == 2 &&
   (Expression.sum (adv 0) (Expression.constant 3)).degree == 1 &&
   (Expression.negated (Expression.product (adv 0) (adv 1))).degree == 2 &&
   (Expression.scaled (adv 0) 5).degree == 1 &&
   (Expression.product (Expression.product (adv 0) (adv 1)) (adv 2)).degree == 3)

-- evaluate with advice column i returning i+1 and everything else 0:
-- sum(advice 0, product(advice 1, constant 3)) = 1 + (2 * 3) = 7 mod 17.
def evaluate_kats_ok : Bool :=
  let e : Expression (Fr 17) :=
    .sum (adv 0) (.product (adv 1) (.constant 3));
  let v := e.evaluate (fun c => c) (fun _ => 0) (fun _ => 0)
    (fun q => Nat.cast (q.columnIndex + 1)) (fun _ => 0) (fun _ => 0)
    (fun x => -x) (fun a b => a + b) (fun a b => a * b) (fun a s => a * s);
  v.val == 7

-- A constraint system with the minimum fields set: the permutation argument
-- alone forces degree 3 even with no gates at all (permutation.rs:75-77, there
-- are constraints of degree 3 regardless of the number of columns).
def minCs : ConstraintSystem (Fr 17) :=
  { numFixedColumns := 0, numAdviceColumns := 0, numInstanceColumns := 0,
    numSelectors := 0, selectorFlags := #[], numChallenges := 0,
    unblindedAdviceColumns := #[], adviceColumnPhase := #[],
    challengePhase := #[], gates := #[], adviceQueries := #[],
    numAdviceQueries := #[], instanceQueries := #[], fixedQueries := #[],
    permutation := ⟨#[]⟩, lookups := #[], trashcans := #[],
    generalColumnAnnotations := #[], constants := #[], minimumDegree := none }

def cubicGate : Gate (Fr 17) :=
  { name := "g", constraintNames := #["c"],
    polys := #[Expression.product (Expression.product (adv 0) (adv 1)) (adv 2)],
    queriedSelectors := #[], queriedCells := #[] }

def trash4 : Trash.Argument (Fr 17) :=
  { name := "t", selector := adv 0,
    constraintExpressions :=
      #[Expression.product (Expression.product (adv 0) (adv 1))
         (Expression.product (adv 2) (adv 3))] }

def degreeCs_kats_ok : Bool :=
  let withGate := { minCs with gates := #[cubicGate] };
  let withMin := { minCs with minimumDegree := some 7 };
  let withTrash := { minCs with trashcans := #[trash4] };
  (minCs.degree == 3 &&
   -- the cubic gate does not raise it: permutation already demands 3
   withGate.degree == 3 &&
   withMin.degree == 7 &&
   -- trash requiredDegree is max 2 over the constraint degrees, here 4
   withTrash.degree == 4)

-- blinding_factors with no advice queries: max(3, 1) = 3, then +1 +1 +1 = 6
-- (multiopen at x3, the off-by-one defence, the linearization opening).
def emptyTrash : Trash.Argument (Fr 17) :=
  { name := "t", selector := adv 0, constraintExpressions := #[] }

def blinding_kats_ok : Bool :=
  let two := { minCs with numAdviceQueries := #[2] };
  let five := { minCs with numAdviceQueries := #[5] };
  let oneTrash := { minCs with trashcans := #[emptyTrash] };
  (minCs.blindingFactors == 6 &&
   two.blindingFactors == 6 &&
   -- queried five times: max(3, 5) = 5, then +3 = 8
   five.blindingFactors == 8 &&
   -- one trashcan adds 1 to the factors AND its own required degree is 2,
   -- so the degree stays 3 and the count goes 3 + 1 + 3 = 7
   oneTrash.blindingFactors == 7)

-- logUp chunking: with cs_degree 4, max_degree = (4-1).next_power_of_two()+1
-- = 4+1 = 5, input degree 1 gives nb = 4, so 3 inputs fit in one chunk and 5
-- need two.
def logup_kats_ok : Bool :=
  let a : Logup.BatchedArgument (Fr 17) :=
    { name := "l", selector := adv 0,
      inputExpressions := #[#[adv 0], #[adv 1], #[adv 2]],
      tableExpressions := #[adv 3] };
  let five := { a with inputExpressions :=
    #[#[adv 0], #[adv 1], #[adv 2], #[adv 3], #[adv 0]] };
  (a.nbParallelLookupsPerChunk 4 == 4 &&
   a.numChunks 4 == 1 &&
   five.numChunks 4 == 2 &&
   -- helper = 4*1+1 = 5, accumulator = 2+1+1 = 4, max 5,
   -- rounded (5-1).next_power_of_two()+1 = 5
   a.degreeBatchedArgument 4 == 5)
end Kats

#eval nextPowerOfTwo_kats_ok   -- expect true
#eval degree_kats_ok           -- expect true
#eval evaluate_kats_ok         -- expect true
#eval degreeCs_kats_ok         -- expect true
#eval blinding_kats_ok         -- expect true
#eval logup_kats_ok            -- expect true

end Midfall.Halo2
