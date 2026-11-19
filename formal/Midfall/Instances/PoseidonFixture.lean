-- |
-- Midfall.Instances.PoseidonFixture
--
-- F.1 (GEN - PORT, half 2): the deployment's conformance bundle read as DATA, one level
-- below every consumer of it. This module exists because the constraint system the bundle
-- describes is needed by TWO consumers that sit on opposite sides of the import graph:
-- Instances/PoseidonEnv (which builds the verifier-side VerifyingKey) and
-- Instances/DeployedProfile (which builds the generator-side ConstraintSystemMeta, and
-- therefore the plan, the model and the render). PoseidonEnv imports PoseidonInputs imports
-- DeployedProfile, so the parser cannot live in either of them; it lives here, and both
-- import it.
--
-- WHAT MOVED HERE from PoseidonEnv, unchanged: the vk.json payload (section 1 there), and
-- the constraint system built from it (section 4 there). WHAT IS NEW: section 4b, the
-- cs.json importer - gates, lookups, trashcans, permutation columns and challenge_phase,
-- each Expression rebuilt from the exporter's variant-tagged encoding.
--
-- NOTHING HERE IS TYPED IN. Every value is read out of a file the Rust exporter wrote, with
-- a strict accessor that errors on a missing or malformed key, and the empty payload a parse
-- failure leaves behind is deliberately unusable so that gate 1 of PoseidonEnv reddens.
--
import Midfall.Common.Json
import Midfall.Common.Bytes
import Midfall.Conformance.Bundle
import Midfall.Halo2.Exec.Circuit
import Midfall.Yul.Externals

namespace Midfall.Instances.PoseidonFixture

open Midfall Midfall.Halo2 Midfall.Conformance
open Midfall.Yul

/-- vk.json, baked in at build time. include_str resolves relative to THIS file and not to the CWD
    (measured in D.1, re-measured here), so the path is ../../fixtures/... from Midfall/Instances/. -/
def vkText : String := include_str "../../fixtures/conformance/poseidon/vk.json"

/-- params.json, same channel. -/
def paramsText : String := include_str "../../fixtures/conformance/poseidon/params.json"

/-- The one totaliser this file needs: a failed parse leaves the EMPTY payload behind, and gate 1 is
    what reddens if it is ever taken. Same shape as D.1's poseidonVkUnparsed, for the same reason: a
    default a parse failure can reach must be obviously broken, not plausibly fine. -/
def fromExcept {ε : Type} {α : Type} (e : Except ε α) (d : α) : α :=
  match e with | .ok a => a | .error _ => d

/-- col_idx is Option<usize> in Rust, and the exporter writes null for a selector that was converted
    away. jNat would call that an error, so the option gets its own strict reader. -/
def jOptNat (o : JValue) (k : String) : Except String (Option Nat) :=
  match o.getObjVal? k with
  | .ok Lean.Json.null => .ok none
  | .ok v => do pure (some (← jNatVal v))
  | .error e => .error e

/-- A hex field whose width the schema fixes. jHexBytes' would accept any even length, and R-20 is
    the record of what a width slip costs, so the width is asserted here. -/
def jHexFixed (o : JValue) (k : String) (nBytes : Nat) : Except String Bytes :=
  do jHexBytes (← jString o k) nBytes

/-- The vk.json payload as data. Every field is read with a strict accessor and nothing is coerced.
    The record keeps the JSON's shapes - (column, rotation) pairs, phases as Nat - rather than the
    Exec record's, so the KATs compare against the file and not against a translation of it. -/
structure PoseidonVkData where
  k : Nat
  n : Nat
  extendedK : Nat
  csDegree : Nat
  quotientPolyDegree : Nat
  numFixedColumns : Nat
  numAdviceColumns : Nat
  numInstanceColumns : Nat
  numChallenges : Nat
  numLookups : Nat
  numTrashcans : Nat
  numCommittedInstances : Nat
  nbPublicInputs : Nat
  scalarNumBits : Nat
  truncatedChallenges : Bool
  adviceColumnPhases : Array Nat
  adviceQueries : Array (Nat × Int)
  instanceQueries : Array (Nat × Int)
  fixedQueries : Array (Nat × Int)
  selectorFlags : Array SelectorFlag
  omegaBytes : Bytes
  omegaInvBytes : Bytes
  transcriptReprBytes : Bytes
  fixedCommitmentHex : Array Bytes
  permutationCommitmentHex : Array Bytes

def jSelectorFlags (o : JValue) (k : String) : Except String (Array SelectorFlag) := do
  let a ← jArray o k
  a.mapM fun f => do pure { isSimple := (← jBool f "is_simple"), colIdx := (← jOptNat f "col_idx") }

def poseidonVkData? : Except String PoseidonVkData := do
  let j ← jParse vkText
  pure {
    k := (← jNat j "k"), n := (← jNat j "n"), extendedK := (← jNat j "extended_k"),
    csDegree := (← jNat j "cs_degree"),
    quotientPolyDegree := (← jNat j "quotient_poly_degree"),
    numFixedColumns := (← jNat j "num_fixed_columns"),
    numAdviceColumns := (← jNat j "num_advice_columns"),
    numInstanceColumns := (← jNat j "num_instance_columns"),
    numChallenges := (← jNat j "num_challenges"),
    numLookups := (← jNat j "num_lookups"),
    numTrashcans := (← jNat j "num_trashcans"),
    numCommittedInstances := (← jNat j "num_committed_instances"),
    nbPublicInputs := (← jNat j "nb_public_inputs"),
    scalarNumBits := (← jNat j "scalar_num_bits"),
    truncatedChallenges := (← jBool j "truncated_challenges"),
    adviceColumnPhases := (← jNatArr j "advice_column_phase"),
    adviceQueries := (← jQueryArr j "advice_queries"),
    instanceQueries := (← jQueryArr j "instance_queries"),
    fixedQueries := (← jQueryArr j "fixed_queries"),
    selectorFlags := (← jSelectorFlags j "selector_flags"),
    omegaBytes := (← jHexFixed j "omega_be_hex" 32),
    omegaInvBytes := (← jHexFixed j "omega_inv_be_hex" 32),
    transcriptReprBytes := (← jHexFixed j "transcript_repr_be_hex" 32),
    fixedCommitmentHex := (← jHexArr j "fixed_commitments_compressed_hex"),
    permutationCommitmentHex := (← jHexArr j "permutation_commitments_compressed_hex") }

/-- The empty payload: every count 0, every list empty. A parse failure therefore cannot masquerade
    as a small key - poseidonVkExec built from it has an empty CS and a zero domain, and gate 1
    fails long before anything downstream could be believed. -/
def poseidonVkDataUnparsed : PoseidonVkData :=
  { k := 0, n := 0, extendedK := 0, csDegree := 0, quotientPolyDegree := 0,
    numFixedColumns := 0, numAdviceColumns := 0, numInstanceColumns := 0, numChallenges := 0,
    numLookups := 0, numTrashcans := 0, numCommittedInstances := 0, nbPublicInputs := 0,
    scalarNumBits := 0, truncatedChallenges := false, adviceColumnPhases := #[],
    adviceQueries := #[], instanceQueries := #[], fixedQueries := #[], selectorFlags := #[],
    omegaBytes := ByteArray.mk #[], omegaInvBytes := ByteArray.mk #[],
    transcriptReprBytes := ByteArray.mk #[], fixedCommitmentHex := #[],
    permutationCommitmentHex := #[] }

def poseidonVkData : PoseidonVkData := fromExcept poseidonVkData? poseidonVkDataUnparsed


/-! ## 4. The constraint system, from the keys vk.json has -/

/-- An advice column carries its phase in its kind (Exec/Circuit structural choice 2), and the phase
    is vk.json's advice_column_phase[i]. -/
def poseidonAdviceColumn (idx : Nat) : Column :=
  { index := idx, columnType := Any.advice { phase := { val :=
      (poseidonVkData.adviceColumnPhases[idx]?.getD 0) } } }

/-- A JSON rotation is an i32, so it becomes Rotation.value and never Rotation.cur. This is SAFE
    for deduplication only because REF.2 repaired `BEq Rotation` to compare the integer, as Rust's
    derived `PartialEq` on `Rotation(pub i32)` does: `Rotation.value 0 == Rotation.cur` is true
    here and in Rust, so a query the reference deduplicates, this import deduplicates. Before REF.2
    the structural instance kept the two spellings apart and the verifier could not find the key's
    own permutation queries (pinned by `poseidonPermutationQueries_ok`). -/
def poseidonRotation (r : Int) : Rotation := Rotation.value r

def poseidonAdviceQueries : Array (Column × Rotation) :=
  poseidonVkData.adviceQueries.map fun (c, r) => (poseidonAdviceColumn c, poseidonRotation r)

def poseidonInstanceQueries : Array (Column × Rotation) :=
  poseidonVkData.instanceQueries.map fun (c, r) =>
    ({ index := c, columnType := Any.instance }, poseidonRotation r)

def poseidonFixedQueries : Array (Column × Rotation) :=
  poseidonVkData.fixedQueries.map fun (c, r) =>
    ({ index := c, columnType := Any.fixed }, poseidonRotation r)

/-- num_advice_queries[i] is how many distinct queries advice column i has: circuit.rs's
    query_advice_index bumps it exactly when the (column, rotation) pair is new. So it is derivable
    from advice_queries, and it is derived here rather than invented. -/
def poseidonNumAdviceQueries : Array Nat :=
  (List.range poseidonVkData.numAdviceColumns).toArray.map fun i =>
    (poseidonVkData.adviceQueries.filter (fun q => q.1 == i)).size

/-! ## 4b. cs.json - the constraint system's STRUCTURE (F.1) -/

/-- cs.json, baked in exactly like vk.json and written by the SAME exporter run:
    proofs/solidity-verifier/tests/conformance_export.rs half 1. It carries the four
    structures vk.json never had - gates, lookups, trashcans and permutation.columns - plus
    challenge_phase, each expression tree intact, every value read out of the reference's
    own public accessors on the very vk.cs() the native verifier just checked the proof
    against. Nothing in this section is typed in. -/
def csText : String := include_str "../../fixtures/conformance/poseidon/cs.json"

/-- A field element the exporter wrote as big-endian hex: an Expression::Constant or the
    scalar of a Scaled. The same cast PoseidonEnv already uses for omega, faithful because
    the value is below blsR. -/
def jFieldBE (o : JValue) (k : String) : Except String (Fr blsR) := do
  let b ← jHexBytes' (← jString o k)
  return (bytesToNatBE b : Fr blsR)

/-- A rotation as the reference's raw i32, so Rotation.value and never .cur/.next/.prev -
    the same choice poseidonRotation makes for the query lists. Since REF.2 the two spellings are
    EQUAL by the repaired `BEq Rotation`, so this is a naming convention and not a divergence:
    `Rotation.value 0` and `Rotation.cur` find the same query, exactly as in Rust. -/
def jRotationOf (o : JValue) (k : String) : Except String Rotation := do
  let r ← jIntVal (← jObject o k)
  return (Rotation.value r)

/-- A bare JSON string inside an array; jString takes a key and the constraint-name lists
    are arrays of bare strings. -/
def jStrVal (v : JValue) : Except String String :=
  match v with
  | Lean.Json.str s => .ok s
  | _ => .error "json: not a string"

/-- One Expression back out of the exporter's variant-tagged encoding, which mirrors
    proofs/src/plonk/circuit.rs:824-849 one variant per key. An unknown tag is an ERROR and
    not a default: a cs.json from a newer reference must redden gate 15, not import a
    constraint system that quietly lost a node type. -/
partial def jExpr (v : JValue) : Except String (Expression (Fr blsR)) := do
  let kind ← jString v "k"
  match kind with
  | "constant" =>
      let c ← jFieldBE v "f"
      return (.constant c)
  | "selector" =>
      let i ← jNat v "index"
      let s ← jBool v "is_simple"
      return (.selector { index := i, isSimple := s })
  | "fixed" =>
      let i ← jOptNat v "index"
      let c ← jNat v "col"
      let r ← jRotationOf v "rot"
      return (.fixed { index := i, columnIndex := c, rotation := r })
  | "advice" =>
      let i ← jOptNat v "index"
      let c ← jNat v "col"
      let r ← jRotationOf v "rot"
      let ph ← jNat v "phase"
      return (.advice { index := i, columnIndex := c, rotation := r, phase := { val := ph } })
  | "instance" =>
      let i ← jOptNat v "index"
      let c ← jNat v "col"
      let r ← jRotationOf v "rot"
      return (.instance { index := i, columnIndex := c, rotation := r })
  | "challenge" =>
      let i ← jNat v "index"
      let ph ← jNat v "phase"
      return (.challenge { index := i, phase := { val := ph } })
  | "negated" =>
      let a ← jExpr (← jObject v "a")
      return (.negated a)
  | "sum" =>
      let a ← jExpr (← jObject v "a")
      let b ← jExpr (← jObject v "b")
      return (.sum a b)
  | "product" =>
      let a ← jExpr (← jObject v "a")
      let b ← jExpr (← jObject v "b")
      return (.product a b)
  | "scaled" =>
      let a ← jExpr (← jObject v "a")
      let s ← jFieldBE v "f"
      return (.scaled a s)
  | other => .error ("cs.json: unknown expression kind " ++ other)

/-- An array of expressions under a key. -/
def jExprArr (o : JValue) (k : String) : Except String (Array (Expression (Fr blsR))) := do
  let a ← jArray o k
  a.mapM jExpr

/-- A JSON array that is a VALUE rather than a field - the inner level of a lookup's
    input_expressions, which is an array of parallel lookups each of which is an array of
    width. jArray takes a key, so the bare form needs its own strict reader. -/
def jArrayVal (v : JValue) : Except String (Array JValue) :=
  match v with
  | Lean.Json.arr a => .ok a
  | _ => .error "json: not an array"

/-- A Column<Any> as the exporter names it: kind, index and - advice only - the phase that
    lives in the column's kind. -/
def jColumnOf (v : JValue) : Except String Column := do
  let t ← jString v "type"
  let idx ← jNat v "index"
  match t with
  | "advice" =>
      let ph ← jOptNat v "phase"
      return { index := idx, columnType := Any.advice { phase := { val := ph.getD 0 } } }
  | "fixed" => return { index := idx, columnType := Any.fixed }
  | "instance" => return { index := idx, columnType := Any.instance }
  | other => .error ("cs.json: unknown column type " ++ other)

/-- A Selector as the exporter names it: index and the simple flag, in the Rust's tuple
    order (circuit.rs:463). -/
def jSelectorOf (v : JValue) : Except String Selector := do
  let i ← jNat v "index"
  let s ← jBool v "is_simple"
  return { index := i, isSimple := s }

/-- One gate. queriedCells is the ONE field of Gate that is not here: Gate::queried_cells is
    pub(crate) (circuit.rs:1651) and so is unreachable from an integration test. It is listed
    in cs.json's own not_exported array and it is EMPTY here, not guessed - and nothing on the
    plan path reads it: ConstraintSystem::degree walks polys,
    ProtocolPlan::from_constraint_system counts them, and the verifier's own use
    (plonk/mod.rs:543) is on neither path. -/
def jGate (v : JValue) : Except String (Gate (Fr blsR)) := do
  let name ← jString v "name"
  let cn ← (← jArray v "constraint_names").mapM jStrVal
  let polys ← jExprArr v "polys"
  let qs ← (← jArray v "queried_selectors").mapM jSelectorOf
  return { name := name, constraintNames := cn, polys := polys,
           queriedSelectors := qs, queriedCells := #[] }

/-- One lookup. The reference's BatchedArgument exposes NO name accessor (logup.rs:172 is
    pub(crate)), so the name here is positional and says so, and nothing on the plan path
    reads a lookup name. inputExpressions is the flattened chunk list, which IS the original
    input_expressions: chunk_by_degree partitions it in order (logup.rs:326-338). -/
def jLookup (i : Nat) (v : JValue) : Except String (LogupBatchedArgument (Fr blsR)) := do
  let sel ← jExpr (← jObject v "selector")
  let ie ← (← jArray v "input_expressions").mapM fun inner => do
    (← jArrayVal inner).mapM jExpr
  let te ← jExprArr v "table_expressions"
  return { name := "lookup[" ++ toString i ++ "]", selector := sel,
           inputExpressions := ie, tableExpressions := te }

/-- The lookups, indexed so the positional name is honest about being positional. -/
def jLookups (ls : Array JValue) :
    Except String (Array (LogupBatchedArgument (Fr blsR))) :=
  ls.foldlM (fun (acc : Array (LogupBatchedArgument (Fr blsR))) v => do
    let l ← jLookup acc.size v
    return acc.push l) #[]

/-- One trashcan: name, selector and constraints, all three of which the reference does
    expose (trash.rs:37-48). -/
def jTrash (v : JValue) : Except String (TrashArgument (Fr blsR)) := do
  let n ← jString v "name"
  let sel ← jExpr (← jObject v "selector")
  let ce ← jExprArr v "constraint_expressions"
  return { name := n, selector := sel, constraintExpressions := ce }

/-- cs.json as data, including the summary numbers the exporter computes from the same
    accessors, so an importer that dropped a subtree cannot pass a count gate by accident. -/
structure PoseidonCsData where
  csDegree : Nat
  blindingFactors : Nat
  numSimpleSelectors : Nat
  challengePhase : Array Nat
  permutationColumns : Array Column
  gates : Array (Gate (Fr blsR))
  lookups : Array (LogupBatchedArgument (Fr blsR))
  trashcans : Array (TrashArgument (Fr blsR))
  numGates : Nat
  gatePolyTotal : Nat
  numChunks : Array Nat

def poseidonCsData? : Except String PoseidonCsData := do
  let j ← jParse csText
  let sum ← jObject j "summary"
  let csDegree ← jNat j "cs_degree"
  let blindingFactors ← jNat j "blinding_factors"
  let numSimpleSelectors ← jNat j "num_simple_selectors"
  let challengePhase ← jNatArr j "challenge_phase"
  let permutationColumns ← (← jArray j "permutation_columns").mapM jColumnOf
  let gates ← (← jArray j "gates").mapM jGate
  let ls ← jArray j "lookups"
  let lookups ← jLookups ls
  let trashcans ← (← jArray j "trashcans").mapM jTrash
  let numGates ← jNat sum "num_gates"
  let gatePolyTotal ← jNat sum "gate_poly_total"
  let numChunks ← ls.mapM fun v => jNat v "num_chunks_at_cs_degree"
  return { csDegree := csDegree, blindingFactors := blindingFactors,
           numSimpleSelectors := numSimpleSelectors, challengePhase := challengePhase,
           permutationColumns := permutationColumns, gates := gates, lookups := lookups,
           trashcans := trashcans, numGates := numGates, gatePolyTotal := gatePolyTotal,
           numChunks := numChunks }

/-- The empty payload, so a parse failure cannot masquerade as a small circuit: every array is
    empty and every count 0, and gate 15 fails long before anything downstream is believed. -/
def poseidonCsDataUnparsed : PoseidonCsData :=
  { csDegree := 0, blindingFactors := 0, numSimpleSelectors := 0, challengePhase := #[],
    permutationColumns := #[], gates := #[], lookups := #[], trashcans := #[],
    numGates := 0, gatePolyTotal := 0, numChunks := #[] }

def poseidonCsData : PoseidonCsData := fromExcept poseidonCsData? poseidonCsDataUnparsed

/-- THE CONSTRAINT SYSTEM. Filled from vk.json where vk.json has the data and from
    ConstraintSystem.default where it does not. The four fields with no source are named in the
    header (gap A): gates, lookups, trashcans, permutation.columns. numSelectors is NOT one of them:
    the reference's selector() pushes one flag per selector, so num_selectors = selector_flags.len(),
    and that is how it is derived here. -/
def poseidonCsVkOnly : ConstraintSystem (Fr blsR) :=
  { ConstraintSystem.default with
    numFixedColumns := poseidonVkData.numFixedColumns
    numAdviceColumns := poseidonVkData.numAdviceColumns
    numInstanceColumns := poseidonVkData.numInstanceColumns
    numSelectors := poseidonVkData.selectorFlags.size
    selectorFlags := poseidonVkData.selectorFlags
    numChallenges := poseidonVkData.numChallenges
    adviceColumnPhase := poseidonVkData.adviceColumnPhases.map fun ph => { val := ph }
    adviceQueries := poseidonAdviceQueries
    numAdviceQueries := poseidonNumAdviceQueries
    instanceQueries := poseidonInstanceQueries
    fixedQueries := poseidonFixedQueries }

/-- THE CONSTRAINT SYSTEM, WHOLE: the vk.json half above plus the five fields cs.json supplies
    (F.1) - challenge_phase, the gates, the permutation columns, the lookups and the trashcans.
    Stated as a second update rather than as more lines of the first because a single
    structure-update over ConstraintSystem.default that reaches all sixteen of these fields does
    NOT elaborate ("don't know how to synthesize implicit argument F", measured: any ONE of the
    five added fields builds, any TWO do not). The split is notation, not semantics - the term is
    the same record - and it is recorded here rather than left as a mystery. -/
def poseidonCs : ConstraintSystem (Fr blsR) :=
  { poseidonCsVkOnly with
    challengePhase := poseidonCsData.challengePhase.map fun ph => ({ val := ph } : Phase)
    gates := poseidonCsData.gates
    permutation := { columns := poseidonCsData.permutationColumns }
    lookups := poseidonCsData.lookups
    trashcans := poseidonCsData.trashcans }


end Midfall.Instances.PoseidonFixture
