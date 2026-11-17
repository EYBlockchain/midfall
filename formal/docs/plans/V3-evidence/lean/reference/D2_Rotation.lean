/-
  D2 - THE ROTATION REPAIR (E-6): semantic equality on `Rotation`.
  Part 1: who depends on the derived structural `BEq Rotation` instance (measured, not grepped).
  Part 2: the eight permutation columns of the imported poseidon constraint system - today and
          after the repair.
-/
import Lean
import Midfall.Instances.PoseidonFixture
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Domain

set_option autoImplicit false

open Lean Meta Elab Command in
/-- Direct users of a constant among the declarations of the `Midfall` namespace. -/
elab "#direct_users " id:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`Midfall).isPrefixOf n && !n.isInternalDetail then
      let used := (ci.value?.map (·.getUsedConstants)).getD #[] ++ ci.type.getUsedConstants
      if used.contains target then hits := hits.push n
  let sorted := hits.qsort (fun a b => a.toString < b.toString)
  logInfo m!"{target}: {sorted.size} direct users\n{sorted.toList}"

namespace RefDesign
open Midfall Midfall.Halo2 Midfall.Instances.PoseidonFixture

/-! ## Part 1 -/

-- the instance `deriving BEq` generated at Exec/Circuit.lean:130-132
#check (inferInstance : BEq Rotation)
#direct_users Midfall.Halo2.instBEqRotation

/-! ## Part 2 -/

/-- THE REPAIR, as it would read at Exec/Circuit.lean:130-132 once `Rotation.int` (today
    Exec/Domain.lean:90-94) is moved up next to the inductive:

      inductive Rotation where
        | cur | next | prev | value (v : Int)

      def Rotation.int : Rotation → Int
        | .cur => 0 | .next => 1 | .prev => -1 | .value v => v

      /-- rust: `#[derive(PartialEq)] pub struct Rotation(pub i32)`: equality of the integer. -/
      instance : BEq Rotation := ⟨fun a b => a.int == b.int⟩

    Stated here as a named instance so both relations can be evaluated side by side. -/
def rotBEqSemantic : BEq Rotation := ⟨fun a b => a.int == b.int⟩

/-- `ConstraintSystem.getAnyQueryIndex` (Exec/Circuit.lean:1291-1325) with the repaired
    instance in scope. The bodies are the tree's, textually; only the instance differs. -/
def getAnyQueryIndexR {F : Type} (cs : ConstraintSystem F) (column : Column) (at' : Rotation) :
    Except Fault Nat :=
  letI : BEq Rotation := rotBEqSemantic
  match column.columnType with
  | .advice _ =>
      match cs.adviceQueries.toList.findIdx? (fun q => q == (column, at')) with
      | some i => .ok i
      | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2074")
  | .fixed =>
      match cs.fixedQueries.toList.findIdx? (fun q => q == (column, at')) with
      | some i => .ok i
      | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2084")
  | .instance =>
      match cs.instanceQueries.toList.findIdx? (fun q => q == (column, at')) with
      | some i => .ok i
      | none => .error (Fault.panic "proofs/src/plonk/circuit.rs:2094")

def show' (r : Except Fault Nat) : String :=
  match r with
  | .ok i => "ok " ++ toString i
  | .error (Fault.panic s) => "PANIC " ++ s
  | .error (Fault.error _) => "error"

def colName (c : Column) : String :=
  (match c.columnType with | .advice _ => "advice" | .fixed => "fixed" | .instance => "instance")
    ++ " " ++ toString c.index

-- the eight permutation columns of the imported key
#eval poseidonCs.permutation.columns.toList.map colName

-- TODAY (the tree's function, structural BEq): every column panics
#eval poseidonCs.permutation.columns.toList.map
  (fun c => show' (poseidonCs.getAnyQueryIndex c Rotation.cur))

-- AFTER THE REPAIR: every column resolves
#eval poseidonCs.permutation.columns.toList.map
  (fun c => show' (getAnyQueryIndexR poseidonCs c Rotation.cur))

/-- The gate: all eight succeed after the repair, all eight fail today, and each repaired index
    points at a query for THAT column at integer rotation 0. -/
def rotationRepair_ok : Bool :=
  poseidonCs.permutation.columns.size == 8 &&
  poseidonCs.permutation.columns.toList.all (fun c =>
    (match poseidonCs.getAnyQueryIndex c Rotation.cur with | .ok _ => false | .error _ => true) &&
    (match getAnyQueryIndexR poseidonCs c Rotation.cur with
     | .error _ => false
     | .ok i =>
        let qs := match c.columnType with
          | .advice _ => poseidonCs.adviceQueries
          | .fixed => poseidonCs.fixedQueries
          | .instance => poseidonCs.instanceQueries
        (match qs[i]? with
         | some q => q.1.index == c.index && q.2.int == (0 : Int)
         | none => false)))

#eval rotationRepair_ok      -- expect true

-- the hazard KAT of Exec/Circuit.lean:1892 flips: the two spellings of rotation 0 are EQUAL
#eval (rotBEqSemantic.beq Rotation.cur (Rotation.value 0),
       rotBEqSemantic.beq Rotation.next (Rotation.value 1),
       rotBEqSemantic.beq Rotation.prev (Rotation.value (-1)),
       rotBEqSemantic.beq Rotation.cur Rotation.next)   -- expect (true, true, true, false)

end RefDesign
