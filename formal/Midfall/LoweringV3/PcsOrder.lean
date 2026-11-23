-- |
-- Midfall.LoweringV3.PcsOrder
--
-- The literal PCS-query block order of `ProtocolPlan.fromConstraintSystem`,
-- exposed as a standalone list `pcsBlockList` and projected out of the final
-- `match plan.validate` wrapper.  This is the generator-side spine for the
-- same-order comparison with `Verifier.collectQueries`: advice, committed
-- instance, permutationZ, lookup, trash, fixed, permutation common, and the
-- linearization singleton, in exactly that order.
import Midfall.Generator.Encoding
import Midfall.LoweringV3.KzgQueryMap

set_option autoImplicit false

namespace Midfall.Generator

open Midfall Midfall.Halo2

/-- The permutationZ PCS block in the generator's own order: per set
    `cur, next`, plus `last` for every set but the final one. -/
def permZBlock (k : Nat) : List PcsQuerySource :=
  ((List.range k).map fun set =>
    [PcsQuerySource.permutationZ set PermutationZEval.cur,
      PcsQuerySource.permutationZ set PermutationZEval.next]
      ++ (if set + 1 != k then
            [PcsQuerySource.permutationZ set PermutationZEval.last] else [])).flatten

/-- The same block reordered the way the upstream verifier emits it: all
    `cur/next` openings in ascending set order, then the `last` openings in
    descending set order (`KZ:159-186`). -/
def permZUpstream (k : Nat) : List PcsQuerySource :=
  (((List.range k).map fun set =>
      [PcsQuerySource.permutationZ set PermutationZEval.cur,
        PcsQuerySource.permutationZ set PermutationZEval.next]).flatten)
    ++ ((((List.range k).reverse.drop 1).map fun set =>
      [PcsQuerySource.permutationZ set PermutationZEval.last]).flatten)

/-- At the deployment's three permutation sets the two orders differ.  This is
    the exact reason a literal same-order theorem against raw `pcsQueries`
    cannot hold; the generator's own upstream reordering is the target. -/
theorem permZBlock_three :
    permZBlock 3 =
      [PcsQuerySource.permutationZ 0 PermutationZEval.cur,
        PcsQuerySource.permutationZ 0 PermutationZEval.next,
        PcsQuerySource.permutationZ 0 PermutationZEval.last,
        PcsQuerySource.permutationZ 1 PermutationZEval.cur,
        PcsQuerySource.permutationZ 1 PermutationZEval.next,
        PcsQuerySource.permutationZ 1 PermutationZEval.last,
        PcsQuerySource.permutationZ 2 PermutationZEval.cur,
        PcsQuerySource.permutationZ 2 PermutationZEval.next] := rfl

theorem permZUpstream_three :
    permZUpstream 3 =
      [PcsQuerySource.permutationZ 0 PermutationZEval.cur,
        PcsQuerySource.permutationZ 0 PermutationZEval.next,
        PcsQuerySource.permutationZ 1 PermutationZEval.cur,
        PcsQuerySource.permutationZ 1 PermutationZEval.next,
        PcsQuerySource.permutationZ 2 PermutationZEval.cur,
        PcsQuerySource.permutationZ 2 PermutationZEval.next,
        PcsQuerySource.permutationZ 1 PermutationZEval.last,
        PcsQuerySource.permutationZ 0 PermutationZEval.last] := rfl

theorem permZBlock_three_beq_upstream :
    (permZBlock 3 == permZUpstream 3) = false := rfl

/-- The literal `pcsQueries` construction of
    `ProtocolPlan.fromConstraintSystem` (PM:527-580), with the two computed
    values it depends on made parameters: the degree `dg` (`cs.degree`) and the
    flattened lookup chunk counts `lc` (`mapExceptArray ... |>.toList`).
    Everything else is a pure function of `cs` and `nbCommittedInstances`. -/
def pcsBlocks {F : Type} (cs : ConstraintSystem F) (nbCommittedInstances dg : Nat)
    (lc : List Nat) : List (List PcsQuerySource) :=
  let numPermutationZs :=
    if cs.permutation.getColumns.toList.isEmpty then 0
    else divCeil cs.permutation.getColumns.toList.length (dg - 2)
  let adviceQueries :=
    cs.adviceQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  let fixedQueries :=
    cs.fixedQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  let instanceQueries :=
    cs.instanceQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  let simpleSelectorCols :=
    (List.range cs.numFixedColumns).filter (fun idx => cs.hasSimpleSelectorCol idx)
  let committedInstanceQueries :=
    instanceQueries.filter fun q => q.column < nbCommittedInstances
  let nonSimpleFixedQueryList :=
    fixedQueries.filter fun q => !(q.column ∈ simpleSelectorCols)
  let pcsAdvice := adviceQueries.map PcsQuerySource.advice
  let pcsCommittedInstances := committedInstanceQueries.map PcsQuerySource.committedInstance
  let pcsPermutationZ := permZBlock numPermutationZs
  let pcsLookup :=
    ((List.range lc.length).zip lc).map fun (lookup, chunks) =>
      [PcsQuerySource.lookupMultiplicity lookup]
        ++ (List.range chunks).map (fun chunk => PcsQuerySource.lookupHelper lookup chunk)
        ++ [PcsQuerySource.lookupAccumulator lookup 0,
            PcsQuerySource.lookupAccumulator lookup 1]
  let pcsTrash := (List.range cs.trashcans.size).map PcsQuerySource.trash
  let pcsFixed := nonSimpleFixedQueryList.map PcsQuerySource.fixed
  let pcsPermutationCommon :=
    cs.permutation.getColumns.toList.map PcsQuerySource.permutationCommon
  [pcsAdvice, pcsCommittedInstances, pcsPermutationZ, pcsLookup.flatten,
    pcsTrash, pcsFixed, pcsPermutationCommon, [PcsQuerySource.linearization]]

/-- The flat form of `pcsBlocks`: the eight-block spine the KZG lane compares. -/
def pcsBlockList {F : Type} (cs : ConstraintSystem F) (nbCommittedInstances dg : Nat)
    (lc : List Nat) : List PcsQuerySource :=
  (pcsBlocks cs nbCommittedInstances dg lc).flatten

theorem cert_except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `fromConstraintSystem` writes exactly `pcsBlockList` into `pcsQueries`.
    The only wrapper is the final `match plan.validate`; it is split, not
    inverted, so no validity hypothesis is needed. -/
theorem ProtocolPlan.fromConstraintSystem_pcsQueries {F : Type} (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) (plan : ProtocolPlan)
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok plan) :
    ∃ (dg : Nat) (lc : Array Nat), cs.degree = .ok dg ∧
      plan.pcsQueries = pcsBlockList cs nb dg lc.toList := by
  unfold ProtocolPlan.fromConstraintSystem at h
  simp only [Bind.bind] at h
  obtain ⟨dg, hdg, h⟩ := cert_except_bind_ok h
  obtain ⟨lc, _hlc, h⟩ := cert_except_bind_ok h
  obtain ⟨_nua, _hnua, h⟩ := cert_except_bind_ok h
  obtain ⟨_nuc, _hnuc, h⟩ := cert_except_bind_ok h
  obtain ⟨_bf, _hbf, h⟩ := cert_except_bind_ok h
  split at h
  · split at h
    · cases h
      refine ⟨dg, lc, hdg, ?_⟩
      simp [pcsBlockList, pcsBlocks, permZBlock, List.append_assoc]
    · cases h
  · cases h

end Midfall.Generator

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

/-- The same projection, restated in the `LoweringV3` namespace for the KZG
    lane. -/
theorem fromConstraintSystem_pcsQueries {F : Type} (feat : Features)
    (cs : ConstraintSystem F) (nb : Nat) (plan : ProtocolPlan)
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok plan) :
    ∃ (dg : Nat) (lc : Array Nat), cs.degree = .ok dg ∧
      plan.pcsQueries = pcsBlockList cs nb dg lc.toList :=
  ProtocolPlan.fromConstraintSystem_pcsQueries feat cs nb plan h

end Midfall.LoweringV3
