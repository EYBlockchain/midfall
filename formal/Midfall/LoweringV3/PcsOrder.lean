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

/-- The literal `pcsQueries` construction of
    `ProtocolPlan.fromConstraintSystem` (PM:527-580), with the two computed
    values it depends on made parameters: the degree `dg` (`cs.degree`) and the
    flattened lookup chunk counts `lc` (`mapExceptArray ... |>.toList`).
    Everything else is a pure function of `cs` and `nbCommittedInstances`. -/
def pcsBlockList {F : Type} (cs : ConstraintSystem F) (nbCommittedInstances dg : Nat)
    (lc : List Nat) : List PcsQuerySource :=
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
  let pcsPermutationZ :=
    (List.range numPermutationZs).map fun set =>
      [PcsQuerySource.permutationZ set PermutationZEval.cur,
        PcsQuerySource.permutationZ set PermutationZEval.next]
        ++ (if set + 1 != numPermutationZs
            then [PcsQuerySource.permutationZ set PermutationZEval.last] else [])
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
  pcsAdvice ++ pcsCommittedInstances ++ pcsPermutationZ.flatten ++ pcsLookup.flatten
    ++ pcsTrash ++ pcsFixed ++ pcsPermutationCommon ++ [PcsQuerySource.linearization]

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
      simp only [pcsBlockList, List.append_assoc]
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
