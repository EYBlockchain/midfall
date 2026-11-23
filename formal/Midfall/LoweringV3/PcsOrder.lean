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

/-- The permutationZ block count: `ceil(columns / (degree - 2))`, with the
    empty-columns arm at zero (`PM:334-339`). -/
def pcsNumPermutationZs {F : Type} (cs : ConstraintSystem F) (dg : Nat) : Nat :=
  if cs.permutation.getColumns.toList.isEmpty then 0
  else divCeil cs.permutation.getColumns.toList.length (dg - 2)

def pcsAdviceBlock {F : Type} (cs : ConstraintSystem F) : List PcsQuerySource :=
  (cs.adviceQueries.toList.map fun (column, rotation) =>
    QueryKey.new column.index rotation.int).map PcsQuerySource.advice

def pcsCommittedInstanceBlock {F : Type} (cs : ConstraintSystem F)
    (nbCommittedInstances : Nat) : List PcsQuerySource :=
  ((cs.instanceQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int).filter
    fun q => q.column < nbCommittedInstances).map PcsQuerySource.committedInstance

def pcsLookupBlock {F : Type} (cs : ConstraintSystem F) (dg : Nat)
    (lc : List Nat) : List PcsQuerySource :=
  (((List.range lc.length).zip lc).map fun (lookup, chunks) =>
    [PcsQuerySource.lookupMultiplicity lookup]
      ++ (List.range chunks).map (fun chunk => PcsQuerySource.lookupHelper lookup chunk)
      ++ [PcsQuerySource.lookupAccumulator lookup 0,
          PcsQuerySource.lookupAccumulator lookup 1]).flatten

def pcsTrashBlock {F : Type} (cs : ConstraintSystem F) : List PcsQuerySource :=
  (List.range cs.trashcans.size).map PcsQuerySource.trash

def pcsFixedBlock {F : Type} (cs : ConstraintSystem F) : List PcsQuerySource :=
  let fixedQueries :=
    cs.fixedQueries.toList.map fun (column, rotation) =>
      QueryKey.new column.index rotation.int
  let simpleSelectorCols :=
    (List.range cs.numFixedColumns).filter (fun idx => cs.hasSimpleSelectorCol idx)
  (fixedQueries.filter fun q => !(q.column ∈ simpleSelectorCols)).map PcsQuerySource.fixed

def pcsPermutationCommonBlock {F : Type} (cs : ConstraintSystem F) : List PcsQuerySource :=
  cs.permutation.getColumns.toList.map PcsQuerySource.permutationCommon

/-- The literal `pcsQueries` construction of
    `ProtocolPlan.fromConstraintSystem` (PM:527-580), with the two computed
    values it depends on made parameters: the degree `dg` (`cs.degree`) and the
    flattened lookup chunk counts `lc` (`mapExceptArray ... |>.toList`).
    Everything else is a pure function of `cs` and `nbCommittedInstances`. -/
def pcsBlocks {F : Type} (cs : ConstraintSystem F) (nbCommittedInstances dg : Nat)
    (lc : List Nat) : List (List PcsQuerySource) :=
  [pcsAdviceBlock cs, pcsCommittedInstanceBlock cs nbCommittedInstances,
    permZBlock (pcsNumPermutationZs cs dg), pcsLookupBlock cs dg lc,
    pcsTrashBlock cs, pcsFixedBlock cs, pcsPermutationCommonBlock cs,
    [PcsQuerySource.linearization]]

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
      simp [pcsBlockList, pcsBlocks, pcsAdviceBlock, pcsCommittedInstanceBlock,
        pcsLookupBlock, pcsTrashBlock, pcsFixedBlock, pcsPermutationCommonBlock,
        pcsNumPermutationZs, permZBlock, List.append_assoc]
    · cases h
  · cases h

/-- The reordering `KZ:159-186` applies to the z-sources: all `cur/next` in
    ascending set order, then the `last` openings reversed. -/
def upstreamBlock (z : List PcsQuerySource) : List PcsQuerySource :=
  (z.filter permZIsCurOrNext) ++ (z.filter permZIsLast).reverse

theorem flatten_map_ite {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    ((l.map fun a => if p a then [f a] else []).flatten) = (l.filter p).map f := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a = true <;> simp [h, ih]

theorem flatten_map_singleton {α β : Type} (l : List α) (f : α → β) :
    ((l.map fun a => [f a]).flatten) = l.map f := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]

theorem filter_range_pred_rev (k : Nat) :
    ((List.range k).filter (fun set => set + 1 != k)).reverse =
      (List.range k).reverse.drop 1 := by
  cases k with
  | zero => simp
  | succ n =>
      rw [List.range_succ, List.filter_append]
      have hnil : List.filter (fun set => set + 1 != n + 1) [n] = [] := by simp
      have hrange : List.filter (fun set => set + 1 != n + 1) (List.range n) =
          List.range n := by
        rw [List.filter_eq_self]
        intro a ha
        have hlt := List.mem_range.mp ha
        simp
        omega
      rw [hnil, hrange, List.append_nil, List.reverse_append]
      rw [List.reverse_singleton, List.singleton_append]
      simp

/-- **The permutationZ block reorders exactly to the upstream verifier
    order.** This is the order half of the KZG pairing for the z block: the
    generator's per-set `cur,next,last` interleaving, filtered and reversed by
    `upstreamBlock`, is the verifier's `head.flatten ++ tail.flatten`
    (`Halo2/Exec/Permutation.lean:276-290`). -/
theorem upstreamBlock_permZBlock (k : Nat) :
    upstreamBlock (permZBlock k) = permZUpstream k := by
  unfold upstreamBlock permZBlock permZUpstream
  rw [List.filter_flatten, List.filter_flatten]
  simp only [List.map_map, Function.comp_def]
  congr 1
  · apply congrArg List.flatten
    apply List.map_congr_left
    intro set _hset
    have hcur : permZIsCurOrNext (PcsQuerySource.permutationZ set PermutationZEval.cur) = true := rfl
    have hnext : permZIsCurOrNext (PcsQuerySource.permutationZ set PermutationZEval.next) = true := rfl
    have hlast : permZIsCurOrNext (PcsQuerySource.permutationZ set PermutationZEval.last) = false := rfl
    by_cases h : set + 1 != k <;> simp [hcur, hnext, hlast, h]
  · have hinside :
        ((List.map (fun set => List.filter permZIsLast
            ([PcsQuerySource.permutationZ set PermutationZEval.cur,
              PcsQuerySource.permutationZ set PermutationZEval.next]
              ++ (if set + 1 != k then
                    [PcsQuerySource.permutationZ set PermutationZEval.last] else [])))
          (List.range k)).flatten) =
        ((List.map (fun set =>
            if set + 1 != k then
              [PcsQuerySource.permutationZ set PermutationZEval.last] else [])
          (List.range k)).flatten) := by
      congr 1
      apply List.map_congr_left
      intro set _hset
      by_cases h : set + 1 != k <;> simp [permZIsLast, h]
    rw [hinside, flatten_map_ite, ← List.map_reverse, filter_range_pred_rev]
    rw [flatten_map_singleton]


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
