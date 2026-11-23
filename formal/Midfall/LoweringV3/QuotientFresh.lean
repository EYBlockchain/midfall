import Midfall.LoweringV3.KzgQueryMap
import Midfall.Generator.LayoutMemory
open Midfall Midfall.Halo2 Midfall.Generator
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Midfall.Generator

def Ptr.Numeric (p : Ptr) : Prop := ∃ i : Int, p.value = .integer i
def EcPoint.Numeric (c : EcPoint) : Prop := c.base.Numeric
def quotientComm : EcPoint := EcPoint.new (ptrMemory (valueFromStr "QUOTIENT_MPTR"))

theorem Ptr.add_numeric (p : Ptr) (n : Nat) (h : p.Numeric) : (p.add n).Numeric := by
  obtain ⟨i, hi⟩ := h
  rcases p with ⟨loc, value⟩
  simp only at hi
  subst hi
  exact ⟨i + (n : Int) * (wordBytes : Int), rfl⟩
theorem EcPoint.fromPtr_numeric (p : Ptr) (h : p.Numeric) : (EcPoint.fromPtr p).Numeric := h
theorem EcPoint.range_numeric (p : EcPoint) (n : Nat) (h : p.Numeric) :
    (EcPoint.range p n).Numeric := by
  unfold EcPoint.range
  exact Ptr.add_numeric p.base (4 * n) h
theorem takeIter_numeric (f : Nat → EcPoint) (n : Nat)
    (h : ∀ a, (f a).Numeric) : ∀ c ∈ takeIter f n, c.Numeric := by
  intro c hc
  simp only [takeIter, List.mem_map] at hc
  obtain ⟨a, _, rfl⟩ := hc
  exact h a

def VerifierMemoryLayout.NumericBases (m : VerifierMemoryLayout) : Prop :=
  m.vkMptr.Numeric ∧ m.commsMptrBase.Numeric ∧ m.permZCommsMptrBase.Numeric ∧
  m.lookupMCommsMptrBase.Numeric ∧ m.lookupHelperCommsMptrBase.Numeric ∧
  m.lookupZCommsMptrBase.Numeric ∧ m.trashcanCommsMptrBase.Numeric

end Midfall.Generator

namespace Midfall.LoweringV3
open Midfall.Generator

theorem dataMatchOk {α β γ : Type} (x : Except α β) (f : β → Except α γ) {η : γ} :
    (match x with
     | Except.error e => Except.error e
     | Except.ok y => f y) = Except.ok η ↔ ∃ y, x = Except.ok y ∧ f y = Except.ok η := by
  constructor
  · intro h
    cases x with
    | error e => cases h
    | ok y => exact ⟨y, rfl, h⟩
  · rintro ⟨y, rfl, hy⟩
    exact hy

theorem Data.new_computedQuotientComm {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (h : Data.new meta_ vk memory = .ok data) :
    data.computedQuotientComm = quotientComm := by
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    rfl

theorem Data.new_fixedComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.fixedComms, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    exact takeIter_numeric (fun i => (EcPoint.fromPtr (memory.vkMptr.add vk.constants.length)).range i)
      meta_.numFixeds (fun i => EcPoint.range_numeric _ i
        (EcPoint.fromPtr_numeric _ (Ptr.add_numeric memory.vkMptr vk.constants.length hvk))) c hc

theorem Data.new_adviceComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.adviceComms, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨idx, _, rfl⟩ := hc
    exact EcPoint.fromPtr_numeric _ (Ptr.add_numeric memory.commsMptrBase _ hcomms)

theorem Data.new_committedInstanceComms_eq {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.committedInstanceComms, c = g1Identity := by
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨idx, _, rfl⟩ := hc
    rfl

end Midfall.LoweringV3

namespace Midfall.LoweringV3
open Midfall.Generator

theorem Data.new_permutationComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ p ∈ data.permutationComms, p.2.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro p hp
    rcases p with ⟨col, pt⟩
    obtain ⟨_, hpt⟩ := List.of_mem_zip hp
    simp only [List.mem_map] at hpt
    obtain ⟨i, _, rfl⟩ := hpt
    exact EcPoint.range_numeric _ _ (EcPoint.fromPtr_numeric _
      (Ptr.add_numeric _ _ (Ptr.add_numeric memory.vkMptr vk.constants.length hvk)))

theorem Data.new_permutationZComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.permutationZComms, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    exact takeIter_numeric (fun i => (EcPoint.fromPtr memory.permZCommsMptrBase).range i)
      meta_.numPermutationZs (fun i => EcPoint.range_numeric _ i
        (EcPoint.fromPtr_numeric _ hpz)) c hc

end Midfall.LoweringV3

namespace Midfall.LoweringV3
open Midfall.Generator

theorem Data.new_lookupMComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.lookupMComms, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    exact takeIter_numeric (fun i => (EcPoint.fromPtr memory.lookupMCommsMptrBase).range i)
      meta_.numLookups (fun i => EcPoint.range_numeric _ i
        (EcPoint.fromPtr_numeric _ hlm)) c hc

theorem Data.new_lookupZComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.lookupZComms, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    exact takeIter_numeric (fun i => (EcPoint.fromPtr memory.lookupZCommsMptrBase).range i)
      meta_.numLookups (fun i => EcPoint.range_numeric _ i
        (EcPoint.fromPtr_numeric _ hlz)) c hc

theorem Data.new_trashcanComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ c ∈ data.trashcanComms, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    intro c hc
    exact takeIter_numeric (fun i => (EcPoint.fromPtr memory.trashcanCommsMptrBase).range i)
      meta_.numTrashcans (fun i => EcPoint.range_numeric _ i
        (EcPoint.fromPtr_numeric _ htr)) c hc

end Midfall.LoweringV3

namespace Midfall.LoweringV3
open Midfall.Generator

theorem helperFold_numeric (chunks : List Nat) (cursor : Ptr) (acc : List (List EcPoint))
    (hcur : cursor.Numeric)
    (hacc : ∀ row ∈ acc, ∀ c ∈ row, c.Numeric) :
    let r := chunks.foldl
      (fun st chunks =>
        let (cursor, acc) := st
        let row := takeIter (EcPoint.range (EcPoint.fromPtr cursor)) chunks
        (Ptr.add cursor (g1WordsCount * chunks), acc ++ [row]))
      (cursor, acc)
    ∀ row ∈ r.snd, ∀ c ∈ row, c.Numeric := by
  induction chunks generalizing cursor acc with
  | nil => dsimp only; exact hacc
  | cons chunks rest ih =>
      dsimp only [List.foldl_cons]
      apply ih
      · exact Ptr.add_numeric cursor (g1WordsCount * chunks) hcur
      · intro row hr c hc
        rw [List.mem_append] at hr
        rcases hr with hr | hr
        · exact hacc row hr c hc
        · simp only [List.mem_singleton] at hr
          subst hr
          exact takeIter_numeric (fun i => (EcPoint.range (EcPoint.fromPtr cursor)) i) chunks
            (fun i => EcPoint.range_numeric _ i (EcPoint.fromPtr_numeric _ hcur)) c hc

end Midfall.LoweringV3

namespace Midfall.LoweringV3
open Midfall.Generator

theorem Data.new_lookupHelperComms_numeric {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    ∀ row ∈ data.lookupHelperComms, ∀ c ∈ row, c.Numeric := by
  obtain ⟨hvk, hcomms, hpz, hlm, hhl, hlz, htr⟩ := hm
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hlen : (meta_.protocol.proof.evals.length != meta_.numMainEvals) = true
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h
    obtain ⟨slots, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨pz, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨le, _, h⟩ := (dataMatchOk _ _).mp h
    obtain ⟨te, _, h⟩ := (dataMatchOk _ _).mp h
    cases h
    dsimp only
    exact helperFold_numeric meta_.lookupChunks memory.lookupHelperCommsMptrBase []
      hhl (by intro row hr; simp at hr)

end Midfall.LoweringV3

namespace Midfall.Generator

/-- Every non-linearization commitment in a `Data` is either a numeric memory
    pointer or the shared `G1_IDENTITY_MPTR` sentinel.  The linearization
    commitment is the separate symbolic `QUOTIENT_MPTR`. -/
def Data.CommsNumericOrIdentity (data : Data) : Prop :=
  (∀ c ∈ data.fixedComms, c.Numeric) ∧
  (∀ p ∈ data.permutationComms, p.2.Numeric) ∧
  (∀ c ∈ data.adviceComms, c.Numeric) ∧
  (∀ c ∈ data.committedInstanceComms, c = g1Identity) ∧
  (∀ c ∈ data.permutationZComms, c.Numeric) ∧
  (∀ c ∈ data.lookupMComms, c.Numeric) ∧
  (∀ row ∈ data.lookupHelperComms, ∀ c ∈ row, c.Numeric) ∧
  (∀ c ∈ data.lookupZComms, c.Numeric) ∧
  (∀ c ∈ data.trashcanComms, c.Numeric)

theorem Data.new_commsNumericOrIdentity {F : Type} (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) (data : Data)
    (hm : memory.NumericBases)
    (h : Data.new meta_ vk memory = .ok data) :
    data.CommsNumericOrIdentity :=
  ⟨Midfall.LoweringV3.Data.new_fixedComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_permutationComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_adviceComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_committedInstanceComms_eq (F := F) meta_ vk memory data h,
    Midfall.LoweringV3.Data.new_permutationZComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_lookupMComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_lookupHelperComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_lookupZComms_numeric (F := F) meta_ vk memory data hm h,
    Midfall.LoweringV3.Data.new_trashcanComms_numeric (F := F) meta_ vk memory data hm h⟩

/-- The quotient commitment is distinct from any numeric commitment pointer. -/
theorem ecPointBeq_quotient_of_numeric (c : EcPoint) (h : c.Numeric) :
    ecPointBeq quotientComm c = false := by
  obtain ⟨i, hi⟩ := h
  rcases c with ⟨base⟩
  rcases base with ⟨loc, value⟩
  simp only at hi
  subst hi
  simp only [ecPointBeq, ptrBeq, locationBeq, valueBeq, quotientComm, EcPoint.new,
    ptrMemory, valueFromStr]
  cases loc <;> rfl

/-- The quotient commitment is distinct from the `G1_IDENTITY_MPTR` sentinel. -/
theorem ecPointBeq_quotient_g1 :
    ecPointBeq quotientComm g1Identity = false := rfl

end Midfall.Generator

namespace Midfall.LoweringV3
open Midfall.Generator

theorem VerifierMemoryLayout.new_numericBases (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig)
    (hvk : vkMptr.Numeric) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).NumericBases := by
  unfold VerifierMemoryLayout.NumericBases
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change vkMptr.Numeric
    exact hvk
  all_goals
    repeat' first
      | apply Ptr.add_numeric
      | exact ⟨_, rfl⟩

end Midfall.LoweringV3

namespace Midfall.LoweringV3
open Midfall.Generator

theorem listGetMut_mem {α : Type} {l : List α} {i : Nat} {site : String} {v : α}
    (h : listGetMut l i site = .ok v) : v ∈ l := by
  unfold listGetMut at h
  cases hd : (l.drop i).head? with
  | none => rw [hd] at h; cases h
  | some x =>
      rw [hd] at h
      cases h
      obtain ⟨ys, hdrop⟩ := List.head?_eq_some_iff.mp hd
      exact List.mem_of_mem_drop (by rw [hdrop]; simp)

theorem hashMapGet_mem {α β : Type} [BEq α] {xs : List (α × β)} {k : α} {v : β}
    (h : hashMapGet xs k = some v) : v ∈ xs.map Prod.snd := by
  unfold hashMapGet at h
  cases hf : xs.find? (fun e => e.1 == k) with
  | none => rw [hf] at h; cases h
  | some p =>
      rw [hf] at h
      cases h
      exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hf, rfl⟩

theorem mem_map_snd_numeric {α : Type} {l : List (α × EcPoint)}
    (h : ∀ p ∈ l, p.2.Numeric) {c : EcPoint} (hc : c ∈ l.map Prod.snd) : c.Numeric := by
  rw [List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact h p hp

theorem queryFromPlan_comm_classification (source : PcsQuerySource)
    (meta_ : ConstraintSystemMeta) (data : Data) (q' : Query)
    (hd : data.CommsNumericOrIdentity)
    (hquot : data.computedQuotientComm = quotientComm)
    (h : queryFromPlan source meta_ data = .ok q') :
    q'.comm = quotientComm ∨ q'.comm.Numeric ∨ q'.comm = g1Identity := by
  obtain ⟨hfix, hperm, hadv, hinst, hpz, hlm, hhl, hlz, htr⟩ := hd
  cases source with
  | advice q =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
      split at h
      · cases h
        exact Or.inr (Or.inl (hadv comm (listGetMut_mem hcomm)))
      · cases h
  | committedInstance q =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
      split at h
      · cases h
        exact Or.inr (Or.inr (hinst comm (listGetMut_mem hcomm)))
      · cases h
  | permutationZ set kind =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨evalTriple, heval, h⟩ := (dataMatchOk _ _).mp h
      cases kind with
      | cur =>
          obtain ⟨comm, hcomm, h⟩ := (dataMatchOk _ _).mp h
          cases h
          exact Or.inr (Or.inl (hpz comm (listGetMut_mem hcomm)))
      | next =>
          obtain ⟨comm, hcomm, h⟩ := (dataMatchOk _ _).mp h
          cases h
          exact Or.inr (Or.inl (hpz comm (listGetMut_mem hcomm)))
      | last =>
          cases hlast : evalTriple.2.2 with
          | none =>
              rw [hlast] at h
              cases h
          | some e =>
              rw [hlast] at h
              obtain ⟨comm, hcomm, h⟩ := (dataMatchOk _ _).mp h
              cases h
              exact Or.inr (Or.inl (hpz comm (listGetMut_mem hcomm)))
  | lookupMultiplicity lookup =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨evalTuple, heval, h⟩ := except_bind_ok h
      obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
      cases h
      exact Or.inr (Or.inl (hlm comm (listGetMut_mem hcomm)))
  | lookupHelper lookup chunk =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨evalTuple, heval, h⟩ := except_bind_ok h
      obtain ⟨helpers, hhelpers, h⟩ := except_bind_ok h
      obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
      obtain ⟨eval, _, h⟩ := except_bind_ok h
      cases h
      exact Or.inr (Or.inl (hhl helpers (listGetMut_mem hhelpers) comm (listGetMut_mem hcomm)))
  | lookupAccumulator lookup rotation =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨evalTuple, heval, h⟩ := except_bind_ok h
      split at h
      · obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
        cases h
        exact Or.inr (Or.inl (hlz comm (listGetMut_mem hcomm)))
      · obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
        cases h
        exact Or.inr (Or.inl (hlz comm (listGetMut_mem hcomm)))
      · cases h
  | trash index =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
      obtain ⟨eval, _, h⟩ := except_bind_ok h
      cases h
      exact Or.inr (Or.inl (htr comm (listGetMut_mem hcomm)))
  | fixed q =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      obtain ⟨comm, hcomm, h⟩ := except_bind_ok h
      split at h
      · cases h
        exact Or.inr (Or.inl (hfix comm (listGetMut_mem hcomm)))
      · cases h
  | permutationCommon column =>
      unfold queryFromPlan at h
      simp only [Bind.bind, Except.bind] at h
      split at h
      · split at h
        · cases h
          exact Or.inr (Or.inl (mem_map_snd_numeric hperm (hashMapGet_mem ‹_›)))
        · cases h
      · cases h
  | linearization =>
      unfold queryFromPlan at h
      cases h
      exact Or.inl hquot

end Midfall.LoweringV3

namespace Midfall.Generator

theorem ecPointBeq_self (c : EcPoint) : ecPointBeq c c = true := by
  rcases c with ⟨base⟩
  rcases base with ⟨loc, value⟩
  cases value <;> cases loc <;> simp [ecPointBeq, ptrBeq, locationBeq, valueBeq]

theorem numeric_ne_quotient (c : EcPoint) (h : c.Numeric) : c ≠ quotientComm := by
  intro hc
  subst hc
  obtain ⟨i, hi⟩ := h
  simp only [quotientComm, EcPoint.Numeric, Ptr.Numeric, EcPoint.new, ptrMemory,
    valueFromStr] at hi
  cases hi

theorem g1Identity_ne_quotient : g1Identity ≠ quotientComm := by
  intro h
  simp only [g1Identity, quotientComm, EcPoint.new, ptrMemory, valueFromStr] at h
  injection h with hbase
  injection hbase with hloc hval
  injection hval with hname
  exact absurd hname (by decide)

theorem ecPointBeq_quotient_of_classification (c : EcPoint)
    (hclass : c = quotientComm ∨ c.Numeric ∨ c = g1Identity)
    (hne : c ≠ quotientComm) :
    ecPointBeq quotientComm c = false := by
  rcases hclass with h | h | h
  · exact absurd h hne
  · exact ecPointBeq_quotient_of_numeric c h
  · subst h
    exact ecPointBeq_quotient_g1

end Midfall.Generator
