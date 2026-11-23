-- |
-- Midfall.Halo2.Exec.TranscriptLogSized
--
-- The SIZE companion of `Transcript.LogWidths`: every record a real verifier-path
-- read logs has a byte repr of exactly its logged width. `LogWidths` says which
-- widths `decodeRust` can dispatch on; this says the recorded bytes are exactly the
-- slice `bytesTake` returned, which is what aligns the transcript log with
-- `decodeWire`'s fixed-width walk. The closure and the three pipeline walks are the
-- same structural induction as `PresWidths`, with the read step consuming
-- `bytesTake`'s exact length instead of the allowed-width hypothesis.
import Midfall.Halo2.Exec.TranscriptLog

set_option autoImplicit false

namespace Midfall.Halo2

open Midfall

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

private theorem ok_pair_sized {α : Type} {A B : α × Transcript}
    (h : (Except.ok A : Except Fault (α × Transcript)) = .ok B) : A = B := by
  cases h; rfl

private theorem pair_eq_sized {α β : Type} {a a' : α} {b b' : β} (h : (a, b) = (a', b')) :
    a = a' ∧ b = b' := by
  cases h; exact ⟨rfl, rfl⟩

/-- `bytesTake` returns exactly the wanted number of bytes. Local because the
    `Lowering` copy is above this file. -/
theorem bytesTake_size_local {bs : Bytes} {i n : Nat} {b : Bytes}
    (h : bytesTake bs i n = some b) : b.size = n := by
  unfold bytesTake at h
  split at h
  · rename_i hle
    cases h
    show (bs.data.extract i (i + n)).size = n
    rw [Array.size_extract]
    have hle' : i + n ≤ bs.data.size := hle
    rw [Nat.min_eq_left hle']
    omega
  · cases h

/-- Every logged record's byte repr has exactly the width the read logged. -/
def Transcript.LogSized (t : Transcript) : Prop :=
  ∀ rec ∈ t.log.toList, rec.2.size = rec.1

namespace Transcript

theorem LogSized.replaceState {t : Transcript} {s : Bytes}
    (ht : t.LogSized) : ({ t with state := s }).LogSized := ht

theorem LogSized.initFromBytes (bytes : Bytes) :
    (Transcript.initFromBytes bytes).LogSized := by
  intro rec hmem
  simp [Transcript.initFromBytes] at hmem

theorem LogSized.initWithHash (H : Bytes → H256) (bytes : Bytes) :
    (Transcript.initWithHash H bytes).LogSized := by
  intro rec hmem
  simp [Transcript.initWithHash] at hmem

theorem LogSized.common {T : Type} (h : Hashable T) {t : Transcript}
    (ht : t.LogSized) (input : T) : (t.common h input).LogSized := ht

theorem LogSized.squeeze {t : Transcript} (ht : t.LogSized) :
    (t.squeeze).2.LogSized := by
  cases t with | mk st buf pos h log => exact Transcript.LogSized.replaceState ht

theorem LogSized.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)]
    {t : Transcript} (ht : t.LogSized) : (t.squeezeChallenge (p := p)).2.LogSized := by
  cases t with | mk st buf pos h log => exact Transcript.LogSized.replaceState ht

theorem LogSized.read {T : Type} (h : Hashable T) {t : Transcript} (ht : t.LogSized)
    {val : T} {t' : Transcript} (hrun : t.read h = .ok (val, t')) : t'.LogSized := by
  cases hbt : bytesTake t.buffer t.pos h.width with
  | none =>
      simp only [Transcript.read, hbt] at hrun
      cases hrun
  | some repr =>
      cases hrr : h.readRepr? repr with
      | none =>
          simp only [Transcript.read, hbt, hrr] at hrun
          cases hrun
      | some val' =>
          have key : t.read h =
              .ok (val', Transcript.common h
                ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val') := by
            simp only [Transcript.read, hbt, hrr]
          have hpair : (val, t') = (val', Transcript.common h
              ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val') := by
            simpa using hrun.symm.trans key
          have hteq : t' = Transcript.common h
              ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val' :=
            congrArg Prod.snd hpair
          subst hteq
          refine Transcript.LogSized.common h ?_ val'
          intro rec hmem
          rw [Array.toList_push] at hmem
          rcases List.mem_append.mp hmem with hold | hnew
          · exact ht rec hold
          · rw [List.mem_singleton] at hnew
            cases hnew
            exact bytesTake_size_local hbt

theorem LogSized.readN {T : Type} (h : Hashable T)
    {t : Transcript} (ht : t.LogSized) (n : Nat) {vs : Array T} {t' : Transcript}
    (hrun : t.readN h n = .ok (vs, t')) : t'.LogSized := by
  have key : ∀ (n : Nat) (acc : Array T) (t : Transcript), Transcript.LogSized t →
      ∀ (vs : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (vs, t') → Transcript.LogSized t' := by
    intro n
    induction n with
    | zero =>
        intro acc t ht vs t' hrun
        simp only [Transcript.readN.go] at hrun
        obtain ⟨rfl, rfl⟩ := pair_eq_sized (ok_pair_sized hrun)
        exact ht
    | succ n ih =>
        intro acc t ht vs t' hrun
        cases hread : Transcript.read h t with
        | error e =>
            simp only [hread, Transcript.readN.go] at hrun
            cases hrun
        | ok p =>
            cases p with
            | mk v t₂ =>
                simp only [hread, Transcript.readN.go] at hrun
                exact ih (acc.push v) t₂ (Transcript.LogSized.read h ht hread) vs t' hrun
  exact key n #[] t ht vs t' hrun

end Transcript

def PresSized {T : Type} (m : TranscriptM T) : Prop :=
  ∀ (t t' : Transcript) (a : T), Transcript.LogSized t →
    m.run t = .ok (a, t') → Transcript.LogSized t'


/-! #### Closure: the same constructs `Pres` is closed under -/

theorem PresSized.pure {T : Type} (x : T) : PresSized (StateT.pure x : TranscriptM T) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq_sized (ok_pair_sized h)
  exact ht

theorem PresSized.lift {T : Type} (e : Except Fault T) : PresSized (StateT.lift e) := by
  intro t t' a ht h
  cases e with
  | error _ => cases h
  | ok x =>
      obtain ⟨rfl, rfl⟩ := pair_eq_sized (ok_pair_sized h)
      exact ht

theorem PresSized.get : PresSized (StateT.get : TranscriptM Transcript) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq_sized (ok_pair_sized h)
  exact ht

theorem PresSized.bind {α β : Type} {m : TranscriptM α} {f : α → TranscriptM β}
    (hm : PresSized m) (hf : ∀ x, PresSized (f x)) : PresSized (m >>= f) := by
  intro t t' b ht h
  have h2 : m t >>= (fun p : α × Transcript => f p.1 p.2) = (.ok (b, t') :
      Except Fault (β × Transcript)) := h
  cases hmt : m t with
  | error e =>
      rw [hmt] at h2
      have h3 : (.error e : Except Fault (β × Transcript)) = .ok (b, t') := h2
      cases h3
  | ok p =>
      cases p with
      | mk a t₁ =>
          rw [hmt] at h2
          have h3 : f a t₁ = (.ok (b, t') : Except Fault (β × Transcript)) := h2
          exact hf a t₁ t' b (hm t t₁ a ht hmt) h3

theorem PresSized.seq {α β : Type} {m : TranscriptM α} {n : TranscriptM β}
    (hm : PresSized m) (hn : PresSized n) : PresSized (m >>= fun _ => n) :=
  PresSized.bind hm (fun _ => hn)

theorem PresSized.ite {α : Type} {c : Prop} [inst : Decidable c] {m n : TranscriptM α}
    (hm : PresSized m) (hn : PresSized n) : PresSized (if c then m else n) := by
  split
  · exact hm
  · exact hn

theorem PresSized.fmap {α β : Type} (g : α → β) {m : TranscriptM α} (hm : PresSized m) :
    PresSized (g <$> m) := by
  intro t t' b ht h
  have h2 : (fun p : α × Transcript => (g p.1, p.2)) <$> m t =
      (.ok (b, t') : Except Fault (β × Transcript)) := h
  cases hrun : m t with
  | error e =>
      rw [hrun] at h2
      have h3 : (.error e : Except Fault (β × Transcript)) = .ok (b, t') := h2
      cases h3
  | ok p =>
      cases p with
      | mk a t₁ =>
          rw [hrun] at h2
          have h3 : (.ok (g a, t₁) : Except Fault (β × Transcript)) = .ok (b, t') := h2
          obtain ⟨h1, rfl⟩ := pair_eq_sized (ok_pair_sized h3)
          subst h1
          exact hm t t₁ a ht hrun

/-- A guard that throws in one branch: the throwing arm never returns, so the
    continuation is proved once. Same shape as `Pres.guard`. -/
theorem PresSized.guard {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresSized k) (h : α → PresSized k) :
    PresSized (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  PresSized.ite (α := β) (c := c) (PresSized.bind (PresSized.lift (Except.error f)) h) hk

/-- The unless form. -/
theorem PresSized.guard' {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresSized k) (h : α → PresSized k) :
    PresSized (if c then k else ((throw f : TranscriptM α) >>= fun x => k)) :=
  PresSized.ite (α := β) (c := c) hk (PresSized.bind (PresSized.lift (Except.error f)) h)

theorem PresSized.read {T : Type} (h : Hashable T) (_hh : h.AllowedWidth) :
    PresSized (tmRead h) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmRead_run_fields h st buf pos hash log] at hrun
      exact Transcript.LogSized.read h ht hrun

theorem PresSized.readN {T : Type} (h : Hashable T) (_hh : h.AllowedWidth) (n : Nat) :
    PresSized (tmReadN h n) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmReadN_run_fields h st buf pos hash log n] at hrun
      exact Transcript.LogSized.readN h ht n hrun

theorem PresSized.common {T : Type} (h : Hashable T) (input : T) :
    PresSized (tmCommon h input) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmCommon_run_fields h st buf pos hash log input] at hrun
      obtain ⟨rfl, rfl⟩ := pair_eq_sized (ok_pair_sized hrun)
      exact Transcript.LogSized.common h ht input

theorem PresSized.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)] :
    PresSized (tmSqueezeChallenge (p := p)) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmSqueeze_run_fields (p := p) st buf pos hash log] at hrun
      obtain ⟨rfl, rfl⟩ := pair_eq_sized (ok_pair_sized hrun)
      exact Transcript.LogSized.squeezeChallenge ht

theorem PresSized.listFoldlM {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, PresSized (f b x)) :
    ∀ (l : List α) (init : β), PresSized (List.foldlM (init := init) f l) := by
  intro l
  induction l with
  | nil => intro init; exact PresSized.pure _
  | cons a t ih =>
      intro init
      rw [List.foldlM_cons]
      refine PresSized.bind (hf init _) (fun b => ih b)

theorem PresSized.listMapM {α β : Type} (l : List α) {f : α → TranscriptM β}
    (hf : ∀ x, PresSized (f x)) : PresSized (List.mapM f l) := by
  induction l with
  | nil => exact PresSized.pure _
  | cons a t ih =>
      rw [List.mapM_cons]
      refine PresSized.bind (hf _) (fun _ => ?_)
      refine PresSized.bind ih (fun _ => PresSized.pure _)

theorem PresSized.arrayFoldlM {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, PresSized (f b x)) (init : β) (as : Array α) :
    PresSized (Array.foldlM (init := init) f as) := by
  rw [← Array.foldlM_toList]
  exact PresSized.listFoldlM hf as.toList init

theorem PresSized.arrayMapM {α β : Type} (as : Array α) {f : α → TranscriptM β}
    (hf : ∀ x, PresSized (f x)) : PresSized (Array.mapM f as) := by
  rw [Array.mapM_eq_foldlM]
  refine PresSized.arrayFoldlM (fun bs a => PresSized.fmap _ (hf a)) #[] as

theorem PresSized.listForIn {α β : Type} (l : List α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, PresSized (f x b)) :
    PresSized (forIn l init f) := by
  classical
  rw [List.forIn_eq_foldlM]
  refine PresSized.fmap _ (PresSized.listFoldlM ?_ l (ForInStep.yield init))
  intro b x
  cases b with
  | yield b => exact hf x b
  | done b => exact PresSized.pure _

theorem PresSized.arrayForIn {α β : Type} (as : Array α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, PresSized (f x b)) :
    PresSized (forIn as init f) := by
  rw [← Array.forIn_toList]
  exact PresSized.listForIn as.toList init hf


/-! #### Transfer: the same pipeline definitions `Pres` reaches, and no further.

    Every definition below is one whose `Pres` already exists in this file; the width
    proof is the same structural walk with the hashable named (because the width
    hypothesis has to be discharged, and `Pres` never needed it). The two definitions
    `Pres` does NOT reach - `Verifier.parseTrace` and
    `Verifier.verifyAlgebraicConstraints` - are absent here for the same reason, and
    their width condition is one more transfer lemma apiece once their `Pres` lands.
    Note the shape of the hypotheses: where a read site takes its hashable as a
    PARAMETER (`Logup.readMultiplicities argument h`), the lemma carries
    `h.AllowedWidth` rather than proving it, because the caller decides. On the
    verifier path every such caller passes `hashableG1`, whose width is 48 for every
    codec - `hashableG1_allowed` - so the hypothesis is discharged at the call site
    without knowing the codec. -/

theorem PresSized.readMultiplicities {F : Type} {G₁ : Type}
    (argument : LogupChunkedArgument F) (h : Hashable G₁) (hh : h.AllowedWidth) :
    PresSized (Logup.readMultiplicities argument h) := by
  unfold Logup.readMultiplicities
  refine PresSized.bind (PresSized.read h hh) (fun _ => PresSized.pure _)

theorem PresSized.trashReadCommitted {F : Type} {G₁ : Type}
    (argument : TrashArgument F) (h : Hashable G₁) (hh : h.AllowedWidth) :
    PresSized (Trash.readCommitted argument h) := by
  unfold Trash.readCommitted
  refine PresSized.bind (PresSized.read h hh) (fun _ => PresSized.pure _)

theorem PresSized.readCommitment {G₁ : Type}
    (cm : Logup.CommittedMultiplicities G₁) (nbChunks : Nat) (h : Hashable G₁)
    (hh : h.AllowedWidth) :
    PresSized (Logup.CommittedMultiplicities.readCommitment cm nbChunks h) := by
  unfold Logup.CommittedMultiplicities.readCommitment
  refine PresSized.bind (PresSized.readN h hh _) (fun _ => ?_)
  refine PresSized.bind (PresSized.read h hh) (fun _ => PresSized.pure _)

theorem PresSized.hashInto {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (vk : VerifyingKey (Fr p) G₁) : PresSized (VerifyingKey.hashInto vk) := by
  unfold VerifyingKey.hashInto
  exact PresSized.common hashableFr vk.transcriptRepr

theorem PresSized.permReadProductCommitments {G₁ : Type} (perm : PermutationArgument)
    (csDegree : Nat) (h : Hashable G₁) (hh : h.AllowedWidth) :
    PresSized (Permutation.readProductCommitments perm csDegree h) := by
  unfold Permutation.readProductCommitments
  refine PresSized.ite ?_ ?_
  · refine PresSized.bind (PresSized.readN h hh _) (fun _ => PresSized.pure _)
  · intro t t' a ht h
    cases h

theorem PresSized.permVKevaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : Permutation.VerifyingKey G₁) :
    PresSized (Permutation.VerifyingKey.evaluate (p := p) vk) := by
  unfold Permutation.VerifyingKey.evaluate
  refine PresSized.bind
    (PresSized.readN (hashableFr (p := p)) hashableFr_allowed _) (fun _ => PresSized.pure _)

theorem PresSized.permCommittedEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Permutation.Committed G₁) :
    PresSized (Permutation.Committed.evaluate (p := p) coms) := by
  unfold Permutation.Committed.evaluate
  refine PresSized.bind (PresSized.listForIn (List.range coms.permutationProductCommitments.size)
      (#[] : Array (Permutation.SetEvaluated (Fr p))) (fun i s => ?_)) (fun _ => PresSized.pure _)
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresSized.ite
      (PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed)
        (fun _ => PresSized.pure _)) (PresSized.pure _)

theorem PresSized.logupEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Logup.Committed G₁) : PresSized (Logup.Committed.evaluate (p := p) coms) := by
  unfold Logup.Committed.evaluate
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresSized.bind
    (PresSized.readN (hashableFr (p := p)) hashableFr_allowed _) (fun _ => ?_)
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed)
    (fun _ => PresSized.pure _)

theorem PresSized.trashEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Trash.Committed G₁) : PresSized (Trash.Committed.evaluate (p := p) coms) := by
  unfold Trash.Committed.evaluate
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed)
    (fun _ => PresSized.pure _)

theorem PresSized.addDummies {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresSized (MultiPrepare.addDummies (G₂ := G₂) (Gₜ := Gₜ) g1 queries) := by
  unfold MultiPrepare.addDummies
  refine PresSized.bind (PresSized.lift _) (fun dummies => ?_)
  refine PresSized.listFoldlM (fun qs x => ?_) dummies queries
  refine PresSized.bind (PresSized.read (hashableFr (p := p)) hashableFr_allowed)
    (fun eval => ?_)
  cases hq : qs[x.1]? with
  | none =>
      show PresSized (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
      exact (PresSized.lift (Except.error (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
        : PresSized (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349")))
  | some o =>
      exact PresSized.pure _

theorem PresSized.phaseA {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresSized (phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries) := by
  unfold Midfall.Halo2.phaseA
  refine PresSized.ite (α := MultiPrepare.PhaseA (Fr p) G₁)
      (c := feat.outerFewerPointSets && fewerPointSetsRuntime) ?_ ?_
  · refine PresSized.bind (PresSized.addDummies g1 queries) (fun _ => ?_)
    refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
    refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
    refine PresSized.bind (PresSized.lift _) (fun _ => ?_)
    refine PresSized.bind (PresSized.lift _) (fun _ => PresSized.pure _)
  · refine PresSized.bind (PresSized.pure queries) (fun _ => ?_)
    refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
    refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
    refine PresSized.bind (PresSized.lift _) (fun _ => ?_)
    refine PresSized.bind (PresSized.lift _) (fun _ => PresSized.pure _)

theorem PresSized.phaseB {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) :
    PresSized (phaseB g1 fc feat a) := by
  unfold Midfall.Halo2.phaseB
  refine PresSized.bind (PresSized.read (hashableG1 g1) (hashableG1_allowed g1)) (fun _ => ?_)
  refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
  refine PresSized.bind (PresSized.listMapM (List.range a.qEvalSets.size)
      (fun _ => PresSized.read (hashableFr (p := p)) hashableFr_allowed)) (fun _ => ?_)
  refine PresSized.bind (PresSized.lift _) (fun _ => PresSized.pure _)

theorem PresSized.phaseC {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) (b : MultiPrepare.PhaseB (Fr p) G₁) :
    PresSized (phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b) := by
  unfold Midfall.Halo2.phaseC
  refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
  refine PresSized.bind (PresSized.lift _) (fun _ => ?_)
  refine PresSized.bind (PresSized.lift _) (fun _ => ?_)
  refine PresSized.bind (PresSized.read (hashableG1 g1) (hashableG1_allowed g1))
    (fun _ => PresSized.pure _)

theorem PresSized.multiPrepare {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresSized (multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime
      queries) := by
  unfold Midfall.Halo2.multiPrepare
  refine PresSized.bind (PresSized.phaseA g1 fc feat fewerPointSetsRuntime queries)
    (fun _ => ?_)
  refine PresSized.bind (PresSized.phaseB g1 fc feat _) (fun _ => ?_)
  refine PresSized.bind (PresSized.phaseC g1 fc feat _ _) (fun _ => PresSized.pure _)


theorem PresSized.readFixedEvals {p : ℕ} [Fact (Nat.Prime p)]
    (cs : ConstraintSystem (Fr p)) :
    PresSized (Verifier.readFixedEvals (p := p) cs) := by
  unfold Verifier.readFixedEvals
  apply PresSized.guard
  · refine PresSized.bind
      (PresSized.readN (hashableFr (p := p)) hashableFr_allowed _) (fun read => ?_)
    refine PresSized.bind (PresSized.listFoldlM (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => PresSized.pure _)
    refine PresSized.ite (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (PresSized.lift _) (PresSized.pure _)
  · intro z
    refine PresSized.bind
      (PresSized.readN (hashableFr (p := p)) hashableFr_allowed _) (fun read => ?_)
    refine PresSized.bind (PresSized.listFoldlM (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => PresSized.pure _)
    refine PresSized.ite (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (PresSized.lift _) (PresSized.pure _)

theorem PresSized.readAlgebra {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    PresSized (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
      nbCommitted numProofs instances) := by
  unfold Verifier.readAlgebra
  refine PresSized.bind
    (PresSized.readN (hashableG1 g1) (hashableG1_allowed g1) _) (fun _ => ?_)
  refine PresSized.bind PresSized.squeezeChallenge (fun _ => ?_)
  refine PresSized.bind (PresSized.lift _) (fun _ => ?_)
  refine PresSized.bind (PresSized.listMapM instances.toList (fun row =>
      PresSized.listMapM vk.cs.instanceQueries.toList (fun q => ?_))) (fun _ => ?_)
  · refine PresSized.ite (α := Fr p) (c := q.1.index < nbCommitted)
      (PresSized.read (hashableFr (p := p)) hashableFr_allowed) ?_
    dsimp only
    cases hq : row[q.1.index - nbCommitted]? with
    | none =>
        exact (PresSized.lift (Except.error (Fault.panic "proofs/src/plonk/verifier.rs:366"))
          : PresSized (throw (Fault.panic "proofs/src/plonk/verifier.rs:366")))
    | some col =>
        dsimp only
        apply PresSized.guard'
        · exact PresSized.lift _
        · intro z
          exact PresSized.lift _
  refine PresSized.bind (PresSized.listMapM (List.range numProofs)
      (fun _ => PresSized.readN (hashableFr (p := p)) hashableFr_allowed _)) (fun _ => ?_)
  refine PresSized.bind (PresSized.readFixedEvals vk.cs) (fun _ => ?_)
  refine PresSized.bind (PresSized.permVKevaluate vk.permutation) (fun _ => ?_)
  refine PresSized.bind (PresSized.listMapM permutations.toList (fun pc =>
      PresSized.permCommittedEvaluate pc)) (fun _ => ?_)
  refine PresSized.bind (PresSized.listMapM lookups.toList (fun row =>
      PresSized.listMapM row.toList (fun l => PresSized.logupEvaluate l))) (fun _ => ?_)
  refine PresSized.bind (PresSized.listMapM trashcans.toList (fun row =>
      PresSized.listMapM row.toList (fun t => PresSized.trashEvaluate t)))
      (fun _ => PresSized.pure _)


/-! #### The consequence `decodeRust` needs, and the D-P23 halves -/

/-- **The width condition in the form `decodeRust` consumes it.** Its map over the log is
    `if rec.1 == wG1 then ... else if rec.1 == wFr then ... else none`. If every logged
    width is 32 or `g1CompressedWidth`, the third arm is unreachable: the three-arm
    dispatch is the two-arm one, record by record. So a proof of `PresSized` for the
    whole pipeline is exactly what turns "the log tiles the consumed prefix" (item 1 of
    P-LOGCONCAT, and `transcript_log_concat` above) into "the messages `decodeRust`
    returns re-serialise to that prefix". -/

theorem PresSized.guardWhen {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresSized k) :
    PresSized (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  PresSized.ite (α := β) (c := c)
    (PresSized.bind (PresSized.lift (Except.error f)) (fun _ => hk)) hk

/-- Pointwise equality of runs transfers `PresSized`. -/
theorem PresSized.congr_of_run_eq {α : Type} {m n : TranscriptM α}
    (h : ∀ s, m.run s = n.run s) (hm : PresSized m) : PresSized n := by
  intro t t' a ht hrun
  exact hm t t' a ht ((h t).trans hrun)

theorem presSized_parseTrace     (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) :
    PresSized (parseTrace g1 feat vk committed₀ inst) := by
  unfold parseTrace
  apply PresSized.guardWhen
  · apply PresSized.guardWhen
    · apply PresSized.guardWhen
      · refine PresSized.bind (PresSized.hashInto vk) (fun _ => ?_)
        -- absorb the committed instance commitments
        refine PresSized.bind ?_ (fun _ => ?_)
        · apply PresSized.listForIn
          · intro row __s
            refine PresSized.bind ?_ (fun _ => PresSized.pure _)
            · apply PresSized.arrayForIn
              · intro com __s
                exact PresSized.bind (PresSized.common (hashableG1 g1) com) (fun _ => PresSized.pure _)
        -- absorb each instance column's length then its values
        · refine PresSized.bind ?_ (fun _ => ?_)
          · apply PresSized.listForIn
            · intro row __s
              refine PresSized.bind ?_ (fun _ => PresSized.pure _)
              · apply PresSized.arrayForIn
                · intro col __s
                  refine PresSized.bind (PresSized.common hashableFr (Nat.cast col.size)) (fun _ => ?_)
                  refine PresSized.bind ?_ (fun _ => PresSized.pure _)
                  · apply PresSized.arrayForIn
                    · intro v __s
                      exact PresSized.bind (PresSized.common hashableFr v) (fun _ => PresSized.pure _)
          -- the phase loop
          · refine PresSized.bind ?_ (fun x => ?_)
            · apply PresSized.listFoldlM
              · intro st ph
                dsimp only []
                refine PresSized.bind ?_ (fun adv => ?_)
                · apply PresSized.listFoldlM
                  · intro acc k
                    refine PresSized.bind (PresSized.readN (hashableG1 g1) (hashableG1_allowed g1) _) (fun _ => PresSized.pure _)
                · refine PresSized.bind ?_ (fun chals => PresSized.pure _)
                  · apply PresSized.listFoldlM
                    · intro acc e
                      apply PresSized.ite
                      · refine PresSized.bind PresSized.squeezeChallenge (fun _ => PresSized.pure _)
                      · exact PresSized.pure _
            · cases x with
              | mk advPairs chalPairs =>
                refine PresSized.bind ?_ (fun adviceCommitments => ?_)
                · apply PresSized.listFoldlM
                  · intro acc pairs
                    refine PresSized.bind
                        (PresSized.lift (scatterIndexed vk.cs.numAdviceColumns pairs
                          "proofs/src/plonk/verifier.rs:118")) (fun _ => PresSized.pure _)
                · refine PresSized.bind
                      (PresSized.lift (scatterIndexed vk.cs.numChallenges chalPairs
                        "proofs/src/plonk/verifier.rs:134")) (fun challenges => ?_)
                  refine PresSized.bind PresSized.squeezeChallenge (fun theta => ?_)
                  refine PresSized.bind ?_ (fun lookupMultiplicities => ?_)
                  · apply PresSized.listFoldlM
                    · intro acc x
                      refine PresSized.bind ?_ (fun row => PresSized.pure _)
                      · apply PresSized.listFoldlM
                        · intro acc' l
                          refine PresSized.bind (PresSized.lift (l.chunkByDegree vk.csDegree))
                            (fun chunked => ?_)
                          refine PresSized.bind (PresSized.readMultiplicities chunked (hashableG1 g1) (hashableG1_allowed g1))
                            (fun m => PresSized.pure _)
                  refine PresSized.bind PresSized.squeezeChallenge (fun beta => ?_)
                  refine PresSized.bind PresSized.squeezeChallenge (fun gamma => ?_)
                  refine PresSized.bind ?_ (fun permutations => ?_)
                  · apply PresSized.listFoldlM
                    · intro acc x
                      refine PresSized.bind
                          (PresSized.permReadProductCommitments vk.cs.permutation vk.csDegree (hashableG1 g1) (hashableG1_allowed g1)) (fun _ => PresSized.pure _)
                  refine PresSized.bind ?_ (fun lookups => ?_)
                  · apply PresSized.listFoldlM
                    · intro acc row
                      refine PresSized.bind ?_ (fun out => PresSized.pure _)
                      · apply PresSized.listFoldlM
                        · intro acc' x
                          cases x with
                          | mk m chunked =>
                            refine PresSized.bind
                                (PresSized.readCommitment m chunked.numChunks (hashableG1 g1) (hashableG1_allowed g1))
                                (fun _ => PresSized.pure _)
                  refine PresSized.bind PresSized.squeezeChallenge (fun trashChallenge => ?_)
                  refine PresSized.bind ?_ (fun trashcans => ?_)
                  · apply PresSized.listFoldlM
                    · intro acc x
                      refine PresSized.bind ?_ (fun row => PresSized.pure _)
                      · apply PresSized.listFoldlM
                        · intro acc' t
                          refine PresSized.bind (PresSized.trashReadCommitted t (hashableG1 g1) (hashableG1_allowed g1))
                            (fun _ => PresSized.pure _)
                  refine PresSized.bind PresSized.squeezeChallenge (fun y => ?_)
                  exact PresSized.pure _


theorem presSized_verifyAlgebraicConstraints     (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁))
    (instances : Array (Array (Array (Fr p))))
    (hpcs : ∀ queries, PresSized (pcs.multiPrepare queries)) :
    PresSized (Verifier.verifyAlgebraicConstraints (p := p) g1 delta feat pcs vk trace
      committedInstances instances) := by
  unfold Verifier.verifyAlgebraicConstraints
  apply PresSized.guardWhen
  · refine PresSized.bind ?_ (fun alg => ?_)
    · apply PresSized.readAlgebra
    · refine PresSized.bind ?_ (fun queries => ?_)
      · apply PresSized.lift
      · intro t t' b ht h
        simp only [StateT.run, StateT.bind, StateT.get, Bind.bind, Pure.pure, Except.bind,
          Except.pure] at h
        cases hrun : (pcs.multiPrepare queries).run t with
        | ok p =>
            cases p with
            | mk a s' =>
                simp only [StateT.run] at hrun
                simp only [StateT.run, StateT.bind, StateT.set, StateT.pure, StateT.lift,
                  Bind.bind, Pure.pure, Except.bind, Except.pure, hrun] at h
                cases h
                exact (hpcs queries) t t' b ht hrun
        | error f =>
            cases f with
            | panic site =>
                simp only [StateT.run] at hrun
                simp only [StateT.run, StateT.bind, StateT.set, StateT.pure, StateT.lift,
                  Bind.bind, Pure.pure, Except.bind, Except.pure, hrun] at h
                cases h
            | error er =>
                simp only [StateT.run] at hrun
                simp only [StateT.run, StateT.bind, StateT.set, StateT.pure, StateT.lift,
                  Bind.bind, Pure.pure, Except.bind, Except.pure, hrun] at h
                cases h




theorem presSized_prepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (committed : List (List G₁))
    (inst : List (List (List (Fr p)))) :
    PresSized (prepare (Gₜ := Gₜ) E F vk committed inst) := by
  unfold prepare prepareWith Verifier.prepare
  refine PresSized.bind ?_ (fun trace => ?_)
  · apply presSized_parseTrace
  · refine presSized_verifyAlgebraicConstraints E.g1 E.delta F
        (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime) vk trace _ _ ?_
    intro queries
    exact PresSized.multiPrepare E.g1 E.field F E.fewerPointSetsRuntime queries

end Midfall.Halo2
