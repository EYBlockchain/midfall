-- |
-- Midfall.Halo2.Exec.TranscriptLog
--
-- transcript_log_concat: THE LOG'S REPRS CONCATENATE TO THE CONSUMED TRANSCRIPT PREFIX.
-- P-LOGCONCAT. This is the one named lemma that did not exist anywhere in the tree and
-- that Obligations.lean:669 ONCE named as the only substantive obstacle between this
-- codebase and a proof of verifyNative_iff_msgs_codec. That sentence was false in both
-- directions by the time P-CODEC-B read it - the log lemma exists and applies to the
-- pipeline, and an obstacle the sketch never mentioned (the fold, then decodability) sat
-- behind it - and it is now corrected in place at Obligations.lean. verifyNative_iff_msgs_codec
-- IS PROVED as of P-CODEC-C, from three pipeline walks rather than one lemma. What still
-- separates the frozen Statements.verifyNative_iff_msgs from it is only the deliberate
-- D-P27 hold-out at Statements.lean:68, which needs a human decision and a re-pin.
--
-- SIX OBSTACLES WERE NAMED ACROSS THIS CHAIN, NOT ONE: (1) the tiling itself, (2) the
-- width condition on logged records, (3) the two do-block walks parseTrace /
-- verifyAlgebraicConstraints, (4) the fold connecting the log's mapM to the recorded
-- bytes, (5) the StateT.set non-closure that forced the transfer-lemma method, and
-- (6) decodability: the log records a read's width and bytes but not WHICH Hashable
-- produced them. See the P-CODEC-B and P-CODEC-C sections at the foot of this file.
--
-- WHAT THE RUST ACTUALLY SAYS (fact-checked at proofs/src/transcript/mod.rs, not taken
-- from the sketch). CircuitTranscript is { state: H, buffer: Cursor<Vec<u8>> }
-- (mod.rs:109-112). read (mod.rs:149-154) is T::read(&mut self.buffer) followed by
-- common(&val): the cursor advances by exactly the repr width and NOTHING else advances
-- it on the verifier path. common (:143-147) absorbs into state. squeeze
-- (implementors.rs:198-212) REPLACES state. assert_empty (:166-175) compares
-- get_ref().len() with position(). So: the buffer is a Vec that the verifier never
-- writes, position is the sum of the widths of the reads that succeeded, and the bytes
-- at those positions are exactly what was read. That is the tiling below. The sketch at
-- design2.md:977 had the right shape - (t.log.map snd).foldl append = pi.extract 0 t.pos -
-- and extract (not take) is right because ByteArray has no take.
--
-- WHY IT IS NOT ONE LEMMA. The Lean port records the log inside Transcript.read
-- (Exec/Transcript.lean:153), the only writer of pos and log in the whole tree (grep
-- 'pos :=' finds the two constructors and that line). So the invariant holds of every
-- REACHABLE transcript - but decodeRust consumes the transcript Verifier.prepare leaves
-- behind, and prepare is a StateT do-block over parseTrace + verifyAlgebraicConstraints
-- + multiPrepare with ~20 read sites behind ~10 loops. Getting the invariant for THAT
-- transcript means proving it is preserved by every construct the pipeline is built from.
-- That is Pres: a compositional preservation predicate, one closure lemma per monadic
-- construct (bind, seq, ite, fmap, pure, lift, get, set, List/Array foldlM, mapM, forIn),
-- and then one lemma per pipeline definition, bottom-up. design2.md:954 costed it at
-- three days and design1.md:184 calls it the largest single item. It is large and it is
-- mechanical; nothing about it is blocked.
--
-- A WHNF LANDMINE, RECORDED SO THE NEXT PACKAGE DOES NOT REDISCOVER IT.
-- Transcript.squeeze's body contains wordToBytesBE (t.hash t.state), and whnf on
-- natToBytesLowFirst with a SYMBOLIC value argument does not terminate in the default
-- heartbeat budget: 'example : (t.squeeze).2.Tiled := ht' times out at 200000 heartbeats,
-- and so does '(t.squeeze).2.log = t.log := rfl'. Two fixes, both used below:
-- Transcript.Tiled.replaceState (same fact with the new state as a VARIABLE), and
-- 'cases t with | mk st buf pos h log =>' before any rfl that must reduce squeeze.
-- Neither works around a false statement; both keep the kernel from normalising a
-- 32-digit byte emitter it does not need.
--
-- A SECOND ONE, SAME KIND. The StateT.run_* equation lemmas in core do NOT match the
-- elaborated do-blocks (rw [StateT.run_get] fails to find get.run s even though the
-- instance is rfl-provable). The unfolding that works is the delta set
-- [StateT.run, StateT.bind, StateT.get, StateT.set, StateT.lift, StateT.pure, Bind.bind,
-- Pure.pure, Except.bind, Except.map, Except.pure] - see tmRead_run_fields.
--
-- D-P23 BOTH HALVES. Satisfiability: transcriptLogKat_tiles and
-- transcriptLogKat_twoReads run real reads on real buffers and pin that the log tiles
-- exactly the consumed prefix, in read order. Falsifiability, as THEOREMS and not only
-- as Bool conjuncts (the KAT gate compares the printed Bool of a whole def, so a dropped
-- conjunct is invisible - the gap P-BYTES reported; a dropped THEOREM stops the build):
-- transcriptLogRefutesUntiled exhibits a transcript that is not tiled, and
-- transcriptLogKat_strictPrefix pins a case where the prefix is NOT consumed, where the
-- concatenation is a STRICT prefix of the stream. That last conjunct is what stops the
-- lemma from being read as 'the log concatenates to the buffer', which is exactly the
-- claim decodeRust's trailing-bytes check exists to reject.
--
-- GATE GAP, REPORTED NOT HIDDEN: kat_gate.py compares only the whole def's Bool, so
-- deleting a conjunct from transcriptLogKats_ok leaves every gate green. Each
-- falsification is therefore also a named theorem above.
--
-- WHAT THIS FILE DOES NOT YET DO, AND EXACTLY WHY. [SUPERSEDED BY P-CODEC-B STEP 3 AND
-- P-CODEC-C STEP 1: parseTrace and verifyAlgebraicConstraints now carry Pres, PresWidths
-- AND PresDecoded walks, and the codec lemma is proved. The paragraph is kept because it
-- records the Lean mechanic that made them possible, not a current gap.] It used to read:
-- verifyNative_iff_msgs_codec needs
-- Pres (Verifier.prepare ...), i.e. the tiling for the transcript the §9.2 pipeline
-- leaves behind. Everything the pipeline is made of is proved Pres here EXCEPT two
-- definitions, Verifier.parseTrace and Verifier.verifyAlgebraicConstraints, and the
-- obstacle in both is one Lean mechanic, not a mathematical gap:
--
--   * parseTrace: three 'if c then throw f' guards, each of which desugars so that the if
--     wraps the REST of the block. Pres.guardWhen proves such a guard from ONE proof of
--     the rest, so the guards are linear, not exponential; the rest is 20 bind/fold/squeeze
--     steps and every construct they use has a closure lemma here. This is writing, not
--     thinking.
--   * verifyAlgebraicConstraints: its last statement is
--     'match (pcs.multiPrepare queries).run t with | .ok (guard, t2) => StateT.set t2 >>
--     pure guard | ...'. The match's arms are STATE values, so the elaborated term is
--     (match ... with ...) applied to a state, and 'cases h : m.run s' refuses to abstract
--     a scrutinee in that position (dependent elimination fails). The fix is a transfer
--     lemma Pres.congr_of_run_eq (pointwise equality of runs transfers Pres) plus proving
--     the pointwise equality by 'intro s; cases h : m.run s' - where the goal, not a
--     hypothesis, carries the scrutinee. Left as the next package's first move.
--
-- The tiling itself is not in doubt: every read site in the tree goes through
-- Transcript.read, which is the only writer of pos and log, and 15 of the 17 pipeline
-- definitions already carry the Pres proof end to end.
--
-- P-CODEC-B STEP 1 LANDED HERE: the FOLD LEMMA (Transcript.recorded_eq_fold,
-- list_mapM_roundtrip_snd, recorded_fold_of_mapM, decodeRust_recorded). P-CODEC-A found
-- it as a fifth obstacle nobody had listed: transcript_log_concat says the log's reprs
-- concatenate to the consumed prefix, and decodeRust recovers messages by mapping the
-- log through a per-record decoder, but NOTHING connected the two - the fold over
-- List.mapM versus the Array.foldl inside Transcript.recordedList was stated nowhere.
-- The fact was computed at Instances/NativeE2E.lean:347 (n2RoundTrip_ok), which D-P17
-- confines, so it had gate evidence and no proof. That file is NOT imported here; the
-- proof is the three-piece walk in the section at the end of this file. The import of
-- Midfall.Assumptions.Codec below is what step 1 needs: the Fr arm of the per-record
-- round trip is frOfRepr_frToRepr_bytes.

import Midfall.Halo2.Exec.Native
import Midfall.Assumptions.Codec

namespace Midfall.Halo2
open Midfall

/-! ### Byte arithmetic the tiling step needs -/

private theorem list_toArray_toList (l : List UInt8) : l.toArray.toList = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

private theorem array_toList_toArray (a : Array UInt8) : a.toList.toArray = a := by
  cases a with | mk l => simp

/-- Slicing a list at two increasing offsets tiles it. -/
theorem list_extract_tile {α : Type} (l : List α) {i j : Nat} (hij : i ≤ j) :
    l.extract 0 i ++ l.extract i j = l.extract 0 j := by
  have h1 : l.extract 0 i = l.take i := by rw [List.extract_eq_take_drop]; simp
  have h2 : l.extract i j = (l.drop i).take (j - i) := List.extract_eq_take_drop
  have h3 : l.extract 0 j = l.take j := by rw [List.extract_eq_take_drop]; simp
  rw [h1, h2, h3, ← List.take_add, Nat.add_sub_of_le hij]

/-! ### The invariant -/

/-- The bytes the transcript log has recorded, concatenated in read order. -/
def Transcript.recordedList (t : Transcript) : List UInt8 :=
  t.log.toList.foldl (init := []) fun acc r => acc ++ r.2.data.toList

/-- The same, as a ByteArray. -/
def Transcript.recorded (t : Transcript) : Bytes :=
  ByteArray.mk (t.recordedList.toArray)

@[simp] theorem Transcript.data_recorded (t : Transcript) :
    t.recorded.data = t.recordedList.toArray := rfl

/-- **The transcript-log tiling invariant.** -/
def Transcript.Tiled (t : Transcript) : Prop :=
  t.recordedList = t.buffer.data.toList.extract 0 t.pos

/-- The ByteArray spelling. -/
theorem Transcript.recorded_eq_extract (t : Transcript) :
    t.recorded = t.buffer.extract 0 t.pos ↔ t.Tiled := by
  constructor
  · intro h
    have h1 := congrArg ByteArray.data h
    rw [Transcript.data_recorded, ByteArray.data_extract] at h1
    have h2 := congrArg Array.toList h1
    rw [list_toArray_toList, Array.toList_extract] at h2
    exact h2
  · intro h
    apply ByteArray.ext
    rw [Transcript.data_recorded, ByteArray.data_extract]
    rw [← array_toList_toArray (a := t.buffer.data.extract 0 t.pos)]
    show t.recordedList.toArray = (t.buffer.data.extract 0 t.pos).toList.toArray
    rw [h, Array.toList_extract]

/-- The invariant sees three fields and nothing else. -/
theorem Transcript.Tiled.congr {x y : Transcript} (hl : x.log = y.log)
    (hb : x.buffer = y.buffer) (hp : x.pos = y.pos) (hx : x.Tiled) : y.Tiled := by
  unfold Transcript.Tiled Transcript.recordedList at *
  show y.log.toList.foldl (init := []) (fun acc r => acc ++ r.2.data.toList) = _
  rw [← hl, hx, hb, hp]

/-- Replacing the hasher state cannot touch the tiling. -/
theorem Transcript.Tiled.replaceState {t : Transcript} {s : Bytes} (ht : t.Tiled) :
    ({ t with state := s }).Tiled := ht

theorem Transcript.tiled_initFromBytes (bytes : Bytes) :
    (Transcript.initFromBytes bytes).Tiled := by
  show ([] : List UInt8) = bytes.data.toList.extract 0 0
  rw [List.extract_eq_take_drop]
  simp

/-- **The one line P-CODEC-A verified but could not land:** the keccak-specialised
    hash-initialiser IS the byte-initialiser, definitionally. This is what lets
    `prepareMsgs` (which uses `initWithHash`) and `verifyNative` (which uses
    `initFromBytes`) execute literally the same run. -/
theorem Transcript.initWithHash_keccak (bytes : Bytes) :
    Transcript.initWithHash keccak256 bytes = Transcript.initFromBytes bytes := rfl

theorem Transcript.tiled_initWithHash (H : Bytes → H256) (bytes : Bytes) :
    (Transcript.initWithHash H bytes).Tiled := by
  show ([] : List UInt8) = bytes.data.toList.extract 0 0
  rw [List.extract_eq_take_drop]
  simp

theorem Transcript.Tiled.common {T : Type} (h : Hashable T) {t : Transcript}
    (ht : t.Tiled) (input : T) : (t.common h input).Tiled := ht

theorem Transcript.Tiled.squeeze {t : Transcript} (ht : t.Tiled) :
    (t.squeeze).2.Tiled := by
  cases t with | mk st buf pos h log => exact Transcript.Tiled.replaceState ht

theorem Transcript.Tiled.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)]
    {t : Transcript} (ht : t.Tiled) : (t.squeezeChallenge (p := p)).2.Tiled := by
  cases t with | mk st buf pos h log => exact Transcript.Tiled.replaceState ht

/-- **The step.** A read that succeeds extends the tiling by exactly the repr it
    logged: the slice of the buffer at the old cursor position, of the hashable's width.
    This is mod.rs:149-154 plus Exec/Transcript.lean:145-154. -/
theorem Transcript.Tiled.read {T : Type} (h : Hashable T) {t : Transcript} (ht : t.Tiled)
    {val : T} {t' : Transcript} (hrun : t.read h = .ok (val, t')) : t'.Tiled := by
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
          let t2 : Transcript := { t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }
          have key : t.read h = .ok (val', t2.common h val') := by
            simp only [Transcript.read, hbt, hrr]
            rfl
          have hpair : (val, t') = (val', t2.common h val') := by
            simpa using hrun.symm.trans key
          have hteq : t' = t2.common h val' := congrArg Prod.snd hpair
          subst hteq
          have hsize : t.pos + h.width ≤ t.buffer.size := by
            by_contra hne
            rw [bytesTake, if_neg hne] at hbt
            cases hbt
          have hrepr : repr.data.toList =
              t.buffer.data.toList.extract t.pos (t.pos + h.width) := by
            rw [bytesTake, if_pos hsize] at hbt
            cases hbt
            rw [Array.toList_extract]
          have hsing : ∀ (b : List UInt8), List.foldl (init := b)
              (fun acc r => acc ++ r.2.data.toList) [(h.width, repr)]
              = b ++ repr.data.toList := fun _ => rfl
          have hstep : t2.Tiled := by
            unfold Transcript.Tiled Transcript.recordedList at ht ⊢
            rw [Array.toList_push, List.foldl_append, hsing, hrepr, ht]
            exact list_extract_tile t.buffer.data.toList (by omega)
          exact Transcript.Tiled.common h hstep val'


/-- The companion of the step lemma: a successful read leaves the buffer alone. -/
theorem Transcript.read_ok_buffer {T : Type} (h : Hashable T) {t : Transcript}
    {val : T} {t' : Transcript} (hrun : t.read h = .ok (val, t')) : t'.buffer = t.buffer := by
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
          have key : t.read h = .ok (val', Transcript.common h ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val') := by
            simp only [Transcript.read, hbt, hrr]
          have hpair : (val, t') = (val', Transcript.common h ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val') := by
            simpa using hrun.symm.trans key
          have hteq : t' = Transcript.common h ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val' :=
            congrArg Prod.snd hpair
          rw [hteq]
          rfl

/-! ### The transfer predicate -/

/-- An action of the transcript monad that preserves the tiling invariant: from a tiled
    state, every run that succeeds leaves a tiled state over the SAME buffer. The buffer
    conjunct is what turns "tiles the consumed prefix of the final buffer" into "tiles the
    consumed prefix of the proof stream", which is the form decodeRust needs. Every
    construct the pipeline is built from has a closure lemma below, so proving an action
    Pres is a structural walk of its definition, not a re-derivation of the pipeline. -/
def Pres {α : Type} (m : TranscriptM α) : Prop :=
  ∀ (t t' : Transcript) (a : α), Transcript.Tiled t →
    m.run t = .ok (a, t') → Transcript.Tiled t' ∧ t'.buffer = t.buffer

private theorem ok_pair {α : Type} {A B : α × Transcript}
    (h : (Except.ok A : Except Fault (α × Transcript)) = .ok B) : A = B := by
  cases h; rfl

private theorem pair_eq {α β : Type} {a a' : α} {b b' : β} (h : (a, b) = (a', b')) :
    a = a' ∧ b = b' := by
  cases h; exact ⟨rfl, rfl⟩

theorem Pres.of_run {α : Type} {m : TranscriptM α} (hm : Pres m) {t t' : Transcript}
    {a : α} (ht : Transcript.Tiled t) (hrun : m.run t = .ok (a, t')) : Transcript.Tiled t' :=
  (hm t t' a ht hrun).1

theorem Pres.buffer {α : Type} {m : TranscriptM α} (hm : Pres m) {t t' : Transcript}
    {a : α} (ht : Transcript.Tiled t) (hrun : m.run t = .ok (a, t')) : t'.buffer = t.buffer :=
  (hm t t' a ht hrun).2

theorem Pres.pure {α : Type} (x : α) : Pres (pure x : TranscriptM α) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
  exact ⟨ht, rfl⟩

theorem Pres.lift {α : Type} (e : Except Fault α) : Pres (StateT.lift e) := by
  intro t t' a ht h
  cases e with
  | error _ => cases h
  | ok x =>
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
      exact ⟨ht, rfl⟩

theorem Pres.get : Pres (StateT.get : TranscriptM Transcript) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
  exact ⟨ht, rfl⟩

theorem Pres.bind {α β : Type} {m : TranscriptM α} {f : α → TranscriptM β}
    (hm : Pres m) (hf : ∀ x, Pres (f x)) : Pres (m >>= f) := by
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
          have hm' := hm t t₁ a ht hmt
          have hf' := hf a t₁ t' b hm'.1 h3
          exact ⟨hf'.1, hf'.2.trans hm'.2⟩

theorem Pres.seq {α β : Type} {m : TranscriptM α} {n : TranscriptM β}
    (hm : Pres m) (hn : Pres n) : Pres (m >>= fun _ => n) :=
  Pres.bind hm (fun _ => hn)

theorem Pres.ite {α : Type} {c : Prop} [inst : Decidable c] {m n : TranscriptM α}
    (hm : Pres m) (hn : Pres n) : Pres (if c then m else n) := by
  split
  · exact hm
  · exact hn

theorem Pres.fmap {α β : Type} (g : α → β) {m : TranscriptM α} (hm : Pres m) :
    Pres (g <$> m) := by
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
          obtain ⟨h1, rfl⟩ := pair_eq (ok_pair h3)
          subst h1
          exact hm t t₁ a ht hrun

/-! #### Running the four transcript primitives -/

/-- On a state given field by field, running tmRead h is exactly reading h. The
    unfolding needs the explicit StateT delta rules: the StateT.run_* equation lemmas
    do not match the elaborated term. -/
theorem tmRead_run_fields {T : Type} (h : Hashable T) (st buf : Bytes) (pos : Nat)
    (hash : Bytes → H256) (log : Array (Nat × Bytes)) :
    (tmRead h).run (Transcript.mk st buf pos hash log)
    = (Transcript.mk st buf pos hash log).read h := by
  unfold tmRead Transcript.read
  simp only [StateT.run, StateT.bind, StateT.get, StateT.set, StateT.lift, StateT.pure,
    Bind.bind, Pure.pure, Except.bind, Except.map, Except.pure]
  cases hbt : bytesTake buf pos h.width with
  | none => simp only [hbt]
  | some repr =>
      cases hrr : h.readRepr? repr with
      | none => simp only [hrr]
      | some val => simp only [hrr]

theorem tmReadN_run_fields {T : Type} (h : Hashable T) (st buf : Bytes) (pos : Nat)
    (hash : Bytes → H256) (log : Array (Nat × Bytes)) (n : Nat) :
    (tmReadN h n).run (Transcript.mk st buf pos hash log)
    = (Transcript.mk st buf pos hash log).readN h n := by
  unfold tmReadN
  simp only [StateT.run, StateT.bind, StateT.get, StateT.set, StateT.lift, StateT.pure,
    Bind.bind, Pure.pure, Except.bind, Except.map, Except.pure]
  cases hr : (Transcript.mk st buf pos hash log).readN h n with
  | error e => simp only [hr]
  | ok p => cases p with | mk vs t₂ => simp only [hr]

theorem tmCommon_run_fields {T : Type} (h : Hashable T) (st buf : Bytes) (pos : Nat)
    (hash : Bytes → H256) (log : Array (Nat × Bytes)) (input : T) :
    (tmCommon h input).run (Transcript.mk st buf pos hash log)
    = .ok ((), (Transcript.mk st buf pos hash log).common h input) := rfl

theorem tmSqueeze_run_fields {p : ℕ} [Fact (Nat.Prime p)] (st buf : Bytes) (pos : Nat)
    (hash : Bytes → H256) (log : Array (Nat × Bytes)) :
    (tmSqueezeChallenge (p := p)).run (Transcript.mk st buf pos hash log)
    = .ok ((Transcript.mk st buf pos hash log).squeezeChallenge (p := p).1,
          (Transcript.mk st buf pos hash log).squeezeChallenge (p := p).2) := by
  cases hs : Transcript.squeezeChallenge (p := p) (Transcript.mk st buf pos hash log) with
  | mk c t₂ => simp only [tmSqueezeChallenge, StateT.run, StateT.bind, StateT.get, StateT.set,
      StateT.pure, Bind.bind, Pure.pure, Except.bind, Except.pure, hs]

theorem Pres.read {T : Type} (h : Hashable T) : Pres (tmRead h) := by
  intro s t' a ht hrun
  cases s with | mk st buf pos hash log =>
    rw [tmRead_run_fields h st buf pos hash log] at hrun
    refine ⟨Transcript.Tiled.read h ht hrun, Transcript.read_ok_buffer h hrun⟩

/-- read_n: n reads in order, the whole thing failing if any one fails (mod.rs:178-184). -/
theorem Transcript.Tiled.readN {T : Type} (h : Hashable T) {t : Transcript}
    (ht : t.Tiled) (n : Nat) {vs : Array T} {t' : Transcript}
    (hrun : t.readN h n = .ok (vs, t')) : t'.Tiled := by
  have key : ∀ (n : Nat) (acc : Array T) (t : Transcript), Transcript.Tiled t →
      ∀ (vs : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (vs, t') → Transcript.Tiled t' := by
    intro n
    induction n with
    | zero =>
        intro acc t ht vs t' hrun
        simp only [Transcript.readN.go] at hrun
        obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
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
                exact ih (acc.push v) t₂ (Transcript.Tiled.read h ht hread) vs t' hrun
  exact key n #[] t ht vs t' hrun

/-- The companion of readN: n successful reads leave the buffer alone. -/
theorem readN_ok_buffer {T : Type} (h : Hashable T) {t : Transcript} (n : Nat)
    {vs : Array T} {t' : Transcript} (hrun : t.readN h n = .ok (vs, t')) :
    t'.buffer = t.buffer := by
  have key : ∀ (n : Nat) (acc : Array T) (t : Transcript) (vs : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (vs, t') → t'.buffer = t.buffer := by
    intro n
    induction n with
    | zero =>
        intro acc t vs t' hrun
        simp only [Transcript.readN.go] at hrun
        obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
        rfl
    | succ n ih =>
        intro acc t vs t' hrun
        cases hread : Transcript.read h t with
        | error e =>
            simp only [hread, Transcript.readN.go] at hrun
            cases hrun
        | ok p =>
            cases p with
            | mk v t₂ =>
                simp only [hread, Transcript.readN.go] at hrun
                exact ((ih (acc.push v) t₂ vs t' hrun).trans (Transcript.read_ok_buffer h hread))
  exact key n #[] t vs t' hrun

theorem Pres.readN {T : Type} (h : Hashable T) (n : Nat) : Pres (tmReadN h n) := by
  intro s t' a ht hrun
  cases s with | mk st buf pos hash log =>
    rw [tmReadN_run_fields h st buf pos hash log n] at hrun
    refine ⟨Transcript.Tiled.readN h ht n hrun, readN_ok_buffer h n hrun⟩

theorem Pres.common {T : Type} (h : Hashable T) (input : T) : Pres (tmCommon h input) := by
  intro s t' a ht hrun
  cases s with | mk st buf pos hash log =>
    rw [tmCommon_run_fields h st buf pos hash log input] at hrun
    obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
    exact ⟨Transcript.Tiled.common h ht input, rfl⟩

theorem Pres.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)] :
    Pres (tmSqueezeChallenge (p := p)) := by
  intro s t' a ht hrun
  cases s with | mk st buf pos hash log =>
    rw [tmSqueeze_run_fields (p := p) st buf pos hash log] at hrun
    obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
    exact ⟨Transcript.Tiled.squeezeChallenge ht, rfl⟩

/-! ### Closure under the loops the pipeline uses -/

theorem Pres.listFoldlM {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, Pres (f b x)) :
    ∀ (l : List α) (init : β), Pres (List.foldlM (init := init) f l) := by
  intro l
  induction l with
  | nil => intro init; exact Pres.pure _
  | cons a t ih =>
      intro init
      rw [List.foldlM_cons]
      refine Pres.bind (hf init _) (fun b => ih b)

theorem Pres.listMapM {α β : Type} (l : List α) {f : α → TranscriptM β}
    (hf : ∀ x, Pres (f x)) : Pres (List.mapM f l) := by
  induction l with
  | nil => exact Pres.pure _
  | cons a t ih =>
      rw [List.mapM_cons]
      refine Pres.bind (hf _) (fun _ => ?_)
      refine Pres.bind ih (fun _ => Pres.pure _)

theorem Pres.arrayFoldlM {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, Pres (f b x)) (init : β) (as : Array α) :
    Pres (Array.foldlM (init := init) f as) := by
  rw [← Array.foldlM_toList]
  exact Pres.listFoldlM hf as.toList init

theorem Pres.arrayMapM {α β : Type} (as : Array α) {f : α → TranscriptM β}
    (hf : ∀ x, Pres (f x)) : Pres (Array.mapM f as) := by
  rw [Array.mapM_eq_foldlM]
  refine Pres.arrayFoldlM (fun bs a => Pres.fmap _ (hf a)) #[] as

theorem Pres.listForIn {α β : Type} (l : List α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, Pres (f x b)) :
    Pres (forIn l init f) := by
  classical
  rw [List.forIn_eq_foldlM]
  refine Pres.fmap _ (Pres.listFoldlM ?_ l (ForInStep.yield init))
  intro b x
  cases b with
  | yield b => exact hf x b
  | done b => exact Pres.pure _

theorem Pres.arrayForIn {α β : Type} (as : Array α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, Pres (f x b)) :
    Pres (forIn as init f) := by
  rw [← Array.forIn_toList]
  exact Pres.listForIn as.toList init hf

/-! ### Transfer: the leaf read sites -/

theorem pres_readMultiplicities {F : Type} {G₁ : Type} (argument : LogupChunkedArgument F)
    (h : Hashable G₁) : Pres (Logup.readMultiplicities argument h) := by
  unfold Logup.readMultiplicities
  refine Pres.bind (Pres.read _) (fun _ => Pres.pure _)

theorem pres_trashReadCommitted {F : Type} {G₁ : Type} (argument : TrashArgument F)
    (h : Hashable G₁) : Pres (Trash.readCommitted argument h) := by
  unfold Trash.readCommitted
  refine Pres.bind (Pres.read _) (fun _ => Pres.pure _)

theorem pres_readCommitment {G₁ : Type} (cm : Logup.CommittedMultiplicities G₁)
    (nbChunks : Nat) (h : Hashable G₁) : Pres (Logup.CommittedMultiplicities.readCommitment cm nbChunks h) := by
  unfold Logup.CommittedMultiplicities.readCommitment
  refine Pres.bind (Pres.readN _ _) (fun _ => ?_)
  refine Pres.bind (Pres.read _) (fun _ => Pres.pure _)

theorem pres_hashInto {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (vk : VerifyingKey (Fr p) G₁) : Pres (VerifyingKey.hashInto vk) := by
  unfold VerifyingKey.hashInto
  exact Pres.common hashableFr vk.transcriptRepr

theorem pres_permReadProductCommitments {G₁ : Type} (perm : PermutationArgument)
    (csDegree : Nat) (h : Hashable G₁) :
    Pres (Permutation.readProductCommitments perm csDegree h) := by
  unfold Permutation.readProductCommitments
  refine Pres.ite ?_ ?_
  · refine Pres.bind (Pres.readN _ _) (fun _ => Pres.pure _)
  · intro t t' a ht h
    cases h

theorem pres_permVKevaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : Permutation.VerifyingKey G₁) :
    Pres (Permutation.VerifyingKey.evaluate (p := p) vk) := by
  unfold Permutation.VerifyingKey.evaluate
  refine Pres.bind (Pres.readN _ _) (fun _ => Pres.pure _)

theorem pres_permCommittedEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Permutation.Committed G₁) :
    Pres (Permutation.Committed.evaluate (p := p) coms) := by
  unfold Permutation.Committed.evaluate
  refine Pres.bind (Pres.listForIn (List.range coms.permutationProductCommitments.size)
      (#[] : Array (Permutation.SetEvaluated (Fr p))) (fun i s => ?_)) (fun _ => Pres.pure _)
  refine Pres.bind (Pres.read _) (fun _ => ?_)
  refine Pres.bind (Pres.read _) (fun _ => ?_)
  refine Pres.ite (Pres.bind (Pres.read _) (fun _ => Pres.pure _)) (Pres.pure _)

theorem pres_logupEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Logup.Committed G₁) : Pres (Logup.Committed.evaluate (p := p) coms) := by
  unfold Logup.Committed.evaluate
  refine Pres.bind (Pres.read _) (fun _ => ?_)
  refine Pres.bind (Pres.readN _ _) (fun _ => ?_)
  refine Pres.bind (Pres.read _) (fun _ => ?_)
  refine Pres.bind (Pres.read _) (fun _ => Pres.pure _)

theorem pres_trashEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Trash.Committed G₁) : Pres (Trash.Committed.evaluate (p := p) coms) := by
  unfold Trash.Committed.evaluate
  refine Pres.bind (Pres.read _) (fun _ => Pres.pure _)

/-! ### Transfer: the KZG multi-open half -/

theorem pres_addDummies {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (queries : Array (VerifierQuery (Fr p) G₁)) :
    Pres (MultiPrepare.addDummies (G₂ := G₂) (Gₜ := Gₜ) g1 queries) := by
  unfold MultiPrepare.addDummies
  refine Pres.bind (Pres.lift _) (fun dummies => ?_)
  refine Pres.listFoldlM (fun qs x => ?_) dummies queries
  refine Pres.bind (Pres.read _) (fun eval => ?_)
  cases hq : qs[x.1]? with
  | none =>
      show Pres (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
      exact (Pres.lift (Except.error (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
        : Pres (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349")))
  | some o =>
      show Pres (pure (qs.push { point := x.2, commitmentLabel := o.commitmentLabel, commitment := o.commitment, eval := eval }))
      exact Pres.pure _

theorem pres_phaseA {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    Pres (phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries) := by
  unfold phaseA
  refine Pres.ite (α := MultiPrepare.PhaseA (Fr p) G₁)
      (c := feat.outerFewerPointSets && fewerPointSetsRuntime) ?_ ?_
  · refine Pres.bind (pres_addDummies g1 queries) (fun _ => ?_)
    refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
    refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
    refine Pres.bind (Pres.lift _) (fun _ => ?_)
    refine Pres.bind (Pres.lift _) (fun _ => Pres.pure _)
  · refine Pres.bind (Pres.pure queries) (fun _ => ?_)
    refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
    refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
    refine Pres.bind (Pres.lift _) (fun _ => ?_)
    refine Pres.bind (Pres.lift _) (fun _ => Pres.pure _)

theorem pres_phaseB {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) :
    Pres (phaseB g1 fc feat a) := by
  unfold phaseB
  refine Pres.bind (Pres.read _) (fun _ => ?_)
  refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
  refine Pres.bind (Pres.listMapM (List.range a.qEvalSets.size) (fun _ => Pres.read _)) (fun _ => ?_)
  refine Pres.bind (Pres.lift _) (fun _ => Pres.pure _)

theorem pres_phaseC {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) (b : MultiPrepare.PhaseB (Fr p) G₁) :
    Pres (phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b) := by
  unfold phaseC
  refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
  refine Pres.bind (Pres.lift _) (fun _ => ?_)
  refine Pres.bind (Pres.lift _) (fun _ => ?_)
  refine Pres.bind (Pres.read _) (fun _ => Pres.pure _)

theorem pres_multiPrepare {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    Pres (multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries) := by
  unfold multiPrepare
  refine Pres.bind (pres_phaseA g1 fc feat fewerPointSetsRuntime queries) (fun _ => ?_)
  refine Pres.bind (pres_phaseB g1 fc feat _) (fun _ => ?_)
  refine Pres.bind (pres_phaseC g1 fc feat _ _) (fun _ => Pres.pure _)

/-! ### transcript_log_concat -/

/-- **transcript_log_concat** - the log's reprs concatenate to the consumed transcript
    prefix.

    Stated for an arbitrary transcript action that preserves the invariant (every
    pipeline action does, by the transfer lemmas above), over the proof stream `pi` the
    transcript was initialised with. This is the fact `decodeRust` and `verifyMsgs`
    need: the messages `decodeRust` recovers are the log entries re-decoded, so their
    re-serialisation is the concatenation of the log reprs, which by this lemma is
    exactly the prefix of `pi` the pipeline consumed - and when `assertEmpty` has
    fired, all of `pi`.

    The shape is design2.md:977's `(t.log.map (·.2)).foldl append = pi.extract 0 t.pos`,
    with `extract` rather than `take` because ByteArray has no take. -/
theorem transcript_log_concat {α : Type} {m : TranscriptM α} (hm : Pres m) (pi : Bytes)
    {a : α} {t : Transcript}
    (hrun : m.run (Transcript.initFromBytes pi) = .ok (a, t)) :
    t.recorded = pi.extract 0 t.pos := by
  have h1 : Transcript.Tiled t := Pres.of_run hm (Transcript.tiled_initFromBytes pi) hrun
  have h2 : t.buffer = pi := Pres.buffer hm (Transcript.tiled_initFromBytes pi) hrun
  rw [← Transcript.recorded_eq_extract] at h1
  rw [h1, h2]

/-- The same for a transcript initialised with an explicit hash, which is the
    `prepareMsgs` side of the codec equivalence. -/
theorem transcript_log_concat_hash {α : Type} {m : TranscriptM α} (hm : Pres m)
    (H : Bytes → H256) (pi : Bytes) {a : α} {t : Transcript}
    (hrun : m.run (Transcript.initWithHash H pi) = .ok (a, t)) :
    t.recorded = pi.extract 0 t.pos := by
  have h1 : Transcript.Tiled t := Pres.of_run hm (Transcript.tiled_initWithHash H pi) hrun
  have h2 : t.buffer = pi := Pres.buffer hm (Transcript.tiled_initWithHash H pi) hrun
  rw [← Transcript.recorded_eq_extract] at h1
  rw [h1, h2]

/-! ### D-P23: satisfiability and falsification -/

/-- The invariant can fail: a transcript whose cursor disagrees with its log is not
    tiled. This is the only shape it can fail at, and it is what makes the lemma say
    something. -/
theorem transcriptLogRefutesUntiled : ∃ t : Transcript, ¬ Transcript.Tiled t := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 7 4) 3 keccak256 #[], ?_⟩
  unfold Transcript.Tiled Transcript.recordedList
  decide

/-- Satisfiability, computed: one real read of a real buffer tiles exactly the consumed
    prefix. -/
def transcriptLogKat_tiles : Bool :=
  match (Transcript.initFromBytes (natToBytesLE 7 4)).read hashableU32 with
  | .ok (v, t) =>
      v == 7 && t.pos == 4 && t.recorded == natToBytesLE 7 4 &&
        t.recorded == t.buffer.extract 0 t.pos
  | .error _ => false

/-- Satisfiability over TWO reads: the concatenation is in read order. -/
def transcriptLogKat_twoReads : Bool :=
  match (Transcript.initFromBytes (natToBytesLE 7 4 ++ natToBytesLE 9 4)).read hashableU32 >>=
        (fun p => p.2.read hashableU32) with
  | .ok (v, t) =>
      v == 9 && t.pos == 8 && t.recorded == (natToBytesLE 7 4 ++ natToBytesLE 9 4) &&
        t.recorded == t.buffer.extract 0 t.pos
  | .error _ => false

/-- Falsifiability, computed: with a byte left UNCONSUMED the concatenation is a strict
    prefix of the stream. Without this the lemma could be read as saying the log
    concatenates to the whole buffer, which is exactly what decodeRust's trailing-bytes
    check exists to reject. -/
def transcriptLogKat_strictPrefix : Bool :=
  match (Transcript.initFromBytes (natToBytesLE 7 4 ++ natToBytesLE 1 1)).read hashableU32 with
  | .ok (_, t) => t.recorded.size == 4 && t.buffer.size == 5 &&
      t.recorded ≠ t.buffer && t.recorded == t.buffer.extract 0 t.pos
  | .error _ => false

/-- Falsifiability of the invariant itself, computed: a hand-built transcript whose
    cursor disagrees with its log fails the tiling. -/
def transcriptLogKat_untiled : Bool :=
  let t : Transcript := Transcript.mk Bytes.empty (natToBytesLE 7 4) 3 keccak256 #[]
  !(t.recorded == t.buffer.extract 0 t.pos)

def transcriptLogKats_ok : Bool :=
  [ transcriptLogKat_tiles, transcriptLogKat_twoReads,
    transcriptLogKat_strictPrefix, transcriptLogKat_untiled ].all id

#eval transcriptLogKats_ok   -- expect true

/-! ### Transfer: the algebraic half -/

/-- A guard that throws in one branch preserves the invariant: the throwing branch never
    returns, and the other branch is the rest of the block. This is what 'if c then throw
    f' and 'unless c do throw f' desugar to in a do-block: the if wraps the continuation
    in BOTH branches, so the continuation is proved once and passed twice. -/
theorem Pres.guard {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : Pres k) (h : α → Pres k) :
    Pres (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  Pres.ite (α := β) (c := c) (Pres.bind (Pres.lift (Except.error f)) h) hk

/-- The unless form: the throwing branch is the else one. -/
theorem Pres.guard' {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : Pres k) (h : α → Pres k) :
    Pres (if c then k else ((throw f : TranscriptM α) >>= fun x => k)) :=
  Pres.ite (α := β) (c := c) hk (Pres.bind (Pres.lift (Except.error f)) h)

theorem pres_readFixedEvals {p : ℕ} [Fact (Nat.Prime p)]
    (cs : ConstraintSystem (Fr p)) : Pres (Verifier.readFixedEvals (p := p) cs) := by
  unfold Verifier.readFixedEvals
  apply Pres.guard
  · refine Pres.bind (Pres.readN _ _) (fun read => ?_)
    refine Pres.bind (Pres.listFoldlM (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => Pres.pure _)
    refine Pres.ite (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (Pres.lift _) (Pres.pure _)
  · intro z
    refine Pres.bind (Pres.readN _ _) (fun read => ?_)
    refine Pres.bind (Pres.listFoldlM (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => Pres.pure _)
    refine Pres.ite (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (Pres.lift _) (Pres.pure _)

/-- The single-hypothesis form of the two guards: the continuation is proved ONCE, which
    is what makes parseTrace's three guards linear instead of exponential. -/
theorem Pres.guardWhen {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : Pres k) :
    Pres (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  Pres.ite (α := β) (c := c) (Pres.bind (Pres.lift (Except.error f)) (fun _ => hk)) hk

theorem Pres.guardUnless {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : Pres k) :
    Pres (if c then k else ((throw f : TranscriptM α) >>= fun x => k)) :=
  Pres.ite (α := β) (c := c) hk (Pres.bind (Pres.lift (Except.error f)) (fun _ => hk))

theorem pres_readAlgebra {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    Pres (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
      nbCommitted numProofs instances) := by
  unfold Verifier.readAlgebra
  refine Pres.bind (Pres.readN _ _) (fun _ => ?_)
  refine Pres.bind Pres.squeezeChallenge (fun _ => ?_)
  refine Pres.bind (Pres.lift _) (fun _ => ?_)
  refine Pres.bind (Pres.listMapM instances.toList (fun row =>
      Pres.listMapM vk.cs.instanceQueries.toList (fun q => ?_))) (fun _ => ?_)
  · refine Pres.ite (α := Fr p) (c := q.1.index < nbCommitted) (Pres.read _) ?_
    dsimp only
    cases hq : row[q.1.index - nbCommitted]? with
    | none =>
        exact (Pres.lift (Except.error (Fault.panic "proofs/src/plonk/verifier.rs:366"))
          : Pres (throw (Fault.panic "proofs/src/plonk/verifier.rs:366")))
    | some col =>
        dsimp only
        apply Pres.guard'
        · exact Pres.lift _
        · intro z
          exact Pres.lift _
  refine Pres.bind (Pres.listMapM (List.range numProofs) (fun _ => Pres.readN _ _)) (fun _ => ?_)
  refine Pres.bind (pres_readFixedEvals vk.cs) (fun _ => ?_)
  refine Pres.bind (pres_permVKevaluate vk.permutation) (fun _ => ?_)
  refine Pres.bind (Pres.listMapM permutations.toList (fun pc =>
      pres_permCommittedEvaluate pc)) (fun _ => ?_)
  refine Pres.bind (Pres.listMapM lookups.toList (fun row =>
      Pres.listMapM row.toList (fun l => pres_logupEvaluate l))) (fun _ => ?_)
  refine Pres.bind (Pres.listMapM trashcans.toList (fun row =>
      Pres.listMapM row.toList (fun t => pres_trashEvaluate t))) (fun _ => Pres.pure _)


/-! ### Item 2 of P-CODEC-A: the width condition on transcript log entries

    `decodeRust` (Exec/Native.lean:244-261) maps every log record by

        if rec.1 == wG1 then ... else if rec.1 == wFr then ... else none

    with `wG1 = (hashableG1 E.g1).width` and `wFr = (hashableFr (p := p)).width`.
    The `else none` arm means: if ANY verifier-path read logged a third width,
    `verifyNative` can accept while `decodeRust = none`, and the right-hand side of
    `verifyNative_iff_msgs_codec` is empty - the `iff` would be FALSE, not merely
    unproved. So the width condition is an obligation of that theorem, not tidiness.

    WHAT IS PROVED HERE, and what is not. The three `Hashable`s the tree defines
    have widths 32 (`hashableFr`, every `p`), `g1CompressedWidth` = 48
    (`hashableG1`, every codec - so the codec PARAMETER cannot move the width), and
    4 (`hashableU32`). The condition is therefore exactly: no verifier-path read
    uses `hashableU32`. `critic.md:81` asserts that; it is asserted here as a
    predicate (`Transcript.LogWidths`), with the closure machinery that proves it
    for every pipeline definition that `Pres` is proved for, and with the
    `hashableU32` case refuted as a THEOREM rather than left as a comment. The two
    definitions `Pres` does not reach (`Verifier.parseTrace`,
    `Verifier.verifyAlgebraicConstraints`) are the same two gaps here: see the
    report. Nothing below depends on them; each is one more transfer lemma once
    their `Pres` exists.

    THE WHNF LANDMINE APPLIES HERE TOO, and bit again while writing this:
    `Transcript.LogWidths.squeeze` cannot be proved by `exact ht` even after
    `cases t` - the unifier whnfs `(t.squeeze).2` and burns the heartbeat budget on
    the byte emitter. The fix is the same one `Transcript.Tiled.replaceState` uses:
    state the fact with the new state as a VARIABLE and let unification do nothing
    that requires reducing `squeeze`. -/

/-- A logged width `decodeRust` can dispatch on: a scalar repr, or a compressed G1
    point. Exactly the two arms of its `if` chain. -/
def Hashable.AllowedWidth {T : Type} (h : Hashable T) : Prop :=
  h.width = 32 ∨ h.width = g1CompressedWidth

/-- The three widths, pinned as theorems rather than as prose: 32 for every scalar
    field, `g1CompressedWidth` for EVERY G1 codec (so no codec choice can move it),
    and 4 for the u32 reader that must never appear on the verifier path. -/
theorem hashableFr_width {p : ℕ} [Fact (Nat.Prime p)] :
    (hashableFr (p := p)).width = 32 := rfl

theorem hashableG1_width {G₁ : Type} (c : G1Codec G₁) :
    (hashableG1 c).width = g1CompressedWidth := rfl

theorem hashableU32_width : hashableU32.width = 4 := rfl

theorem hashableFr_allowed {p : ℕ} [Fact (Nat.Prime p)] :
    (hashableFr (p := p)).AllowedWidth := Or.inl rfl

theorem hashableG1_allowed {G₁ : Type} (c : G1Codec G₁) :
    (hashableG1 c).AllowedWidth := Or.inr rfl

/-- `hashableU32` is the one reader whose width the decoder cannot dispatch on. This
    is why the audit of the verifier path matters, and it is a theorem, not a quote
    from critic.md. -/
theorem hashableU32_not_allowed : ¬ hashableU32.AllowedWidth := by
  intro h
  cases h with
  | inl h => exact absurd h (by decide)
  | inr h => exact absurd h (by decide)

/-- **The width condition.** Every width the transcript has logged is one the decoder
    dispatches on. -/
def Transcript.LogWidths (t : Transcript) : Prop :=
  ∀ rec ∈ t.log.toList, rec.1 = 32 ∨ rec.1 = g1CompressedWidth

/-- Replacing the hasher state cannot touch the logged widths - the same shape, and
    for the same reason, as `Transcript.Tiled.replaceState`. -/
theorem Transcript.LogWidths.replaceState {t : Transcript} {s : Bytes}
    (ht : t.LogWidths) : ({ t with state := s }).LogWidths := ht

theorem Transcript.LogWidths.initFromBytes (bytes : Bytes) :
    (Transcript.initFromBytes bytes).LogWidths := by
  intro rec hmem
  simp [Transcript.initFromBytes] at hmem

theorem Transcript.LogWidths.initWithHash (H : Bytes → H256) (bytes : Bytes) :
    (Transcript.initWithHash H bytes).LogWidths := by
  intro rec hmem
  simp [Transcript.initWithHash] at hmem

/-- Absorb logs nothing: only `Transcript.read` writes `log` (Exec/Transcript.lean:153). -/
theorem Transcript.LogWidths.common {T : Type} (h : Hashable T) {t : Transcript}
    (ht : t.LogWidths) (input : T) : (t.common h input).LogWidths := ht

theorem Transcript.LogWidths.squeeze {t : Transcript} (ht : t.LogWidths) :
    (t.squeeze).2.LogWidths := by
  cases t with | mk st buf pos h log => exact Transcript.LogWidths.replaceState ht

theorem Transcript.LogWidths.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)]
    {t : Transcript} (ht : t.LogWidths) : (t.squeezeChallenge (p := p)).2.LogWidths := by
  cases t with | mk st buf pos h log => exact Transcript.LogWidths.replaceState ht

/-- **The step.** A successful read extends the logged widths by exactly the hashable
    it read, and by nothing else. This is the only place a width enters the log. -/
theorem Transcript.LogWidths.read {T : Type} (h : Hashable T) (hh : h.AllowedWidth)
    {t : Transcript} (ht : t.LogWidths) {val : T} {t' : Transcript}
    (hrun : t.read h = .ok (val, t')) : t'.LogWidths := by
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
          refine Transcript.LogWidths.common h ?_ val'
          intro rec hmem
          rw [Array.toList_push] at hmem
          rcases List.mem_append.mp hmem with hold | hnew
          · exact ht rec hold
          · rw [List.mem_singleton] at hnew
            cases hnew
            exact hh

/-- n reads in order log n allowed widths and nothing else. -/
theorem Transcript.LogWidths.readN {T : Type} (h : Hashable T) (hh : h.AllowedWidth)
    {t : Transcript} (ht : t.LogWidths) (n : Nat) {vs : Array T} {t' : Transcript}
    (hrun : t.readN h n = .ok (vs, t')) : t'.LogWidths := by
  have key : ∀ (n : Nat) (acc : Array T) (t : Transcript), Transcript.LogWidths t →
      ∀ (vs : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (vs, t') → Transcript.LogWidths t' := by
    intro n
    induction n with
    | zero =>
        intro acc t ht vs t' hrun
        simp only [Transcript.readN.go] at hrun
        obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
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
                exact ih (acc.push v) t₂ (Transcript.LogWidths.read h hh ht hread) vs t' hrun
  exact key n #[] t ht vs t' hrun

/-- An action that never logs a width the decoder cannot dispatch on: the companion
    of `Pres`, and discharged by the same structural walk. `Pres` says where the
    cursor got to; this says what the decoder can read back. Neither implies the
    other, so the codec lemma needs both. -/
def PresWidths {T : Type} (m : TranscriptM T) : Prop :=
  ∀ (t t' : Transcript) (a : T), Transcript.LogWidths t →
    m.run t = .ok (a, t') → Transcript.LogWidths t'


/-! #### Closure: the same constructs `Pres` is closed under -/

theorem PresWidths.pure {T : Type} (x : T) : PresWidths (StateT.pure x : TranscriptM T) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
  exact ht

theorem PresWidths.lift {T : Type} (e : Except Fault T) : PresWidths (StateT.lift e) := by
  intro t t' a ht h
  cases e with
  | error _ => cases h
  | ok x =>
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
      exact ht

theorem PresWidths.get : PresWidths (StateT.get : TranscriptM Transcript) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
  exact ht

theorem PresWidths.bind {α β : Type} {m : TranscriptM α} {f : α → TranscriptM β}
    (hm : PresWidths m) (hf : ∀ x, PresWidths (f x)) : PresWidths (m >>= f) := by
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

theorem PresWidths.seq {α β : Type} {m : TranscriptM α} {n : TranscriptM β}
    (hm : PresWidths m) (hn : PresWidths n) : PresWidths (m >>= fun _ => n) :=
  PresWidths.bind hm (fun _ => hn)

theorem PresWidths.ite {α : Type} {c : Prop} [inst : Decidable c] {m n : TranscriptM α}
    (hm : PresWidths m) (hn : PresWidths n) : PresWidths (if c then m else n) := by
  split
  · exact hm
  · exact hn

theorem PresWidths.fmap {α β : Type} (g : α → β) {m : TranscriptM α} (hm : PresWidths m) :
    PresWidths (g <$> m) := by
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
          obtain ⟨h1, rfl⟩ := pair_eq (ok_pair h3)
          subst h1
          exact hm t t₁ a ht hrun

/-- A guard that throws in one branch: the throwing arm never returns, so the
    continuation is proved once. Same shape as `Pres.guard`. -/
theorem PresWidths.guard {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresWidths k) (h : α → PresWidths k) :
    PresWidths (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  PresWidths.ite (α := β) (c := c) (PresWidths.bind (PresWidths.lift (Except.error f)) h) hk

/-- The unless form. -/
theorem PresWidths.guard' {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresWidths k) (h : α → PresWidths k) :
    PresWidths (if c then k else ((throw f : TranscriptM α) >>= fun x => k)) :=
  PresWidths.ite (α := β) (c := c) hk (PresWidths.bind (PresWidths.lift (Except.error f)) h)

theorem PresWidths.read {T : Type} (h : Hashable T) (hh : h.AllowedWidth) :
    PresWidths (tmRead h) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmRead_run_fields h st buf pos hash log] at hrun
      exact Transcript.LogWidths.read h hh ht hrun

theorem PresWidths.readN {T : Type} (h : Hashable T) (hh : h.AllowedWidth) (n : Nat) :
    PresWidths (tmReadN h n) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmReadN_run_fields h st buf pos hash log n] at hrun
      exact Transcript.LogWidths.readN h hh ht n hrun

theorem PresWidths.common {T : Type} (h : Hashable T) (input : T) :
    PresWidths (tmCommon h input) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmCommon_run_fields h st buf pos hash log input] at hrun
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
      exact Transcript.LogWidths.common h ht input

theorem PresWidths.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)] :
    PresWidths (tmSqueezeChallenge (p := p)) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmSqueeze_run_fields (p := p) st buf pos hash log] at hrun
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
      exact Transcript.LogWidths.squeezeChallenge ht

theorem PresWidths.listFoldlM {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, PresWidths (f b x)) :
    ∀ (l : List α) (init : β), PresWidths (List.foldlM (init := init) f l) := by
  intro l
  induction l with
  | nil => intro init; exact PresWidths.pure _
  | cons a t ih =>
      intro init
      rw [List.foldlM_cons]
      refine PresWidths.bind (hf init _) (fun b => ih b)

theorem PresWidths.listMapM {α β : Type} (l : List α) {f : α → TranscriptM β}
    (hf : ∀ x, PresWidths (f x)) : PresWidths (List.mapM f l) := by
  induction l with
  | nil => exact PresWidths.pure _
  | cons a t ih =>
      rw [List.mapM_cons]
      refine PresWidths.bind (hf _) (fun _ => ?_)
      refine PresWidths.bind ih (fun _ => PresWidths.pure _)

theorem PresWidths.arrayFoldlM {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, PresWidths (f b x)) (init : β) (as : Array α) :
    PresWidths (Array.foldlM (init := init) f as) := by
  rw [← Array.foldlM_toList]
  exact PresWidths.listFoldlM hf as.toList init

theorem PresWidths.arrayMapM {α β : Type} (as : Array α) {f : α → TranscriptM β}
    (hf : ∀ x, PresWidths (f x)) : PresWidths (Array.mapM f as) := by
  rw [Array.mapM_eq_foldlM]
  refine PresWidths.arrayFoldlM (fun bs a => PresWidths.fmap _ (hf a)) #[] as

theorem PresWidths.listForIn {α β : Type} (l : List α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, PresWidths (f x b)) :
    PresWidths (forIn l init f) := by
  classical
  rw [List.forIn_eq_foldlM]
  refine PresWidths.fmap _ (PresWidths.listFoldlM ?_ l (ForInStep.yield init))
  intro b x
  cases b with
  | yield b => exact hf x b
  | done b => exact PresWidths.pure _

theorem PresWidths.arrayForIn {α β : Type} (as : Array α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, PresWidths (f x b)) :
    PresWidths (forIn as init f) := by
  rw [← Array.forIn_toList]
  exact PresWidths.listForIn as.toList init hf


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

theorem PresWidths.readMultiplicities {F : Type} {G₁ : Type}
    (argument : LogupChunkedArgument F) (h : Hashable G₁) (hh : h.AllowedWidth) :
    PresWidths (Logup.readMultiplicities argument h) := by
  unfold Logup.readMultiplicities
  refine PresWidths.bind (PresWidths.read h hh) (fun _ => PresWidths.pure _)

theorem PresWidths.trashReadCommitted {F : Type} {G₁ : Type}
    (argument : TrashArgument F) (h : Hashable G₁) (hh : h.AllowedWidth) :
    PresWidths (Trash.readCommitted argument h) := by
  unfold Trash.readCommitted
  refine PresWidths.bind (PresWidths.read h hh) (fun _ => PresWidths.pure _)

theorem PresWidths.readCommitment {G₁ : Type}
    (cm : Logup.CommittedMultiplicities G₁) (nbChunks : Nat) (h : Hashable G₁)
    (hh : h.AllowedWidth) :
    PresWidths (Logup.CommittedMultiplicities.readCommitment cm nbChunks h) := by
  unfold Logup.CommittedMultiplicities.readCommitment
  refine PresWidths.bind (PresWidths.readN h hh _) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.read h hh) (fun _ => PresWidths.pure _)

theorem PresWidths.hashInto {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (vk : VerifyingKey (Fr p) G₁) : PresWidths (VerifyingKey.hashInto vk) := by
  unfold VerifyingKey.hashInto
  exact PresWidths.common hashableFr vk.transcriptRepr

theorem PresWidths.permReadProductCommitments {G₁ : Type} (perm : PermutationArgument)
    (csDegree : Nat) (h : Hashable G₁) (hh : h.AllowedWidth) :
    PresWidths (Permutation.readProductCommitments perm csDegree h) := by
  unfold Permutation.readProductCommitments
  refine PresWidths.ite ?_ ?_
  · refine PresWidths.bind (PresWidths.readN h hh _) (fun _ => PresWidths.pure _)
  · intro t t' a ht h
    cases h

theorem PresWidths.permVKevaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : Permutation.VerifyingKey G₁) :
    PresWidths (Permutation.VerifyingKey.evaluate (p := p) vk) := by
  unfold Permutation.VerifyingKey.evaluate
  refine PresWidths.bind
    (PresWidths.readN (hashableFr (p := p)) hashableFr_allowed _) (fun _ => PresWidths.pure _)

theorem PresWidths.permCommittedEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Permutation.Committed G₁) :
    PresWidths (Permutation.Committed.evaluate (p := p) coms) := by
  unfold Permutation.Committed.evaluate
  refine PresWidths.bind (PresWidths.listForIn (List.range coms.permutationProductCommitments.size)
      (#[] : Array (Permutation.SetEvaluated (Fr p))) (fun i s => ?_)) (fun _ => PresWidths.pure _)
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresWidths.ite
      (PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed)
        (fun _ => PresWidths.pure _)) (PresWidths.pure _)

theorem PresWidths.logupEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Logup.Committed G₁) : PresWidths (Logup.Committed.evaluate (p := p) coms) := by
  unfold Logup.Committed.evaluate
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresWidths.bind
    (PresWidths.readN (hashableFr (p := p)) hashableFr_allowed _) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed)
    (fun _ => PresWidths.pure _)

theorem PresWidths.trashEvaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Trash.Committed G₁) : PresWidths (Trash.Committed.evaluate (p := p) coms) := by
  unfold Trash.Committed.evaluate
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed)
    (fun _ => PresWidths.pure _)

theorem PresWidths.addDummies {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresWidths (MultiPrepare.addDummies (G₂ := G₂) (Gₜ := Gₜ) g1 queries) := by
  unfold MultiPrepare.addDummies
  refine PresWidths.bind (PresWidths.lift _) (fun dummies => ?_)
  refine PresWidths.listFoldlM (fun qs x => ?_) dummies queries
  refine PresWidths.bind (PresWidths.read (hashableFr (p := p)) hashableFr_allowed)
    (fun eval => ?_)
  cases hq : qs[x.1]? with
  | none =>
      show PresWidths (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
      exact (PresWidths.lift (Except.error (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
        : PresWidths (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349")))
  | some o =>
      exact PresWidths.pure _

theorem PresWidths.phaseA {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresWidths (phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries) := by
  unfold Midfall.Halo2.phaseA
  refine PresWidths.ite (α := MultiPrepare.PhaseA (Fr p) G₁)
      (c := feat.outerFewerPointSets && fewerPointSetsRuntime) ?_ ?_
  · refine PresWidths.bind (PresWidths.addDummies g1 queries) (fun _ => ?_)
    refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
    refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
    refine PresWidths.bind (PresWidths.lift _) (fun _ => ?_)
    refine PresWidths.bind (PresWidths.lift _) (fun _ => PresWidths.pure _)
  · refine PresWidths.bind (PresWidths.pure queries) (fun _ => ?_)
    refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
    refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
    refine PresWidths.bind (PresWidths.lift _) (fun _ => ?_)
    refine PresWidths.bind (PresWidths.lift _) (fun _ => PresWidths.pure _)

theorem PresWidths.phaseB {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) :
    PresWidths (phaseB g1 fc feat a) := by
  unfold Midfall.Halo2.phaseB
  refine PresWidths.bind (PresWidths.read (hashableG1 g1) (hashableG1_allowed g1)) (fun _ => ?_)
  refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
  refine PresWidths.bind (PresWidths.listMapM (List.range a.qEvalSets.size)
      (fun _ => PresWidths.read (hashableFr (p := p)) hashableFr_allowed)) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.lift _) (fun _ => PresWidths.pure _)

theorem PresWidths.phaseC {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) (b : MultiPrepare.PhaseB (Fr p) G₁) :
    PresWidths (phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b) := by
  unfold Midfall.Halo2.phaseC
  refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
  refine PresWidths.bind (PresWidths.lift _) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.lift _) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.read (hashableG1 g1) (hashableG1_allowed g1))
    (fun _ => PresWidths.pure _)

theorem PresWidths.multiPrepare {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresWidths (multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime
      queries) := by
  unfold Midfall.Halo2.multiPrepare
  refine PresWidths.bind (PresWidths.phaseA g1 fc feat fewerPointSetsRuntime queries)
    (fun _ => ?_)
  refine PresWidths.bind (PresWidths.phaseB g1 fc feat _) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.phaseC g1 fc feat _ _) (fun _ => PresWidths.pure _)


theorem PresWidths.readFixedEvals {p : ℕ} [Fact (Nat.Prime p)]
    (cs : ConstraintSystem (Fr p)) :
    PresWidths (Verifier.readFixedEvals (p := p) cs) := by
  unfold Verifier.readFixedEvals
  apply PresWidths.guard
  · refine PresWidths.bind
      (PresWidths.readN (hashableFr (p := p)) hashableFr_allowed _) (fun read => ?_)
    refine PresWidths.bind (PresWidths.listFoldlM (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => PresWidths.pure _)
    refine PresWidths.ite (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (PresWidths.lift _) (PresWidths.pure _)
  · intro z
    refine PresWidths.bind
      (PresWidths.readN (hashableFr (p := p)) hashableFr_allowed _) (fun read => ?_)
    refine PresWidths.bind (PresWidths.listFoldlM (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => PresWidths.pure _)
    refine PresWidths.ite (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (PresWidths.lift _) (PresWidths.pure _)

theorem PresWidths.readAlgebra {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    PresWidths (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
      nbCommitted numProofs instances) := by
  unfold Verifier.readAlgebra
  refine PresWidths.bind
    (PresWidths.readN (hashableG1 g1) (hashableG1_allowed g1) _) (fun _ => ?_)
  refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => ?_)
  refine PresWidths.bind (PresWidths.lift _) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.listMapM instances.toList (fun row =>
      PresWidths.listMapM vk.cs.instanceQueries.toList (fun q => ?_))) (fun _ => ?_)
  · refine PresWidths.ite (α := Fr p) (c := q.1.index < nbCommitted)
      (PresWidths.read (hashableFr (p := p)) hashableFr_allowed) ?_
    dsimp only
    cases hq : row[q.1.index - nbCommitted]? with
    | none =>
        exact (PresWidths.lift (Except.error (Fault.panic "proofs/src/plonk/verifier.rs:366"))
          : PresWidths (throw (Fault.panic "proofs/src/plonk/verifier.rs:366")))
    | some col =>
        dsimp only
        apply PresWidths.guard'
        · exact PresWidths.lift _
        · intro z
          exact PresWidths.lift _
  refine PresWidths.bind (PresWidths.listMapM (List.range numProofs)
      (fun _ => PresWidths.readN (hashableFr (p := p)) hashableFr_allowed _)) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.readFixedEvals vk.cs) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.permVKevaluate vk.permutation) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.listMapM permutations.toList (fun pc =>
      PresWidths.permCommittedEvaluate pc)) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.listMapM lookups.toList (fun row =>
      PresWidths.listMapM row.toList (fun l => PresWidths.logupEvaluate l))) (fun _ => ?_)
  refine PresWidths.bind (PresWidths.listMapM trashcans.toList (fun row =>
      PresWidths.listMapM row.toList (fun t => PresWidths.trashEvaluate t)))
      (fun _ => PresWidths.pure _)


/-! #### The consequence `decodeRust` needs, and the D-P23 halves -/

/-- **The width condition in the form `decodeRust` consumes it.** Its map over the log is
    `if rec.1 == wG1 then ... else if rec.1 == wFr then ... else none`. If every logged
    width is 32 or `g1CompressedWidth`, the third arm is unreachable: the three-arm
    dispatch is the two-arm one, record by record. So a proof of `PresWidths` for the
    whole pipeline is exactly what turns "the log tiles the consumed prefix" (item 1 of
    P-LOGCONCAT, and `transcript_log_concat` above) into "the messages `decodeRust`
    returns re-serialise to that prefix". -/
theorem widthDispatch_exhaustive {T : Type} (f g : Bytes → Option T) (rec : Nat × Bytes)
    (h : rec.1 = 32 ∨ rec.1 = g1CompressedWidth) :
    (if rec.1 == g1CompressedWidth then f rec.2
      else if rec.1 == 32 then g rec.2 else none) =
      (if rec.1 == g1CompressedWidth then f rec.2 else g rec.2) := by
  cases h with
  | inl h32 => rw [h32]; rfl
  | inr h48 => rw [h48]; rfl

/-- The whole-log form: with every width allowed, `decodeRust` can fail on a record only
    if that record's own decoder fails - never on the width test. -/
theorem widthDispatch_exhaustive_list {T : Type} (f g : Bytes → Option T)
    (l : List (Nat × Bytes)) (h : ∀ rec ∈ l, rec.1 = 32 ∨ rec.1 = g1CompressedWidth) :
    l.mapM (fun rec => if rec.1 == g1CompressedWidth then f rec.2
        else if rec.1 == 32 then g rec.2 else none)
      = l.mapM (fun rec => if rec.1 == g1CompressedWidth then f rec.2 else g rec.2) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.mapM_cons, List.mapM_cons,
        widthDispatch_exhaustive f g a (h a List.mem_cons_self),
        ih (fun rec hmem => h rec (List.mem_cons_of_mem a hmem))]

/-- D-P23 falsification, as a THEOREM: the third arm is not decoration. A record of the
    width a real `hashableU32` read logs is dropped by the dispatch even though the read
    succeeded - which is exactly how `verifyNative` could accept while `decodeRust` is
    `none`, and so how the `iff` of `verifyNative_iff_msgs_codec` would be FALSE without
    the width condition. -/
theorem widthDispatch_refutesOtherWidth :
    ∃ (rec : Nat × Bytes),
      (if rec.1 == g1CompressedWidth then (some 1 : Option Nat)
        else if rec.1 == 32 then some 2 else none) = none ∧
      rec.1 = hashableU32.width ∧ rec.1 ≠ 32 ∧ rec.1 ≠ g1CompressedWidth := by
  refine ⟨(hashableU32.width, Bytes.empty), rfl, rfl, by decide, by decide⟩

/-- D-P23 falsification, as a THEOREM: the width condition can fail, and it fails at the
    shape a real read produces - one logged record, of width 4. -/
theorem transcriptLogWidths_refutesU32Read :
    ∃ (t : Transcript), ¬ Transcript.LogWidths t := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 7 4) 4 keccak256
      #[(hashableU32.width, natToBytesLE 7 4)], ?_⟩
  intro h
  have h1 : hashableU32.width = 32 ∨ hashableU32.width = g1CompressedWidth :=
    h (hashableU32.width, natToBytesLE 7 4) (by simp)
  exact hashableU32_not_allowed h1

/-- A toy G1 codec for the width checks: it accepts exactly the 48-byte strings, so the
    read succeeds and the width it logs is the codec-INDEPENDENT `g1CompressedWidth` -
    which is the point: no choice of codec can move a G1 read off 48. -/
def widthKatCodec : G1Codec Nat where
  ofCompressed? := fun b => if b.size == 48 then some 1 else none
  toCompressed := fun _ => natToBytesLE 1 48
  toEip := fun _ => natToBytesLE 1 128
  ofEip? := fun _ => none

local instance fact17logw : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- D-P23 satisfiability, as a THEOREM: the condition is inhabited (an empty log
    satisfies it), and both verifier-path readers preserve it - the scalar reader for
    every field and the compressed-G1 reader for every codec. -/
theorem transcriptLogWidths_witness (bytes : Bytes) :
    Transcript.LogWidths (Transcript.initFromBytes bytes) ∧
      PresWidths (tmRead (hashableFr (p := 17))) ∧
      PresWidths (tmRead (hashableG1 widthKatCodec)) ∧
      PresWidths (tmReadN (hashableFr (p := 17)) 3) :=
  ⟨Transcript.LogWidths.initFromBytes bytes,
   PresWidths.read (hashableFr (p := 17)) hashableFr_allowed,
   PresWidths.read (hashableG1 widthKatCodec) (hashableG1_allowed widthKatCodec),
   PresWidths.readN (hashableFr (p := 17)) hashableFr_allowed 3⟩

/-- D-P23 satisfiability, computed: real reads of real buffers log exactly the widths the
    decoder dispatches on, in read order, and the cursor advances by the same amounts. The
    last conjunct is the falsification, computed: the u32 reader logs 4, which is neither. -/
def transcriptLogWidthsKats_ok : Bool :=
  (match (Transcript.initFromBytes (frToRepr (p := 17) (5 : Fr 17))).read
        (hashableFr (p := 17)) with
   | .ok (_, t) => t.log.toList.map (fun r => r.1) == [32] && t.pos == 32
   | .error _ => false) &&
  (match (Transcript.initFromBytes (natToBytesLE 1 48)).read (hashableG1 widthKatCodec) with
   | .ok (_, t) => t.log.toList.map (fun r => r.1) == [g1CompressedWidth] &&
       t.pos == g1CompressedWidth
   | .error _ => false) &&
  (let buf := frToRepr (p := 17) (5 : Fr 17) ++ natToBytesLE 1 48
   match ((Transcript.initFromBytes buf).read (hashableFr (p := 17)) >>=
          fun p => p.2.read (hashableG1 widthKatCodec)) with
   | .ok (_, t) =>
       t.log.toList.map (fun r => r.1) == [32, g1CompressedWidth] &&
         t.pos == 32 + g1CompressedWidth &&
         (List.mapM (fun rec =>
             if rec.1 == g1CompressedWidth then some 1
             else if rec.1 == 32 then some 2 else none) t.log.toList).isSome
   | .error _ => false) &&
  (match (Transcript.initFromBytes (natToBytesLE 7 4)).read hashableU32 with
   | .ok (_, t) =>
       t.log.toList.map (fun r => r.1) == [hashableU32.width] &&
         (List.mapM (fun rec =>
             if rec.1 == g1CompressedWidth then some 1
             else if rec.1 == 32 then some 2 else none) t.log.toList) == none
   | .error _ => false) &&
  (g1CompressedWidth == 48) && (hashableU32.width == 4)

#eval transcriptLogWidthsKats_ok   -- expect true


/-! ### P-CODEC-B step 1: the fold lemma - `decodeRust`'s messages re-encode to the log

    The last missing link between `transcript_log_concat` and
    `verifyNative_iff_msgs_codec`. `decodeRust` (Exec/Native.lean) turns the transcript
    log into messages by a per-record `List.mapM`; `prepareMsgs` turns messages back
    into bytes by a `foldl` of `ByteArray.append` over `msgWire`; `Transcript.recorded`
    is a `foldl` over `Array.toList` inside `Transcript.recordedList`. Three different
    folds, and no lemma said the round trip is the identity. It is, record by record, and
    each record's half comes from a different source: the Fr arm from
    `Midfall.Assumptions.frOfRepr_frToRepr_bytes` (P-CODEC-A item 1), the G1 arm from the
    codec's own `compressedRoundtrip` law (the ONLY codec law the statement carries), and
    the dead third arm from `widthDispatch_exhaustive` (P-CODEC-A item 2).

    THE WHNF LANDMINE APPLIES AND WAS AVOIDED, not by luck: nothing below whnfs a
    `natToBytesLowFirst` with a symbolic argument. `Transcript.recorded_eq_fold` is proved
    by pushing the equality down to `List UInt8` (`bytes_eq_of_toList`) and doing one
    induction over the log with the accumulator as a VARIABLE - the same discipline
    `Transcript.Tiled.replaceState` records. The exhibits at the end of the section build
    transcripts by hand rather than by running a read whose `squeeze` would have to be
    normalised. -/

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

private theorem bytes_eq_of_toList {x y : Bytes} (h : x.data.toList = y.data.toList) : x = y := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  exact h

private theorem foldl_shift (l : List Bytes) (init : List UInt8) :
    l.foldl (init := init) (fun xs b => xs ++ b.data.toList)
      = init ++ l.foldl (init := ([] : List UInt8)) (fun xs b => xs ++ b.data.toList) := by
  induction l generalizing init with
  | nil => simp
  | cons b t ih =>
      rw [List.foldl_cons, List.foldl_cons, List.nil_append, ih, ih (b.data.toList),
        List.append_assoc]

private theorem foldl_append_data_toList (l : List Bytes) (acc : Bytes) :
    (l.foldl (init := acc) (fun x b => ByteArray.append x b)).data.toList
      = acc.data.toList ++ l.foldl (init := ([] : List UInt8)) (fun xs b => xs ++ b.data.toList) := by
  induction l generalizing acc with
  | nil => simp
  | cons b t ih =>
      rw [List.foldl_cons, ih,
        show (ByteArray.append acc b).data.toList = acc.data.toList ++ b.data.toList from rfl,
        List.foldl_cons, List.nil_append]
      rw [foldl_shift t (b.data.toList), List.append_assoc]

/-- `recorded`, spelled as the `ByteArray.append` fold of the log's reprs - the shape
    `prepareMsgs` builds and the shape `decodeRust` has to reproduce. The two definitions
    are written with different folds (`List.foldl` over `List UInt8` in `recordedList`,
    `ByteArray.append` over `Bytes` at the call site), which is why this was needed. -/
theorem Transcript.recorded_eq_fold (t : Transcript) :
    (t.log.toList.map Prod.snd).foldl (init := Bytes.empty)
        (fun x b => ByteArray.append x b) = t.recorded := by
  apply bytes_eq_of_toList
  show ((t.log.toList.map Prod.snd).foldl (init := Bytes.empty)
      (fun x b => ByteArray.append x b)).data.toList = t.recordedList
  rw [foldl_append_data_toList, Transcript.recordedList]
  have h0 : (Bytes.empty : Bytes).data.toList = ([] : List UInt8) := rfl
  rw [h0, List.nil_append, List.foldl_map]

/-- **The fold shape.** A successful `List.mapM` whose per-element decoder round trips
    against a re-encoder recovers the source list's second components in order. This is
    the step that was stated nowhere: it is what turns "the log tiles the consumed prefix"
    into "the decoded messages re-encode to the consumed prefix". -/
theorem list_mapM_roundtrip_snd {β : Type} (f : (Nat × Bytes) → Option β) (wire : β → Bytes)
    (l : List (Nat × Bytes)) (ms : List β) (h : l.mapM f = some ms)
    (hrt : ∀ rec ∈ l, ∀ a, f rec = some a → wire a = rec.2) :
    ms.map wire = l.map Prod.snd := by
  induction l generalizing ms with
  | nil => cases h; rfl
  | cons a t ih =>
      cases hfa : f a with
      | none => rw [List.mapM_cons, hfa] at h; simp at h
      | some v =>
          cases hmt : t.mapM f with
          | none => rw [List.mapM_cons, hfa, hmt] at h; simp at h
          | some vs =>
              rw [List.mapM_cons, hfa, hmt] at h
              simp at h
              rw [← h]
              show wire v :: vs.map wire = a.2 :: t.map Prod.snd
              rw [ih vs hmt (fun rec hrec y hy => hrt rec (List.mem_cons_of_mem a hrec) y hy),
                hrt a List.mem_cons_self v hfa]

/-- The per-record dispatch `decodeRust` runs over the transcript log, named so that it
    can be spoken about. Its three arms are exactly `decodeRust`'s. -/
def logDispatch (E : VerifierEnv p G₁ G₂ Gₜ) : (Nat × Bytes) → Option (Msg (Fr p) G₁) :=
  fun rec =>
    if rec.1 == (hashableG1 E.g1).width then (E.g1.ofCompressed? rec.2).map Msg.g1
    else if rec.1 == (hashableFr (p := p)).width then (frOfRepr? (p := p) rec.2).map Msg.fr
    else none

/-- `decodeRust` IS the log's `mapM` over `logDispatch`, whenever the run succeeds and
    the cursor has eaten the whole stream. -/
theorem decodeRust_eq_mapM (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (t : Transcript)
    (hrun : (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
        (Transcript.initFromBytes π) = .ok (d, t))
    (hpos : t.pos = t.buffer.size) :
    decodeRust (Gₜ := Gₜ) E F vk inst π = t.log.toList.mapM (logDispatch E) := by
  unfold decodeRust
  dsimp only []
  rw [hrun]
  simp only [Except.toOption, Bind.bind, Option.bind_some]
  rw [if_neg (by omega : ¬ (t.buffer.size ≠ t.pos))]
  rfl

/-- **Per-record round trip.** A log record whose width the decoder dispatches on decodes
    to a message whose wire encoding is the record's own bytes. Two arms, two sources:
    `compressedRoundtrip` for G1, `frOfRepr_frToRepr_bytes` for Fr; the third arm is dead
    by `widthDispatch_exhaustive`, which is what the `hw` hypothesis buys. -/
theorem msgWire_logDispatch (E : VerifierEnv p G₁ G₂ Gₜ) (hc : E.g1.compressedRoundtrip)
    (rec : Nat × Bytes) (m : Msg (Fr p) G₁)
    (hw : rec.1 = 32 ∨ rec.1 = g1CompressedWidth)
    (h : logDispatch E rec = some m) : msgWire E m = rec.2 := by
  have htwo : logDispatch E rec =
      (if rec.1 == (hashableG1 E.g1).width then (E.g1.ofCompressed? rec.2).map Msg.g1
        else (frOfRepr? (p := p) rec.2).map Msg.fr) := by
    unfold logDispatch
    rw [hashableG1_width, hashableFr_width]
    exact widthDispatch_exhaustive (fun b => (E.g1.ofCompressed? b).map Msg.g1)
      (fun b => (frOfRepr? (p := p) b).map Msg.fr) rec hw
  rw [htwo] at h
  by_cases hg1 : rec.1 == (hashableG1 E.g1).width
  · rw [if_pos hg1] at h
    cases hP : E.g1.ofCompressed? rec.2 with
    | none => rw [hP, Option.map_none] at h; cases h
    | some P =>
        rw [hP, Option.map_some] at h
        obtain rfl := Option.some.inj h
        show E.g1.toCompressed P = rec.2
        exact hc rec.2 P hP
  · rw [if_neg hg1] at h
    cases hfr : frOfRepr? (p := p) rec.2 with
    | none => rw [hfr, Option.map_none] at h; cases h
    | some x =>
        rw [hfr, Option.map_some] at h
        obtain rfl := Option.some.inj h
        show Midfall.frToRepr x = rec.2
        exact Midfall.Assumptions.frOfRepr_frToRepr_bytes hfr

/-- **THE FOLD LEMMA (P-CODEC-B step 1).** If the log's per-record decode round trips
    against the wire encoder, then re-encoding the decoded messages and concatenating is
    exactly the recorded prefix. Stated with an abstract `wire`/`dispatch` pair so that
    the exhibit below needs no pairing model (D-P17): `decodeRust_recorded` is the
    `decodeRust` instance. -/
theorem recorded_fold_of_mapM (t : Transcript) {α : Type} (wire : α → Bytes)
    (dispatch : (Nat × Bytes) → Option α) (ms : List α)
    (hmap : t.log.toList.mapM dispatch = some ms)
    (hround : ∀ rec ∈ t.log.toList, ∀ a, dispatch rec = some a → wire a = rec.2) :
    ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (wire m))
      = t.recorded := by
  have hmap' : ms.map wire = t.log.toList.map Prod.snd :=
    list_mapM_roundtrip_snd dispatch wire t.log.toList ms hmap hround
  have hfold : ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (wire m))
      = (ms.map wire).foldl (init := Bytes.empty) (fun x b => ByteArray.append x b) := by
    rw [← List.foldl_map]
  rw [hfold, hmap']
  exact Transcript.recorded_eq_fold t

/-- **Step 1 in the shape the codec lemma consumes.** `decodeRust` returns messages whose
    re-serialisation is the recorded prefix of the stream - the missing link named by
    P-CODEC-A. Chain it with `transcript_log_concat` and `Transcript.Tiled` to get
    "= `pi.extract 0 t.pos`", and with `assertEmpty` to get "= `pi`". -/
theorem decodeRust_recorded (E : VerifierEnv p G₁ G₂ Gₜ) (hc : E.g1.compressedRoundtrip)
    (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (t : Transcript)
    (hrun : (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
        (Transcript.initFromBytes π) = .ok (d, t))
    (hpos : t.pos = t.buffer.size) (hw : Transcript.LogWidths t)
    (ms : List (Msg (Fr p) G₁)) (hdec : decodeRust (Gₜ := Gₜ) E F vk inst π = some ms) :
    ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (msgWire E m))
      = t.recorded := by
  have hmap : t.log.toList.mapM (logDispatch E) = some ms := by
    rw [← decodeRust_eq_mapM (p := p) E F vk inst π d t hrun hpos]
    exact hdec
  refine recorded_fold_of_mapM t (msgWire E) (logDispatch E) ms hmap ?_
  intro rec hmem a ha
  exact msgWire_logDispatch (p := p) E hc rec a (hw rec hmem) ha

/-! #### D-P23: the fold lemma's two halves -/

/-- Satisfiability, as a THEOREM: the fold lemma's hypotheses are inhabited, by a
    transcript of exactly the shape a real read leaves - two records, the two allowed
    widths, a cursor that has eaten the whole buffer - and the conclusion is a fact about
    a specific byte string, not a vacuity. -/
theorem fold_lemma_witness :
    ∃ (t : Transcript) (ms : List Bytes),
      t.log.toList.mapM (fun rec => some rec.2) = some ms ∧
        ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc m) = t.recorded ∧
        t.LogWidths ∧ t.Tiled ∧
        t.recorded = frToRepr (p := 17) (5 : Fr 17) ++ natToBytesLE 1 48 := by
  refine ⟨Transcript.mk Bytes.empty
      (frToRepr (p := 17) (5 : Fr 17) ++ natToBytesLE 1 48)
      (32 + g1CompressedWidth) keccak256
      #[(32, frToRepr (p := 17) (5 : Fr 17)), (g1CompressedWidth, natToBytesLE 1 48)],
      [frToRepr (p := 17) (5 : Fr 17), natToBytesLE 1 48], rfl, rfl, ?_, ?_, rfl⟩
  · intro rec hmem
    have hlist : ((#[(32, frToRepr (p := 17) (5 : Fr 17)),
        (g1CompressedWidth, natToBytesLE 1 48)] : Array (Nat × Bytes)).toList)
        = [(32, frToRepr (p := 17) (5 : Fr 17)), (g1CompressedWidth, natToBytesLE 1 48)] := rfl
    rw [hlist] at hmem
    simp at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · show ((#[(32, frToRepr (p := 17) (5 : Fr 17)),
        (g1CompressedWidth, natToBytesLE 1 48)] : Array (Nat × Bytes)).toList).foldl
        (init := []) (fun acc r => acc ++ r.2.data.toList)
      = (ByteArray.append (frToRepr (p := 17) (5 : Fr 17)) (natToBytesLE 1 48)).data.toList
    rfl

/-- Falsifiability, as a THEOREM: the per-record round trip is what makes the fold lemma
    true, and it is exactly what `compressedRoundtrip` supplies. Here is a log whose one
    record is a NON-canonical scalar repr: the dispatch succeeds (the width is allowed),
    so `mapM` is `some ms`, but the re-encoding is the canonical repr of the decoded
    value and not the bytes that were read. A codec that maps two byte strings to the
    same point breaks the fold lemma, which is why the codec law is a hypothesis of
    `verifyNative_iff_msgs_codec` and not decoration. -/
theorem fold_lemma_refutesNonRoundtrip :
    ∃ (t : Transcript) (ms : List Nat) (wire : Nat → Bytes)
        (dispatch : (Nat × Bytes) → Option Nat),
      t.log.toList.mapM dispatch = some ms ∧
        (∀ rec ∈ t.log.toList, rec.1 = 32 ∨ rec.1 = g1CompressedWidth) ∧
        ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (wire m))
          ≠ t.recorded := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 17 32) 32 keccak256
      #[(32, natToBytesLE 17 32)], [0], (fun _ => frToRepr (p := 17) (5 : Fr 17)),
      (fun _ => some 0), rfl, ?_, by decide⟩
  · intro rec hmem
    have hlist : ((#[ (32, natToBytesLE 17 32) ] : Array (Nat × Bytes)).toList)
        = [(32, natToBytesLE 17 32)] := rfl
    rw [hlist] at hmem
    simp at hmem
    rcases hmem with rfl
    exact Or.inl rfl

/-- Falsifiability, as a THEOREM: without the width condition there is no message list at
    all. A log carrying one record of the width a real `hashableU32` read produces makes
    the dispatch's third arm fire, so the `mapM` is `none` and the fold lemma's hypothesis
    is uninhabited - which is exactly how `verifyNative` could accept while `decodeRust`
    is `none`. Compare `widthDispatch_refutesOtherWidth`, which refutes the same arm at
    the level of one record rather than of the whole fold. -/
theorem fold_lemma_refutesOtherWidth :
    ∃ (t : Transcript), ¬ ∃ (ms : List Bytes),
        t.log.toList.mapM (fun rec =>
          if rec.1 == g1CompressedWidth then some rec.2
          else if rec.1 == 32 then some rec.2 else none) = some ms := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 7 4) 4 keccak256
      #[(hashableU32.width, natToBytesLE 7 4)], ?_⟩
  intro ⟨ms, h⟩
  have hlist : ((#[ (hashableU32.width, natToBytesLE 7 4) ] : Array (Nat × Bytes)).toList)
      = [(hashableU32.width, natToBytesLE 7 4)] := rfl
  rw [hlist] at h
  simp at h
  cases h

/-- Satisfiability, computed: two REAL reads of a real buffer, in order, through the two
    verifier-path hashables; the fold of the log's reprs is the recorded prefix, the
    recorded prefix is the whole buffer, and the cursor agrees. -/
def foldLemmaKat_ok : Bool :=
  let buf := frToRepr (p := 17) (5 : Fr 17) ++ natToBytesLE 1 48
  match ((Transcript.initFromBytes buf).read (hashableFr (p := 17)) >>=
          fun q => q.2.read (hashableG1 widthKatCodec)) with
  | .ok (_, t) =>
      t.log.toList.map (fun r => r.1) == [32, g1CompressedWidth] &&
        (t.log.toList.mapM (fun rec => some rec.2)) == some (t.log.toList.map Prod.snd) &&
        (t.log.toList.map Prod.snd).foldl (init := Bytes.empty)
            (fun x b => ByteArray.append x b) == t.recorded &&
        t.recorded == buf && t.pos == buf.size && t.recorded == t.buffer.extract 0 t.pos
  | .error _ => false

#eval foldLemmaKat_ok   -- expect true


/-! ### P-CODEC-B steps 2 and 3: the transfer lemmas, the two do-block walks, the pipeline

    P-CODEC-A's warning, honoured: **`StateT.set` is not `Pres`-closed and not
    `PresWidths`-closed.** `set` installs an ARBITRARY transcript, which need not be
    tiled and may carry any log, so no `Pres.set`/`PresWidths.set` closure lemma is
    stated here - `set_not_Pres` and `set_not_PresWidths` refute the claim as a theorem.
    What `verifyAlgebraicConstraints` needs is narrower: the transcript it installs is the
    one `pcs.multiPrepare` produced FROM the state it was given, which is the state the
    preceding `StateT.get` read.

    That is discharged by the pointwise-run method P-LOGCONCAT characterised: case-split
    on `m.run s` where the GOAL carries the scrutinee. The hypothesis form does not: after
    `unfold`, the do-block's own `let t ← StateT.get` binder shadows `s`, so
    `cases h : m.run s` finds no occurrence to abstract and dependent elimination fails.
    `Pres.congr_of_run_eq` / `PresWidths.congr_of_run_eq` are the transfer principles that
    make the method reusable; the walks below use them where the term is a def and the
    inline case-split where it is not.

    REPORTED COST, since the brief asked for honesty about it: the two `parseTrace` walks
    are ~95 lines each, not the 5-15 P-CODEC-A estimated. Nothing about them was hard -
    every construct did have its closure lemma - but `parseTrace` has 20 monadic steps over
    nested `for` loops (which desugar to `forIn` over BOTH List and Array, so each needs
    the right variant), and the `refine` holes for `listForIn`/`listFoldlM` need `intro`
    without `dsimp` (the beta redex is already reduced) while the fold bodies need the
    opposite. `verifyAlgebraicConstraints` is ~40 lines each, as estimated.

    ONE NEW OBLIGATION, found here: `Pcs` is a RECORD whose `multiPrepare` field is an
    arbitrary function, so `Pres (pcs.multiPrepare queries)` is not provable for a general
    `pcs`. Both walks therefore carry `hpcs : ∀ queries, Pres (pcs.multiPrepare queries)`
    (resp. `PresWidths`), discharged at the call site by `pres_multiPrepare` for
    `Pcs.kzg` - which is the only instantiation `verifyNative` uses. -/


/-- The single-hypothesis guard form for the widths predicate: the twin of
    `Pres.guardWhen`. -/
theorem PresWidths.guardWhen {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresWidths k) :
    PresWidths (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  PresWidths.ite (α := β) (c := c)
    (PresWidths.bind (PresWidths.lift (Except.error f)) (fun _ => hk)) hk

/-- Pointwise equality of runs transfers `Pres`. -/
theorem Pres.congr_of_run_eq {α : Type} {m n : TranscriptM α}
    (h : ∀ s, m.run s = n.run s) (hm : Pres m) : Pres n := by
  intro t t' a ht hrun
  exact hm t t' a ht ((h t).trans hrun)

/-- Pointwise equality of runs transfers `PresWidths`. -/
theorem PresWidths.congr_of_run_eq {α : Type} {m n : TranscriptM α}
    (h : ∀ s, m.run s = n.run s) (hm : PresWidths m) : PresWidths n := by
  intro t t' a ht hrun
  exact hm t t' a ht ((h t).trans hrun)

/-- D-P23 falsification, as a THEOREM: `Pres` is NOT closed under `StateT.set`. -/
theorem set_not_Pres : ∃ (x : Transcript), ¬ Pres (StateT.set x) := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 7 4) 3 keccak256 #[], ?_⟩
  intro h
  have h1 := (h (Transcript.initFromBytes Bytes.empty) _ ()
    (Transcript.tiled_initFromBytes _) rfl).1
  have hn : ¬ Transcript.Tiled (Transcript.mk Bytes.empty (natToBytesLE 7 4) 3 keccak256 #[]) := by
    show ¬ ([] : List UInt8) = (natToBytesLE 7 4).data.toList.extract 0 3
    decide
  exact absurd h1 hn

/-- D-P23 falsification, as a THEOREM: `PresWidths` is NOT closed under `StateT.set`. -/
theorem set_not_PresWidths : ∃ (x : Transcript), ¬ PresWidths (StateT.set x) := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 7 4) 4 keccak256
      #[(hashableU32.width, natToBytesLE 7 4)], ?_⟩
  intro h
  have h1 := h (Transcript.initFromBytes Bytes.empty) _ ()
    (Transcript.LogWidths.initFromBytes _) rfl
  exact hashableU32_not_allowed (h1 (hashableU32.width, natToBytesLE 7 4) (by simp))

theorem presWidths_parseTrace     (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) :
    PresWidths (parseTrace g1 feat vk committed₀ inst) := by
  unfold parseTrace
  apply PresWidths.guardWhen
  · apply PresWidths.guardWhen
    · apply PresWidths.guardWhen
      · refine PresWidths.bind (PresWidths.hashInto vk) (fun _ => ?_)
        -- absorb the committed instance commitments
        refine PresWidths.bind ?_ (fun _ => ?_)
        · apply PresWidths.listForIn
          · intro row __s
            refine PresWidths.bind ?_ (fun _ => PresWidths.pure _)
            · apply PresWidths.arrayForIn
              · intro com __s
                exact PresWidths.bind (PresWidths.common (hashableG1 g1) com) (fun _ => PresWidths.pure _)
        -- absorb each instance column's length then its values
        · refine PresWidths.bind ?_ (fun _ => ?_)
          · apply PresWidths.listForIn
            · intro row __s
              refine PresWidths.bind ?_ (fun _ => PresWidths.pure _)
              · apply PresWidths.arrayForIn
                · intro col __s
                  refine PresWidths.bind (PresWidths.common hashableFr (Nat.cast col.size)) (fun _ => ?_)
                  refine PresWidths.bind ?_ (fun _ => PresWidths.pure _)
                  · apply PresWidths.arrayForIn
                    · intro v __s
                      exact PresWidths.bind (PresWidths.common hashableFr v) (fun _ => PresWidths.pure _)
          -- the phase loop
          · refine PresWidths.bind ?_ (fun x => ?_)
            · apply PresWidths.listFoldlM
              · intro st ph
                dsimp only []
                refine PresWidths.bind ?_ (fun adv => ?_)
                · apply PresWidths.listFoldlM
                  · intro acc k
                    refine PresWidths.bind (PresWidths.readN (hashableG1 g1) (hashableG1_allowed g1) _) (fun _ => PresWidths.pure _)
                · refine PresWidths.bind ?_ (fun chals => PresWidths.pure _)
                  · apply PresWidths.listFoldlM
                    · intro acc e
                      apply PresWidths.ite
                      · refine PresWidths.bind PresWidths.squeezeChallenge (fun _ => PresWidths.pure _)
                      · exact PresWidths.pure _
            · cases x with
              | mk advPairs chalPairs =>
                refine PresWidths.bind ?_ (fun adviceCommitments => ?_)
                · apply PresWidths.listFoldlM
                  · intro acc pairs
                    refine PresWidths.bind
                        (PresWidths.lift (scatterIndexed vk.cs.numAdviceColumns pairs
                          "proofs/src/plonk/verifier.rs:118")) (fun _ => PresWidths.pure _)
                · refine PresWidths.bind
                      (PresWidths.lift (scatterIndexed vk.cs.numChallenges chalPairs
                        "proofs/src/plonk/verifier.rs:134")) (fun challenges => ?_)
                  refine PresWidths.bind PresWidths.squeezeChallenge (fun theta => ?_)
                  refine PresWidths.bind ?_ (fun lookupMultiplicities => ?_)
                  · apply PresWidths.listFoldlM
                    · intro acc x
                      refine PresWidths.bind ?_ (fun row => PresWidths.pure _)
                      · apply PresWidths.listFoldlM
                        · intro acc' l
                          refine PresWidths.bind (PresWidths.lift (l.chunkByDegree vk.csDegree))
                            (fun chunked => ?_)
                          refine PresWidths.bind (PresWidths.readMultiplicities chunked (hashableG1 g1) (hashableG1_allowed g1))
                            (fun m => PresWidths.pure _)
                  refine PresWidths.bind PresWidths.squeezeChallenge (fun beta => ?_)
                  refine PresWidths.bind PresWidths.squeezeChallenge (fun gamma => ?_)
                  refine PresWidths.bind ?_ (fun permutations => ?_)
                  · apply PresWidths.listFoldlM
                    · intro acc x
                      refine PresWidths.bind
                          (PresWidths.permReadProductCommitments vk.cs.permutation vk.csDegree (hashableG1 g1) (hashableG1_allowed g1)) (fun _ => PresWidths.pure _)
                  refine PresWidths.bind ?_ (fun lookups => ?_)
                  · apply PresWidths.listFoldlM
                    · intro acc row
                      refine PresWidths.bind ?_ (fun out => PresWidths.pure _)
                      · apply PresWidths.listFoldlM
                        · intro acc' x
                          cases x with
                          | mk m chunked =>
                            refine PresWidths.bind
                                (PresWidths.readCommitment m chunked.numChunks (hashableG1 g1) (hashableG1_allowed g1))
                                (fun _ => PresWidths.pure _)
                  refine PresWidths.bind PresWidths.squeezeChallenge (fun trashChallenge => ?_)
                  refine PresWidths.bind ?_ (fun trashcans => ?_)
                  · apply PresWidths.listFoldlM
                    · intro acc x
                      refine PresWidths.bind ?_ (fun row => PresWidths.pure _)
                      · apply PresWidths.listFoldlM
                        · intro acc' t
                          refine PresWidths.bind (PresWidths.trashReadCommitted t (hashableG1 g1) (hashableG1_allowed g1))
                            (fun _ => PresWidths.pure _)
                  refine PresWidths.bind PresWidths.squeezeChallenge (fun y => ?_)
                  exact PresWidths.pure _

theorem pres_parseTrace     (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) :
    Pres (parseTrace g1 feat vk committed₀ inst) := by
  unfold parseTrace
  apply Pres.guardWhen
  · apply Pres.guardWhen
    · apply Pres.guardWhen
      · refine Pres.bind (pres_hashInto vk) (fun _ => ?_)
        -- absorb the committed instance commitments
        refine Pres.bind ?_ (fun _ => ?_)
        · apply Pres.listForIn
          · intro row __s
            refine Pres.bind ?_ (fun _ => Pres.pure _)
            · apply Pres.arrayForIn
              · intro com __s
                exact Pres.bind (Pres.common (hashableG1 g1) com) (fun _ => Pres.pure _)
        -- absorb each instance column's length then its values
        · refine Pres.bind ?_ (fun _ => ?_)
          · apply Pres.listForIn
            · intro row __s
              refine Pres.bind ?_ (fun _ => Pres.pure _)
              · apply Pres.arrayForIn
                · intro col __s
                  refine Pres.bind (Pres.common hashableFr (Nat.cast col.size)) (fun _ => ?_)
                  refine Pres.bind ?_ (fun _ => Pres.pure _)
                  · apply Pres.arrayForIn
                    · intro v __s
                      exact Pres.bind (Pres.common hashableFr v) (fun _ => Pres.pure _)
          -- the phase loop
          · refine Pres.bind ?_ (fun x => ?_)
            · apply Pres.listFoldlM
              · intro st ph
                dsimp only []
                refine Pres.bind ?_ (fun adv => ?_)
                · apply Pres.listFoldlM
                  · intro acc k
                    refine Pres.bind (Pres.readN (hashableG1 g1) _) (fun _ => Pres.pure _)
                · refine Pres.bind ?_ (fun chals => Pres.pure _)
                  · apply Pres.listFoldlM
                    · intro acc e
                      apply Pres.ite
                      · refine Pres.bind Pres.squeezeChallenge (fun _ => Pres.pure _)
                      · exact Pres.pure _
            · cases x with
              | mk advPairs chalPairs =>
                refine Pres.bind ?_ (fun adviceCommitments => ?_)
                · apply Pres.listFoldlM
                  · intro acc pairs
                    refine Pres.bind
                        (Pres.lift (scatterIndexed vk.cs.numAdviceColumns pairs
                          "proofs/src/plonk/verifier.rs:118")) (fun _ => Pres.pure _)
                · refine Pres.bind
                      (Pres.lift (scatterIndexed vk.cs.numChallenges chalPairs
                        "proofs/src/plonk/verifier.rs:134")) (fun challenges => ?_)
                  refine Pres.bind Pres.squeezeChallenge (fun theta => ?_)
                  refine Pres.bind ?_ (fun lookupMultiplicities => ?_)
                  · apply Pres.listFoldlM
                    · intro acc x
                      refine Pres.bind ?_ (fun row => Pres.pure _)
                      · apply Pres.listFoldlM
                        · intro acc' l
                          refine Pres.bind (Pres.lift (l.chunkByDegree vk.csDegree))
                            (fun chunked => ?_)
                          refine Pres.bind (pres_readMultiplicities chunked (hashableG1 g1))
                            (fun m => Pres.pure _)
                  refine Pres.bind Pres.squeezeChallenge (fun beta => ?_)
                  refine Pres.bind Pres.squeezeChallenge (fun gamma => ?_)
                  refine Pres.bind ?_ (fun permutations => ?_)
                  · apply Pres.listFoldlM
                    · intro acc x
                      refine Pres.bind
                          (pres_permReadProductCommitments vk.cs.permutation vk.csDegree
                            (hashableG1 g1)) (fun _ => Pres.pure _)
                  refine Pres.bind ?_ (fun lookups => ?_)
                  · apply Pres.listFoldlM
                    · intro acc row
                      refine Pres.bind ?_ (fun out => Pres.pure _)
                      · apply Pres.listFoldlM
                        · intro acc' x
                          cases x with
                          | mk m chunked =>
                            refine Pres.bind
                                (pres_readCommitment m chunked.numChunks (hashableG1 g1))
                                (fun _ => Pres.pure _)
                  refine Pres.bind Pres.squeezeChallenge (fun trashChallenge => ?_)
                  refine Pres.bind ?_ (fun trashcans => ?_)
                  · apply Pres.listFoldlM
                    · intro acc x
                      refine Pres.bind ?_ (fun row => Pres.pure _)
                      · apply Pres.listFoldlM
                        · intro acc' t
                          refine Pres.bind (pres_trashReadCommitted t (hashableG1 g1))
                            (fun _ => Pres.pure _)
                  refine Pres.bind Pres.squeezeChallenge (fun y => ?_)
                  exact Pres.pure _

theorem presWidths_verifyAlgebraicConstraints     (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁))
    (instances : Array (Array (Array (Fr p))))
    (hpcs : ∀ queries, PresWidths (pcs.multiPrepare queries)) :
    PresWidths (Verifier.verifyAlgebraicConstraints (p := p) g1 delta feat pcs vk trace
      committedInstances instances) := by
  unfold Verifier.verifyAlgebraicConstraints
  apply PresWidths.guardWhen
  · refine PresWidths.bind ?_ (fun alg => ?_)
    · apply PresWidths.readAlgebra
    · refine PresWidths.bind ?_ (fun queries => ?_)
      · apply PresWidths.lift
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



theorem pres_verifyAlgebraicConstraints     (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁))
    (instances : Array (Array (Array (Fr p))))
    (hpcs : ∀ queries, Pres (pcs.multiPrepare queries)) :
    Pres (Verifier.verifyAlgebraicConstraints (p := p) g1 delta feat pcs vk trace
      committedInstances instances) := by
  unfold Verifier.verifyAlgebraicConstraints
  apply Pres.guardWhen
  · refine Pres.bind ?_ (fun alg => ?_)
    · apply pres_readAlgebra
    · refine Pres.bind ?_ (fun queries => ?_)
      · apply Pres.lift
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

/-- **The whole §9.2 read schedule preserves the tiling.** -/
theorem pres_prepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (committed : List (List G₁))
    (inst : List (List (List (Fr p)))) :
    Pres (prepare (Gₜ := Gₜ) E F vk committed inst) := by
  unfold prepare prepareWith Verifier.prepare
  refine Pres.bind ?_ (fun trace => ?_)
  · apply pres_parseTrace
  · refine pres_verifyAlgebraicConstraints E.g1 E.delta F
        (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime) vk trace _ _ ?_
    intro queries
    exact pres_multiPrepare E.g1 E.field F E.fewerPointSetsRuntime queries

/-- The same for the width condition. -/
theorem presWidths_prepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (committed : List (List G₁))
    (inst : List (List (List (Fr p)))) :
    PresWidths (prepare (Gₜ := Gₜ) E F vk committed inst) := by
  unfold prepare prepareWith Verifier.prepare
  refine PresWidths.bind ?_ (fun trace => ?_)
  · apply presWidths_parseTrace
  · refine presWidths_verifyAlgebraicConstraints E.g1 E.delta F
        (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime) vk trace _ _ ?_
    intro queries
    exact PresWidths.multiPrepare E.g1 E.field F E.fewerPointSetsRuntime queries


/-! ### P-CODEC-B step 4: how far it gets, and the sixth obstacle named as a theorem

    [THIS SECTION IS THE OBSTACLE, RECORDED AS A THEOREM - AND IT IS NOW CLOSED: see the
    P-CODEC-C section at the foot of this file, which adds `Hashable.Dispatchable`,
    `Transcript.LogDecoded` and the third walk, and discharges
    `Midfall.Lowering.verifyNative_iff_msgs_codec`.]

    Step 4 - discharging `Midfall.Lowering.verifyNative_iff_msgs_codec` - did NOT land.
    The reason is not any of the five obstacles the plan listed: it is a SIXTH, and it is
    recorded here as a theorem rather than as a comment, because that is the only form the
    next package will believe.

    Everything else the codec lemma needs is now proved: `pres_prepare` and
    `presWidths_prepare` give the tiling and the width condition for the transcript
    `verifyNative` leaves behind, `transcript_log_concat turns that into the consumed
    prefix, `decodeRust_recorded turns a successful decode into the same prefix, and
    `Transcript.initWithHash_keccak makes `prepareMsgs` and `verifyNative` execute one
    run rather than two. What is missing is the hypothesis of `decodeRust_recorded itself:
    that `decodeRust` returns `some ms` at all.

    `logWidths_not_logDecoded below is the gap: a transcript whose every logged width is
    one the dispatch reaches for, and whose dispatch is nevertheless `none`. So the two
    invariants the pipeline is proved to preserve do NOT imply `decodeRust = some ms`, and
    no chaining of the existing lemmas can produce it. What would: a third pipeline
    predicate alongside `Pres` and `PresWidths`, carrying not the WIDTH a read logged but
    the `Hashable` that logged it - because for `hashableFr` and `hashableG1` the reading
    function IS the decoder the dispatch reaches for (`hashableFr_readRepr_eq`,
    `hashableG1_readRepr_eq`, both `rfl`), and for any other hashable of the same width it
    need not be. That is a third copy of walks that are now mechanical, not a new idea.
-/
/-- **The sixth obstacle, as a theorem, not as a comment.** `Transcript.LogWidths` - the
    strongest thing the pipeline is currently proved to log - does NOT imply that the
    decoder's per-record dispatch succeeds. Here is a transcript whose every logged width
    is one the dispatch reaches for, and whose dispatch is nevertheless `none`: one record
    of width 32 carrying a NON-canonical scalar repr. The width test passes; the decoder
    the width selects rejects the bytes. So `decodeRust = some ms` does not follow from
    the tiling and the width condition, and closing `verifyNative_iff_msgs_codec` needs a
    third pipeline invariant: not which WIDTH a read logged, but which `Hashable` logged
    it - because for `hashableFr` and `hashableG1` the reading function IS the decoder the
    dispatch reaches for (`Exec/Transcript.lean:59`, `:69`), and for anything else of the
    same width it need not be. -/
theorem logWidths_not_logDecoded :
    ∃ (t : Transcript), Transcript.LogWidths t ∧
      (t.log.toList.mapM (fun rec =>
          if rec.1 == g1CompressedWidth then (none : Option (Fr 17))
          else if rec.1 == 32 then frOfRepr? (p := 17) rec.2 else none) = none) := by
  refine ⟨Transcript.mk Bytes.empty (natToBytesLE 17 32) 32 keccak256
      #[(32, natToBytesLE 17 32)], ?_, ?_⟩
  · intro rec hmem
    have hlist : ((#[ (32, natToBytesLE 17 32) ] : Array (Nat × Bytes)).toList)
        = [(32, natToBytesLE 17 32)] := rfl
    rw [hlist] at hmem
    simp at hmem
    rcases hmem with rfl
    exact Or.inl rfl
  · have hlist : ((#[ (32, natToBytesLE 17 32) ] : Array (Nat × Bytes)).toList)
        = [(32, natToBytesLE 17 32)] := rfl
    rw [hlist]
    have hnone : frOfRepr? (p := 17) (natToBytesLE 17 32) = none := by decide
    show (if (32 : Nat) == g1CompressedWidth then (none : Option (Fr 17))
          else if (32 : Nat) == 32 then frOfRepr? (p := 17) (natToBytesLE 17 32)
          else none).bind (fun a => some [a]) = none
    rw [hnone]
    rfl


/-! ### P-CODEC-C step 1: the sixth obstacle CLOSED - `Hashable.Dispatchable`,
    `Transcript.LogDecoded`, and the third pipeline walk

    P-CODEC-B named the sixth obstacle as a theorem (`logWidths_not_logDecoded` above):
    the log records a read's WIDTH and BYTES but not WHICH `Hashable` produced them,
    while `decodeRust` dispatches BY WIDTH. `Transcript.LogWidths` buys that the third
    dispatch arm is unreachable; it does NOT buy that the arm reached ACCEPTS the bytes.
    So `decodeRust = some ms` - the hypothesis of `decodeRust_recorded`, and therefore of
    the whole codec lemma - does not follow from the two invariants the pipeline is
    already proved to preserve.

    THE FIX, exactly as characterised: a third predicate alongside `Pres` and
    `PresWidths`, carrying not which WIDTH a read logged but which `Hashable` logged it.
    `Hashable.Dispatchable E h` says: whatever bytes the own reader of `h` accepts, the
    dispatch `decodeRust` runs for `E` accepts them too at the width of `h`. For
    `hashableFr` and `hashableG1 E.g1` that is true DEFINITIONALLY - the reading function
    IS the decoder the dispatch reaches for (`hashableFr_readRepr_eq`,
    `hashableG1_readRepr_eq`, both `rfl`) - which is exactly why those two, and only
    those two, are the verifier path's readers.

    THE TRAP, and it is why this is a predicate rather than a proof. Unlike
    `hashableG1_allowed`, which holds for EVERY codec (and that is its point: no codec
    choice can move a G1 read off width 48), `Hashable.Dispatchable E (hashableG1 c)` is
    FALSE for a codec `c` other than `E.g1`: the dispatch decodes with `E.g1`, so the
    accepted bytes of another codec need not be accepted by it. So every G1-reading
    transfer lemma here CARRIES the hypothesis `(hg1 : Hashable.Dispatchable E (hashableG1
    g1))` rather than discharging it, and it is discharged exactly where the pipeline codec
    IS `E.g1`: at `presDecoded_prepare` and at the `Pcs.kzg` call sites.
    `hashableG1_dispatchable` is stated for `hashableG1 E.g1` and for nothing else, and
    `dispatchable_refutesOtherReader` below is the theorem that says why it cannot be
    generalised.

    `Transcript.LogDecoded E` is STRONGER than `Transcript.LogWidths`:
    `logDecoded_imp_logWidths` proves the implication and `logWidths_not_logDecoded`
    refutes the converse. So the third walk subsumes the second for the codec lemma. The
    `PresWidths` walk is kept anyway: it is already proved, and it is what
    `decodeRust_recorded` and `msgWire_logDispatch` are stated against.

    THE `Pcs` OBLIGATION, same as the two existing walks: `Pcs` is a RECORD whose
    `multiPrepare` field is an arbitrary function, so `PresDecoded E (pcs.multiPrepare
    queries)` is not provable for a general `pcs`. `presDecoded_verifyAlgebraicConstraints`
    carries it as `hpcs` and `presDecoded_prepare` discharges it with
    `PresDecoded.multiPrepare` for `Pcs.kzg`, the only instantiation `verifyNative` uses.

    THE LANDMINES FROM THE FILE HEADER APPLY AND WERE RESPECTED: no `whnf` of
    `natToBytesLowFirst` with a symbolic value (the squeeze/squeezeChallenge steps go
    through `replaceState`, which keeps the new state a VARIABLE, and the transcripts in
    the exhibits are built by hand); the working `StateT` delta set in the algebraic walk;
    `StateT.pure` spelled out because inside a theorem named `PresDecoded.foo`, `pure`
    resolves to `PresDecoded.pure`; anonymous-structure updates on one line.

    D-P23 BOTH HALVES, per new lemma, as THEOREMS: `hashableFr_dispatchable` and
    `hashableG1_dispatchable` (witnesses) against `dispatchable_refutesOtherReader` and
    `hashableU32_not_dispatchable` (falsifications); `logDecoded_witness` against
    `logDecoded_refutesWrongSize`; `logDecoded_mapM_some` against
    `logDecoded_mapM_refutesUndecodable`; `logDecoded_imp_logWidths` against
    `logWidths_not_logDecoded`; and `set_not_PresDecoded` for the walk predicate. -/

/-- **`Hashable.Dispatchable E h`.** Every byte string the own reader of `h` accepts is a
    byte string the per-record decoder `decodeRust` dispatches to at that width also
    accepts. This is the fact the log cannot record and the codec lemma needs: a read that
    succeeded must leave behind a record the decoder can read back. -/
def Hashable.Dispatchable {T : Type} (E : VerifierEnv p G₁ G₂ Gₜ) (h : Hashable T) : Prop :=
  ∀ (b : Bytes) (v : T), h.readRepr? b = some v →
    ∃ m, logDispatch E (h.width, b) = some m

/-- The two `rfl` lemmas the sixth-obstacle header of this file promised. They are the
    reason the two verifier-path readers are safe: the function that ACCEPTED the bytes
    during the read is literally the function the dispatch REACHES FOR at that width. Not
    two codecs agreeing up to a proof - the same function. -/
theorem hashableFr_readRepr_eq (b : Bytes) :
    (hashableFr (p := p)).readRepr? b = frOfRepr? (p := p) b := rfl

theorem hashableG1_readRepr_eq {H : Type} (c : G1Codec H) (b : Bytes) :
    (hashableG1 c).readRepr? b = c.ofCompressed? b := rfl

/-- At the scalar width the dispatch IS `frOfRepr?`, and at the G1 width it IS the
    `ofCompressed?` of THE ENVIRONMENT'S OWN codec. These two equations are the whole
    content of `Dispatchable`, stated where the width tests are already resolved - and
    they are where the second arm's codec choice is visible: a different codec does not
    appear on the right-hand side. -/
theorem logDispatch_at_fr (E : VerifierEnv p G₁ G₂ Gₜ) (b : Bytes) :
    logDispatch E (32, b) = (frOfRepr? (p := p) b).map Msg.fr := by
  unfold logDispatch
  dsimp only []
  rw [hashableG1_width, hashableFr_width]
  rw [if_neg (by decide : ¬ ((32 : Nat) == g1CompressedWidth)),
    if_pos (by decide : (32 : Nat) == (32 : Nat))]

theorem logDispatch_at_g1 (E : VerifierEnv p G₁ G₂ Gₜ) (b : Bytes) :
    logDispatch E (g1CompressedWidth, b) = (E.g1.ofCompressed? b).map Msg.g1 := by
  unfold logDispatch
  dsimp only []
  rw [hashableG1_width]
  rw [if_pos (by decide : (g1CompressedWidth : Nat) == g1CompressedWidth)]

/-- The scalar reader is dispatchable for EVERY environment: its `readRepr?` is
    `frOfRepr?`, its width is 32, and 32 selects the `frOfRepr?` arm. -/
theorem hashableFr_dispatchable (E : VerifierEnv p G₁ G₂ Gₜ) :
    Hashable.Dispatchable E (hashableFr (p := p)) := by
  intro b v hv
  have hv2 : frOfRepr? (p := p) b = some v := hv
  refine ⟨Msg.fr v, ?_⟩
  rw [hashableFr_width, logDispatch_at_fr, hv2]
  rfl

/-- The compressed-G1 reader is dispatchable FOR THE ENVIRONMENT'S OWN CODEC, and this is
    the only form that is true: the dispatch decodes with `E.g1`, so the reader that
    agrees with it is `hashableG1 E.g1`. -/
theorem hashableG1_dispatchable (E : VerifierEnv p G₁ G₂ Gₜ) :
    Hashable.Dispatchable E (hashableG1 E.g1) := by
  intro b v hv
  rw [hashableG1_readRepr_eq] at hv
  refine ⟨Msg.g1 v, ?_⟩
  rw [hashableG1_width, logDispatch_at_g1, hv]
  rfl

/-- **The decodability condition.** Every record the transcript has logged is a record the
    decoder can read back. Where `LogWidths` asked only which WIDTH came in, this asks
    whether the BYTES decode - the question `decodeRust` actually asks. -/
def Transcript.LogDecoded (E : VerifierEnv p G₁ G₂ Gₜ) (t : Transcript) : Prop :=
  ∀ rec ∈ t.log.toList, ∃ m, logDispatch E rec = some m

/-- Replacing the hasher state cannot touch the logged bytes - the same shape, and for the
    same reason, as `Transcript.Tiled.replaceState`. -/
theorem Transcript.LogDecoded.replaceState (E : VerifierEnv p G₁ G₂ Gₜ)
    {t : Transcript} (ht : Transcript.LogDecoded E t) {s : Bytes} :
    Transcript.LogDecoded E ({ t with state := s }) := ht

theorem Transcript.LogDecoded.initFromBytes (E : VerifierEnv p G₁ G₂ Gₜ) (bytes : Bytes) :
    Transcript.LogDecoded E (Transcript.initFromBytes bytes) := by
  intro rec hmem
  simp [Transcript.initFromBytes] at hmem

theorem Transcript.LogDecoded.initWithHash (E : VerifierEnv p G₁ G₂ Gₜ)
    (H : Bytes → H256) (bytes : Bytes) :
    Transcript.LogDecoded E (Transcript.initWithHash H bytes) := by
  intro rec hmem
  simp [Transcript.initWithHash] at hmem

/-- Absorb logs nothing: only `Transcript.read` writes `log`. -/
theorem Transcript.LogDecoded.common (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type}
    (h : Hashable T) {t : Transcript} (ht : Transcript.LogDecoded E t) (input : T) :
    Transcript.LogDecoded E (t.common h input) := ht

theorem Transcript.LogDecoded.squeeze (E : VerifierEnv p G₁ G₂ Gₜ) {t : Transcript}
    (ht : Transcript.LogDecoded E t) : Transcript.LogDecoded E (t.squeeze).2 := by
  cases t with | mk st buf pos h log => exact Transcript.LogDecoded.replaceState E ht

theorem Transcript.LogDecoded.squeezeChallenge (E : VerifierEnv p G₁ G₂ Gₜ) {t : Transcript}
    (ht : Transcript.LogDecoded E t) : Transcript.LogDecoded E (t.squeezeChallenge (p := p)).2 := by
  cases t with | mk st buf pos h log => exact Transcript.LogDecoded.replaceState E ht

/-- **The step.** A successful read of a DISPATCHABLE hashable extends the decodable log
    by exactly the record it logged. This is the one place a new record enters the log
    (`Exec/Transcript.lean:153`), and the one place `Dispatchable` is consumed. -/
theorem Transcript.LogDecoded.read (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (h : Hashable T)
    (hh : Hashable.Dispatchable E h) {t : Transcript} (ht : Transcript.LogDecoded E t)
    {val : T} {t' : Transcript} (hrun : t.read h = .ok (val, t')) :
    Transcript.LogDecoded E t' := by
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
          have key : t.read h = .ok (val', Transcript.common h
              ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val') := by
            simp only [Transcript.read, hbt, hrr]
          have hpair : (val, t') = (val', Transcript.common h
              ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val') := by
            simpa using hrun.symm.trans key
          have hteq : t' = Transcript.common h
              ({ t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }) val' :=
            congrArg Prod.snd hpair
          subst hteq
          refine Transcript.LogDecoded.common E h ?_ val'
          intro rec hmem
          rw [Array.toList_push] at hmem
          rcases List.mem_append.mp hmem with hold | hnew
          · exact ht rec hold
          · rw [List.mem_singleton] at hnew
            cases hnew
            exact hh repr val' hrr

/-- n reads in order log n decodable records and nothing else. -/
theorem Transcript.LogDecoded.readN (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type}
    (h : Hashable T) (hh : Hashable.Dispatchable E h) {t : Transcript}
    (ht : Transcript.LogDecoded E t) (n : Nat) {vs : Array T} {t' : Transcript}
    (hrun : t.readN h n = .ok (vs, t')) : Transcript.LogDecoded E t' := by
  have key : ∀ (n : Nat) (acc : Array T) (t : Transcript), Transcript.LogDecoded E t →
      ∀ (vs : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (vs, t') → Transcript.LogDecoded E t' := by
    intro n
    induction n with
    | zero =>
        intro acc t ht vs t' hrun
        simp only [Transcript.readN.go] at hrun
        obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
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
                exact ih (acc.push v) t₂
                  (Transcript.LogDecoded.read E h hh ht hread) vs t' hrun
  exact key n #[] t ht vs t' hrun

/-- **The third pipeline predicate**, alongside `Pres` (where the cursor got to) and
    `PresWidths` (which widths came in): whether every record the action appends to the log
    is one the decoder can read back. The three are independent in one direction and ordered
    in the other: `PresDecoded E` implies `PresWidths` via `Transcript.logDecoded_imp_logWidths`, the converse is refuted by
    `logWidths_not_logDecoded`, and NEITHER says anything about the cursor, so neither
    implies `Pres` and `Pres` implies neither. The codec lemma needs `Pres` for where the
    bytes came from and `PresDecoded` for whether they read back - which is why there are
    three walks and not two. -/
def PresDecoded {T : Type} (E : VerifierEnv p G₁ G₂ Gₜ) (m : TranscriptM T) : Prop :=
  ∀ (t t' : Transcript) (a : T), Transcript.LogDecoded E t →
    m.run t = .ok (a, t') → Transcript.LogDecoded E t'

/-- Pointwise equality of runs transfers `PresDecoded` - the third twin of the transfer
    principle the algebraic walk needs, where `cases h : m.run s` on a HYPOTHESIS cannot
    abstract the scrutinee but the goal form can. -/
theorem PresDecoded.congr_of_run_eq {α : Type} (E : VerifierEnv p G₁ G₂ Gₜ)
    {m n : TranscriptM α} (h : ∀ s, m.run s = n.run s) (hm : PresDecoded E m) :
    PresDecoded E n := by
  intro t t' a ht hrun
  exact hm t t' a ht ((h t).trans hrun)

/-! #### Closure: the same constructs `Pres` and `PresWidths` are closed under

    Every lemma below is the literal twin of the `PresWidths` one of the same name, with
    `LogWidths` replaced by `LogDecoded E` and `h.AllowedWidth` replaced by
    `Hashable.Dispatchable E h`. They carry no separate doc strings on purpose: a second
    copy of the prose would be a second thing to let drift. The interesting differences are
    all in the hypotheses the G1-reading lemmas now carry - see the section header. -/



theorem PresDecoded.pure (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (x : T) : PresDecoded E (StateT.pure x : TranscriptM T) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
  exact ht



theorem PresDecoded.lift (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (e : Except Fault T) : PresDecoded E (StateT.lift e) := by
  intro t t' a ht h
  cases e with
  | error _ => cases h
  | ok x =>
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
      exact ht



theorem PresDecoded.get (E : VerifierEnv p G₁ G₂ Gₜ) : PresDecoded E (StateT.get : TranscriptM Transcript) := by
  intro t t' a ht h
  obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair h)
  exact ht



theorem PresDecoded.bind (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {m : TranscriptM α} {f : α → TranscriptM β}
    (hm : PresDecoded E m) (hf : ∀ x, PresDecoded E (f x)) : PresDecoded E (m >>= f) := by
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



theorem PresDecoded.seq (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {m : TranscriptM α} {n : TranscriptM β}
    (hm : PresDecoded E m) (hn : PresDecoded E n) : PresDecoded E (m >>= fun _ => n) :=
  PresDecoded.bind (E) hm (fun _ => hn)



theorem PresDecoded.ite (E : VerifierEnv p G₁ G₂ Gₜ) {α : Type} {c : Prop} [inst : Decidable c] {m n : TranscriptM α}
    (hm : PresDecoded E m) (hn : PresDecoded E n) : PresDecoded E (if c then m else n) := by
  split
  · exact hm
  · exact hn



theorem PresDecoded.fmap (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} (g : α → β) {m : TranscriptM α} (hm : PresDecoded E m) :
    PresDecoded E (g <$> m) := by
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
          obtain ⟨h1, rfl⟩ := pair_eq (ok_pair h3)
          subst h1
          exact hm t t₁ a ht hrun



theorem PresDecoded.guard (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresDecoded E k) (h : α → PresDecoded E k) :
    PresDecoded E (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  PresDecoded.ite (E) (α := β) (c := c) (PresDecoded.bind (E) (PresDecoded.lift (E) (Except.error f)) h) hk



theorem PresDecoded.guard' (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresDecoded E k) (h : α → PresDecoded E k) :
    PresDecoded E (if c then k else ((throw f : TranscriptM α) >>= fun x => k)) :=
  PresDecoded.ite (E) (α := β) (c := c) hk (PresDecoded.bind (E) (PresDecoded.lift (E) (Except.error f)) h)



theorem PresDecoded.read (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (h : Hashable T) (hh : Hashable.Dispatchable E h) :
    PresDecoded E (tmRead h) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmRead_run_fields h st buf pos hash log] at hrun
      exact Transcript.LogDecoded.read (E) h hh ht hrun



theorem PresDecoded.readN (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (h : Hashable T) (hh : Hashable.Dispatchable E h) (n : Nat) :
    PresDecoded E (tmReadN h n) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmReadN_run_fields h st buf pos hash log n] at hrun
      exact Transcript.LogDecoded.readN (E) h hh ht n hrun



theorem PresDecoded.common (E : VerifierEnv p G₁ G₂ Gₜ) {T : Type} (h : Hashable T) (input : T) :
    PresDecoded E (tmCommon h input) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmCommon_run_fields h st buf pos hash log input] at hrun
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
      exact Transcript.LogDecoded.common (E) h ht input



theorem PresDecoded.squeezeChallenge (E : VerifierEnv p G₁ G₂ Gₜ) :
    PresDecoded E (tmSqueezeChallenge (p := p)) := by
  intro s t' a ht hrun
  cases s with
  | mk st buf pos hash log =>
      rw [tmSqueeze_run_fields (p := p) st buf pos hash log] at hrun
      obtain ⟨rfl, rfl⟩ := pair_eq (ok_pair hrun)
      exact Transcript.LogDecoded.squeezeChallenge (E) ht



theorem PresDecoded.listFoldlM (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, PresDecoded E (f b x)) :
    ∀ (l : List α) (init : β), PresDecoded E (List.foldlM (init := init) f l) := by
  intro l
  induction l with
  | nil => intro init; exact PresDecoded.pure (E) _
  | cons a t ih =>
      intro init
      rw [List.foldlM_cons]
      refine PresDecoded.bind (E) (hf init _) (fun b => ih b)



theorem PresDecoded.listMapM (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} (l : List α) {f : α → TranscriptM β}
    (hf : ∀ x, PresDecoded E (f x)) : PresDecoded E (List.mapM f l) := by
  induction l with
  | nil => exact PresDecoded.pure (E) _
  | cons a t ih =>
      rw [List.mapM_cons]
      refine PresDecoded.bind (E) (hf _) (fun _ => ?_)
      refine PresDecoded.bind (E) ih (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.arrayFoldlM (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {f : β → α → TranscriptM β}
    (hf : ∀ b x, PresDecoded E (f b x)) (init : β) (as : Array α) :
    PresDecoded E (Array.foldlM (init := init) f as) := by
  rw [← Array.foldlM_toList]
  exact PresDecoded.listFoldlM (E) hf as.toList init



theorem PresDecoded.arrayMapM (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} (as : Array α) {f : α → TranscriptM β}
    (hf : ∀ x, PresDecoded E (f x)) : PresDecoded E (Array.mapM f as) := by
  rw [Array.mapM_eq_foldlM]
  refine PresDecoded.arrayFoldlM (E) (fun bs a => PresDecoded.fmap (E) _ (hf a)) #[] as



theorem PresDecoded.listForIn (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} (l : List α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, PresDecoded E (f x b)) :
    PresDecoded E (forIn l init f) := by
  classical
  rw [List.forIn_eq_foldlM]
  refine PresDecoded.fmap (E) _ (PresDecoded.listFoldlM (E) ?_ l (ForInStep.yield init))
  intro b x
  cases b with
  | yield b => exact hf x b
  | done b => exact PresDecoded.pure (E) _



theorem PresDecoded.arrayForIn (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} (as : Array α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (hf : ∀ x b, PresDecoded E (f x b)) :
    PresDecoded E (forIn as init f) := by
  rw [← Array.forIn_toList]
  exact PresDecoded.listForIn (E) as.toList init hf



theorem PresDecoded.readMultiplicities (E : VerifierEnv p G₁ G₂ Gₜ) {F : Type} {G₁ : Type}
    (argument : LogupChunkedArgument F) (h : Hashable G₁) (hh : Hashable.Dispatchable E h) :
    PresDecoded E (Logup.readMultiplicities argument h) := by
  unfold Logup.readMultiplicities
  refine PresDecoded.bind (E) (PresDecoded.read (E) h hh) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.trashReadCommitted (E : VerifierEnv p G₁ G₂ Gₜ) {F : Type} {G₁ : Type}
    (argument : TrashArgument F) (h : Hashable G₁) (hh : Hashable.Dispatchable E h) :
    PresDecoded E (Trash.readCommitted argument h) := by
  unfold Trash.readCommitted
  refine PresDecoded.bind (E) (PresDecoded.read (E) h hh) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.readCommitment (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (cm : Logup.CommittedMultiplicities G₁) (nbChunks : Nat) (h : Hashable G₁)
    (hh : Hashable.Dispatchable E h) :
    PresDecoded E (Logup.CommittedMultiplicities.readCommitment cm nbChunks h) := by
  unfold Logup.CommittedMultiplicities.readCommitment
  refine PresDecoded.bind (E) (PresDecoded.readN (E) h hh _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.read (E) h hh) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.hashInto (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (vk : VerifyingKey (Fr p) G₁) : PresDecoded E (VerifyingKey.hashInto vk) := by
  unfold VerifyingKey.hashInto
  exact PresDecoded.common (E) hashableFr vk.transcriptRepr



theorem PresDecoded.permReadProductCommitments (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type} (perm : PermutationArgument)
    (csDegree : Nat) (h : Hashable G₁) (hh : Hashable.Dispatchable E h) :
    PresDecoded E (Permutation.readProductCommitments perm csDegree h) := by
  unfold Permutation.readProductCommitments
  refine PresDecoded.ite (E) ?_ ?_
  · refine PresDecoded.bind (E) (PresDecoded.readN (E) h hh _) (fun _ => PresDecoded.pure (E) _)
  · intro t t' a ht h
    cases h



theorem PresDecoded.permVKevaluate (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (vk : Permutation.VerifyingKey G₁) :
    PresDecoded E (Permutation.VerifyingKey.evaluate (p := p) vk) := by
  unfold Permutation.VerifyingKey.evaluate
  refine PresDecoded.bind (E)
    (PresDecoded.readN (E) (hashableFr (p := p)) (hashableFr_dispatchable E) _) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.permCommittedEvaluate (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (coms : Permutation.Committed G₁) :
    PresDecoded E (Permutation.Committed.evaluate (p := p) coms) := by
  unfold Permutation.Committed.evaluate
  refine PresDecoded.bind (E) (PresDecoded.listForIn (E) (List.range coms.permutationProductCommitments.size)
      (#[] : Array (Permutation.SetEvaluated (Fr p))) (fun i s => ?_)) (fun _ => PresDecoded.pure (E) _)
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E)) (fun _ => ?_)
  refine PresDecoded.ite (E)
      (PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E))
        (fun _ => PresDecoded.pure (E) _)) (PresDecoded.pure (E) _)



theorem PresDecoded.logupEvaluate (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (coms : Logup.Committed G₁) : PresDecoded E (Logup.Committed.evaluate (p := p) coms) := by
  unfold Logup.Committed.evaluate
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E)) (fun _ => ?_)
  refine PresDecoded.bind (E)
    (PresDecoded.readN (E) (hashableFr (p := p)) (hashableFr_dispatchable E) _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E))
    (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.trashEvaluate (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (coms : Trash.Committed G₁) : PresDecoded E (Trash.Committed.evaluate (p := p) coms) := by
  unfold Trash.Committed.evaluate
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E))
    (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.addDummies (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresDecoded E (MultiPrepare.addDummies (G₂ := G₂) (Gₜ := Gₜ) g1 queries) := by
  unfold MultiPrepare.addDummies
  refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun dummies => ?_)
  refine PresDecoded.listFoldlM (E) (fun qs x => ?_) dummies queries
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E))
    (fun eval => ?_)
  cases hq : qs[x.1]? with
  | none =>
      show PresDecoded E (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
      exact (PresDecoded.lift (E) (Except.error (Fault.panic "proofs/src/poly/kzg/mod.rs:349"))
        : PresDecoded E (throw (Fault.panic "proofs/src/poly/kzg/mod.rs:349")))
  | some o =>
      exact PresDecoded.pure (E) _



theorem PresDecoded.phaseA (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresDecoded E (phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries) := by
  unfold Midfall.Halo2.phaseA
  refine PresDecoded.ite (E) (α := MultiPrepare.PhaseA (Fr p) G₁)
      (c := feat.outerFewerPointSets && fewerPointSetsRuntime) ?_ ?_
  · refine PresDecoded.bind (E) (PresDecoded.addDummies (E) g1 queries) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => PresDecoded.pure (E) _)
  · refine PresDecoded.bind (E) (PresDecoded.pure (E) queries) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => ?_)
    refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.phaseB (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (g1 : G1Codec G₁) (hg1 : Hashable.Dispatchable E (hashableG1 g1)) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) :
    PresDecoded E (phaseB g1 fc feat a) := by
  unfold Midfall.Halo2.phaseB
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableG1 g1) (hg1)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.listMapM (E) (List.range a.qEvalSets.size)
      (fun _ => PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E))) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.phaseC (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (hg1 : Hashable.Dispatchable E (hashableG1 g1)) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) (b : MultiPrepare.PhaseB (Fr p) G₁) :
    PresDecoded E (phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b) := by
  unfold Midfall.Halo2.phaseC
  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.read (E) (hashableG1 g1) (hg1))
    (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.multiPrepare (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (hg1 : Hashable.Dispatchable E (hashableG1 g1)) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) :
    PresDecoded E (multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime
      queries) := by
  unfold Midfall.Halo2.multiPrepare
  refine PresDecoded.bind (E) (PresDecoded.phaseA (E) g1 fc feat fewerPointSetsRuntime queries)
    (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.phaseB (E) g1 hg1 fc feat _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.phaseC (E) g1 hg1 fc feat _ _) (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.readFixedEvals (E : VerifierEnv p G₁ G₂ Gₜ)
    (cs : ConstraintSystem (Fr p)) :
    PresDecoded E (Verifier.readFixedEvals (p := p) cs) := by
  unfold Verifier.readFixedEvals
  apply PresDecoded.guard (E)
  · refine PresDecoded.bind (E)
      (PresDecoded.readN (E) (hashableFr (p := p)) (hashableFr_dispatchable E) _) (fun read => ?_)
    refine PresDecoded.bind (E) (PresDecoded.listFoldlM (E) (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => PresDecoded.pure (E) _)
    refine PresDecoded.ite (E) (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (PresDecoded.lift (E) _) (PresDecoded.pure (E) _)
  · intro z
    refine PresDecoded.bind (E)
      (PresDecoded.readN (E) (hashableFr (p := p)) (hashableFr_dispatchable E) _) (fun read => ?_)
    refine PresDecoded.bind (E) (PresDecoded.listFoldlM (E) (fun acc step => ?_)
        (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList) read.toList)
        (fun _ => PresDecoded.pure (E) _)
    refine PresDecoded.ite (E) (α := List (Fr p)) (c := cs.hasSimpleSelectorCol step.2.1.index)
      (PresDecoded.lift (E) _) (PresDecoded.pure (E) _)



theorem PresDecoded.readAlgebra (E : VerifierEnv p G₁ G₂ Gₜ) {G₁ : Type}
    (g1 : G1Codec G₁) (hg1 : Hashable.Dispatchable E (hashableG1 g1)) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    PresDecoded E (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
      nbCommitted numProofs instances) := by
  unfold Verifier.readAlgebra
  refine PresDecoded.bind (E)
    (PresDecoded.readN (E) (hashableG1 g1) (hg1) _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.lift (E) _) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.listMapM (E) instances.toList (fun row =>
      PresDecoded.listMapM (E) vk.cs.instanceQueries.toList (fun q => ?_))) (fun _ => ?_)
  · refine PresDecoded.ite (E) (α := Fr p) (c := q.1.index < nbCommitted)
      (PresDecoded.read (E) (hashableFr (p := p)) (hashableFr_dispatchable E)) ?_
    dsimp only
    cases hq : row[q.1.index - nbCommitted]? with
    | none =>
        exact (PresDecoded.lift (E) (Except.error (Fault.panic "proofs/src/plonk/verifier.rs:366"))
          : PresDecoded E (throw (Fault.panic "proofs/src/plonk/verifier.rs:366")))
    | some col =>
        dsimp only
        apply PresDecoded.guard' (E)
        · exact PresDecoded.lift (E) _
        · intro z
          exact PresDecoded.lift (E) _
  refine PresDecoded.bind (E) (PresDecoded.listMapM (E) (List.range numProofs)
      (fun _ => PresDecoded.readN (E) (hashableFr (p := p)) (hashableFr_dispatchable E) _)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.readFixedEvals (E) vk.cs) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.permVKevaluate (E) vk.permutation) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.listMapM (E) permutations.toList (fun pc =>
      PresDecoded.permCommittedEvaluate (E) pc)) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.listMapM (E) lookups.toList (fun row =>
      PresDecoded.listMapM (E) row.toList (fun l => PresDecoded.logupEvaluate (E) l))) (fun _ => ?_)
  refine PresDecoded.bind (E) (PresDecoded.listMapM (E) trashcans.toList (fun row =>
      PresDecoded.listMapM (E) row.toList (fun t => PresDecoded.trashEvaluate (E) t)))
      (fun _ => PresDecoded.pure (E) _)



theorem PresDecoded.guardWhen (E : VerifierEnv p G₁ G₂ Gₜ) {α β : Type} {c : Prop} [inst : Decidable c] (f : Fault)
    (k : TranscriptM β) (hk : PresDecoded E k) :
    PresDecoded E (if c then ((throw f : TranscriptM α) >>= fun x => k) else k) :=
  PresDecoded.ite (E) (α := β) (c := c)
    (PresDecoded.bind (E) (PresDecoded.lift (E) (Except.error f)) (fun _ => hk)) hk



theorem presDecoded_parseTrace (E : VerifierEnv p G₁ G₂ Gₜ)     (g1 : G1Codec G₁) (hg1 : Hashable.Dispatchable E (hashableG1 g1)) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) :
    PresDecoded E (parseTrace g1 feat vk committed₀ inst) := by
  unfold parseTrace
  apply PresDecoded.guardWhen (E)
  · apply PresDecoded.guardWhen (E)
    · apply PresDecoded.guardWhen (E)
      · refine PresDecoded.bind (E) (PresDecoded.hashInto (E) vk) (fun _ => ?_)
        -- absorb the committed instance commitments
        refine PresDecoded.bind (E) ?_ (fun _ => ?_)
        · apply PresDecoded.listForIn (E)
          · intro row __s
            refine PresDecoded.bind (E) ?_ (fun _ => PresDecoded.pure (E) _)
            · apply PresDecoded.arrayForIn (E)
              · intro com __s
                exact PresDecoded.bind (E) (PresDecoded.common (E) (hashableG1 g1) com) (fun _ => PresDecoded.pure (E) _)
        -- absorb each instance column's length then its values
        · refine PresDecoded.bind (E) ?_ (fun _ => ?_)
          · apply PresDecoded.listForIn (E)
            · intro row __s
              refine PresDecoded.bind (E) ?_ (fun _ => PresDecoded.pure (E) _)
              · apply PresDecoded.arrayForIn (E)
                · intro col __s
                  refine PresDecoded.bind (E) (PresDecoded.common (E) hashableFr (Nat.cast col.size)) (fun _ => ?_)
                  refine PresDecoded.bind (E) ?_ (fun _ => PresDecoded.pure (E) _)
                  · apply PresDecoded.arrayForIn (E)
                    · intro v __s
                      exact PresDecoded.bind (E) (PresDecoded.common (E) hashableFr v) (fun _ => PresDecoded.pure (E) _)
          -- the phase loop
          · refine PresDecoded.bind (E) ?_ (fun x => ?_)
            · apply PresDecoded.listFoldlM (E)
              · intro st ph
                dsimp only []
                refine PresDecoded.bind (E) ?_ (fun adv => ?_)
                · apply PresDecoded.listFoldlM (E)
                  · intro acc k
                    refine PresDecoded.bind (E) (PresDecoded.readN (E) (hashableG1 g1) (hg1) _) (fun _ => PresDecoded.pure (E) _)
                · refine PresDecoded.bind (E) ?_ (fun chals => PresDecoded.pure (E) _)
                  · apply PresDecoded.listFoldlM (E)
                    · intro acc e
                      apply PresDecoded.ite (E)
                      · refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun _ => PresDecoded.pure (E) _)
                      · exact PresDecoded.pure (E) _
            · cases x with
              | mk advPairs chalPairs =>
                refine PresDecoded.bind (E) ?_ (fun adviceCommitments => ?_)
                · apply PresDecoded.listFoldlM (E)
                  · intro acc pairs
                    refine PresDecoded.bind (E)
                        (PresDecoded.lift (E) (scatterIndexed vk.cs.numAdviceColumns pairs
                          "proofs/src/plonk/verifier.rs:118")) (fun _ => PresDecoded.pure (E) _)
                · refine PresDecoded.bind (E)
                      (PresDecoded.lift (E) (scatterIndexed vk.cs.numChallenges chalPairs
                        "proofs/src/plonk/verifier.rs:134")) (fun challenges => ?_)
                  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun theta => ?_)
                  refine PresDecoded.bind (E) ?_ (fun lookupMultiplicities => ?_)
                  · apply PresDecoded.listFoldlM (E)
                    · intro acc x
                      refine PresDecoded.bind (E) ?_ (fun row => PresDecoded.pure (E) _)
                      · apply PresDecoded.listFoldlM (E)
                        · intro acc' l
                          refine PresDecoded.bind (E) (PresDecoded.lift (E) (l.chunkByDegree vk.csDegree))
                            (fun chunked => ?_)
                          refine PresDecoded.bind (E) (PresDecoded.readMultiplicities (E) chunked (hashableG1 g1) (hg1))
                            (fun m => PresDecoded.pure (E) _)
                  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun beta => ?_)
                  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun gamma => ?_)
                  refine PresDecoded.bind (E) ?_ (fun permutations => ?_)
                  · apply PresDecoded.listFoldlM (E)
                    · intro acc x
                      refine PresDecoded.bind (E)
                          (PresDecoded.permReadProductCommitments (E) vk.cs.permutation vk.csDegree (hashableG1 g1) (hg1)) (fun _ => PresDecoded.pure (E) _)
                  refine PresDecoded.bind (E) ?_ (fun lookups => ?_)
                  · apply PresDecoded.listFoldlM (E)
                    · intro acc row
                      refine PresDecoded.bind (E) ?_ (fun out => PresDecoded.pure (E) _)
                      · apply PresDecoded.listFoldlM (E)
                        · intro acc' x
                          cases x with
                          | mk m chunked =>
                            refine PresDecoded.bind (E)
                                (PresDecoded.readCommitment (E) m chunked.numChunks (hashableG1 g1) (hg1))
                                (fun _ => PresDecoded.pure (E) _)
                  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun trashChallenge => ?_)
                  refine PresDecoded.bind (E) ?_ (fun trashcans => ?_)
                  · apply PresDecoded.listFoldlM (E)
                    · intro acc x
                      refine PresDecoded.bind (E) ?_ (fun row => PresDecoded.pure (E) _)
                      · apply PresDecoded.listFoldlM (E)
                        · intro acc' t
                          refine PresDecoded.bind (E) (PresDecoded.trashReadCommitted (E) t (hashableG1 g1) (hg1))
                            (fun _ => PresDecoded.pure (E) _)
                  refine PresDecoded.bind (E) (PresDecoded.squeezeChallenge (E)) (fun y => ?_)
                  exact PresDecoded.pure (E) _



theorem presDecoded_verifyAlgebraicConstraints (E : VerifierEnv p G₁ G₂ Gₜ)     (g1 : G1Codec G₁) (hg1 : Hashable.Dispatchable E (hashableG1 g1)) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ)
    (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁))
    (instances : Array (Array (Array (Fr p))))
    (hpcs : ∀ queries, PresDecoded E (pcs.multiPrepare queries)) :
    PresDecoded E (Verifier.verifyAlgebraicConstraints (p := p) g1 delta feat pcs vk trace
      committedInstances instances) := by
  unfold Verifier.verifyAlgebraicConstraints
  apply PresDecoded.guardWhen (E)
  · refine PresDecoded.bind (E) ?_ (fun alg => ?_)
    · apply PresDecoded.readAlgebra (E) g1 hg1
    · refine PresDecoded.bind (E) ?_ (fun queries => ?_)
      · apply PresDecoded.lift (E)
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


/-- **The consequence the codec lemma consumes.** Decodability of the log is exactly what
    makes the per-record `mapM` succeed: a list whose every element decodes has a decoded
    list. This is the missing hypothesis of `decodeRust_recorded`, and therefore of
    `verifyNative_iff_msgs_codec`. -/
theorem list_mapM_all_some {α β : Type} (f : α → Option β) (l : List α)
    (h : ∀ a ∈ l, ∃ b, f a = some b) : ∃ ms, l.mapM f = some ms := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a t ih =>
      obtain ⟨b, hb⟩ := h a List.mem_cons_self
      obtain ⟨ms, hms⟩ := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      refine ⟨b :: ms, ?_⟩
      rw [List.mapM_cons, hb, hms]
      simp

theorem logDecoded_mapM_some (E : VerifierEnv p G₁ G₂ Gₜ) (t : Transcript)
    (ht : Transcript.LogDecoded E t) :
    ∃ ms, t.log.toList.mapM (logDispatch E) = some ms :=
  list_mapM_all_some (logDispatch E) t.log.toList (fun rec hmem => ht rec hmem)

/-- **The new predicate is the stronger one.** Decodable implies allowed width: a record
    whose width the dispatch does not reach for has no decoder at all, so a log all of
    whose records decode can only have logged the two widths. Paired with
    `logWidths_not_logDecoded`, which refutes the converse, this pins the strict ordering
    the third walk exists to establish: `LogDecoded E` implies `LogWidths` and is
    strictly stronger than it. -/
theorem Transcript.logDecoded_imp_logWidths (E : VerifierEnv p G₁ G₂ Gₜ) {t : Transcript}
    (ht : Transcript.LogDecoded E t) : t.LogWidths := by
  intro rec hmem
  obtain ⟨m, hm⟩ := ht rec hmem
  unfold logDispatch at hm
  by_cases h1 : rec.1 == (hashableG1 E.g1).width
  · right
    exact (Nat.beq_eq.mp h1).trans (hashableG1_width (c := E.g1))
  · by_cases h2 : rec.1 == (hashableFr (p := p)).width
    · left
      exact (Nat.beq_eq.mp h2).trans hashableFr_width
    · rw [if_neg h1, if_neg h2] at hm
      cases hm

/-- **The whole §9.2 read schedule leaves a decodable log.** The third and last of the
    three pipeline theorems. Every hypothesis the walk could not discharge is discharged
    here, once, at the only codec and the only `Pcs` the verifier path uses. -/
theorem presDecoded_prepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (committed : List (List G₁))
    (inst : List (List (List (Fr p)))) :
    PresDecoded E (prepare (Gₜ := Gₜ) E F vk committed inst) := by
  unfold prepare prepareWith Verifier.prepare
  refine PresDecoded.bind (E) ?_ (fun trace => ?_)
  · exact presDecoded_parseTrace (E) E.g1 (hashableG1_dispatchable E) F vk _ _
  · refine presDecoded_verifyAlgebraicConstraints (E) E.g1 (hashableG1_dispatchable E)
        E.delta F (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime)
        vk trace _ _ ?_
    · intro queries
      exact PresDecoded.multiPrepare (E) E.g1 (hashableG1_dispatchable E) E.field F
        E.fewerPointSetsRuntime queries

/-! #### D-P23: both halves of the decodability predicate -/

/-- A width-32 reader that accepts EVERY byte string. It is the sixth obstacle as a
    definition: right width, wrong reader. -/
def alwaysAccepts32 : Hashable Bytes where
  toInput := fun _ => Bytes.empty
  toBytes := fun b => b
  width := 32
  readRepr? := fun b => some b

/-- `frOfRepr?` rejects anything that is not 32 bytes long, whatever the modulus. The
    exhibits below need this at the ABSTRACT section modulus, where the byte arithmetic
    cannot be decided by evaluation, so it is proved once here. -/
theorem frOfRepr_none_of_size_ne (b : Bytes) (h : b.size ≠ 32) :
    frOfRepr? (p := p) b = none := by
  rw [frOfRepr?]
  refine if_neg ?_
  intro hc
  rw [Bool.and_eq_true] at hc
  exact h (Nat.eq_of_beq_eq_true hc.1)

/-- The converse fact the witness needs: whatever `frOfRepr?` accepts really is 32 bytes
    long, i.e. the record a successful scalar read logs has the width the dispatch reads
    it back at. -/
theorem frOfRepr_size_of_some {b : Bytes} {x : Fr p} (h : frOfRepr? (p := p) b = some x) :
    b.size = 32 := by
  rw [frOfRepr?] at h
  by_cases hc : (b.size == 32 && bytesToNatLE b < p)
  · rw [if_pos hc] at h
    rw [Bool.and_eq_true] at hc
    exact Nat.eq_of_beq_eq_true hc.1
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- **Falsification, as a THEOREM: allowed width does NOT imply dispatchability.** This
    hashable has an allowed width and a reader that never fails, and it is not
    `Dispatchable`, because at width 32 the dispatch runs `frOfRepr?`, which rejects a
    string that is not 32 bytes long. This is exactly why the codec lemma needs a third
    predicate rather than a re-statement of the width one, and why
    `hashableG1_dispatchable` is stated for `E.g1` alone. -/
theorem dispatchable_refutesOtherReader (E : VerifierEnv p G₁ G₂ Gₜ) :
    alwaysAccepts32.AllowedWidth ∧ ¬ Hashable.Dispatchable E alwaysAccepts32 := by
  refine ⟨Or.inl rfl, ?_⟩
  intro h
  obtain ⟨m, hm⟩ := h Bytes.empty Bytes.empty rfl
  have hw : alwaysAccepts32.width = 32 := rfl
  rw [hw, logDispatch_at_fr,
    frOfRepr_none_of_size_ne (p := p) Bytes.empty (by decide)] at hm
  cases hm

/-- **Falsification, as a THEOREM: the u32 reader is not dispatchable**, because the
    dispatch has no arm for width 4. The verifier path must never read through it, and
    this is the theorem that says what goes wrong if it does. -/
theorem hashableU32_not_dispatchable (E : VerifierEnv p G₁ G₂ Gₜ) :
    ¬ Hashable.Dispatchable E hashableU32 := by
  intro h
  obtain ⟨m, hm⟩ := h (natToBytesLE 7 4) 7 (by
    show (if (natToBytesLE 7 4).size == 4 then some (bytesToNatLE (natToBytesLE 7 4))
      else none) = some 7
    rw [if_pos (by decide : (natToBytesLE 7 4).size == 4), bytesToNatLE_natToBytesLE,
      Nat.mod_eq_of_lt (by decide)])
  have : logDispatch E (hashableU32.width, natToBytesLE 7 4) = none := by
    unfold logDispatch
    dsimp only []
    rw [hashableU32_width, hashableG1_width, hashableFr_width]
    rw [if_neg (by decide : ¬ ((4 : Nat) == g1CompressedWidth)),
      if_neg (by decide : ¬ ((4 : Nat) == (32 : Nat)))]
  rw [this] at hm
  cases hm

/-- **Satisfiability, as a THEOREM.** The hypothesis of the walk is inhabited, and its
    conclusion is a fact about a specific message list rather than a bare existence: take
    any scalar repr the decoder accepts - `frOfRepr_bytes_witness` in
    `Midfall/Assumptions/Codec.lean` exhibits real ones at `p = 17` - and log exactly the
    record a real read of it produces. The dispatch reads it back as `Msg.fr x`, the width
    condition holds of the same transcript, and the recorded bytes are the repr itself. -/
theorem logDecoded_witness (E : VerifierEnv p G₁ G₂ Gₜ) (b : Bytes) (x : Fr p)
    (hx : frOfRepr? (p := p) b = some x) :
    ∃ (t : Transcript) (ms : List (Msg (Fr p) G₁)),
      Transcript.LogDecoded E t ∧ t.LogWidths ∧
        t.log.toList.mapM (logDispatch E) = some ms ∧ ms = [Msg.fr x] ∧
        t.recorded = b ∧ t.pos = b.size ∧ t.pos = 32 := by
  have hsz : b.size = 32 := frOfRepr_size_of_some hx
  refine ⟨Transcript.mk Bytes.empty b 32 keccak256 #[(32, b)], [Msg.fr x], ?_, ?_, ?_,
    rfl, ?_, by rw [hsz], rfl⟩
  · intro rec hmem
    have hl : ((#[(32, b)] : Array (Nat × Bytes)).toList) = [(32, b)] := rfl
    rw [hl] at hmem
    simp at hmem
    rcases hmem with rfl
    exact ⟨Msg.fr x, by rw [logDispatch_at_fr, hx]; rfl⟩
  · intro rec hmem
    have hl : ((#[(32, b)] : Array (Nat × Bytes)).toList) = [(32, b)] := rfl
    rw [hl] at hmem
    simp at hmem
    rcases hmem with rfl
    exact Or.inl rfl
  · show List.mapM (logDispatch E) [(32, b)] = some [Msg.fr x]
    rw [List.mapM_cons, logDispatch_at_fr, hx]
    simp
  · show ByteArray.mk (b.data.toList.toArray) = b
    rw [array_toList_toArray]

/-- **Falsification, as a THEOREM: a decodable log is not free.** Here is a transcript
    whose single record has an ALLOWED width but bytes no decoder accepts: a 0-byte
    string logged as if it were a scalar repr. `LogWidths` holds of it and `LogDecoded`
    does not, so the walk that proves `LogDecoded` does work the width walk cannot do. -/
theorem logDecoded_refutesWrongSize (E : VerifierEnv p G₁ G₂ Gₜ) :
    Transcript.LogWidths (Transcript.mk Bytes.empty Bytes.empty 32 keccak256
        #[(32, Bytes.empty)]) ∧
      ¬ Transcript.LogDecoded E (Transcript.mk Bytes.empty Bytes.empty 32 keccak256
        #[(32, Bytes.empty)]) := by
  refine ⟨?_, ?_⟩
  · intro rec hmem
    have hl : ((#[(32, Bytes.empty)] : Array (Nat × Bytes)).toList)
        = [(32, Bytes.empty)] := rfl
    rw [hl] at hmem
    simp at hmem
    rcases hmem with rfl
    exact Or.inl rfl
  · intro h
    obtain ⟨m, hm⟩ := h (32, Bytes.empty) (by simp)
    rw [logDispatch_at_fr,
      frOfRepr_none_of_size_ne (p := p) Bytes.empty (by decide)] at hm
    cases hm

/-- **Falsification, as a THEOREM: without decodability there is no message stream at
    all.** The same transcript, at the level of the whole `mapM`: the width condition
    holds, the map fails, so `decodeRust` is `none` on a log whose every width the
    dispatch reaches for. This is the sixth obstacle in the exact shape
    `decodeRust_recorded` consumes it. -/
theorem logDecoded_mapM_refutesUndecodable (E : VerifierEnv p G₁ G₂ Gₜ) :
    ¬ ∃ (ms : List (Msg (Fr p) G₁)),
        (Transcript.mk Bytes.empty Bytes.empty 32 keccak256
            #[(32, Bytes.empty)]).log.toList.mapM (logDispatch E) = some ms := by
  intro ⟨ms, h⟩
  have hl : ((#[(32, Bytes.empty)] : Array (Nat × Bytes)).toList)
      = [(32, Bytes.empty)] := rfl
  have hw : (Transcript.mk Bytes.empty Bytes.empty 32 keccak256
      #[(32, Bytes.empty)]).log.toList.mapM (logDispatch E)
      = List.mapM (logDispatch E) [(32, Bytes.empty)] := by rw [hl]
  rw [hw, List.mapM_cons, logDispatch_at_fr,
    frOfRepr_none_of_size_ne (p := p) Bytes.empty (by decide)] at h
  simp at h

/-- **D-P23 falsification, as a THEOREM: `PresDecoded` is NOT closed under `StateT.set`**,
    for the same reason as the other two: `set` installs an arbitrary transcript, whose
    log may carry a record nothing decodes. No `PresDecoded.set` lemma is stated anywhere
    in this file, and this is the proof that none exists. -/
theorem set_not_PresDecoded (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∃ (x : Transcript), ¬ PresDecoded E (StateT.set x) := by
  refine ⟨Transcript.mk Bytes.empty Bytes.empty 32 keccak256 #[(32, Bytes.empty)], ?_⟩
  intro h
  have h1 := h (Transcript.initFromBytes Bytes.empty) _ ()
    (Transcript.LogDecoded.initFromBytes E _) rfl
  exact (logDecoded_refutesWrongSize E).2 h1

/-- Satisfiability, computed: two REAL reads of a real buffer through the two verifier-path
    readers, and the dispatch - spelled at `p = 17` with `widthKatCodec` in place of the
    environment codec, since this file may not build a `VerifierEnv` (D-P17) - reads both
    records back to pinned values. `Msg` carries no `BEq`, so the decode is observed
    through the code each arm returns: 5 for the scalar that was read, 48 for the point.
    The last two conjuncts are the falsifications, computed: a record of an ALLOWED width
    whose bytes do not read back makes the whole map `none`. -/
def logDecodedKat_ok : Bool :=
  let dispatch := fun rec : Nat × Bytes =>
    if rec.1 == g1CompressedWidth then (widthKatCodec.ofCompressed? rec.2).map (fun _ => 48)
    else if rec.1 == 32 then (frOfRepr? (p := 17) rec.2).map (fun x => x.val) else none
  let buf := frToRepr (p := 17) (5 : Fr 17) ++ natToBytesLE 1 48
  let bad : Transcript := Transcript.mk Bytes.empty Bytes.empty 32 keccak256
    #[(32, Bytes.empty)]
  match ((Transcript.initFromBytes buf).read (hashableFr (p := 17)) >>=
          fun q => q.2.read (hashableG1 widthKatCodec)) with
  | .ok (_, t) =>
      t.log.toList.mapM dispatch == some [5, 48] &&
        (t.log.toList.mapM dispatch).isSome &&
        t.log.toList.all (fun rec => (dispatch rec).isSome) &&
        t.log.toList.all (fun rec => rec.1 == 32 || rec.1 == g1CompressedWidth) &&
        (bad.log.toList.mapM dispatch == none) &&
        (dispatch (32, frToRepr (p := 17) (5 : Fr 17)) == some 5)
  | .error _ => false

#eval logDecodedKat_ok   -- expect true

/-! ### P-CODEC-C step 2: the pipeline shape the codec lemma consumes

    `verifyNative` and `verifyMsgs` are the SAME composition - run the §9.2 schedule on a
    stream, require the cursor to have eaten the whole stream, then run the opening check -
    over two different streams. `verifyShape` names that composition once, so the codec
    lemma is an equality of streams rather than a re-derivation of the verifier.
    `verifyNative_eq_verifyShape` and `verifyMsgs_eq_verifyShape` are the two
    recognitions, and they are `rfl` up to the do-block desugaring: the port really does
    execute one schedule twice, which is the property the §9.2 design was built to have.

    `decodeRust_some` is the inversion the backward direction needs: a successful
    `decodeRust` means the run succeeded, the cursor ate the whole stream, and the log's
    per-record decode produced exactly those messages. -/
/-- The shape both sides of the codec lemma share: run the §9.2 schedule on a stream,
    require the cursor to have eaten the whole stream, then run the opening check. -/
def verifyShape (params : ParamsVerifierKZG G₁ G₂)
    (x : Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)) : Except Fault Unit :=
  x >>= fun q => q.2.assertEmpty >>= fun _ =>
    if DualMSM.check q.1 params = true then pure () else throw (Fault.error Error.opening)

theorem verifyShape_ok {params : ParamsVerifierKZG G₁ G₂}
    {x : Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)}
    (h : verifyShape params x = Except.ok ()) :
    ∃ g t, x = Except.ok (g, t) ∧ t.assertEmpty = Except.ok () ∧
      DualMSM.check g params = true := by
  cases x with
  | error e => cases h
  | ok q =>
      cases q with
      | mk g t =>
          have h1 : (t.assertEmpty >>= fun _ =>
              if DualMSM.check g params = true then (pure () : Except Fault Unit)
              else throw (Fault.error Error.opening)) = Except.ok () := h
          cases h2 : t.assertEmpty with
          | error e =>
              rw [h2] at h1
              cases h1
          | ok u =>
              have h3 : (if DualMSM.check g params = true then (pure () : Except Fault Unit)
                    else throw (Fault.error Error.opening)) = Except.ok () := by
                rw [h2] at h1
                exact h1
              by_cases hc : DualMSM.check g params
              · exact ⟨g, t, rfl, h2, hc⟩
              · have h4 : (throw (Fault.error Error.opening) : Except Fault Unit)
                    = Except.ok () := by simp [hc] at h3 ⊢
                cases h4

theorem verifyShape_ok_of {params : ParamsVerifierKZG G₁ G₂}
    {x : Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)} {g t}
    (hx : x = Except.ok (g, t)) (hempty : t.assertEmpty = Except.ok ())
    (hcheck : DualMSM.check g params = true) : verifyShape params x = Except.ok () := by
  subst hx
  show (t.assertEmpty >>= fun _ =>
      if DualMSM.check g params = true then (pure () : Except Fault Unit)
      else throw (Fault.error Error.opening)) = Except.ok ()
  rw [hempty]
  show (if DualMSM.check g params = true then (pure () : Except Fault Unit)
      else throw (Fault.error Error.opening)) = Except.ok ()
  rw [hcheck]
  rfl

theorem verifyNative_eq_verifyShape (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (π : Bytes) :
    verifyNative (Gₜ := Gₜ) E F params vk inst π
      = verifyShape params ((prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
          (Transcript.initFromBytes π)) := by
  unfold verifyNative verifyShape
  dsimp only []

theorem verifyMsgs_eq_verifyShape (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    verifyMsgs (Gₜ := Gₜ) E H F params vk inst ms
      = verifyShape params ((prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
          (Transcript.initWithHash H
            (ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (msgWire E m))))) := by
  unfold verifyMsgs prepareMsgs verifyShape
  dsimp only []
  simp only [Bind.bind, Pure.pure, Except.bind, Except.pure]
  cases hrun : (StateT.run (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]])
      (Transcript.initWithHash H _)) with
  | error e => simp
  | ok q =>
      cases q with
      | mk g t =>
          cases h2 : t.assertEmpty with
          | error e => simp [h2]
          | ok u => simp [h2]

theorem assertEmpty_ok_iff (t : Transcript) :
    t.assertEmpty = Except.ok () ↔ t.buffer.size = t.pos := by
  unfold Transcript.assertEmpty
  by_cases h : t.buffer.size == t.pos
  · rw [if_pos h]; exact ⟨fun _ => Nat.eq_of_beq_eq_true h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun e => absurd e (by simp), fun e => absurd h (by simpa using e)⟩

theorem extract_whole (pi : Bytes) (n : Nat) (h : n = pi.size) : pi.extract 0 n = pi := by
  subst h
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rw [show (ByteArray.size pi) = pi.data.toList.length from Array.length_toList.symm]
  rw [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, List.take_length]

theorem decodeRust_some (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes)
    (ms : List (Msg (Fr p) G₁))
    (h0 : decodeRust (Gₜ := Gₜ) E F vk inst π = some ms) :
    ∃ g t, (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
        (Transcript.initFromBytes π) = .ok (g, t) ∧ t.pos = t.buffer.size ∧
      t.log.toList.mapM (logDispatch E) = some ms := by
  classical
  unfold decodeRust at h0
  dsimp only [] at h0
  have hcase : (∃ g t, (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
        (Transcript.initFromBytes π) = .ok (g, t)) ∨
      (∃ e, (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
        (Transcript.initFromBytes π) = .error e) := by
    cases h : (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
        (Transcript.initFromBytes π) with
    | ok q => cases q with | mk g t => exact Or.inl ⟨g, t, rfl⟩
    | error e => exact Or.inr ⟨e, rfl⟩
  rcases hcase with ⟨g, t, hrun⟩ | ⟨e, hrun⟩
  · rw [hrun] at h0
    simp only [Except.toOption, Option.bind, Bind.bind] at h0
    by_cases hne : ByteArray.size t.buffer ≠ t.pos
    · simp only [if_pos hne] at h0
      cases h0
    · simp only [if_neg hne] at h0
      have h2 : t.pos = ByteArray.size t.buffer := by omega
      exact ⟨g, t, hrun, h2, h0⟩
  · rw [hrun] at h0
    simp only [Except.toOption, Option.bind, Bind.bind] at h0
    cases h0

/-! #### D-P23 for the step-2 shape lemmas -/

/-- Satisfiability of `assertEmpty_ok_iff`: a cursor that has eaten the stream.
    Falsification, as a THEOREM: a cursor one byte short is NOT empty, and the failure is
    the NotFound kind the Rust uses (mod.rs:150-159), not a success. Without this the
    right-hand side could be read as "the log tiles a prefix of the buffer", which is
    exactly what `decodeRust`'s trailing-bytes test exists to reject. -/
theorem assertEmpty_ok_witness_and_refutation :
    (Transcript.initFromBytes Bytes.empty).assertEmpty = Except.ok () ∧
      ¬ (Transcript.mk Bytes.empty (natToBytesLE 7 4) 3 keccak256 #[]).assertEmpty
        = Except.ok () :=
  ⟨rfl, by
    show Except.error (Fault.error (Error.transcript IoErrorKind.notFound)) ≠ Except.ok ()
    intro h
    cases h⟩

/-- Satisfiability of `extract_whole` at the only length that works, and the falsification
    that the length hypothesis is load-bearing: at one byte short the slice is NOT the
    stream. -/
theorem extract_whole_refutesShortPrefix :
    (natToBytesLE 7 4).extract 0 4 = natToBytesLE 7 4 ∧
      (natToBytesLE 7 4).extract 0 3 ≠ natToBytesLE 7 4 := by
  refine ⟨extract_whole _ _ rfl, ?_⟩
  intro h
  have h1 := congrArg ByteArray.size h
  have h2 : ByteArray.size ((natToBytesLE 7 4).extract 0 3) = 3 := by decide
  have h3 : ByteArray.size (natToBytesLE 7 4) = 4 := by decide
  rw [h2, h3] at h1
  exact absurd h1 (by decide)

/-- Falsification, as a THEOREM: `verifyShape` is not the constant `ok ()`. A failed
    opening check makes it an error even when the run and the cursor are perfect - which
    is what makes `verifyShape_ok` an inversion rather than a tautology. -/
theorem verifyShape_refutesFailedCheck {params : ParamsVerifierKZG G₁ G₂} {g t}
    (hcheck : DualMSM.check g params = false) (_hempty : t.assertEmpty = Except.ok ()) :
    verifyShape params (Except.ok (g, t)) ≠ Except.ok () := by
  intro h
  obtain ⟨g2, t2, hx, _hempty2, hcheck2⟩ := verifyShape_ok h
  cases hx
  exact absurd hcheck2 (by simp [hcheck])

end Midfall.Halo2
