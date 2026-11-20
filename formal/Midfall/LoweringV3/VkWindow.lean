/-
  Midfall.LoweringV3.VkWindow

  **WP A3b gap (i): the bytesAt window lemmas, and the bridges they stand on.**

  'Inv .vk' has two memory clauses and one calldata clause, and the vkLoading block's only write is
  the 'extcodecopy' of statement 2. Nothing in the tree reads a 'bytesAt' window through a
  'copyInto': 'Midfall/Yul/Word.lean' has the WORD version ('loadWord_copyInto') and the byte
  version is reached at the fixture only by 'native_decide', which D-P71 forbids inside
  'lowering_correct''s cone. Two lemmas do it here, sorry-free and generic:

  * a read whose window is DISJOINT from the copy is untouched - that is the g1_identity transfer,
    and it is what 'vkPins.disjoint' ('MemoryPairs.vkPins_disjoint_of_generated') is FOR;
  * a read whose window is INSIDE the copy is the source list's slice - that is the payload clause,
    where the source is the deployed runtime and the offset is 1, the INVALID prefix
    ('runtimeBytes_toList' is that fact as an equation, so the 1 is not a magic number).

  The bridges the statements need are here too, because no existing file states them:
  'wordFrom cd.data.toList i = cdWord cd i' (what 'calldataload' answers IS what the Lean decoder
  reads - gap (ii)'s first step) and the big-endian fold identity it rests on. Section 4 lands the
  five constant-table lookups the clean half reads, at 'ValidV3' (the 'LoweringV2' face takes the
  frozen 'Render.Valid', and 'ValidV3' is a parallel copy that is not defeq with it).

  TOOLCHAIN NOTES, all paid for. 'data' is a reserved word in any file that reaches
  'YulSemantics.Syntax', so no BINDER may be called 'data' (field access 'x.data' is fine).
  'List.take'/'List.drop' take the COUNT FIRST and their '_cons' lemmas have the element and the
  count implicit, so the only explicit argument is the positivity proof. 'List.congr' and
  'List.map_congr' do not exist here: 'map_congr_of' is the three-line replacement, and it must
  range over 'List.range m' rather than extend functionally, because the 'copyInto' guard is only
  decidable for an index below the read length.

  D-P71: generic in everything; no fixture, no 'native_decide', nothing added to a row, a bundle,
  the root or 'ValidV3'.
-/
import Midfall.LoweringV2.Stages
import Midfall.LoweringV3.Statements
import Midfall.LoweringV2.Consts
import Midfall.Yul.Word
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.LoweringV3.VkWindow

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. LIST PLUMBING: getD, drop, take -/

/-- Mapping two functions that agree on every element of a list gives the same list. Core states
    neither 'List.congr' nor 'List.map_congr' at this toolchain. -/
theorem map_congr_of {β : Type} (l : List Nat) (f g : Nat → β)
    (h : ∀ x ∈ l, f x = g x) : List.map f l = List.map g l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

/-- 'bs.getD (k + i) 0 = (bs.drop k).getD i 0': a shifted index into a list is an index into its
    drop. -/
theorem getD_drop (bs : List UInt8) (k : Nat) : ∀ i,
    bs.getD (k + i) 0 = (bs.drop k).getD i 0 := by
  intro i
  induction k generalizing bs i with
  | zero => simp
  | succ k ih =>
      cases bs with
      | nil => simp [List.drop, List.getD]
      | cons a rest =>
          rw [List.drop_cons (Nat.succ_pos k), Nat.succ_eq_add_one, Nat.add_sub_cancel,
            Nat.add_right_comm, List.getD_cons_succ]
          exact ih rest i

/-- 'byteFrom' at an offset is the head of the drop: the pointwise form of the same fact. -/
theorem byteFrom_drop (l : List UInt8) (k : Nat) :
    byteFrom l k = (l.drop k).head?.getD 0 := by
  unfold byteFrom
  induction k generalizing l with
  | zero => cases l <;> simp [List.getD, List.head?]
  | succ k ih =>
      cases l with
      | nil => simp [List.drop, List.getD, List.head?]
      | cons a rest =>
          rw [List.drop_cons (Nat.succ_pos k), Nat.succ_eq_add_one, Nat.add_sub_cancel,
            List.getD_cons_succ]
          exact ih rest

/-- Two lists are equal when they have the same length and the same zero-padded reads. The
    extensionality that goes through 'get' is not available at this toolchain; 'getD' is what
    'byteFrom' is made of, so this is the right face of it. -/
theorem list_eq_of_getD : ∀ (l₁ l₂ : List UInt8), l₁.length = l₂.length →
    (∀ i, l₁.getD i 0 = l₂.getD i 0) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hlen _
      cases l₂ with
      | nil => rfl
      | cons a t => exact absurd hlen (by simp)
  | cons a s ih =>
      intro l₂ hlen h
      cases l₂ with
      | nil => exact absurd hlen (by simp)
      | cons b t =>
          have hab : a = b := by simpa using h 0
          subst hab
          have hst : s = t := ih t (by simpa using hlen) (by
            intro i
            simpa using h (i + 1))
          subst hst
          rfl

/-- The first 'm' zero-padded reads of a list ARE its 'take m', when there are that many. -/
theorem range_map_getD_take (l : List UInt8) : ∀ m, m ≤ l.length →
    (List.range m).map (fun i => l.getD i 0) = l.take m := by
  induction l with
  | nil =>
      intro m h
      cases m with
      | zero => rfl
      | succ m => exact absurd h (by simp)
  | cons a s ih =>
      intro m h
      cases m with
      | zero => simp
      | succ m =>
          have h' : m ≤ s.length := by
            have := h
            simp only [List.length_cons] at this
            omega
          have hf : (fun i => (a :: s).getD (i + 1) 0) = (fun i => s.getD i 0) := by
            funext i
            exact List.getD_cons_succ
          rw [List.range_succ_eq_map, List.map_cons, List.map_map]
          have hf2 : (fun i => (a :: s).getD i 0) ∘ Nat.succ = (fun i => s.getD i 0) := by
            funext i
            show (a :: s).getD (Nat.succ i) 0 = s.getD i 0
            rw [Nat.succ_eq_add_one, List.getD_cons_succ]
          rw [hf2, ih m h', List.take_cons (Nat.succ_pos m), List.getD_cons_zero,
            Nat.succ_eq_add_one, Nat.add_sub_cancel]

/-- A run of 'byteFrom' over a range is a slice: the engine of both window lemmas. -/
theorem map_byteFrom_take (bs : List UInt8) (k m : Nat) (h : k + m ≤ bs.length) :
    (List.range m).map (fun i => byteFrom bs (k + i)) = (bs.drop k).take m := by
  have hpt : (fun i => byteFrom bs (k + i)) = (fun i => (bs.drop k).getD i 0) := by
    funext i
    unfold byteFrom
    exact getD_drop bs k i
  rw [hpt]
  exact range_map_getD_take (bs.drop k) m (by
    have := h
    simp only [List.length_drop] at this ⊢
    omega)

/-! ## 2. THE TWO bytesAt WINDOW LEMMAS -/

/-- **A READ OUTSIDE THE COPY IS UNTOUCHED.** The g1_identity transfer: the copy the VK block
    performs cannot disturb the window 'Inv' pins to zero, provided the two windows are disjoint -
    which is exactly 'vkPins.disjoint', i.e. exactly what 'MemoryPairs' derives from 'generated'. -/
theorem readBytes_copyInto_disjoint (mem : Nat → UInt8) (dst src n p m : Nat) (bs : List UInt8)
    (h : dst + n ≤ p ∨ p + m ≤ dst) :
    readBytes (copyInto mem dst src n bs) p m = readBytes mem p m := by
  unfold readBytes
  refine map_congr_of (List.range m) (fun i => copyInto mem dst src n bs (p + i))
    (fun i => mem (p + i)) (fun i hi => ?_)
  have : i < m := List.mem_range.mp hi
  show (if dst ≤ p + i ∧ p + i < dst + n then byteFrom bs (src + (p + i - dst)) else mem (p + i))
    = mem (p + i)
  rw [if_neg]
  rcases h with hq | hp
  · omega
  · omega

/-- **A READ INSIDE THE COPY IS THE SOURCE SLICE.** The payload transfer. -/
theorem readBytes_copyInto_window (mem : Nat → UInt8) (dst src n p m : Nat) (bs : List UInt8)
    (h1 : dst ≤ p) (h2 : p + m ≤ dst + n) (h3 : src + (p - dst) + m ≤ bs.length) :
    readBytes (copyInto mem dst src n bs) p m = (bs.drop (src + (p - dst))).take m := by
  unfold readBytes
  have h1 : (List.range m).map (fun i => copyInto mem dst src n bs (p + i))
      = (List.range m).map (fun i => byteFrom bs (src + (p - dst) + i)) := by
    refine map_congr_of (List.range m) (fun i => copyInto mem dst src n bs (p + i))
      (fun i => byteFrom bs (src + (p - dst) + i)) (fun i hi => ?_)
    have : i < m := List.mem_range.mp hi
    show (if dst ≤ p + i ∧ p + i < dst + n then byteFrom bs (src + (p + i - dst))
        else mem (p + i)) = byteFrom bs (src + (p - dst) + i)
    rw [if_pos ⟨by omega, by omega⟩]
    congr 1
    omega
  rw [h1, map_byteFrom_take]
  exact h3

/-- The 'bytesAt' face of the two window lemmas. -/
theorem bytesAt_copyInto_disjoint (st : EvmState) (dst src n p m : Nat) (bs : List UInt8)
    (h : dst + n ≤ p ∨ p + m ≤ dst) :
    bytesAt { st with memory := copyInto st.memory dst src n bs } p m = bytesAt st p m := by
  show ByteArray.mk (readBytes (copyInto st.memory dst src n bs) p m).toArray =
      ByteArray.mk (readBytes st.memory p m).toArray
  rw [readBytes_copyInto_disjoint st.memory dst src n p m bs h]

theorem bytesAt_copyInto_window (st : EvmState) (dst src n p m : Nat) (bs : List UInt8)
    (h1 : dst ≤ p) (h2 : p + m ≤ dst + n) (h3 : src + (p - dst) + m ≤ bs.length) :
    bytesAt { st with memory := copyInto st.memory dst src n bs } p m =
      ByteArray.mk ((bs.drop (src + (p - dst))).take m).toArray := by
  show ByteArray.mk (readBytes (copyInto st.memory dst src n bs) p m).toArray = _
  rw [readBytes_copyInto_window st.memory dst src n p m bs h1 h2 h3]

/-! ### Bytes and lists -/

private theorem array_toList_toArray {α : Type} (a : Array α) : a.toList.toArray = a := by
  cases a with
  | mk l => simp

private theorem bytes_eq_of_toList {x y : Bytes} (h : x.data.toList = y.data.toList) : x = y := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  exact h

theorem bytes_mk_toList (b : Bytes) : ByteArray.mk b.data.toList.toArray = b := by
  cases b with
  | mk arr => rw [array_toList_toArray]

/-- 'runtimeBytes' is the 0xfe prefix and then the payload, AS A LIST: the copy's source offset of 1
    is not a magic number, it is this equation. -/
theorem runtimeBytes_toList (vk : Halo2VerifyingKey) :
    vk.runtimeBytes.data.toList = Nat.toUInt8 vkRuntimePrefix :: vk.bytes.data.toList := by
  show ((ByteArray.push Bytes.empty (Nat.toUInt8 vkRuntimePrefix)).append vk.bytes).data.toList = _
  rw [ByteArray.toList_data_append']
  have h0 : (Bytes.empty : Bytes).data.toList = [] := rfl
  have hp : (ByteArray.push Bytes.empty (Nat.toUInt8 vkRuntimePrefix)).data.toList
      = [Nat.toUInt8 vkRuntimePrefix] := by
    rw [ByteArray.push]
    show (Bytes.empty.data.push (Nat.toUInt8 vkRuntimePrefix)).toList = _
    rw [Array.toList_push, h0, List.nil_append]
  rw [hp, List.singleton_append]

theorem runtimeBytes_length (vk : Halo2VerifyingKey) :
    vk.runtimeBytes.data.toList.length = vk.len + 1 := by
  have hb : vk.bytes.data.toList.length = vk.bytes.size :=
    Array.size_eq_length_toList (xs := vk.bytes.data)
  rw [runtimeBytes_toList, List.length_cons, hb, Halo2VerifyingKey.bytes_size]

/-- **THE COPY'S PAYLOAD.** Dropping the INVALID prefix and taking 'vk.len' bytes is the payload
    image 'Inv .vk' demands. -/
theorem runtimeBytes_drop_one_take (vk : Halo2VerifyingKey) :
    (vk.runtimeBytes.data.toList.drop 1).take vk.len = vk.bytes.data.toList := by
  have h1 : vk.runtimeBytes.data.toList.drop 1 = vk.bytes.data.toList := by
    rw [runtimeBytes_toList]
    exact List.drop_cons (Nat.one_pos)
  rw [h1]
  have hb : vk.bytes.data.toList.length = vk.bytes.size :=
    Array.size_eq_length_toList (xs := vk.bytes.data)
  rw [show vk.len = vk.bytes.data.toList.length from by
        rw [← Halo2VerifyingKey.bytes_size, ← hb], List.take_length]

/-! ## 3. THE BIG-ENDIAN FOLD, AND wordFrom = cdWord -/

/-- One big-endian step in the Nat model: shifting up by a byte and OR-ing a byte in is ADDING,
    modulo the word. The '|||' becomes a '+' because the shifted part is a multiple of 256 and the
    byte is below 256. -/
private theorem nat_or_byte (A y : Nat) (hy : y < 256) :
    (A * 256 % 2 ^ 256) ||| y = (A * 256 + y) % 2 ^ 256 := by
  have hd : 256 ∣ A * 256 % 2 ^ 256 := by
    have hdiv : 256 ∣ A * 256 := ⟨A, by ring⟩
    have h2 : 256 ∣ 2 ^ 256 := by decide
    exact (Nat.dvd_mod_iff h2).mpr hdiv
  obtain ⟨s, hs0⟩ := hd
  -- hs0 : A * 256 % 2 ^ 256 = 256 * s, the shape 'dvd' hands back.
  have h2 : 2 ^ 256 = 256 * 2 ^ 248 := by decide
  have h7 : s < 2 ^ 248 := by
    have h6 : 256 * s < 256 * 2 ^ 248 := by
      rw [← h2, ← hs0]
      exact Nat.mod_lt _ (by decide : 0 < 2 ^ 256)
    exact Nat.lt_of_mul_lt_mul_left h6
  have hs : A * 256 % 2 ^ 256 = s * 256 := by
    rw [hs0]
    ring
  have hlt : s * 256 + y < 2 ^ 256 := by
    have h8 : s + 1 ≤ 2 ^ 248 := Nat.lt_iff_add_one_le.mp h7
    have h9 : 256 * (s + 1) ≤ 256 * 2 ^ 248 := Nat.mul_le_mul_left _ h8
    have h10 : 256 * (s + 1) = s * 256 + 256 := by ring
    have h11 : s * 256 + 256 ≤ 2 ^ 256 := by
      rwa [h10, ← h2] at h9
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hy _) h11
  have hsh : s * 256 = s <<< 8 := by
    show s * 2 ^ 8 = s <<< 8
    rw [Nat.shiftLeft_eq]
  have hor : (s * 256) ||| y = s * 256 + y := by
    rw [hsh]
    exact (Nat.shiftLeft_add_eq_or_of_lt (b_lt := hy) (a := s)).symm
  have hy' : y % 2 ^ 256 = y :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy (by decide : 256 ≤ 2 ^ 256))
  have hsum : (A * 256 + y) % 2 ^ 256 = s * 256 + y := by
    rw [Nat.add_mod, hs, hy', Nat.mod_eq_of_lt hlt]
  rw [hs, hor, hsum]

/-- One big-endian step at the word level. -/
theorem be_step (X y : Nat) (hy : y < 256) :
    (BitVec.ofNat 256 X <<< 8) ||| BitVec.ofNat 256 y = BitVec.ofNat 256 (X * 256 + y) := by
  apply BitVec.eq_of_toNat_eq
  have hy' : y % 2 ^ 256 = y :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy (by decide : 256 ≤ 2 ^ 256))
  have hsl : (BitVec.ofNat 256 X <<< 8).toNat = X * 256 % 2 ^ 256 := by
    show (BitVec.ofNat 256 X <<< 8).toNat = X * 2 ^ 8 % 2 ^ 256
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have h : X * 2 ^ 8 % 2 ^ 256 = X % 2 ^ 256 * 2 ^ 8 % 2 ^ 256 := by
      rw [Nat.mul_mod, Nat.mod_eq_of_lt (by decide : 2 ^ 8 < 2 ^ 256)]
    rw [h]
  rw [BitVec.toNat_or, hsl, BitVec.toNat_ofNat, hy', nat_or_byte X y hy,
    BitVec.toNat_ofNat]

/-- The fold identity: a big-endian fold of bytes is the Nat fold, taken modulo the word. -/
theorem fold_be_eq (b : Nat → Nat) (hb : ∀ i, b i < 256) :
    ∀ (l : List Nat) (n : Nat),
      (l.foldl (fun (acc : U256) x => acc <<< 8 ||| BitVec.ofNat 256 (b x)) (BitVec.ofNat 256 n)) =
        BitVec.ofNat 256 (l.foldl (fun (acc : Nat) x => acc * 256 + b x) n) := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons a t ih =>
      intro n
      rw [List.foldl_cons, List.foldl_cons, be_step n (b a) (hb a), ih]

/-- **THE BRIDGE GAP (ii) STANDS ON:** what 'calldataload' answers IS what the Lean decoder reads.
    No existing file states it: 'cdWord' folds in Nat and 'wordFrom' folds in U256. -/
theorem wordFrom_cdWord (cd : Bytes) (i : Nat) : wordFrom cd.data.toList i = cdWord cd i := by
  unfold wordFrom cdWord
  have key (o : Option UInt8) : (o.getD 0).toNat = (o.map UInt8.toNat).getD 0 := by
    cases o <;> rfl
  have hb : ∀ x : Nat, ((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0 < 256 := by
    intro x
    cases h : (cd.data.toList.drop (i + x)).head? with
    | none => simp [h]
    | some u =>
        have hu := UInt8.toNat_lt_size u
        simpa using hu
  have hpt : ∀ x ∈ List.range 32,
      (byteFrom cd.data.toList (i + x)).toNat =
        ((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0 := by
    intro x _
    rw [byteFrom_drop, key]
  have h1 : (List.range 32).foldl
        (fun (acc : U256) x => acc <<< 8 ||| BitVec.ofNat 256 (byteFrom cd.data.toList (i + x)).toNat)
        0
      = (List.range 32).foldl
          (fun (acc : U256) x =>
            acc <<< 8 ||| BitVec.ofNat 256
              (((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0)) 0 := by
    refine Midfall.Yul.Word.foldl_congr
      (fun (acc : U256) (x : Nat) =>
        acc <<< 8 ||| BitVec.ofNat 256 (byteFrom cd.data.toList (i + x)).toNat)
      (fun (acc : U256) (x : Nat) =>
        acc <<< 8 ||| BitVec.ofNat 256
          (((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0))
      (List.range 32) (fun x hx acc =>
        congrArg (fun y : Nat => acc <<< 8 ||| BitVec.ofNat 256 y) (hpt x hx)) _
  have h0 : (0 : U256) = BitVec.ofNat 256 0 := rfl
  have h2 : (List.range 32).foldl
          (fun (acc : U256) x =>
            acc <<< 8 ||| BitVec.ofNat 256
              (((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0)) 0
      = BitVec.ofNat 256 ((List.range 32).foldl
          (fun (acc : Nat) x =>
            acc * 256 + ((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0) 0) := by
    rw [h0, fold_be_eq
      (fun x => ((cd.data.toList.drop (i + x)).head?.map UInt8.toNat).getD 0) hb
      (List.range 32) 0]
  rw [h1, h2]

/-! ## 4. THE CONSTANT TABLE AT ValidV3 -/

/-- The generic transfer: at a 'ValidV3' render a lookup in the table the program READS is a lookup
    in the table the plan view SAYS. 'LoweringV2' has the 'Render.Valid' face of this and 'ValidV3'
    is a parallel copy that is not defeq with it, so the row needs this one. -/
theorem consts_lookup_of_validV3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) (name : String)
    (v : Nat) (h : (Midfall.LoweringV3.expectedConsts R.pv R.model).lookup name = some v) :
    R.consts.lookup name = some v := by
  show (constTableOf R.model).lookup name = some v
  rw [Midfall.LoweringV3.lookup_expectedConsts_of_programOkB
    (Midfall.LoweringV3.programOkB_of_valid hR), h]

theorem expectedConsts_lookup_vkWindow (pv : PlanView) (m : Model) :
    (Midfall.LoweringV3.expectedConsts pv m).lookup "VK_MPTR" = some (cAddr pv.memory.vkMptr) ∧
    (Midfall.LoweringV3.expectedConsts pv m).lookup "PROOF_LEN_CPTR" =
      some (pv.proofLayout.proofCptr - 32) ∧
    (Midfall.LoweringV3.expectedConsts pv m).lookup "INSTANCE_CPTR" =
      some (pv.proofLayout.proofEnd + 32) ∧
    (Midfall.LoweringV3.expectedConsts pv m).lookup "NUM_INSTANCE_CPTR" =
      some pv.proofLayout.proofEnd := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup]

theorem expectedConsts_lookup_payload (pv : PlanView) (m : Model) (h : vkCodehashArm m) :
    (Midfall.LoweringV3.expectedConsts pv m).lookup "EXPECTED_VK_PAYLOAD_LENGTH" =
      some pv.vk.len := by
  obtain ⟨x, hx⟩ := h
  cases h2 : m.quotientExternal <;> cases h3 : m.expectedQuotientCodehash <;>
    cases h4 : m.expectedHasAccumulator <;>
      simp [Midfall.LoweringV3.expectedConsts, hx, h2, h3, h4, List.lookup]

/-- The five table values the clean half reads, at a 'ValidV3' render. -/
theorem vkTableV3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) (hcode : vkCodehashArm R.model) :
    R.consts.lookup "VK_MPTR" = some (ptrAddr R.pv.memory.vkMptr) ∧
      R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some R.pv.vk.len ∧
      R.consts.lookup "PROOF_LEN_CPTR" = some (R.pv.proofLayout.proofCptr - 32) ∧
      R.consts.lookup "NUM_INSTANCE_CPTR" = some R.pv.proofLayout.proofEnd ∧
      R.consts.lookup "INSTANCE_CPTR" = some (R.pv.proofLayout.proofEnd + 32) := by
  have hvk := consts_lookup_of_validV3 hR "VK_MPTR" (cAddr R.pv.memory.vkMptr)
    (expectedConsts_lookup_vkWindow R.pv R.model).1
  have hpl := consts_lookup_of_validV3 hR "EXPECTED_VK_PAYLOAD_LENGTH" R.pv.vk.len
    (expectedConsts_lookup_payload R.pv R.model hcode)
  have h1 := consts_lookup_of_validV3 hR "PROOF_LEN_CPTR" (R.pv.proofLayout.proofCptr - 32)
    ((expectedConsts_lookup_vkWindow R.pv R.model).2.1)
  have h2 := consts_lookup_of_validV3 hR "NUM_INSTANCE_CPTR" R.pv.proofLayout.proofEnd
    ((expectedConsts_lookup_vkWindow R.pv R.model).2.2.2)
  have h3 := consts_lookup_of_validV3 hR "INSTANCE_CPTR" (R.pv.proofLayout.proofEnd + 32)
    ((expectedConsts_lookup_vkWindow R.pv R.model).2.2.1)
  exact ⟨hvk, hpl, h1, h2, h3⟩

end Midfall.LoweringV3.VkWindow

/-! ## 5. AXIOMS AND CONE -/

#print axioms Midfall.LoweringV3.VkWindow.readBytes_copyInto_disjoint
#print axioms Midfall.LoweringV3.VkWindow.readBytes_copyInto_window
#print axioms Midfall.LoweringV3.VkWindow.bytesAt_copyInto_disjoint
#print axioms Midfall.LoweringV3.VkWindow.bytesAt_copyInto_window
#print axioms Midfall.LoweringV3.VkWindow.runtimeBytes_drop_one_take
#print axioms Midfall.LoweringV3.VkWindow.wordFrom_cdWord
#print axioms Midfall.LoweringV3.VkWindow.vkTableV3
#cone_sorries Midfall.LoweringV3.VkWindow.vkTableV3