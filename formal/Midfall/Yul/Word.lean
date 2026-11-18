/-
  Midfall.Yul.Word

  THE WORD AND MEMORY LAYER (T3.5, PLAN-V3): Boolean words, `touchMemory` projections, and
  read-over-write for the 32-byte word window. These are the lemmas the `vkLoading` residue asks
  for (docs/plans/V3-evidence/design/prooftech.md section 3 lists "any lemma relating loadWord to
  storeWord, copyInto or copyReturn" and "a touchMemory projection simp set" as the two named gaps,
  each with zero grep hits before this file), and this is the file that carries the named simp set
  `yul_word`.

  WHAT IS HERE.

    * Boolean words (`b2w`): the shapes a `b2w` term can take, stated on the LITERAL forms
      `0#256` / `1#256` that simp actually produces inside a residue. The recorded trap (T.1, and
      prooftech.md:130) is that a lemma stated as `(1 : U256)` does NOT match `1#256`: the two are
      defeq, but simp matches syntax, so the first vkLoading attempt rewrote nothing.
      `Midfall.Yul.WpTac.b2w_eq_zero_iff` already exists at `(0 : U256)`; it is NOT restated here -
      `yul_word` carries both forms so either shape fires.
    * `touchMemory` / `touchMemory2` projections: every `EvmState` field except
      `activeWords` is untouched by a memory touch, and each fact is `rfl`. They are deliberately
      NOT tagged `@[simp]` globally - a projection set of this size, always on, would rewrite
      memory terms in files that were proved without it - they are reachable through
      `simp only [yul_word]`.
    * Read-over-write. `loadWord_storeWord_same` (a word reads back what an mstore wrote) and
      `loadWord_storeWord_disjoint` (a write outside the 32-byte window is invisible to a read) are
      the two cases with content. The OVERLAP case is genuinely undetermined - it depends on the old
      memory and on the stored word together - which is why the registered statement in
      `Midfall/Yul/WpX.lean` keeps that branch as itself, and why no stronger statement is available
      without a side condition the registered statement does not have. The card's falsifier is real:
      `loadWord (storeWord mem p v) (p+1) = v` fails on any memory whose byte at `p+32` is
      nonzero.
    * `loadWord_copyInto` / `loadWord_copyReturn`: a read whose whole window lies inside a copy
      reads the source, reassembled by `wordFrom`.

  HOW THE REASSEMBLY GOES. `loadWord` is a `foldl` over `List.range 32` that shifts left by 8
  and ors in a byte, so a word read is a big-endian reassembly. `reassemble` is that fact for
  `n` bytes: for `v.toNat < 256 ^ n`, folding `byteAt v (n-1-i)` rebuilds `v`. Induction on
  `n`; the step peels the low byte with `byteAt_shiftRight8` and `lowByte_or_rest`. Per the
  card's guidance the byte maps are matched index by index (`foldl_congr`, the
  `List.range`-map technique T.1 recorded) and `simp [storeWord]` is never run wholesale.

  D-P71 / D-P17: no `native_decide` anywhere in this file. Every `decide` is on a closed Bool or
  a closed Nat literal (kernel reduction), and the `#print axioms` probes at the bottom are the
  gate.
-/
import YulSemantics.Dialect.EVMExec
import Midfall.Yul.WordAttr
set_option autoImplicit false

namespace Midfall.Yul.Word
open YulSemantics YulSemantics.EVM

/-! ## 1. Boolean words -/

/-- A Boolean word is the literal zero iff the Boolean is false. -/
theorem b2w_eq_zero_lit (b : Bool) : b2w b = 0#256 ↔ b = false := by
  cases b <;> decide

/-- A Boolean word is the literal `1#256` iff the Boolean is true. -/
theorem b2w_eq_one_lit (b : Bool) : b2w b = 1#256 ↔ b = true := by
  cases b <;> decide

/-- A Boolean word is nonzero iff the Boolean is true. -/
theorem b2w_ne_zero_lit (b : Bool) : b2w b ≠ 0#256 ↔ b = true := by
  cases b <;> decide

/-- The guard shape a residue actually shows: `stepOp` writes `b2w (a = b)`, which elaborates
    to `b2w (decide (a = b))` because `b2w` takes a `Bool`. -/
theorem b2w_decide_eq_one_iff (p : Prop) [Decidable p] : b2w (decide p) = 1#256 ↔ p := by
  by_cases hp : p
  · rw [decide_eq_true hp]
    exact ⟨fun _ => hp, fun _ => rfl⟩
  · rw [decide_eq_false hp]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h hp⟩

/-- The `iszero` form: `stepOp`'s `.iszero` arm is `fun a => b2w (a = 0)`, so a residue
    shows `b2w (decide (a = 0#256))`. -/
theorem b2w_iszero_eq_one (a : U256) : b2w (decide (a = 0#256)) = 1#256 ↔ a = 0#256 :=
  b2w_decide_eq_one_iff _

/-- The `iszero` form, negated: `iszero` is zero exactly when the word is nonzero. -/
theorem b2w_iszero_eq_zero (a : U256) : b2w (decide (a = 0#256)) = 0#256 ↔ a ≠ 0#256 := by
  by_cases h : a = 0#256 <;> simp [h, b2w]

/-- The leading `1#256` of a guard chain is a no-op under `&&&`. -/
theorem one_and_b2w (b : Bool) : (1#256 : U256) &&& b2w b = b2w b := by
  cases b <;> decide

/-- Two Boolean words AND to the word of the AND. -/
theorem b2w_and_b2w (a b : Bool) : b2w a &&& b2w b = b2w (a && b) := by
  cases a <;> cases b <;> decide

/-- The other orientation of `one_and_b2w`. -/
theorem b2w_and_one (b : Bool) : b2w b &&& (1#256 : U256) = b2w b := by
  cases b <;> decide

/-- Two Boolean words OR to the word of the OR. -/
theorem b2w_or_b2w (a b : Bool) : b2w a ||| b2w b = b2w (a || b) := by
  cases a <;> cases b <;> decide

/-! ## 2. `touchMemory` projections -/

/-- A memory touch does not touch memory itself: only `activeWords` moves. -/
theorem touchMemory_memory (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).memory = st.memory := rfl

/-- A memory touch does not touch storage. -/
theorem touchMemory_storage (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).storage = st.storage := rfl

/-- A memory touch does not touch transient storage. -/
theorem touchMemory_transient (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).transient = st.transient := rfl

/-- A memory touch does not touch the environment (calldata, code, balances, ...). -/
theorem touchMemory_env (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).env = st.env := rfl

/-- A memory touch does not touch the return-data buffer. -/
theorem touchMemory_returndata (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).returndata = st.returndata := rfl

/-- A memory touch emits no logs. -/
theorem touchMemory_logs (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).logs = st.logs := rfl

/-- A memory touch records no selfdestruct. -/
theorem touchMemory_selfdestructs (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).selfdestructs = st.selfdestructs := rfl

/-- A memory touch does not halt the frame. -/
theorem touchMemory_halted (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).halted = st.halted := rfl

/-- The one field a memory touch does move, spelled out. -/
theorem touchMemory_activeWords (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).activeWords =
      BitVec.ofNat 256 (activeWordsAfter st.activeWords.toNat offset size) := rfl

/-- `touchMemory2` (the `mcopy` pair) also leaves memory alone. -/
theorem touchMemory2_memory (st : EvmState) (o₁ s₁ o₂ s₂ : Nat) :
    (touchMemory2 st o₁ s₁ o₂ s₂).memory = st.memory := rfl

/-- `touchMemory2` leaves the environment alone. -/
theorem touchMemory2_env (st : EvmState) (o₁ s₁ o₂ s₂ : Nat) :
    (touchMemory2 st o₁ s₁ o₂ s₂).env = st.env := rfl

/-- `touchMemory2` leaves returndata alone. -/
theorem touchMemory2_returndata (st : EvmState) (o₁ s₁ o₂ s₂ : Nat) :
    (touchMemory2 st o₁ s₁ o₂ s₂).returndata = st.returndata := rfl

/-- `touchMemory2` does not halt the frame. -/
theorem touchMemory2_halted (st : EvmState) (o₁ s₁ o₂ s₂ : Nat) :
    (touchMemory2 st o₁ s₁ o₂ s₂).halted = st.halted := rfl

/-- A zero-size touch is the identity on the whole state: the `activeWordsAfter` zero case. -/
theorem touchMemory_zero (st : EvmState) (offset : Nat) : touchMemory st offset 0 = st := by
  simp [touchMemory, activeWordsAfter]

/-! ## 3. Read-over-write -/

/-- Folding over a list whose steps agree elementwise (for every accumulator) on that list's
    elements gives the same result. The engine behind every window lemma below: the two byte maps
    differ only inside the window, so the congruence is restricted to `List.range 32`. -/
theorem foldl_congr {α β : Type} (f g : α → β → α) (l : List β)
    (h : ∀ x ∈ l, ∀ a, f a x = g a x) : ∀ init, List.foldl f init l = List.foldl g init l := by
  induction l with
  | nil => intro init; rfl
  | cons b t ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih (fun x hx a => h x (List.mem_cons_of_mem b hx) a)]
      rw [h b (by simp) init]

private theorem pow8 : (2 : Nat) ^ 8 = 256 := by decide

/-- Dropping the low byte and putting it back: `byteAt` of a shifted word is `byteAt` one index
    further along. -/
theorem byteAt_shiftRight8 (v : U256) (k : Nat) : byteAt (v >>> 8) k = byteAt v (k + 1) := by
  have h : (v >>> 8) >>> (8 * k) = v >>> (8 * (k + 1)) := by
    refine BitVec.eq_of_toNat_eq ?_
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pow8]
    rw [Nat.div_div_eq_div_mul]
    exact congrArg (fun t : Nat => BitVec.toNat v / t)
      (by rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_add]; congr 1; omega)
  show UInt8.ofNat ((v >>> 8) >>> (8 * k)).toNat = UInt8.ofNat (v >>> (8 * (k + 1))).toNat
  rw [h]

/-- The low byte of a word, as a `Nat`. -/
theorem byteAt_zero_toNat (v : U256) : (byteAt v 0).toNat = v.toNat % 256 := by
  show (UInt8.ofNat ((v >>> 0).toNat)).toNat = _
  rw [BitVec.ushiftRight_zero, UInt8.toNat_ofNat', pow8]

/-- The arithmetic fact the reassembly rests on: a word is its top part shifted up by 8 or'd with its
    low byte. `Nat.shiftLeft_add_eq_or_of_lt` is what makes the `|||` an addition. -/
theorem lowByte_or_rest (v : U256) :
    (v >>> 8) <<< 8 ||| BitVec.ofNat 256 (v.toNat % 256) = v := by
  refine BitVec.eq_of_toNat_eq ?_
  have h1 : BitVec.toNat v >>> 8 <<< 8 % 2 ^ 256 = BitVec.toNat v >>> 8 <<< 8 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by
        simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, pow8]
        exact Nat.div_mul_le_self _ _) (BitVec.isLt v))
  have h2 : BitVec.toNat v % 256 % 2 ^ 256 = BitVec.toNat v % 256 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 256))
      (by decide : 256 ≤ 2 ^ 256))
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, h1, h2,
    ← Nat.shiftLeft_add_eq_or_of_lt (b_lt := Nat.mod_lt _ (by decide : 0 < 256))]
  have key : ∀ a : Nat, a >>> 8 <<< 8 + a % 256 = a := by
    intro a
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, pow8]
    rw [Nat.mul_comm (a / 256) 256]
    exact Nat.div_add_mod a 256
  exact key _

/-- **Big-endian reassembly.** If `v` fits in `n` bytes, folding the bytes `byteAt v (n-1-i)` -
    most significant first - rebuilds `v`. -/
theorem reassemble (n : Nat) : ∀ (v : U256), v.toNat < 256 ^ n →
    (List.range n).foldl (fun (acc : U256) i =>
      (acc <<< 8) ||| BitVec.ofNat 256 (byteAt v (n - 1 - i)).toNat) (0 : U256) = v := by
  induction n with
  | zero =>
      intro v hv
      rw [List.range_zero, List.foldl_nil]
      refine BitVec.eq_of_toNat_eq ?_
      have : v.toNat < 1 := by rw [Nat.pow_zero] at hv; exact hv
      have h0 : BitVec.toNat (0 : U256) = 0 := rfl
      omega
  | succ n ih =>
      intro v hv
      have hv' : (v >>> 8).toNat < 256 ^ n := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pow8]
        have := hv
        rw [Nat.pow_add, Nat.pow_one] at this
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr this
      have hidx : ∀ i, i < n → n - 1 - i + 1 = n - i := by
        intro i hi; omega
      have fold_eq : (List.range n).foldl (fun (acc : U256) i =>
            (acc <<< 8) ||| BitVec.ofNat 256 (byteAt v (n - i)).toNat) (0 : U256)
          = (List.range n).foldl (fun (acc : U256) i =>
            (acc <<< 8) ||| BitVec.ofNat 256 (byteAt (v >>> 8) (n - 1 - i)).toNat) (0 : U256) :=
        foldl_congr _ _ _ (fun (i : Nat) (hi : i ∈ List.range n) (acc : U256) =>
          congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat)
            (by have h := byteAt_shiftRight8 v (n - 1 - i)
                rw [hidx i (List.mem_range.mp hi)] at h
                exact h.symm)) _
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.add_sub_cancel_right, Nat.sub_self]
      rw [fold_eq, ih (v >>> 8) hv', byteAt_zero_toNat]
      exact lowByte_or_rest v

/-- Two byte maps that agree on the 32-byte window at `p` load the same word. -/
theorem loadWord_congr (f g : Nat → UInt8) (p : Nat)
    (h : ∀ i, i < 32 → f (p + i) = g (p + i)) : loadWord f p = loadWord g p := by
  unfold loadWord
  refine foldl_congr _ _ _ (fun i hi acc =>
    congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat)
      (h i (List.mem_range.mp hi))) _

/-- **Read back what an mstore wrote.** The word loaded at the address an mstore wrote to IS the
    stored word, whatever the rest of memory was. -/
theorem loadWord_storeWord_same (mem : Nat → UInt8) (p : Nat) (v : U256) :
    loadWord (storeWord mem p v) p = v := by
  have pt : ∀ i ∈ List.range 32, storeWord mem p v (p + i) = byteAt v (31 - i) := by
    intro i hi
    have : i < 32 := List.mem_range.mp hi
    show (if p ≤ p + i ∧ p + i < p + 32 then byteAt v (31 - (p + i - p)) else mem (p + i))
      = byteAt v (31 - i)
    simp [this]
  unfold loadWord
  have hfold : (List.range 32).foldl (fun (acc : U256) i =>
        acc <<< 8 ||| BitVec.ofNat 256 (storeWord mem p v (p + i)).toNat) (0 : U256)
      = (List.range 32).foldl (fun (acc : U256) i =>
        acc <<< 8 ||| BitVec.ofNat 256 (byteAt v (31 - i)).toNat) (0 : U256) :=
    foldl_congr _ _ _ (fun (i : Nat) (hi : i ∈ List.range 32) (acc : U256) =>
      congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat) (pt i hi)) _
  rw [hfold]
  exact reassemble 32 v (by rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide]; exact BitVec.isLt v)

/-- **A write outside the window is invisible to the read.** For disjoint 32-byte windows, loading
    after storing equals loading before. -/
theorem loadWord_storeWord_disjoint (mem : Nat → UInt8) (p q : Nat) (v : U256)
    (h : q + 32 ≤ p ∨ p + 32 ≤ q) : loadWord (storeWord mem p v) q = loadWord mem q := by
  unfold loadWord
  refine foldl_congr _ _ _ (fun (i : Nat) (hi : i ∈ List.range 32) (acc : U256) =>
    congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat) ?_) _
  have : i < 32 := List.mem_range.mp hi
  show (if p ≤ q + i ∧ q + i < p + 32 then byteAt v (31 - (q + i - p)) else mem (q + i)) = mem (q + i)
  have hnot : ¬ (p ≤ q + i ∧ q + i < p + 32) := by
    rcases h with hq | hp
    · omega
    · omega
  rw [ite_eq_right hnot]

/-- A read whose whole 32-byte window lies inside a `copyInto` range reads the source bytes:
    `calldatacopy`/`extcodecopy`/`returndatacopy` followed by `mload`. -/
theorem loadWord_copyInto (mem : Nat → UInt8) (dst src n q : Nat) (data : List UInt8)
    (h : dst ≤ q ∧ q + 32 ≤ dst + n) :
    loadWord (copyInto mem dst src n data) q = wordFrom data (src + (q - dst)) := by
  have pt : ∀ i ∈ List.range 32,
      copyInto mem dst src n data (q + i) = byteFrom data (src + (q - dst) + i) := by
    intro i hi
    have : i < 32 := List.mem_range.mp hi
    show (if dst ≤ q + i ∧ q + i < dst + n then byteFrom data (src + (q + i - dst)) else mem (q + i))
      = byteFrom data (src + (q - dst) + i)
    have hmem : dst ≤ q + i ∧ q + i < dst + n := ⟨by omega, by omega⟩
    rw [ite_eq_left hmem]
    exact congrArg (byteFrom data) (by omega)
  unfold loadWord wordFrom
  rw [foldl_congr _ _ _ (fun (i : Nat) (hi : i ∈ List.range 32) (acc : U256) =>
    congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat) (pt i hi)) _]

/-- A read whose whole window lies inside a `copyReturn` range (a call's return data landing in
    memory) reads the return buffer, zero-padded past its end. -/
theorem loadWord_copyReturn (memory : Nat → UInt8) (dst size q : Nat) (data : List UInt8)
    (h : dst ≤ q ∧ q + 32 ≤ dst + min size data.length) :
    loadWord (copyReturn memory dst size data) q = wordFrom data (q - dst) := by
  have pt : ∀ i ∈ List.range 32,
      copyReturn memory dst size data (q + i) = byteFrom data (q - dst + i) := by
    intro i hi
    have : i < 32 := List.mem_range.mp hi
    show (if dst ≤ q + i ∧ q + i < dst + min size data.length
      then byteFrom data (q + i - dst) else memory (q + i)) = byteFrom data (q - dst + i)
    have hmem : dst ≤ q + i ∧ q + i < dst + min size data.length := ⟨by omega, by omega⟩
    rw [ite_eq_left hmem]
    exact congrArg (byteFrom data) (by omega)
  unfold loadWord wordFrom
  rw [foldl_congr _ _ _ (fun (i : Nat) (hi : i ∈ List.range 32) (acc : U256) =>
    congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat) (pt i hi)) _]

/-- The `mstore` step shape: the state update `stepOp` builds writes `storeWord` and touches
    memory, and its `memory` field is exactly `storeWord`. -/
theorem mstore_step (st : EvmState) (p : Nat) (v : U256) :
    ({ touchMemory st p 32 with memory := storeWord st.memory p v } : EvmState).memory =
      storeWord st.memory p v := rfl

/-- The `mstore`-then-`mload` step pair, on the state update `stepOp` builds. -/
theorem mstore_mload (st : EvmState) (p : Nat) (v : U256) :
    loadWord ({ touchMemory st p 32 with memory := storeWord st.memory p v } : EvmState).memory p = v :=
  loadWord_storeWord_same st.memory p v

end Midfall.Yul.Word

/-- **The named word/memory simp set (T3.5): `yul_word`.** Boolean-word shapes, `touchMemory`
    projections and the read-over-write window lemmas, in one place. Use it as

    ```lean
    simp only [Midfall.Yul.Word.yul_word]
    simp only [Midfall.Yul.Word.yul_word, extra1, extra2]
    ```

    Two rules because a Lean macro list antiquote does not match the empty tail, so the bare form
    needs its own pattern. Nothing here is tagged `@[simp]` globally on purpose: a projection set of
    this size, always on, would rewrite memory terms in files that were proved without it. -/
macro_rules
  | `(tactic| simp only [Midfall.Yul.Word.yul_word]) =>
      `(tactic| simp only [Midfall.Yul.Word.b2w_eq_zero_lit, Midfall.Yul.Word.b2w_eq_one_lit, Midfall.Yul.Word.b2w_ne_zero_lit,
        Midfall.Yul.Word.b2w_decide_eq_one_iff, Midfall.Yul.Word.b2w_iszero_eq_one, Midfall.Yul.Word.b2w_iszero_eq_zero,
        Midfall.Yul.Word.one_and_b2w, Midfall.Yul.Word.b2w_and_b2w, Midfall.Yul.Word.b2w_and_one,
        Midfall.Yul.Word.b2w_or_b2w, Midfall.Yul.Word.touchMemory_memory, Midfall.Yul.Word.touchMemory_storage,
        Midfall.Yul.Word.touchMemory_transient, Midfall.Yul.Word.touchMemory_env, Midfall.Yul.Word.touchMemory_returndata,
        Midfall.Yul.Word.touchMemory_logs, Midfall.Yul.Word.touchMemory_selfdestructs, Midfall.Yul.Word.touchMemory_halted,
        Midfall.Yul.Word.touchMemory_activeWords, Midfall.Yul.Word.touchMemory2_memory, Midfall.Yul.Word.touchMemory2_env,
        Midfall.Yul.Word.touchMemory2_returndata, Midfall.Yul.Word.touchMemory2_halted, Midfall.Yul.Word.loadWord_storeWord_same,
        Midfall.Yul.Word.loadWord_storeWord_disjoint, Midfall.Yul.Word.loadWord_copyInto, Midfall.Yul.Word.loadWord_copyReturn,
        Midfall.Yul.Word.mstore_step, Midfall.Yul.Word.mstore_mload])

macro_rules
  | `(tactic| simp only [Midfall.Yul.Word.yul_word, $fs,*]) =>
      `(tactic| simp only [Midfall.Yul.Word.b2w_eq_zero_lit, Midfall.Yul.Word.b2w_eq_one_lit, Midfall.Yul.Word.b2w_ne_zero_lit,
        Midfall.Yul.Word.b2w_decide_eq_one_iff, Midfall.Yul.Word.b2w_iszero_eq_one, Midfall.Yul.Word.b2w_iszero_eq_zero,
        Midfall.Yul.Word.one_and_b2w, Midfall.Yul.Word.b2w_and_b2w, Midfall.Yul.Word.b2w_and_one,
        Midfall.Yul.Word.b2w_or_b2w, Midfall.Yul.Word.touchMemory_memory, Midfall.Yul.Word.touchMemory_storage,
        Midfall.Yul.Word.touchMemory_transient, Midfall.Yul.Word.touchMemory_env, Midfall.Yul.Word.touchMemory_returndata,
        Midfall.Yul.Word.touchMemory_logs, Midfall.Yul.Word.touchMemory_selfdestructs, Midfall.Yul.Word.touchMemory_halted,
        Midfall.Yul.Word.touchMemory_activeWords, Midfall.Yul.Word.touchMemory2_memory, Midfall.Yul.Word.touchMemory2_env,
        Midfall.Yul.Word.touchMemory2_returndata, Midfall.Yul.Word.touchMemory2_halted, Midfall.Yul.Word.loadWord_storeWord_same,
        Midfall.Yul.Word.loadWord_storeWord_disjoint, Midfall.Yul.Word.loadWord_copyInto, Midfall.Yul.Word.loadWord_copyReturn,
        Midfall.Yul.Word.mstore_step, Midfall.Yul.Word.mstore_mload, $fs,*])

/-! ### `yul_word` as a real simp attribute (ticket WORDATTR)

The SAME 29 lemmas, in the same order, tagged with the attribute registered in
`Midfall/Yul/WordAttr.lean`. That is what lets the set be handed to `simp` in the two positions
the macro pair above cannot reach - at a location, and anywhere but first in the list:

```lean
simp only [Midfall.Yul.Word.yul_word] at h
simp only [extra1, Midfall.Yul.Word.yul_word]
```

ANNOTATION ONLY: no statement and no proof step in this file is changed by this block, and the
list below is the list above. The macro pair stays so T3.5's existing call sites keep elaborating
exactly as they did. -/
attribute [Midfall.Yul.Word.yul_word]
  Midfall.Yul.Word.b2w_eq_zero_lit Midfall.Yul.Word.b2w_eq_one_lit Midfall.Yul.Word.b2w_ne_zero_lit
  Midfall.Yul.Word.b2w_decide_eq_one_iff Midfall.Yul.Word.b2w_iszero_eq_one Midfall.Yul.Word.b2w_iszero_eq_zero
  Midfall.Yul.Word.one_and_b2w Midfall.Yul.Word.b2w_and_b2w Midfall.Yul.Word.b2w_and_one
  Midfall.Yul.Word.b2w_or_b2w Midfall.Yul.Word.touchMemory_memory Midfall.Yul.Word.touchMemory_storage
  Midfall.Yul.Word.touchMemory_transient Midfall.Yul.Word.touchMemory_env Midfall.Yul.Word.touchMemory_returndata
  Midfall.Yul.Word.touchMemory_logs Midfall.Yul.Word.touchMemory_selfdestructs Midfall.Yul.Word.touchMemory_halted
  Midfall.Yul.Word.touchMemory_activeWords Midfall.Yul.Word.touchMemory2_memory Midfall.Yul.Word.touchMemory2_env
  Midfall.Yul.Word.touchMemory2_returndata Midfall.Yul.Word.touchMemory2_halted Midfall.Yul.Word.loadWord_storeWord_same
  Midfall.Yul.Word.loadWord_storeWord_disjoint Midfall.Yul.Word.loadWord_copyInto Midfall.Yul.Word.loadWord_copyReturn
  Midfall.Yul.Word.mstore_step Midfall.Yul.Word.mstore_mload

open Midfall.Yul.Word
#print axioms loadWord_storeWord_same
#print axioms loadWord_storeWord_disjoint
#print axioms loadWord_copyInto
#print axioms loadWord_copyReturn
#print axioms reassemble
