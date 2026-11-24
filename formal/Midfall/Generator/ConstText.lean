-- |
-- Midfall.Generator.ConstText
--
-- Character-level facts about the constant renderer's interpolations:
-- `toString` on a Nat is decimal digits, `hexFilter`/`hexPaddedFilter` are
-- `0x` plus lowercase hex, and `printPtr` on a numeric `Value` is `hexFilter`
-- of its non-negative value.
--
-- These are the general lemmas CERT.6's `constLinesLiteral` needs. The
-- remaining generic step is line-splitting the 90-line `renderConstants`
-- template; the concrete F1/poseidon gate is in
-- `Midfall/Instances/ConstsCert6.lean`.
import Midfall.Generator.VerifierPartials
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic
set_option autoImplicit false
open Midfall.Generator
namespace Midfall.Generator.ConstText

/-- Lowercase hex digit or decimal digit, the character class
    `constLinesLiteral` accepts after an optional `0x`. -/
def HexChar (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

theorem digitChar_decimal (n : Nat) (h : n < 10) : (Nat.digitChar n).isDigit = true := by
  interval_cases n <;> rfl

theorem digitChar_hex (n : Nat) (h : n < 16) : HexChar (Nat.digitChar n) = true := by
  interval_cases n <;> rfl

/-- The `Nat.toDigitsCore` step. The true branch's `n % base` is `n` because
    `n / base = 0` and `base > 0`. -/
theorem toDigitsCore_succ (base f n : Nat) (acc : List Char) (hb : 0 < base) :
    Nat.toDigitsCore base (f + 1) n acc =
      if n / base = 0 then [Nat.digitChar n] ++ acc
      else Nat.toDigitsCore base f (n / base) ((n % base).digitChar :: acc) := by
  simp only [Nat.toDigitsCore]
  split
  · rename_i hdiv
    have hn : n < base := Nat.lt_of_div_eq_zero hb hdiv
    rw [Nat.mod_eq_of_lt hn]
    rfl
  · rfl

/-- Every character of `Nat.toDigitsCore` is the digit character of a value
    below the base, provided the accumulator already has that property. -/
theorem toDigitsCore_chars {base : Nat} (hb : 1 < base) (P : Char → Bool)
    (hdigit : ∀ d, d < base → P (Nat.digitChar d) = true) :
    ∀ (f n : Nat) (acc : List Char), (∀ c ∈ acc, P c = true) →
      ∀ c ∈ Nat.toDigitsCore base f n acc, P c = true := by
  intro f
  induction f with
  | zero =>
      intro n acc hacc c hc
      simpa [Nat.toDigitsCore] using hacc c hc
  | succ f ih =>
      intro n acc hacc c hc
      rw [toDigitsCore_succ base f n acc (by omega)] at hc
      split at hc
      · rename_i hdiv
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with rfl | hc
        · have hn : n < base := Nat.lt_of_div_eq_zero (by omega) hdiv
          exact hdigit n hn
        · exact hacc c hc
      · apply ih (n / base) ((n % base).digitChar :: acc)
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hdigit (n % base) (Nat.mod_lt _ (by omega))
          · exact hacc x hx
        · exact hc

/-- Every character of `Nat.toDigits base n` is a digit below `base`. -/
theorem toDigits_chars {base : Nat} (hb : 1 < base) (P : Char → Bool)
    (hdigit : ∀ d, d < base → P (Nat.digitChar d) = true) (n : Nat) :
    ∀ c ∈ Nat.toDigits base n, P c = true := by
  unfold Nat.toDigits
  exact toDigitsCore_chars hb P hdigit (n + 1) n [] (by simp)

/-- `toString n` is decimal digits. -/
theorem toString_chars (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  have h := toDigits_chars (base := 10) (by norm_num) (fun c => c.isDigit)
    (fun d hd => digitChar_decimal d hd) n
  show ∀ c ∈ (Nat.repr n).toList, c.isDigit = true
  simpa [Nat.repr] using h

/-- `hexDigits n` is lowercase hex digits. -/
theorem hexDigits_chars (n : Nat) :
    ∀ c ∈ (hexDigits n).toList, HexChar c = true := by
  have h := toDigits_chars (base := 16) (by norm_num) HexChar
    (fun d hd => digitChar_hex d hd) n
  simpa [hexDigits] using h

/-- The body of `hexFilter` starts after `0x`. -/
theorem hexDigits_ne_nil (n : Nat) : hexDigits n ≠ "" := by
  simpa [hexDigits] using (Nat.toDigits_ne_nil (b := 16) (n := n))

theorem drop_two_hex_copy (s : String) : (("0x" ++ s).drop 2).copy = s := by
  apply String.ext
  simp [String.toList_copy_drop, String.toList_append]

theorem drop_two_hex0_copy (s : String) : (("0x0" ++ s).drop 2).copy = "0" ++ s := by
  apply String.ext
  simp [String.toList_copy_drop, String.toList_append]

theorem hexFilter_body_eq (n : Nat) :
    ((hexFilter n).drop 2).toString =
      if ((hexDigits n).length % 2 == 1) = true then "0" ++ hexDigits n
      else hexDigits n := by
  unfold hexFilter
  by_cases h : ((hexDigits n).length % 2 == 1) = true
  · simp [h, drop_two_hex0_copy]
  · simp [h, drop_two_hex_copy]

theorem hexFilter_starts (n : Nat) : (hexFilter n).startsWith "0x" = true := by
  unfold hexFilter
  by_cases h : ((hexDigits n).length % 2 == 1) = true <;> simp [h]

theorem hexFilter_body_nonempty (n : Nat) : ((hexFilter n).drop 2).toString ≠ "" := by
  rw [hexFilter_body_eq]
  by_cases h : ((hexDigits n).length % 2 == 1) = true
  · simp [h]
  · simp [h, hexDigits_ne_nil]

theorem hexFilter_body_chars (n : Nat) :
    ∀ c ∈ (((hexFilter n).drop 2).toString).toList, HexChar c = true := by
  rw [hexFilter_body_eq]
  by_cases h : ((hexDigits n).length % 2 == 1) = true
  · intro c hc
    simp only [h, if_true, String.toList_append, String.toList_singleton,
      List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · have hc0 : c = '0' := by simpa using hc
      subst hc0
      rfl
    · exact hexDigits_chars n c hc
  · intro c hc
    simp only [h, if_false] at hc
    exact hexDigits_chars n c hc

theorem padLeft_length (pad : Nat) (c : Char) (s : String) :
    (padLeft pad c s).length = max pad s.length := by
  unfold padLeft
  rw [String.length_append, String.length_ofList, List.length_replicate]
  omega

theorem padLeft_ne_nil (pad : Nat) (c : Char) (s : String) (hp : 0 < pad) :
    padLeft pad c s ≠ "" := by
  intro hnil
  have hlen := congrArg String.length hnil
  rw [padLeft_length] at hlen
  simp at hlen
  omega

theorem padLeft_chars (pad : Nat) (c : Char) (s : String) (hc : HexChar c = true)
    (hs : ∀ x ∈ s.toList, HexChar x = true) :
    ∀ x ∈ (padLeft pad c s).toList, HexChar x = true := by
  unfold padLeft
  intro x hx
  simp only [String.toList_append, List.mem_append, String.toList_ofList,
    List.mem_replicate] at hx
  rcases hx with hx | hx
  · rcases hx with ⟨_, rfl⟩
    exact hc
  · exact hs x hx

theorem hexPaddedFilter_body_eq (pad n : Nat) :
    ((hexPaddedFilter pad n).drop 2).toString =
      if (("0x" ++ padLeft pad '0' (hexDigits n)) == "0x0") = true then
        String.ofList (List.replicate pad '0')
      else padLeft pad '0' (hexDigits n) := by
  unfold hexPaddedFilter
  by_cases h : (("0x" ++ padLeft pad '0' (hexDigits n)) == "0x0") = true
  · simp [h, String.Slice.toString, drop_two_hex_copy]
  · simp [h, String.Slice.toString, drop_two_hex_copy]

theorem hexPaddedFilter_starts (pad n : Nat) :
    (hexPaddedFilter pad n).startsWith "0x" = true := by
  unfold hexPaddedFilter
  by_cases h : (("0x" ++ padLeft pad '0' (hexDigits n)) == "0x0") = true <;> simp [h]

theorem hexPaddedFilter_body_nonempty (pad n : Nat) (hp : 0 < pad) :
    ((hexPaddedFilter pad n).drop 2).toString ≠ "" := by
  rw [hexPaddedFilter_body_eq]
  by_cases h : (("0x" ++ padLeft pad '0' (hexDigits n)) == "0x0") = true
  · intro hnil
    have hlen := congrArg String.length hnil
    simp [h] at hlen
    omega
  · rw [if_neg h]
    exact padLeft_ne_nil pad '0' (hexDigits n) hp

theorem hexPaddedFilter_body_chars (pad n : Nat) :
    ∀ c ∈ (((hexPaddedFilter pad n).drop 2).toString).toList, HexChar c = true := by
  rw [hexPaddedFilter_body_eq]
  by_cases h : (("0x" ++ padLeft pad '0' (hexDigits n)) == "0x0") = true
  · intro c hc
    simp only [h, if_true] at hc
    have hmem : c ∈ List.replicate pad '0' := by simpa using hc
    rcases (by simpa using hmem : pad ≠ 0 ∧ c = '0') with ⟨_, rfl⟩
    rfl
  · rw [if_neg h]
    exact padLeft_chars pad '0' (hexDigits n) (by rfl) (hexDigits_chars n)

/-- A non-negative `Value.integer` renders as `hexFilter` of its `Nat` value. -/
theorem printPtr_integer_nonneg (i : Int) (h : 0 ≤ i) :
    printPtr (Value.integer i) = hexFilter i.toNat := by
  simp only [printPtr, printValue, fmtHex]
  rw [if_pos h, if_neg (by omega : ¬ i < 0)]

/-- `valueFromNat n` renders as `hexFilter n`. -/
theorem printPtr_valueFromNat (n : Nat) :
    printPtr (valueFromNat n) = hexFilter n := by
  unfold valueFromNat
  rw [printPtr_integer_nonneg]
  · simp
  · simp

/-- Word-addressed pointer arithmetic: `ptrMemory (valueFromNat n) + k` renders
    as `hexFilter (n + k * wordBytes)`. -/
theorem printPtr_memory_add (n k : Nat) :
    printPtr ((Ptr.add (ptrMemory (valueFromNat n)) k).value) =
      hexFilter (n + k * wordBytes) := by
  simp only [Ptr.add, Value.add, ptrMemory, valueFromNat]
  rw [printPtr_integer_nonneg _ (by
    change (0 : Int) ≤ (n : Int) + (k : Int) * (wordBytes : Int)
    positivity)]
  congr 1

/-- Word-addressed calldata subtraction: when `k * wordBytes ≤ n`,
    `ptrCalldata (valueFromNat n) - k` renders as `hexFilter (n - k * wordBytes)`. -/
theorem printPtr_calldata_sub (n k : Nat) (h : k * wordBytes ≤ n) :
    printPtr ((Ptr.sub (ptrCalldata (valueFromNat n)) k).value) =
      hexFilter (n - k * wordBytes) := by
  simp only [Ptr.sub, Value.sub, ptrCalldata, valueFromNat]
  rw [printPtr_integer_nonneg _ (by
    rw [← Int.natCast_mul]
    change (0 : Int) ≤ (n : Int) - ((k * wordBytes : Nat) : Int)
    exact sub_nonneg.mpr (by exact_mod_cast h))]
  congr 1
  have hk : ((k * wordBytes : Nat) : Int) = (k : Int) * (wordBytes : Int) := by
    push_cast
    ring
  have hsub : (Int.ofNat n - (k : Int) * (wordBytes : Int)) =
      ((n - k * wordBytes : Nat) : Int) := by
    show (n : Int) - (k : Int) * (wordBytes : Int) = _
    rw [← hk, Int.ofNat_sub h]
  rw [hsub, Int.toNat_natCast]

end Midfall.Generator.ConstText
