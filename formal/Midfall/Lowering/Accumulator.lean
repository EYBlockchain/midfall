-- |
-- Midfall.Lowering.Accumulator
--
-- P-SE stage 2 (docs/plans/P-SE-stage2.md, file row 2; PLAN
-- P-SE-semantic-equivalence.md section F and index item 6; design1.md M5-3,
-- M5-4, M5-5, M5-6).
--
-- WHAT THIS FILE IS FOR. This is the layer the headline lowering theorems decode
-- the accumulator through: the normalised instance words (accWords), the
-- contract-convention relabelling (negateByTable), the two round trips
-- (decodeAcc_encode and its point-pair sibling), the S5 batching algebra
-- (batched_complete, batched_atMostOneRoot), the check-level pairing lift
-- (dualMsm_check_iff_contract), and the acceptance predicate with the accumulator
-- arm (ContractRefAcceptsAcc) plus its two lemmas.
--
-- TWO STATEMENTS ARE FALSE AS PLAN 9.5 WRITES THEM, and this file states the true
-- forms rather than the planned ones. Both are recorded in docs/REVIEW.md (R-25,
-- R-26) and annotated at Exec/Accumulator.lean, and the stage-2 brief says not to
-- restate them naively:
--
--   1. decodeAcc_injective. The accumulator decoder IGNORES the coordinate words
--      of an identity-flagged point (AccumulatorHelpers.yul:130-141, ported at
--      Exec/Accumulator.lean:396-403: with the flag set the coordinates are
--      neither decoded nor range-checked), so two instance tails that differ only
--      there decode to the SAME accumulator. Exec/Accumulator.lean states this at
--      the decoder and accIdentityKats_ok exhibits the pair. What survives is
--      injectivity of the NORMALISED words: accWords projects the coordinate words
--      of a flagged point to zero and keeps everything the decoder actually reads.
--      The doc comment on accWords says what the normalisation does and why each
--      kept word is recoverable.
--   2. decodeAcc_encode. encodeAccInstances always emits the two carried scalar
--      words (Exec/Accumulator.lean, via AccMsm.asPublicInput), so for a .pointPair
--      encoding the emitted tail is two words longer than the decoder expects and
--      fixedScalarCount returns none: the round trip is FALSE for .pointPair. It is
--      stated here restricted to hkind : enc.kind = .pointAndScalar, and the
--      point-pair case is stated separately over a kind-aware encoder
--      (encodeAccPublicInput) with the extra hypothesis that shape forces.
--
-- A THIRD DEFECT, found while stating item 2 and reported per PLAN 12: the
-- sketch's decodeAcc_encode_pointPair inherits decodeAcc_encode's binders, which
-- allow a non-empty fixed-base tail. For .pointPair that is impossible -
-- fixedScalarCount rejects any non-zero tail (api.rs:178-186, and the reference's
-- own KAT at lowering/tests.rs:2096-2104) - so with a non-empty table the left side
-- is none and the equation is false. The statement below adds hfb : fb.size = 0,
-- which is the deployed Moonlight shape (a point pair carries no tail at all). That
-- is a strengthening of the hypothesis list, not a weakening of the conclusion.
--
-- WHAT IS NOT HERE. The S5 proofs themselves (M9), the Inv/Partials layer (stages
-- 4-5), and any reference to Midfall/Instances/ (D-P17). The fixed-base table is a
-- parameter because Midfall.Halo2.fixedBases' "-G" entry is the identity (R-52, a
-- live defect in the Exec row) and no statement here may use it.

import Midfall.Lowering.AccEncoding
import Midfall.Assumptions.Codec
import Midfall.Halo2.Exec.Accumulator
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Halo2.Exec.Kzg.GSMul
import Midfall.Lowering.Types
import Midfall.Halo2.Spec.Lemmas

namespace Midfall.Lowering
open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### 1. The R-25 normalisation -/

/-- R-25 projection of an instance array to the accumulator tail the decoder
    actually reads.

    WHAT THE NORMALISATION DOES, clause by clause, and why each clause is forced by
    a real malleability rather than chosen for convenience:

    * inst.extract enc.offset inst.size - decodeAcc reads nothing before enc.offset,
      so the prefix words are not part of the decoded value. Only the LENGTH
      survives, and it does so through the tail window's own length: a successful
      decode forces inst.size >= offset + fixedPayloadWords (fixedScalarCount), so
      the window length determines inst.size and no information is lost.
    * the coordinate words of a point whose identity flag is 1 are set to zero -
      this is the R-25 malleability itself. loadAccPoint returns 128 zero bytes for
      ANY coordinates when the flag is 1, so those words carry no meaning; zeroing
      them is what makes the decoder injective. The flag word itself is KEPT,
      because it is read (a flag of 2 is a rejection, not another encoding).
    * carried scalars and tail scalars are kept verbatim - each is compared against
      p and cast, so two different words give two different Fr values (Nat.cast is
      injective below p) and they must not be projected away.
    * the rhs point sits at pointWords + (1 if carried else 0) inside the window,
      exactly where decodeAcc puts it.

    Without the window, two arrays differing below enc.offset decode identically and
    injectivity fails; without the zeroing, accIdentityKats_ok's pair is a
    counterexample. accWordsKats_ok below exhibits both failures and the fix. -/
def accWords (enc : Midfall.Halo2.AccumulatorEncoding) (inst : Array Word256) :
    Array Word256 :=
  let tail := inst.extract enc.offset inst.size
  let cw := enc.coordinateWords
  let rhsSrc := enc.pointWords + (if enc.hasCarriedScalars then 1 else 0)
  let zeroCoords (a : Array Word256) (src : Nat) : Array Word256 :=
    if a.getD (src + 2 * cw) 0 = 1 then
      (List.range (2 * cw)).foldl (fun acc j => arraySetD acc (src + j) 0) a
    else a
  zeroCoords (zeroCoords tail 0) rhsSrc

/-- PLAN 9.5 decodeAcc_injective in its R-25 form: two instance arrays that decode
    to the same accumulator agree on the NORMALISED tail. Stated over the Exec
    encoding, which is what decodeAcc is typed over; decodeAcc_injective_gen below
    is the same fact for the generator encoding PLAN 9.5 means, via the D-P16
    bridge.

    hypotheses, each of which is load-bearing:
    * hrt : codec.eipRoundtrip - a flag-0 slot rebuilds 128 bytes from the decoded
      coordinates and then decodes them back to the same point, so two accepted
      flag-0 slots with the same point must have had the same bytes; that is exactly
      decoder-first canonicity, and without it two different coordinate words could
      name one point.
    * hone : codec.toEip 1 = 128 zero bytes - without it the identity would have
      BOTH a flag-1 encoding and a flag-0 encoding (the coordinates that decode to
      (0,0) are rejected only when the rebuilt bytes are the all-zero ones), and the
      two have different accWords because the flag word is kept.
    * hnodup - decodeAcc folds the tail through accMapInsert, which OVERWRITES a
      duplicate name, so a repeated base name silently drops a tail word and two
      tails differing there decode alike.

    No p <= 2^256 hypothesis is needed here, unlike decodeAcc_encode: the carried and
    tail words are checked < p before Nat.cast and Nat.cast is injective below p, so
    the words are recovered from the values.

    PROOF OBLIGATION, registered in SORRY.md (M5-3's lemma list:
    decodeAccCoord_inj, loadAccPoint_flag0_bytes, loadAccPoint_flag1,
    accMapInsert_fold_lookup_nodup, Nat.cast_injOn_lt_p, identity_flag_forced). The
    statement is the plan's, not a weakening: the plan's own decodeAcc_injective is
    the unprojected form and is FALSE. -/
theorem decodeAcc_injective {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁)
    (hrt : codec.eipRoundtrip) (hone : codec.toEip 1 = natToBytesBE 0 128)
    (fb : Array (AccFixedBase G₁)) (hnodup : (fb.toList.map AccFixedBase.name).Nodup)
    (i₁ i₂ : Array Word256) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (h₁ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₁ = some a)
    (h₂ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₂ = some a) :
    accWords enc i₁ = accWords enc i₂ := by
  sorry

/-- The same injectivity stated over the GENERATOR encoding, which is what PLAN 9.5
    and Supported.acc quantify over (hazard 1: the bridge direction is generator ->
    Exec, so the generator-typed form is the one a Surface field can consume). It is
    an instantiation, not a second theorem: the normalisation is applied to
    (toExec enc), whose coordinateWords / pointWords / hasCarriedScalars are the
    generator's by toExec_coordinateWords, toExec_fixedPayloadWords and
    toExec_hasCarriedScalars. -/
theorem decodeAcc_injective_gen {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Generator.AccumulatorEncoding) (codec : G1Codec G₁)
    (hrt : codec.eipRoundtrip) (hone : codec.toEip 1 = natToBytesBE 0 128)
    (fb : Array (AccFixedBase G₁)) (hnodup : (fb.toList.map AccFixedBase.name).Nodup)
    (i₁ i₂ : Array Word256) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (h₁ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb i₁ = some a)
    (h₂ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb i₂ = some a) :
    accWords (toExec enc) i₁ = accWords (toExec enc) i₂ :=
  decodeAcc_injective (p := p) (toExec enc) codec hrt hone fb hnodup i₁ i₂ a h₁ h₂

/-! ### 2. The contract's sign convention -/

/-- Contract-convention relabelling (R-26.3). A generated fixed-base entry whose
    negate flag is set carries the NEGATED scalar: the circuit's fixed base for
    "-G" is the negated generator (circuits/src/verifier/mod.rs:119) while the
    contract embeds the positive base from the VK header and negates the public
    scalar instead (artifacts.rs:200, AccumulatorHelpers.yul:322-326). decodeAcc
    models the contract's reading, so the accumulator it returns is a's rhs with
    those scalars flipped - NOT a. -/
def negateByTable {G₁ G₂ Gₜ : Type}
    (fb : Array (AccFixedBase G₁)) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) :
    KzgAcc (Fr p) G₁ G₂ Gₜ :=
  let neg (n : String) : Bool := fb.any (fun b => b.name == n && b.negate)
  { a with rhs := { a.rhs with fixedBaseScalars :=
      a.rhs.fixedBaseScalars.map (fun (n, s) => (n, if neg n then -s else s)) } }

/-! ### 3. The round trips -/

/-- Strictly ascending names. This is the BTreeMap invariant the Rust gets for free
    (circuits/src/verifier/msm.rs:40-54 keeps fixed_base_scalars sorted by key, and
    artifacts.rs:225 sorts the generated table), which decodeAcc's accMapInsert fold
    reproduces only if the input is already ascending.

    It is defined here rather than imported as Mathlib's List.Sorted (· < ·) because
    Mathlib's order/sorted theory is not in this project's imported surface - the
    lakefile builds only the Mathlib modules the tree already uses, and pulling in
    another one for a single predicate is not worth the rebuild. The three-clause
    recursion is the same proposition. -/
def namesAscending : List String → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ namesAscending (b :: rest)

/-- The singleton and empty cases are trivial, so the hypothesis is not vacuous; two
    equal names fail it, which is the case accMapInsert would silently collapse. -/
example : namesAscending [] ∧ namesAscending ["-G"] ∧ namesAscending ["-G", "a_fixed_com_0"] :=
  ⟨trivial, trivial, ⟨by simp, trivial⟩⟩

example : ¬ namesAscending ["a", "a"] := by
  intro h
  exact absurd h.1 (by simp)

/-! ### The `accMapInsert` fold lemmas (P-LIMB step 2)

  `decodeAcc` rebuilds the RHS fixed-base map by folding `accMapInsert` over
  `(fixedBases.zip tailWords)` in table order, so the round trips can only reproduce
  the tail verbatim when that fold loses nothing. It does not in general: the fold
  SORTS by name and OVERWRITES a repeated name. The hypothesis that makes it an
  identity is `namesAscending` - the BTreeMap invariant the Rust gets for free and
  which `decodeAcc_encode` already carries as `hsorted`. No prior table named any of
  these four lemmas; P-BYTES recorded the fold lemma as missing from every diagnosis.
  -/


private theorem accMapInsert_go_app {F : Type} : ∀ (l : List (String × F)) (k : String) (v : F),
    (∀ k2 ∈ l.map Prod.fst, k2 < k) →
      Midfall.Halo2.accMapInsert.go k v l = l ++ [(k, v)] := by
  intro l
  induction l with
  | nil => intro k v _; rfl
  | cons x xs ih =>
      intro k v hk
      cases x with
      | mk k2 v2 =>
          have hlt : k2 < k := hk k2 (by simp)
          have hne : ¬ (k == k2) := by
            intro h
            exact String.lt_irrefl k2 ((of_decide_eq_true h) ▸ hlt)
          have hgt : ¬ (k < k2) := fun h => String.lt_asymm hlt h
          simp only [Midfall.Halo2.accMapInsert.go, if_neg hne, if_neg hgt]
          rw [ih k v (fun y hy => hk y (by simp [hy]))]
          exact List.cons_append.symm

private theorem namesAscending_head_lt_mem : ∀ (l : List String) (a : String),
    namesAscending (a :: l) → ∀ x ∈ l, a < x := by
  intro l
  induction l with
  | nil => intro a _ x hx; exact absurd hx (by simp)
  | cons b rest ih =>
      intro a h x hx
      have hab : a < b := h.1
      obtain he | hx := List.mem_cons.mp hx
      · rw [he]
        exact hab
      · exact String.lt_trans hab (ih b h.2 x hx)

private theorem namesAscending_tail (a : String) : ∀ (l : List String),
    namesAscending (a :: l) → namesAscending l := by
  intro l h
  cases l with
  | nil => exact trivial
  | cons b t => exact h.2

private theorem namesAscending_snoc (l : List String) (k : String) :
    namesAscending l → (∀ x ∈ l, x < k) → namesAscending (l ++ [k]) := by
  induction l with
  | nil => intro _ _; exact trivial
  | cons a rest ih =>
      intro h hall
      have ha : a < k := hall a List.mem_cons_self
      cases rest with
      | nil => exact ⟨ha, trivial⟩
      | cons b t =>
          exact ⟨h.1, ih h.2 (fun x hx => hall x (by simp [hx]))⟩

private theorem accMapInsert_fold_sorted_go {F : Type} :
    ∀ (l : List (String × F)) (acc : Array (String × F)),
      namesAscending (acc.toList.map Prod.fst) →
      namesAscending (l.map Prod.fst) →
      (∀ k2 ∈ acc.toList.map Prod.fst, ∀ j ∈ l.map Prod.fst, k2 < j) →
      (List.foldl (fun a (n, s) => accMapInsert a n s) acc l).toList = acc.toList ++ l := by
  intro l
  induction l with
  | nil =>
      intro acc hacc _ _
      show acc.toList = acc.toList ++ []
      exact (List.append_nil _).symm
  | cons x xs ih =>
      intro acc hacc hl hall
      cases x with
      | mk n s =>
        have hmn : namesAscending (n :: xs.map Prod.fst) := hl
        have hall2 : ∀ k2 ∈ acc.toList.map Prod.fst, ∀ j ∈ n :: xs.map Prod.fst, k2 < j := hall
        have hlast : (accMapInsert acc n s).toList = acc.toList ++ [(n, s)] := by
          show (Midfall.Halo2.accMapInsert.go n s acc.toList).toArray.toList = _
          rw [List.toList_toArray, accMapInsert_go_app]
          exact fun k2 hk2 => hall2 k2 hk2 n List.mem_cons_self
        have hasc : namesAscending ((accMapInsert acc n s).toList.map Prod.fst) := by
          rw [hlast, List.map_append, List.map_singleton]
          exact namesAscending_snoc _ _ hacc
            (fun y hy => hall2 y hy n List.mem_cons_self)
        have h2 : ∀ k2 ∈ (accMapInsert acc n s).toList.map Prod.fst,
            ∀ j ∈ xs.map Prod.fst, k2 < j := by
          rw [hlast, List.map_append, List.map_singleton]
          intro k2 hk2 j hj
          rcases List.mem_append.mp hk2 with hk2 | hk2
          · exact hall2 k2 hk2 j (List.mem_cons_of_mem n hj)
          · rcases List.mem_singleton.mp hk2 with heq
            rw [heq]
            exact namesAscending_head_lt_mem _ n hmn j hj
        show (List.foldl (fun a (n2, s2) => accMapInsert a n2 s2)
            (accMapInsert acc n s) xs).toList = _
        rw [ih _ hasc (namesAscending_tail n _ hmn) h2, hlast]
        exact List.append_assoc _ _ _

theorem accMapInsert_fold_sorted_id {F : Type} (l : List (String × F))
    (hl : namesAscending (l.map Prod.fst)) :
    (List.foldl (fun acc (n, s) => accMapInsert acc n s)
        (#[] : Array (String × F)) l).toList = l := by
  have hnil : ((#[] : Array (String × F)).toList ++ l) = l := by simp
  have := accMapInsert_fold_sorted_go l (#[] : Array (String × F)) trivial hl (by simp)
  rw [hnil] at this
  exact this

/-- **Corollary: the fold is injective on ascending name lists.** Two ascending lists
    that fold to the same map ARE the same list - the form `decodeAcc_encode`
    consumes, since the decoder rebuilds the fixed-base map by folding in table order
    and the round trip only reproduces the tail when that fold loses nothing.

    FINDING on the brief: P-LIMB step 2 asked for a **`Nodup`** fold-injectivity
    lemma for `decodeAcc_injective`. Nodup alone does NOT give the identity form: the
    fold SORTS, so a duplicate-free but descending list folds to a permutation of
    itself - the second falsification below is exactly that. What
    `decodeAcc_injective` needs is injectivity of the map READBACK (a `find?`-level
    statement about `accMapInsert`, needing two interaction lemmas that are not
    landed here). Reported rather than papered over. -/
theorem accMapInsert_fold_inj {F : Type} (l₁ l₂ : List (String × F))
    (h₁ : namesAscending (l₁.map Prod.fst)) (h₂ : namesAscending (l₂.map Prod.fst))
    (hfold : List.foldl (fun acc (n, s) => accMapInsert acc n s)
        (#[] : Array (String × F)) l₁
      = List.foldl (fun acc (n, s) => accMapInsert acc n s)
        (#[] : Array (String × F)) l₂) : l₁ = l₂ := by
  have e₁ := accMapInsert_fold_sorted_id l₁ h₁
  have e₂ := accMapInsert_fold_sorted_id l₂ h₂
  rw [← e₁, ← e₂]
  exact congrArg Array.toList hfold

/-- **`accMapInsert_fold_sorted_id`, witness**: the deployed fixed-base name order
    (what `artifacts.rs:225` sorts to) really is ascending and the fold reproduces it
    verbatim. -/
theorem accMapInsert_fold_sorted_witness :
    (List.foldl (fun acc (n, s) => accMapInsert acc n s)
        (#[] : Array (String × Nat))
      [("-G", 0), ("self_vk_fixed_com_0", 1), ("self_vk_perm_com_0", 2)]).toList =
      [("-G", 0), ("self_vk_fixed_com_0", 1), ("self_vk_perm_com_0", 2)] :=
  accMapInsert_fold_sorted_id _ ⟨by simp, by simp, trivial⟩

/-- **`accMapInsert_fold_sorted_id`, falsification (duplicates)**: with a repeated
    name the fold OVERWRITES and silently drops an entry - the malleability `hnodup`
    rules out in `decodeAcc_injective`. -/
theorem accMapInsert_fold_sorted_needs_nodup :
    (List.foldl (fun acc (n, s) => accMapInsert acc n s)
        (#[] : Array (String × Nat)) [("a", 1), ("a", 2)]).toList
      ≠ [("a", 1), ("a", 2)] := by decide

/-- **`accMapInsert_fold_sorted_id`, falsification (order)**: duplicate-free is NOT
    enough. `[("b", 1), ("a", 2)]` has two distinct names, yet the fold sorts them,
    so the result is a different list and the identity fails. This is why the
    hypothesis is `namesAscending` and not `Nodup`. -/
theorem accMapInsert_fold_sorted_needs_ascending :
    (List.foldl (fun acc (n, s) => accMapInsert acc n s)
        (#[] : Array (String × Nat)) [("b", 1), ("a", 2)]).toList
      ≠ [("b", 1), ("a", 2)] := by decide


/-! ### P-TRUNK link (d): the fold alignment no earlier table wrote down

  `decodeAcc` does NOT fold the tail as `(name, scalar)` pairs. It folds
  `List.zip fixedBases.toList tailWords` - a PAIR OF A RECORD AND A WORD - and the value it
  inserts is `if b.negate then -s else s`. `negateByTable`, the thing the round trip must
  come out to, computes its sign a different way: `fb.any (fun b => b.name == n && b.negate)`.
  `accMapInsert_fold_sorted_id` cannot bridge those two: it knows nothing about records,
  nothing about a per-entry value function, and nothing about `any`. This section is the
  three lemmas that do, and no prior table (P-LIMB, P-BYTES, P-ACCENC, P-TRUNK's own sketch
  pointer) named more than a fragment of it. -/

/-- **Link (d), first half: the fold with a per-entry value function.** The general-accumulator
    form, mirroring `accMapInsert_fold_sorted_go`: folding `accMapInsert` over an ascending
    list of (base, word) pairs appends the entries in order, each carrying the value the
    function computes for it. `emb` is the word-to-field map - `Nat.cast` at the use site,
    because `decodeAcc` reads words as `Nat` and negates them in `Fr p`, so the coercion
    sits INSIDE the conditional and a lemma without it cannot match the term. -/
private theorem accMapInsert_fold_negate_go {G₁ : Type} {F : Type} [Neg F] {W : Type}
    (emb : W → F) :
    ∀ (l : List (AccFixedBase G₁ × W)) (acc : Array (String × F)),
      namesAscending (acc.toList.map Prod.fst) →
      namesAscending (l.map (fun x => x.1.name)) →
      (∀ k2 ∈ acc.toList.map Prod.fst, ∀ j ∈ l.map (fun x => x.1.name), k2 < j) →
      (List.foldl (fun acc x => accMapInsert acc x.1.name
          (if x.1.negate then -emb x.2 else emb x.2)) acc l).toList
        = acc.toList ++ l.map (fun x =>
            (x.1.name, if x.1.negate then -emb x.2 else emb x.2)) := by
  intro l
  induction l with
  | nil =>
      intro acc _ _ _
      show acc.toList = acc.toList ++ []
      exact (List.append_nil _).symm
  | cons x xs ih =>
      intro acc hacc hl hall
      cases x with
      | mk b s =>
        have hlast : (accMapInsert acc b.name (if b.negate then -emb s else emb s)).toList
            = acc.toList ++ [(b.name, if b.negate then -emb s else emb s)] := by
          show (Midfall.Halo2.accMapInsert.go b.name
            (if b.negate then -emb s else emb s) acc.toList).toArray.toList = _
          rw [List.toList_toArray, accMapInsert_go_app]
          exact fun k2 hk2 => hall k2 hk2 b.name List.mem_cons_self
        have hasc : namesAscending
            ((accMapInsert acc b.name (if b.negate then -emb s else emb s)).toList.map Prod.fst) := by
          rw [hlast, List.map_append, List.map_singleton]
          exact namesAscending_snoc _ _ hacc
            (fun y hy => hall y hy b.name List.mem_cons_self)
        have h2 : ∀ k2 ∈ (Array.toList
            (accMapInsert acc b.name (if b.negate then -emb s else emb s))).map Prod.fst,
            ∀ j ∈ xs.map (fun x => x.1.name), k2 < j := by
          rw [hlast, List.map_append, List.map_singleton]
          intro k2 hk2 j hj
          rcases List.mem_append.mp hk2 with hk2 | hk2
          · exact hall k2 hk2 j (List.mem_cons_of_mem b.name hj)
          · rcases List.mem_singleton.mp hk2 with heq
            rw [heq]
            exact namesAscending_head_lt_mem _ b.name hl j hj
        show (List.foldl (fun acc x => accMapInsert acc x.1.name
            (if x.1.negate then -emb x.2 else emb x.2))
            (accMapInsert acc b.name (if b.negate then -emb s else emb s)) xs).toList = _
        rw [ih _ hasc (namesAscending_tail b.name _ hl) h2, hlast]
        exact List.append_assoc _ _ _

/-- **Link (d), first half at the empty map.** What `decodeAcc` actually runs. -/
theorem accMapInsert_fold_negate {G₁ : Type} {F : Type} [Neg F] {W : Type} (emb : W → F)
    (l : List (AccFixedBase G₁ × W))
    (hl : namesAscending (l.map (fun x => x.1.name))) :
    (List.foldl (fun acc x => accMapInsert acc x.1.name
        (if x.1.negate then -emb x.2 else emb x.2)) (#[] : Array (String × F)) l).toList
      = l.map (fun x => (x.1.name, if x.1.negate then -emb x.2 else emb x.2)) := by
  have hnil : ((#[] : Array (String × F)).toList
      ++ l.map (fun x => (x.1.name, if x.1.negate then -emb x.2 else emb x.2)))
      = l.map (fun x => (x.1.name, if x.1.negate then -emb x.2 else emb x.2)) := by simp
  have := accMapInsert_fold_negate_go emb l (#[] : Array (String × F)) trivial hl (by simp)
  rw [hnil] at this
  exact this

/-- **Link (d), second half: the `any` bridge.** `negateByTable` decides a sign by scanning
    the whole table for a name match, while the fold reads the flag off the entry it is
    holding. Under `namesAscending` - which is strict, so the names are distinct - the two
    agree, and that is the ONLY reason they agree: with a repeated name the scan can pick up
    a negated entry that is not the one being folded. This is the hypothesis the brief's
    "the `fb.any ↔ b.negate` bridge under distinctness" names. -/
theorem accFixedBase_any_negate {G₁ : Type} (fb : List (AccFixedBase G₁))
    (h : namesAscending (fb.map AccFixedBase.name)) (b : AccFixedBase G₁) (hb : b ∈ fb) :
    fb.any (fun c => c.name == b.name && c.negate) = b.negate := by
  induction fb with
  | nil => exact absurd hb (by simp)
  | cons x xs ih =>
      rcases List.mem_cons.mp hb with he | hb'
      · subst he
        have hne : ∀ c ∈ xs, ¬ (c.name == b.name) := by
          intro c hc
          have hlt : b.name < c.name :=
            namesAscending_head_lt_mem (xs.map AccFixedBase.name) b.name h c.name
              ((List.mem_map (f := AccFixedBase.name)).mpr ⟨c, hc, rfl⟩)
          intro g
          exact String.lt_irrefl b.name ((of_decide_eq_true g) ▸ hlt)
        have h2 : xs.any (fun c => c.name == b.name && c.negate) = false := by
          rw [List.any_eq_false]
          intro c hc
          exact by simp [hne c hc]
        rw [List.any_cons, h2, Bool.or_false]
        have h3 : (b.name == b.name) = true := by simp
        rw [h3, Bool.true_and]
      · have hlt : x.name < b.name :=
          namesAscending_head_lt_mem (xs.map AccFixedBase.name) x.name h b.name
            ((List.mem_map (f := AccFixedBase.name)).mpr ⟨b, hb', rfl⟩)
        have hne : ¬ (x.name == b.name) := by
          intro g
          exact String.lt_irrefl x.name ((of_decide_eq_true g) ▸ hlt)
        have h1 : (x.name == b.name && x.negate) = false := by simp [hne]
        rw [List.any_cons, h1, Bool.false_or]
        exact ih (namesAscending_tail x.name _ h) hb'

/-- **Link (d), third half: name/word alignment.** The decoder zips the TABLE with the WORDS
    it read; the encoder emitted the words from the TAIL, and `hnames` is what says the two
    name lists are the same list. Read back through `frWord` and `Nat.cast` (link (c)) the
    word at position `i` is the tail's own scalar at `i`, so the zipped, re-projected list
    IS the tail. Without this the fold lemma lands on a list of pairs nobody can compare with
    `negateByTable`'s map. -/
theorem zip_align_frWord {G₁ : Type} (bs : List (AccFixedBase G₁)) (t : List (String × Fr p))
    (hp : p < 2 ^ 256)
    (h1 : bs.map AccFixedBase.name = t.map Prod.fst) :
    (bs.zip (t.map (fun x => (frWord x.2).toNat))).map (fun x => (x.1.name, (x.2 : Fr p))) = t := by
  induction bs generalizing t with
  | nil =>
      cases t with
      | nil => rfl
      | cons x xs => exact absurd h1 (by simp)
  | cons b bs' ih =>
      cases t with
      | nil => exact absurd h1 (by simp)
      | cons x xs' =>
          simp only [List.map_cons] at h1
          obtain ⟨hnm, h1'⟩ := List.cons.inj h1
          show List.map (fun z => (z.1.name, (z.2 : Fr p)))
              ((b, (frWord x.2).toNat) :: bs'.zip (xs'.map (fun y => (frWord y.2).toNat)))
              = (x.1, x.2) :: xs'
          rw [List.map_cons, natCast_frWord_toNat hp x.2, ih xs' h1', hnm]



/-- PLAN 9.5 decodeAcc_encode, restricted to the only shape the contract can read
    (R-26.2): a COLLAPSED point-and-scalar accumulator - one base with one carried
    scalar per side, plus the RHS fixed-base tail - behind enc.offset prefix words.

    hypotheses, each load-bearing:
    * hp : p < 2^256 - frWord truncates mod 2^256, and the decoder recovers the word
      and casts it back; below 2^256 that is the identity.
    * hkind - the .pointPair case is FALSE, for the reason in this file's header.
    * hshape - fixedScalarCount reaches validFor, which requires the 7x56 limb
      shape; without it the decoder returns none and the equation is about none.
    * hc : G1CodecLaws codec - ofEip_toEip recovers the point from the bytes the
      encoder rebuilt, eipShape makes those bytes the 16-48-16-48 frame with
      in-field non-(0,0) coordinates (which is what makes the rebuild byte-for-byte
      equal to toEip, and what keeps the (0,0) rejection from firing on a real
      point), and toEip_one covers L or R being the identity.
    * hsorted - decodeAcc rebuilds the fixed map with accMapInsert in fb order, so
      only a strictly ascending tail is reproduced verbatim; the BTreeMap invariant
      the Rust gets for free is not in this type.
    * hnames - the tail count must equal the table size and pair name-by-name
      (artifacts.rs:225 sorts by name).
    * hpre - decodeAcc reads at enc.offset, so the prefix must be exactly that long.

    PROVED (P-TRUNK). What the proof actually consumed, in order: the encoder block
    structure (Exec `encodeAccInstances_collapsed`, which no table named either), link (b)
    `fixedScalarCount_exact`, link (a) `getD_append_offset` plus the now-public
    `getD_append_left/right` and `getD_snoc`, the block-width lemma
    `asPublicInputPoint_size`, the array/getD bridge `toList_eq_range_getD`, link (c)
    `frWord_toNat` / `natCast_frWord_toNat`, the P-ACCENC point link `loadAccPoint_encode` through
    `loadAccPoint_congr`, `hc.ofEip_toEip` for the two point decodes, and link (d)
    `accMapInsert_fold_negate` + `accFixedBase_any_negate` + `zip_align_frWord` for the
    fixed-base tail. Of M5-4's predicted list, `accMapInsert_fold_sorted_id` alone was NOT
    enough (it knows nothing about records or about `any`), and
    `loadAccPoint_encode_nonId` is not a name in the tree - the two arms are
    `loadAccPoint_encode_coords` and `loadAccPoint_encode`. -/
theorem decodeAcc_encode {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (hp : p < 2 ^ 256)
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (tail : Array (String × Fr p))
    (hsorted : namesAscending (tail.toList.map Prod.fst))
    (fb : Array (AccFixedBase G₁))
    (hnames : fb.toList.map AccFixedBase.name = tail.toList.map Prod.fst)
    (pre : Array Word256) (hpre : pre.size = enc.offset) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := tail } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (pre ++ encodeAccInstances (toExec enc) codec a) = some (negateByTable fb a) := by
  intro a
  set e := toExec enc with he
  have hkindE : e.kind = AccumulatorEncodingKind.pointAndScalar := by
    show toExecKind enc.kind = _
    rw [hkind]
    rfl
  have hcarr : e.hasCarriedScalars = true := by
    show (toExec enc).hasCarriedScalars = true
    rw [toExec_hasCarriedScalars]
    unfold Midfall.Generator.AccumulatorEncoding.hasCarriedScalars
    rw [hkind]
    rfl
  have hshapeE : e.limbShapeOk = true := hshape
  have hfpw : e.fixedPayloadWords = 2 * e.pointWords + 2 := by
    show e.pointPairWords + (if e.hasCarriedScalars then accCarriedScalars else 0) = _
    rw [hcarr]
    show e.pointPairWords + accCarriedScalars = 2 * e.pointWords + 2
    dsimp only [AccumulatorEncoding.pointPairWords, accCarriedScalars]
  have hpreE : pre.size = e.offset := hpre
  have henc : encodeAccInstances e codec a
      = AccMsm.asPublicInputPoint (G₂ := G₂) (Gₜ := Gₜ) e codec L ++ #[frWord sL]
        ++ (AccMsm.asPublicInputPoint (G₂ := G₂) (Gₜ := Gₜ) e codec R ++ #[frWord sR]
            ++ tail.map (fun x => frWord x.2)) :=
    encodeAccInstances_collapsed e codec L R sL sR tail
  have hptw (Q : G₁) :
      (AccMsm.asPublicInputPoint (G₂ := G₂) (Gₜ := Gₜ) e codec Q).size = e.pointWords :=
    AccMsm.asPublicInputPoint_size e codec Q
  have hfbsize : fb.size = tail.size := by
    have h := congrArg List.length hnames
    rw [List.length_map, List.length_map] at h
    rw [← Array.size_eq_length_toList, ← Array.size_eq_length_toList] at h
    exact h
  -- block abbreviations
  set P1 := AccMsm.asPublicInputPoint (G₂ := G₂) (Gₜ := Gₜ) e codec L with hp1
  set P2 := AccMsm.asPublicInputPoint (G₂ := G₂) (Gₜ := Gₜ) e codec R with hp2
  set T := tail.map (fun x => frWord x.2) with hT
  set blk := P1 ++ #[frWord sL] ++ (P2 ++ #[frWord sR] ++ T) with hblk
  have hpw1 : e.pointWords = 2 * e.coordinateWords + 1 := rfl
  have hsz1 : P1.size = e.pointWords := hptw L
  have hsz2 : P2.size = e.pointWords := hptw R
  have hszT : T.size = tail.size := by rw [hT]; simp only [Array.size_map]
  have hA : (P1 ++ #[frWord sL]).size = e.pointWords + 1 := by
    rw [Array.size_append, hsz1, Array.size_singleton]
  have hD : (P2 ++ #[frWord sR]).size = e.pointWords + 1 := by
    rw [Array.size_append, hsz2, Array.size_singleton]
  have hszC : (P2 ++ #[frWord sR] ++ T).size = e.pointWords + 1 + tail.size := by
    rw [Array.size_append, hD, hszT]
  have hbsz : blk.size = e.fixedPayloadWords + tail.size := by
    rw [hblk]
    simp only [Array.size_append, Array.size_singleton, hsz1, hsz2, hszT]
    rw [hfpw]
    omega
  have hencb : encodeAccInstances e codec a = blk := henc
  have hinstsz : (pre ++ encodeAccInstances e codec a).size =
      e.offset + e.fixedPayloadWords + tail.size := by
    rw [Array.size_append, hencb, hbsz, hpreE]
    omega
  have hfsc : e.fixedScalarCount (pre ++ encodeAccInstances e codec a).size = some tail.size := by
    rw [hinstsz]
    exact AccumulatorEncoding.fixedScalarCount_exact e tail.size hshapeE hkindE
  have hget : ∀ j, j < blk.size →
      (pre ++ encodeAccInstances e codec a).getD (e.offset + j) 0 = blk.getD j 0 := by
    intro j hj
    rw [hencb]
    exact getD_append_offset pre blk e.offset hpreE j 0 hj
  have hjL : e.pointWords < blk.size := by rw [hbsz, hfpw]; omega
  have hjR : e.pointWords + 1 + e.pointWords < blk.size := by rw [hbsz, hfpw]; omega
  have hjT : ∀ j, j < tail.size → e.pointWords + 1 + e.pointWords + 1 + j < blk.size := by
    intro j hj
    rw [hbsz, hfpw]
    omega
  have hreadL : blk.getD e.pointWords 0 = frWord sL := by
    rw [hblk, getD_append_left (P1 ++ #[frWord sL]) (P2 ++ #[frWord sR] ++ T) e.pointWords 0
          (by rw [hA]; omega), ← hsz1]
    exact getD_snoc P1 (frWord sL) 0
  have hreadR : blk.getD (e.pointWords + 1 + e.pointWords) 0 = frWord sR := by
    rw [hblk,
      show e.pointWords + 1 + e.pointWords = (P1 ++ #[frWord sL]).size + e.pointWords from by rw [hA],
      getD_append_right (P1 ++ #[frWord sL]) (P2 ++ #[frWord sR] ++ T) e.pointWords 0
        (by simp only [Array.size_append, Array.size_singleton, hsz2, hszT]; omega)]
    rw [← hsz2,
      getD_append_left (P2 ++ #[frWord sR]) T P2.size 0 (by rw [Array.size_append, hsz2, Array.size_singleton]; omega)]
    exact getD_snoc P2 (frWord sR) 0
  have hreadT : ∀ j, j < tail.size →
      blk.getD (e.pointWords + 1 + e.pointWords + 1 + j) 0 = T.getD j 0 := by
    intro j hj
    rw [hblk,
      show e.pointWords + 1 + e.pointWords + 1 + j =
          (P1 ++ #[frWord sL]).size + ((P2 ++ #[frWord sR]).size + j) from by
        rw [hA, hD]; omega,
      getD_append_right (P1 ++ #[frWord sL]) (P2 ++ #[frWord sR] ++ T)
        ((P2 ++ #[frWord sR]).size + j) 0
        (by simp only [Array.size_append, Array.size_singleton, hsz2, hszT]; omega),
      getD_append_right (P2 ++ #[frWord sR]) T j 0 (by rw [hszT]; exact hj)]
  have h1 : (List.range tail.size).map
      (fun j => blk.getD (e.pointWords + 1 + e.pointWords + 1 + j) 0) = T.toList := by
    rw [← hszT, ← toList_eq_range_getD T 0]
    refine List.map_eq_map_iff.mpr (fun j hj => hreadT j (by rw [← hszT]; exact List.mem_range.mp hj))
  have hTW : (List.range tail.size).map
      (fun j => BitVec.toNat (blk.getD (e.pointWords + 1 + e.pointWords + 1 + j) 0))
      = tail.toList.map (fun x => (frWord x.2).toNat) := by
    have h2 : (List.range tail.size).map
        (fun j => BitVec.toNat (blk.getD (e.pointWords + 1 + e.pointWords + 1 + j) 0))
        = T.toList.map BitVec.toNat := by
      have h2a := congrArg (·.map BitVec.toNat) h1
      rw [List.map_map, Function.comp_def] at h2a
      exact h2a
    rw [h2, hT, Array.toList_map, List.map_map, Function.comp_def]
  have hwordL : BitVec.toNat
      ((pre ++ encodeAccInstances e codec a).getD (e.offset + e.pointWords) 0) = sL.val := by
    rw [hget e.pointWords hjL, hreadL, frWord_toNat hp sL]
  have hwordR : BitVec.toNat
      ((pre ++ encodeAccInstances e codec a).getD (e.offset + e.pointWords + 1 + e.pointWords) 0)
      = sR.val := by
    rw [show e.offset + e.pointWords + 1 + e.pointWords = e.offset + (e.pointWords + 1 + e.pointWords)
          from by omega, hget (e.pointWords + 1 + e.pointWords) hjR, hreadR, frWord_toNat hp sR]
  have hc1 : ∀ jj ≤ 2 * e.coordinateWords,
      (pre ++ encodeAccInstances e codec a).getD (e.offset + jj) 0 = P1.getD (0 + jj) 0 := by
    intro jj hjj
    rw [hget jj (by omega), hblk,
      getD_append_left (P1 ++ #[frWord sL]) (P2 ++ #[frWord sR] ++ T) jj 0 (by rw [hA]; omega),
      getD_append_left P1 (#[frWord sL]) jj 0 (by rw [hsz1]; omega)]
    exact (congrArg (P1.getD · 0) (Nat.zero_add jj)).symm
  have hloadL : loadAccPoint e (pre ++ encodeAccInstances e codec a) e.offset
      = some (codec.toEip L, decideBool (P.decEqG₁ L 1)) := by
    rw [loadAccPoint_congr e _ P1 e.offset 0 hc1, loadAccPoint_encode e hshapeE codec hc L]
  have hc2 : ∀ jj ≤ 2 * e.coordinateWords,
      (pre ++ encodeAccInstances e codec a).getD (e.offset + e.pointWords + 1 + jj) 0
        = P2.getD (0 + jj) 0 := by
    intro jj hjj
    rw [show e.offset + e.pointWords + 1 + jj = e.offset + (e.pointWords + 1 + jj) from by omega,
      hget (e.pointWords + 1 + jj) (by omega), hblk,
      show e.pointWords + 1 + jj = (P1 ++ #[frWord sL]).size + jj from by rw [hA],
      getD_append_right (P1 ++ #[frWord sL]) (P2 ++ #[frWord sR] ++ T) jj 0
        (by simp only [Array.size_append, Array.size_singleton, hsz2, hszT]; omega),
      getD_append_left (P2 ++ #[frWord sR]) T jj 0
        (by rw [Array.size_append, hsz2, Array.size_singleton]; omega),
      getD_append_left P2 (#[frWord sR]) jj 0 (by rw [hsz2]; omega)]
    exact (congrArg (P2.getD · 0) (Nat.zero_add jj)).symm
  have hloadR : loadAccPoint e (pre ++ encodeAccInstances e codec a)
      (e.offset + e.pointWords + 1) = some (codec.toEip R, decideBool (P.decEqG₁ R 1)) := by
    rw [loadAccPoint_congr e _ P2 (e.offset + e.pointWords + 1) 0 hc2,
      loadAccPoint_encode e hshapeE codec hc R]
  have hfbasc : namesAscending (fb.toList.map AccFixedBase.name) := by
    rw [hnames]
    exact hsorted
  have hzl : (fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))).map (fun x => x.1.name)
      = tail.toList.map Prod.fst := by
    have h := zip_align_frWord fb.toList tail.toList hp hnames
    have h2 : (fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))).map (fun x => x.1.name)
        = ((fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))).map
            (fun x => (x.1.name, (x.2 : Fr p)))).map Prod.fst := by
      rw [List.map_map, Function.comp_def]
    rw [h2, h]
  -- the tail word list at the whole-array level
  have hTW2 : (List.range tail.size).map
      (fun j => BitVec.toNat ((pre ++ encodeAccInstances e codec a).getD
        (e.offset + (e.pointWords + 1 + e.pointWords + 1 + j)) 0))
      = tail.toList.map (fun x => (frWord x.2).toNat) := by
    have h : (List.range tail.size).map
        (fun j => BitVec.toNat ((pre ++ encodeAccInstances e codec a).getD
          (e.offset + (e.pointWords + 1 + e.pointWords + 1 + j)) 0))
        = (List.range tail.size).map
            (fun j => BitVec.toNat (blk.getD (e.pointWords + 1 + e.pointWords + 1 + j) 0)) := by
      refine List.map_eq_map_iff.mpr (fun j hj =>
        congrArg BitVec.toNat (hget (e.pointWords + 1 + e.pointWords + 1 + j)
          (hjT j (List.mem_range.mp hj))))
    rw [h, hTW]
  -- the scalar bounds
  have hbL : decide (BitVec.toNat
      ((pre ++ encodeAccInstances e codec a).getD (e.offset + e.pointWords) 0) < p) = true := by
    rw [hwordL]
    exact decide_eq_true (ZMod.val_lt sL)
  have hbR : decide (BitVec.toNat
      ((pre ++ encodeAccInstances e codec a).getD (e.offset + e.pointWords + 1 + e.pointWords) 0) < p)
      = true := by
    rw [hwordR]
    exact decide_eq_true (ZMod.val_lt sR)
  have hbT : (tail.toList.map (fun x => (frWord x.2).toNat)).any
      (fun w => !decide (w < p)) = false := by
    rw [List.any_eq_false]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact by simp [frWord_toNat_lt hp x.2]
  have hscL : (↑(BitVec.toNat
      ((pre ++ encodeAccInstances e codec a).getD (e.offset + e.pointWords) 0)) : Fr p) = sL := by
    rw [hwordL]
    simpa using ZMod.natCast_val (R := Fr p) sL
  have hscR : (↑(BitVec.toNat ((pre ++ encodeAccInstances e codec a).getD
      (e.offset + e.pointWords + 1 + e.pointWords) 0)) : Fr p) = sR := by
    rw [hwordR]
    simpa using ZMod.natCast_val (R := Fr p) sR
  -- the fold
  have hmem_zip : ∀ {α β : Type} (bs : List α) (vs : List β) (p : α × β),
      p ∈ bs.zip vs → p.1 ∈ bs := by
    intro α β bs
    induction bs with
    | nil => intro vs p hp; exact absurd hp (by simp)
    | cons b bs ih =>
        intro vs p hp
        cases vs with
        | nil => exact absurd hp (by simp)
        | cons w ws =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih ws p hp)
  have hany_bridge : ∀ (as : Array (AccFixedBase G₁)) (p : AccFixedBase G₁ → Bool),
      as.any p = as.toList.any p := by
    intro as p
    cases as
    simp [Array.any]
  have hflag : ∀ p ∈ fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat)),
      p.1.negate = fb.any (fun c => c.name == p.1.name && c.negate) := by
    intro p hp
    rw [hany_bridge]
    exact (accFixedBase_any_negate fb.toList hfbasc p.1 (hmem_zip _ _ _ hp)).symm
  have hl_fold : namesAscending
      ((fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))).map (fun x => x.1.name)) := by
    rw [hzl]
    exact hsorted
  have hfold_eq := accMapInsert_fold_negate (emb := (fun (w : Nat) => (w : Fr p)))
      (fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))) hl_fold
  have halign := zip_align_frWord fb.toList tail.toList hp hnames
  have hfold : List.foldl (fun acc x => accMapInsert acc x.1.name
        (if x.1.negate = true then -↑x.2 else ↑x.2)) (#[] : Array (String × Fr p))
        (fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat)))
      = tail.map (fun x => (x.1, if fb.any (fun c => c.name == x.1 && c.negate) then -x.2 else x.2)) := by
    refine Array.toList_inj.mp ?_
    rw [hfold_eq, Array.toList_map]
    have h3 : (fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))).map
          (fun x => (x.1.name, if x.1.negate = true then -↑x.2 else ↑x.2))
        = ((fb.toList.zip (tail.toList.map (fun x => (frWord x.2).toNat))).map
            (fun x => (x.1.name, (x.2 : Fr p)))).map
            (fun y => (y.1, if fb.any (fun c => c.name == y.1 && c.negate) then -y.2 else y.2)) := by
      rw [List.map_map, Function.comp_def]
      refine List.map_eq_map_iff.mpr (fun p hp => ?_)
      rw [hflag p hp]
    rw [h3, halign]
  -- the decoder itself
  unfold decodeAcc
  dsimp only
  rw [hfsc]
  dsimp only [Bind.bind, Option.bind]
  rw [hfbsize]
  have hg1 : ((tail.size : Nat) != tail.size) = false := by simp
  rw [hg1, if_neg (by simp : ¬((false : Bool) = true))]
  simp only [hcarr, reduceIte]
  rw [hbL, hbR]
  simp only [show ∀ j : Nat, ((e.offset + e.pointWords + 1) + e.pointWords + 1) + j
      = e.offset + (e.pointWords + 1 + e.pointWords + 1 + j) from by omega]
  rw [hTW2, hbT]
  simp only [Bool.not_true, Bool.and_false, Bool.false_or, Bool.false_eq_true, reduceIte]
  rw [hloadL]
  dsimp only [Bind.bind, Option.bind]
  rw [hloadR]
  dsimp only [Bind.bind, Option.bind]
  rw [hc.ofEip_toEip L, hc.ofEip_toEip R]
  dsimp only [Bind.bind, Option.bind]
  rw [hscL, hscR]
  rw [hfold]
  exact rfl

/-- **`negateByTable` is the identity when nothing in the table is negated** (P-TRUNK, the
    extra ~10 lines the brief predicted for `decodeAcc_encode_noNeg`). The scan
    `fb.any (fun b => b.name == n && b.negate)` is false for every name the moment every
    `negate` flag is false, so the map relabels nothing. Note this is the ARRAY-level
    `any`, which is why the bridge below is needed: `Array.any` is a bounded loop, not
    `List.any` on `toList` (the same trap as `Array.find?`, and re-probed here). -/
private theorem array_any_toList_any {α : Type} (as : Array α) (p : α → Bool) :
    as.any p = as.toList.any p := by
  cases as
  simp [Array.any]

theorem negateByTable_eq_of_noNeg {G₁ G₂ Gₜ : Type}
    (fb : Array (AccFixedBase G₁)) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hneg : ∀ b ∈ fb.toList, b.negate = false) : negateByTable fb a = a := by
  have hneg : ∀ n : String, fb.any (fun b => b.name == n && b.negate) = false := by
    intro n
    rw [array_any_toList_any, List.any_eq_false]
    intro b hb
    rw [hneg b hb]
    simp
  unfold negateByTable
  dsimp only
  have hmap : a.rhs.fixedBaseScalars.map
      (fun x => (x.1, if fb.any (fun c => c.name == x.1 && c.negate) then -x.2 else x.2))
      = a.rhs.fixedBaseScalars := by
    refine Array.toList_inj.mp ?_
    rw [Array.toList_map]
    show a.rhs.fixedBaseScalars.toList.map
        (fun x => (x.1, if fb.any (fun c => c.name == x.1 && c.negate) = true then -x.2 else x.2))
        = _
    simp only [hneg, Bool.false_eq_true, ite_false, Prod.mk.eta]
    exact List.map_id' _
  rw [hmap]

/-- The PLAN's literal conclusion, which holds exactly when no base is negated.
    Same binders and same hypotheses as decodeAcc_encode; the extra hneg is what
    turns negateByTable fb a back into a. PROVED (P-TRUNK) in four lines from
    decodeAcc_encode plus negateByTable_eq_of_noNeg, as the brief predicted. -/
theorem decodeAcc_encode_noNeg {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (hp : p < 2 ^ 256)
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (tail : Array (String × Fr p))
    (hsorted : namesAscending (tail.toList.map Prod.fst))
    (fb : Array (AccFixedBase G₁))
    (hnames : fb.toList.map AccFixedBase.name = tail.toList.map Prod.fst)
    (pre : Array Word256) (hpre : pre.size = enc.offset)
    (hneg : ∀ b ∈ fb.toList, b.negate = false) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := tail } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (pre ++ encodeAccInstances (toExec enc) codec a) = some a := by
  intro a
  have h : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
      (pre ++ encodeAccInstances (toExec enc) codec a) = some (negateByTable fb a) :=
    decodeAcc_encode (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) hp enc hkind hshape codec hc L R
      sL sR tail hsorted fb hnames pre hpre
  rw [negateByTable_eq_of_noNeg fb a hneg] at h
  exact h

/-- Drop the two carried-scalar slots from an encodeAccInstances word stream: the
    lhs scalar sits at pointWords and the rhs scalar at 2*pointWords + 1, which is
    where decodeAcc would look for them if the layout carried scalars.

    This is the SKETCH name dropCarriedScalarWords from PLAN 9.5 section F, which
    does not exist in the tree (survey.md has no such name either); it is defined
    here rather than invented there, and it is only meaningful for a collapsed
    one-base-per-side accumulator, which is the only shape the point-pair layout
    admits (fixedScalarCount rejects a tail for .pointPair). -/
def dropCarriedScalarWords (enc : Midfall.Halo2.AccumulatorEncoding)
    (w : Array Word256) : Array Word256 :=
  let pw := enc.pointWords
  (w.extract 0 pw) ++ (w.extract (pw + 1) (2 * pw + 1)) ++ (w.extract (2 * pw + 2) w.size)

/-- Adjustment 1 of PLAN 9.5 section F: the kind-aware public-input encoder. For a
    point-pair encoding the contract reads no scalar words at all (the carried
    scalars are implicitly 1, api.rs:53-56), so the two slots are dropped; for a
    point-and-scalar encoding this is encodeAccInstances unchanged. -/
def encodeAccPublicInput {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 :=
  if enc.hasCarriedScalars then encodeAccInstances enc codec a
  else dropCarriedScalarWords enc (encodeAccInstances enc codec a)

/-- The round trip for the DEPLOYED point-pair shape.

    THREE restrictions beyond decodeAcc_encode, and each one is a place the PLAN's
    statement was false rather than a convenience:
    * hkind : enc.kind = .pointPair - the carried scalars are not emitted, so the
      two scalars the decoder produces are the literals 1, which is what hsL / hsR
      pin a's scalars to.
    * hfb : fb.size = 0 - THE PLAN DID NOT SAY THIS AND IT NEEDS IT. For a point-pair
      encoding, fixedScalarCount rejects any non-zero tail, so with a non-empty
      fixed-base table decodeAcc returns none and the equation fails. The deployed
      Moonlight shape has no tail, which is exactly what hfb says. Reported as the
      third false-as-written statement found in this layer.
    * the carried scalars of a are 1, matching what the decoder can produce.

    PROOF OBLIGATION, registered in SORRY.md. -/
theorem decodeAcc_encode_pointPair {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (hp : p < 2 ^ 256)
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointPair)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (hsL : sL = 1) (hsR : sR = 1)
    (fb : Array (AccFixedBase G₁)) (hfb : fb.size = 0)
    (pre : Array Word256) (hpre : pre.size = enc.offset) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := #[] } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (pre ++ encodeAccPublicInput (toExec enc) codec a) =
          some (negateByTable fb a) := by
  sorry

/-! ### 4. The algebra the S5 statements and the pairing lift consume -/

/-- A Decidable witness as a Bool, read back as an iff. The bridge between the
    Bool-typed checks of plan 9.2 and the Prop-level pairing equations. -/
theorem decideBool_eq_true_iff {α : Type} {a b : α} (d : Decidable (a = b)) :
    decideBool d = true <-> a = b := by
  cases d <;> simp [decideBool, *]

section Msm
variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]

/-- The zip-fold of an MSM with the zero-dropping filterMap folded away. -/
private def msmProd (l : List (Fr p × G₁)) : G₁ :=
  l.foldl (fun acc (s, b) => acc * gsmul (p := p) s b) 1

/-- Dropping the zero-scalar pairs changes nothing, because 0 • b = 1 and
    multiplying by 1 on the right is a no-op. Generalised over the accumulator,
    which is what makes the induction go: foldl threads it through the list. -/
private theorem foldl_dropZero (l : List (Fr p × G₁)) :
    ∀ (acc : G₁),
      (l.filterMap fun (s, b) => if s = 0 then none else some (s, b)).foldl
          (fun acc (s, b) => acc * gsmul (p := p) s b) acc
        = l.foldl (fun acc (s, b) => acc * gsmul (p := p) s b) acc := by
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
      cases x with
      | mk s b =>
        intro acc
        by_cases hs : s = 0
        · subst hs
          simp only [List.filterMap_cons, List.foldl_cons, reduceIte, gsmul_zero, mul_one]
          exact ih acc
        · simp only [List.filterMap_cons, List.foldl_cons, hs]
          exact ih (acc * gsmul (p := p) s b)

/-- msmSpecific IS the fold over the zip. This is the lemma both holes reduce to:
    with it the [1] shortcut in MSMKZG.eval is seen to be a no-op and the
    filterMap disappears. -/
private theorem msmSpecific_eq_msmProd (coeffs : Array (Fr p)) (bases : Array G₁) :
    msmSpecific (p := p) coeffs bases = msmProd (List.zip coeffs.toList bases.toList) := by
  show ((List.zip coeffs.toList bases.toList).filterMap
          fun (s, b) => if s = 0 then none else some (s, b)).foldl
          (fun acc (s, b) => acc * gsmul (p := p) s b) 1 = _
  rw [foldl_dropZero]
  rfl

/-- The fold splits over an appended list: prod (l₁ ++ l₂) = prod l₁ * prod l₂.
    This is the whole content of eval_addMsm once the zip splits too. -/
private theorem msmProd_append (l₁ l₂ : List (Fr p × G₁)) :
    msmProd (p := p) (l₁ ++ l₂) = msmProd (p := p) l₁ * msmProd (p := p) l₂ := by
  have hstep : ∀ (l : List (Fr p × G₁)) (s : Fr p) (b : G₁),
      msmProd (p := p) ((s, b) :: l)
        = l.foldl (fun acc q => acc * gsmul (p := p) q.1 q.2) (gsmul (p := p) s b) := by
    intro l s b
    show ((s, b) :: l).foldl (fun acc (s, b) => acc * gsmul (p := p) s b) 1 = _
    simp only [List.foldl_cons, one_mul]
  have key : ∀ (l : List (Fr p × G₁)) (acc : G₁),
      l.foldl (fun acc (s, b) => acc * gsmul (p := p) s b) acc = acc * msmProd (p := p) l := by
    intro l
    induction l with
    | nil => intro acc; simp [msmProd]
    | cons x xs ih =>
        cases x with
        | mk s b =>
          intro acc
          show xs.foldl (fun acc q => acc * gsmul (p := p) q.1 q.2) (acc * gsmul (p := p) s b) = _
          rw [ih (acc * gsmul (p := p) s b), hstep, ih (gsmul (p := p) s b), mul_assoc]
  show (l₁ ++ l₂).foldl (fun acc (s, b) => acc * gsmul (p := p) s b) 1 = _
  rw [List.foldl_append, key, key]
  simp only [one_mul]

/-- Scaling every scalar of the fold by c scales the value by c. The induction is
    over the accumulator, not the list value: gsmul c is a group endomorphism
    (gsmul_mul) and (s * c) • b = c • (s • b) (gsmul_mul_gsmul). -/
private theorem msmProd_map_scale (c : Fr p) (l : List (Fr p × G₁)) :
    msmProd (p := p) (l.map fun q => (q.1 * c, q.2)) = gsmul (p := p) c (msmProd (p := p) l) := by
  have key : ∀ (l : List (Fr p × G₁)) (acc : G₁),
      (l.map fun q => (q.1 * c, q.2)).foldl (fun acc q => acc * gsmul (p := p) q.1 q.2)
          (gsmul (p := p) c acc)
        = gsmul (p := p) c (l.foldl (fun acc q => acc * gsmul (p := p) q.1 q.2) acc) := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x xs ih =>
        cases x with
        | mk s b =>
          intro acc
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have h1 : gsmul (p := p) (s * c) b = gsmul (p := p) c (gsmul (p := p) s b) := by
            rw [mul_comm, gsmul_mul_gsmul]
          rw [h1, ← gsmul_mul, ih (acc * gsmul (p := p) s b)]
  show (l.map fun q => (q.1 * c, q.2)).foldl (fun acc q => acc * gsmul (p := p) q.1 q.2) 1 = _
  rw [← gsmul_one_pt c]
  exact key l 1

/-- Mapping the left list maps the zip: zip (map f cs) bs = map (λ p => (f p.1,
    p.2)) (zip cs bs). Mathlib's List.zip_map_left is stated with Prod.map f id,
    which is the same function but not the same pattern, and the length-free form
    is what scale needs (zip truncates, map does not change lengths). -/
private theorem zip_map_left {α β γ : Type} (f : α → β) :
    ∀ (cs : List α) (bs : List γ),
      List.zip (cs.map f) bs = (List.zip cs bs).map fun q => (f q.1, q.2) := by
  intro cs
  induction cs with
  | nil => intro bs; cases bs <;> rfl
  | cons a t ih =>
      intro bs
      cases bs with
      | nil => rfl
      | cons b rest => simp only [List.map_cons, List.zip_cons_cons, ih rest]

/-- The one-term fold, computed: msmSpecific #[1] bases = bases.getD 0 1. This is
    the [1] shortcut and the msmSpecific branch agreeing on their common domain. -/
private theorem msmSpecific_one_left (bases : Array G₁) :
    msmSpecific (p := p) #[1] bases = bases.getD 0 1 := by
  cases bases with
  | mk l =>
      cases l with
      | nil => simp [msmSpecific, Array.getD]
      | cons b rest => simp [msmSpecific, Array.getD, gsmul_one]

/-- **The [1] shortcut in MSMKZG.eval is a no-op on every input.** Stated once
    here rather than inside each hole, because both holes need it and because it
    is the precise content of the docstring claim that the shortcut "agrees with
    msmSpecific case by case". Positive branch: msmSpecific_one_left. Negative
    branch: reflexivity. -/
theorem MSMKZG.eval_eq_msmSpecific (m : MSMKZG (Fr p) G₁) :
    m.eval = msmSpecific (p := p) m.scalars m.bases := by
  unfold MSMKZG.eval
  split
  · rename_i h
    have hs : m.scalars = #[1] := by
      rw [← Array.toList_inj]
      simpa using h
    rw [hs, msmSpecific_one_left]
  · rfl

/-- Lockstep lengths of a scaled one-term MSM: the hypothesis eval_addMsm needs
    for the accumulator side, where there is no Wf hypothesis to hand. -/
theorem MSMKZG.wf_scale_fromBase (Q : G₁) (c : Fr p) :
    ((MSMKZG.fromBase (p := p) Q).scale c).scalars.size =
      ((MSMKZG.fromBase (p := p) Q).scale c).bases.size := by
  simp [MSMKZG.scale, MSMKZG.fromBase]

/-- A one-term MSM with scalar 1 evaluates to its base: the shortcut in
    MSMKZG.eval fires and there is nothing else to add. -/
theorem MSMKZG.eval_fromBase (Q : G₁) : (MSMKZG.fromBase (p := p) Q).eval = Q := by
  simp [MSMKZG.eval, MSMKZG.fromBase]

/-- Scaling an MSM scales its value. No Wf hypothesis is needed: the [1] shortcut
    in MSMKZG.eval agrees with msmSpecific case by case (scalars #[1] scaled by c
    gives c - B either way, and the empty case is 1 on both sides), which is what
    attack.md's MSMKZG.eval_scale entry concludes and why P1's stronger .Wf
    hypothesis is decorative. PROOF OBLIGATION, registered in SORRY.md. -/
theorem MSMKZG.eval_scale (m : MSMKZG (Fr p) G₁) (c : Fr p) :
    (m.scale c).eval = gsmul c m.eval := by
  rw [MSMKZG.eval_eq_msmSpecific, MSMKZG.eval_eq_msmSpecific]
  show msmSpecific (p := p) (m.scalars.map fun s => s * c) m.bases = _
  rw [msmSpecific_eq_msmProd, msmSpecific_eq_msmProd, Array.toList_map, zip_map_left,
    msmProd_map_scale]

/-- Additivity of the MSM value across addMsm. Lockstep lengths ARE required:
    msmSpecific zips and truncates, so a scalars/bases mismatch silently drops a
    term and the sum changes. PROOF OBLIGATION, registered in SORRY.md. -/
theorem MSMKZG.eval_addMsm (m n : MSMKZG (Fr p) G₁)
    (hm : m.scalars.size = m.bases.size) (hn : n.scalars.size = n.bases.size) :
    (m.addMsm n).eval = m.eval * n.eval := by
  -- Both lockstep lengths are in the statement - they are the MSMKZG.Wf invariant the
  -- sketch carries - but the zip split needs only one of them: List.zip_append takes a
  -- DISJUNCTION, because zip truncates to the shorter side and either equality lines up
  -- the middle boundary. hn is therefore not consumed below; it is kept rather than
  -- dropped because dropping a sketched hypothesis is the drift class this package must
  -- not commit. The have below is what references it.
  have _hnl : n.scalars.toList.length = n.bases.toList.length := by
    rwa [Array.length_toList, Array.length_toList]
  rw [MSMKZG.eval_eq_msmSpecific, MSMKZG.eval_eq_msmSpecific, MSMKZG.eval_eq_msmSpecific]
  show msmSpecific (p := p) (m.scalars ++ n.scalars) (m.bases ++ n.bases) = _
  rw [msmSpecific_eq_msmProd, msmSpecific_eq_msmProd, msmSpecific_eq_msmProd,
    Array.toList_append, Array.toList_append,
    List.zip_append (by rw [Array.length_toList, Array.length_toList]; exact hm),
    msmProd_append]

end Msm

section S5
variable {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! #### The check-level pairing equations the S5 pair and the contract lift consume

    Each of the three Bool checks in this section is decideBool applied to an
    equation in Gt, so each one is a named Prop once decideBool_eq_true_iff and the
    toMul/ofMul identity transport are paid for. Naming them is what makes the four
    holes below one-line rewrites rather than four copies of the same unfolding. -/

/-- The two notations for the identity agree: toMul z = 1 exactly when z = 0. Both
    directions are rfl on the Additive tags (ofMul (toMul z) = z and ofMul 1 = 0),
    so no Mathlib transport lemma is needed - and none is in the built surface. -/
theorem toMul_eq_one_iff_zero {G : Type} [Group G] (z : Additive G) :
    Additive.toMul z = (1 : G) ↔ z = 0 := by
  constructor
  · intro h; apply_fun Additive.ofMul at h; exact h
  · intro h; exact h

/-- DualMSM.check in the Prop it decides. This is the form every pairing lift
    consumes: the two pairing terms, in the reference orientation (left paired
    with sG2, right with nG2 - the swap against the contract orientation is
    dualMsm_check_iff_contract below). -/
theorem dualMsm_check_eq (d : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) :
    DualMSM.check d params = true <->
      P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2Prepared) +
      P.e (Additive.ofMul d.right.eval) (Additive.ofMul params.nG2Prepared) = 0 := by
  unfold DualMSM.check
  dsimp only
  rw [decideBool_eq_true_iff]
  exact toMul_eq_one_iff_zero _

/-- KzgAcc.check in the same Prop: the accumulator invariant e(lhs, [tau]_2) =
    e(rhs, [1]_2) of accumulator.rs:16-25, read through the one-term-per-side
    DualMSM that check builds. -/
theorem kzgAcc_check_eq (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (tbl : Array (String × G₁)) :
    KzgAcc.check a params tbl = true <->
      P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
      P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared) = 0 := by
  unfold KzgAcc.check DualMSM.new
  dsimp only
  rw [dualMsm_check_eq, MSMKZG.eval_fromBase, MSMKZG.eval_fromBase]

/-- **The batched equation, stated once.** batchedCheck adds alpha times the
    accumulator pair to the KZG pair inside one DualMSM.check, so by bilinearity
    its Prop is X + alpha - Y where X is the DualMSM.check equation and Y is the
    KzgAcc.check equation. That single display is what both S5 halves are about,
    and it is why neither needs an exponent model or a cyclic-group lemma. -/
theorem batchedCheck_eq (params : ParamsVerifierKZG G₁ G₂) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (alpha : Fr p) :
    batchedCheck params alpha d a tbl = true <->
      (P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2Prepared) +
       P.e (Additive.ofMul d.right.eval) (Additive.ofMul params.nG2Prepared)) +
      alpha • (P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
               P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared)) = 0 := by
  unfold batchedCheck
  dsimp only
  rw [dualMsm_check_eq, DualMSM.new]
  have hl : (d.left.addMsm ((MSMKZG.fromBase (p := p) (a.lhs.eval tbl)).scale alpha)).eval
      = d.left.eval * gsmul (p := p) alpha (a.lhs.eval tbl) := by
    rw [MSMKZG.eval_addMsm (hm := hWf.1) (hn := MSMKZG.wf_scale_fromBase _ _),
        MSMKZG.eval_scale, MSMKZG.eval_fromBase]
  have hr : (d.right.addMsm ((MSMKZG.fromBase (p := p) (a.rhs.eval tbl)).scale alpha)).eval
      = d.right.eval * gsmul (p := p) alpha (a.rhs.eval tbl) := by
    rw [MSMKZG.eval_addMsm (hm := hWf.2) (hn := MSMKZG.wf_scale_fromBase _ _),
        MSMKZG.eval_scale, MSMKZG.eval_fromBase]
  rw [hl, hr]
  have key : P.e (Additive.ofMul (d.left.eval * gsmul (p := p) alpha (a.lhs.eval tbl)))
        (Additive.ofMul params.sG2Prepared) +
      P.e (Additive.ofMul (d.right.eval * gsmul (p := p) alpha (a.rhs.eval tbl)))
        (Additive.ofMul params.nG2Prepared)
      = (P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2Prepared) +
         P.e (Additive.ofMul d.right.eval) (Additive.ofMul params.nG2Prepared)) +
        alpha • (P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
                 P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared)) := by
    have o1 : (Additive.ofMul (d.left.eval * gsmul (p := p) alpha (a.lhs.eval tbl)) : Additive G₁)
        = Additive.ofMul d.left.eval + Additive.ofMul (gsmul (p := p) alpha (a.lhs.eval tbl)) := rfl
    have o2 : (Additive.ofMul (d.right.eval * gsmul (p := p) alpha (a.rhs.eval tbl)) : Additive G₁)
        = Additive.ofMul d.right.eval + Additive.ofMul (gsmul (p := p) alpha (a.rhs.eval tbl)) := rfl
    have g1 : Additive.ofMul (gsmul (p := p) alpha (a.lhs.eval tbl))
        = alpha • Additive.ofMul (a.lhs.eval tbl) := rfl
    have g2 : Additive.ofMul (gsmul (p := p) alpha (a.rhs.eval tbl))
        = alpha • Additive.ofMul (a.rhs.eval tbl) := rfl
    rw [o1, o2, g1, g2, LinearMap.map_add, LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_add]
    abel
  rw [key]

/-- S5 completeness half: if both equations hold then the alpha-batched equation
    holds, for every alpha (bilinearity: the batched value is X + alpha - Y with X
    and Y each 0). No alpha <> 0 side condition is needed - the argument is linear in
    alpha and alphaOf maps 0 to 1 anyway.

    PROOF OBLIGATION, registered in SORRY.md (M5-5's statement, M9's proof). hWf is
    what eval_addMsm needs and is the owed prepareMsgs-Wf lemma, taken as a
    hypothesis until then. -/
theorem batched_complete (params : ParamsVerifierKZG G₁ G₂) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hd : DualMSM.check d params = true) (ha : KzgAcc.check a params tbl = true)
    (alpha : Fr p) : batchedCheck params alpha d a tbl = true := by
  rw [batchedCheck_eq params d a tbl hWf alpha]
  have hX := (dualMsm_check_eq (p := p) d params).mp hd
  have hY := (kzgAcc_check_eq (p := p) a params tbl).mp ha
  rw [hX, hY, smul_zero, add_zero]

/-- S5 soundness half: if either equation fails then at most one alpha makes the
    batched one pass. Over the ZMod p-module Additive Gt (a field, so no zero
    divisors), X + alpha - Y = 0 = X + beta - Y with alpha <> beta forces
    (alpha - beta) - Y = 0, hence Y = 0, hence X = 0 - contradicting the failure.
    PROOF OBLIGATION, registered in SORRY.md. -/
theorem batched_atMostOneRoot (params : ParamsVerifierKZG G₁ G₂)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hbad : DualMSM.check d params = false \/ KzgAcc.check a params tbl = false)
    (alpha beta : Fr p) (hα : batchedCheck params alpha d a tbl = true)
    (hβ : batchedCheck params beta d a tbl = true) : alpha = beta := by
  have hα' := (batchedCheck_eq params d a tbl hWf alpha).mp hα
  have hβ' := (batchedCheck_eq params d a tbl hWf beta).mp hβ
  by_contra hne
  -- Write X for the DualMSM sum and Y for the accumulator sum, exactly as
  -- batchedCheck_eq displays them. hα' : X + alpha - Y = 0 and hβ' : X + beta - Y = 0,
  -- so (alpha - beta) - Y = 0; ZMod p is a field, so a nonzero scalar is cancellable,
  -- giving Y = 0 and then X = 0 - which says neither check failed, contradicting hbad.
  have hsub : (alpha - beta) • (P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
               P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared)) = 0 := by
    have h2 : P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2Prepared) +
      P.e (Additive.ofMul d.right.eval) (Additive.ofMul params.nG2Prepared) + alpha • (P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
               P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared)) = P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2Prepared) +
      P.e (Additive.ofMul d.right.eval) (Additive.ofMul params.nG2Prepared) + beta • (P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
               P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared)) := by rw [hα', hβ']
    rw [sub_smul, add_left_cancel_iff.mp h2]
    simp
  have hy0 : P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
               P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared) = 0 := by
    have h1 : (alpha - beta)⁻¹ • ((alpha - beta) • (P.e (Additive.ofMul (a.lhs.eval tbl)) (Additive.ofMul params.sG2Prepared) +
               P.e (Additive.ofMul (a.rhs.eval tbl)) (Additive.ofMul params.nG2Prepared))) =
        (alpha - beta)⁻¹ • (0 : Additive Gₜ) := by rw [hsub]
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul, smul_zero] at h1
    exact h1
  have hx0 : P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2Prepared) +
      P.e (Additive.ofMul d.right.eval) (Additive.ofMul params.nG2Prepared) = 0 := by
    rw [hy0, smul_zero] at hα'
    rwa [add_zero] at hα'
  obtain hbd | hbd := hbad
  · exact Bool.false_ne_true
      (hbd.symm.trans ((dualMsm_check_eq (p := p) d params).mpr hx0))
  · exact Bool.false_ne_true
      (hbd.symm.trans ((kzgAcc_check_eq (p := p) a params tbl).mpr hy0))

/-- The contract orientation at CHECK level: e(PAIRING_RHS, G2) *
    e(PAIRING_LHS, NEG_S_G2) = 1. The swap is FinalPairing.yul:88
    (ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)) against the frame
    layout at AssemblyHelpers.yul:284-287 ([lhs | G2_BASE | rhs | NEG_S_G2_BASE]). -/
def contractPairingHolds (g2 negSG2 : G₂) (lhs rhs : G₁) : Prop :=
  P.e (Additive.ofMul rhs) (Additive.ofMul g2) +
      P.e (Additive.ofMul lhs) (Additive.ofMul negSG2) = 0

/-- Lift of Spec.Lemmas.pairing_reorder to DualMSM.check. Only linearity in the G2
    slot is needed (ofMul_inv, map_neg, neg_add), so no exponent model and no
    cyclic-group lemma - attack.md's dualMsm_check entry confirms P3's reading
    against P2's heavier one, and exists_zmod_smul_generator below is kept only for
    Spec-level statements.

    hypotheses: hn : nG2Prepared = g2⁻¹ is R-4 (Params.lean builds ofParams with
    g2⁻¹ while the contract embeds G2_BASE = params.g2), hs : sG2Prepared = negSG2⁻¹
    is the NEG_S_G2_BASE = sG2⁻¹ embedding. Both are necessary: with hn dropped the
    two sides differ on the exponent model for lhs = rhs = g1.

    PROOF OBLIGATION, registered in SORRY.md. -/
theorem dualMsm_check_iff_contract (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (params : ParamsVerifierKZG G₁ G₂) (g2 negSG2 : G₂)
    (hn : params.nG2Prepared = g2⁻¹) (hs : params.sG2Prepared = negSG2⁻¹) :
    DualMSM.check d params = true <->
      contractPairingHolds g2 negSG2 d.left.eval d.right.eval := by
  -- No run leg, no exponent model: the lift is linearity in the G2 slot plus the two
  -- inverse pins hn and hs. This is the claim the index flagged for re-measurement.
  rw [dualMsm_check_eq, hn, hs]
  have n1 : P.e (Additive.ofMul d.left.eval) (Additive.ofMul (negSG2⁻¹))
      = - P.e (Additive.ofMul d.left.eval) (Additive.ofMul negSG2) := by
    rw [show (Additive.ofMul (negSG2⁻¹) : Additive G₂) = - Additive.ofMul negSG2 from rfl,
        LinearMap.map_neg]
  have n2 : P.e (Additive.ofMul d.right.eval) (Additive.ofMul (g2⁻¹))
      = - P.e (Additive.ofMul d.right.eval) (Additive.ofMul g2) := by
    rw [show (Additive.ofMul (g2⁻¹) : Additive G₂) = - Additive.ofMul g2 from rfl,
        LinearMap.map_neg]
  rw [n1, n2, ← neg_add, neg_eq_zero]
  unfold contractPairingHolds
  constructor <;> intro h <;> simpa [add_comm] using h

/-- Spec-level: every G1 element is a multiple of the SRS base (prime order makes
    the group cyclic and g1 is nontrivial). TRUE but not needed by the check-level
    lift above; kept because the Spec-level statements consume it. PROOF
    OBLIGATION, registered in SORRY.md. -/
theorem exists_zmod_smul_generator (Q : G₁) : ∃ s : ZMod p, Q = gsmul s P.g₁ := by
  have hfin : Finite G₁ := by
    by_contra hinf
    have hz : Nat.card G₁ = 0 := @Nat.card_eq_zero_of_infinite G₁ ⟨hinf⟩
    rw [PrimeOrderWith.hCard] at hz
    exact absurd hz (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  haveI : Fintype G₁ := Fintype.ofFinite G₁
  have hc : Fintype.card G₁ = p := by rw [← Nat.card_eq_fintype_card, PrimeOrderWith.hCard]
  -- g₁ is nontrivial and its order divides the group order, which is prime: so its
  -- order IS p, and the first p powers of g₁ are pairwise distinct.
  have hord : orderOf P.g₁ = p := by
    have hd : orderOf P.g₁ ∣ Fintype.card G₁ := orderOf_dvd_card
    rw [hc] at hd
    have hne : orderOf P.g₁ ≠ 1 := fun hh => P.hG₁ (orderOf_eq_one_iff.mp hh)
    exact (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p) _ hd).resolve_left hne
  have hinj : Function.Injective (fun n : Fin p => (P.g₁ : G₁) ^ (n : ℕ)) := by
    intro a b hab
    have hab' : (P.g₁ : G₁) ^ a.val = (P.g₁ : G₁) ^ b.val := hab
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hd : orderOf P.g₁ ∣ (b.val - a.val) := by
        refine orderOf_dvd_of_pow_eq_one ?_
        have h2 : (P.g₁ : G₁) ^ a.val * (P.g₁ : G₁) ^ (b.val - a.val)
            = (P.g₁ : G₁) ^ a.val * 1 := by
          rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt), hab', mul_one]
        exact mul_left_cancel h2
      rw [hord] at hd
      have hle := Nat.le_of_dvd (by omega : 0 < b.val - a.val) hd
      omega
    · have hd : orderOf P.g₁ ∣ (a.val - b.val) := by
        refine orderOf_dvd_of_pow_eq_one ?_
        have h2 : (P.g₁ : G₁) ^ b.val * (P.g₁ : G₁) ^ (a.val - b.val)
            = (P.g₁ : G₁) ^ b.val * 1 := by
          rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hgt), hab'.symm, mul_one]
        exact mul_left_cancel h2
      rw [hord] at hd
      have hle := Nat.le_of_dvd (by omega : 0 < a.val - b.val) hd
      omega
  -- p distinct powers in a p-element group: the pigeonhole closes it.
  have hsurj : Function.Surjective (fun n : Fin p => (P.g₁ : G₁) ^ (n : ℕ)) := by
    by_contra hnot
    have hlt := Fintype.card_lt_of_injective_not_surjective
      (fun n : Fin p => (P.g₁ : G₁) ^ (n : ℕ)) hinj hnot
    rw [Fintype.card_fin, hc] at hlt
    omega
  obtain ⟨⟨n, _hnlt⟩, hn2⟩ := hsurj Q
  have hn2' : (P.g₁ : G₁) ^ (n : ℕ) = Q := hn2
  exact ⟨(n : ZMod p), hn2'.symm.trans ((gsmul_nat n P.g₁).symm)⟩

end S5

/-! ### 5. Canonicality of raw instance words -/

/-- The contract's canonicality gate on one instance word
    (TranscriptProofParser.yul:63-68: lt(inst_be, r)). A word at or above p is
    none, not a reduction - that is the R-26.7 point. -/
def frOfWord? (w : Word256) : Option (Fr p) :=
  if w.toNat < p then some (Nat.cast w.toNat) else none

/-- The same gate lifted over the whole instance array. ContractRefAcceptsAcc below
    takes instW : Array Word256 rather than Array (Fr p) precisely so this rejection
    stays visible. -/
def instOfWords? (ws : Array Word256) : Option (Array (Fr p)) :=
  (ws.toList.mapM frOfWord?).map List.toArray

/-! ### 6. The acceptance predicate with the accumulator arm -/

/-- PLAN 9.5 ContractRef.accepts with the accumulator arm, over RAW instance words
    so the >= r rejections of validate_public_accumulator stay visible (R-26.7), and
    with an explicit vkDigest word (attack.md's ContractRefAcceptsAcc entry settles
    on P1's signature: P2's frWord vk.transcriptRepr loses the >= r rejection and
    P3's liftWord reduces mod p).

    fb is the generated POSITIVE-base table (artifacts.rs:181-227) passed in as a
    parameter because Midfall.Halo2.fixedBases' "-G" entry is the identity (R-52, a
    live Exec-row defect) and must not appear in any statement until it is fixed.
    alphaOf's argument order is (kzgLhs kzgRhs accLhs accRhs) while the hashed
    preimage order is tag || vk_digest || RHS || LHS || ACC_RHS || ACC_LHS
    (FinalPairing.yul:21-26) - the R-11 trap, spelled out in Exec/Accumulator.lean's
    alphaOf doc comment.

    The encoding is the GENERATOR one (hazard 1) and the decoder is applied to
    (toExec enc), which is what makes this the statement PLAN 9.5 means. The
    vkDigest_spec link (vkDigest = frWord vk.transcriptRepr) is an Obligations field
    because it needs feToU256_frToRepr, which is in Lowering/VkDigest.lean. -/
def ContractRefAcceptsAcc {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (cfgAcc : Option Midfall.Generator.AccumulatorEncoding)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (ms : List (Msg (Fr p) G₁)) : Bool :=
  match instOfWords? (p := p) instW with
  | none => false
  | some inst =>
    match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
    | .error _ => false
    | .ok d =>
      match cfgAcc with
      | none => DualMSM.check d params
      | some enc =>
        match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW with
        | none => false
        | some a =>
          let tbl := fb.map (fun b => (b.name, b.base))
          let (accL, accR) := a.fullyCollapse tbl
          batchedCheck params
            (alphaOf (p := p) H vkDigest E.g1 d.left.eval d.right.eval accL accR)
            d a tbl

/-- The no-accumulator arm agrees with the existing ContractRefAccepts, over the
    SAME raw words: the instance rejection is the only difference and with cfgAcc =
    none the decoder is never reached. attack.md's ContractRefAcceptsAcc entry
    requires this lemma to be about the P1 signature (it is) and P3's _none lemma
    restated over it. PROOF OBLIGATION, registered in SORRY.md. -/
theorem contractRefAcceptsAcc_none {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (ms : List (Msg (Fr p) G₁)) :
    ContractRefAcceptsAcc E H params vk none vkDigest fb instW ms = true <->
      (∃ inst, instOfWords? (p := p) instW = some inst ∧
        Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E H params vk inst ms = true) := by
  -- The accumulator arm is unreachable with cfgAcc = none, so the only difference from
  -- ContractRefAccepts is the instance-word gate - and that gate is a conjunct of the
  -- right-hand side rather than a change of behaviour. The show is the delta/iota step
  -- that exposes the outer match; cases on it then finishes both branches.
  show (match instOfWords? (p := p) instW with
        | none => false
        | some inst =>
          Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E H params vk inst ms) = true <->
      (∃ inst, instOfWords? (p := p) instW = some inst ∧
        Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E H params vk inst ms = true)
  cases hw : instOfWords? (p := p) instW <;> simp

/-- PLAN 9.5 contractRef_acc_complete: the R-26.4 direction ONLY (the contract is
    strictly stronger than the reference in accumulator mode, so there is no iff).
    Rust-accepts, plus a decodable accumulator that separately passes its own check,
    implies the contract reference accepts.

    hWf names the DualMSM prepareMsgs produces and gives batched_complete its
    lockstep lengths; it is the owed prepareMsgs-Wf lemma taken as a hypothesis.
    hchk is the accumulator's own invariant, which verifyMsgs does NOT run - that is
    the whole reason the direction is one-way. PROOF OBLIGATION, registered in
    SORRY.md (M5-6; the proof needs batched_complete, i.e. M9). -/
theorem contractRef_acc_complete {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (enc : Midfall.Generator.AccumulatorEncoding)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁))
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hinst : instOfWords? (p := p) instW = some inst)
    (hv : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk inst ms = .ok ())
    (ha : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW = some a)
    (hchk : KzgAcc.check a params (fb.map fun b => (b.name, b.base)) = true)
    (hWf : ∀ d, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok d ->
      d.left.scalars.size = d.left.bases.size /\ d.right.scalars.size = d.right.bases.size) :
    ContractRefAcceptsAcc E H params vk (some enc) vkDigest fb instW ms = true := by
  -- verifyMsgs is prepareMsgs followed by DualMSM.check, so hv names the DualMSM the
  -- contract reference will build and says its own check passed; ha names the decoded
  -- accumulator and hchk its invariant. batched_complete is then the whole argument -
  -- which is exactly what the docstring says this lemma owes to M9.
  obtain ⟨d, hd, hdcheck⟩ :
      ∃ d, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok d ∧
        DualMSM.check d params = true := by
    obtain ⟨d, hd⟩ : ∃ d, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok d := by
      by_contra hno
      obtain ⟨f, hf⟩ : ∃ f, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .error f := by
        cases h : prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
        | ok d => exact absurd ⟨d, h⟩ hno
        | error f => exact ⟨f, rfl⟩
      have h4 : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk inst ms = .error f := by
        unfold verifyMsgs
        rw [hf]
        rfl
      rw [h4] at hv
      simp at hv
    refine ⟨d, hd, ?_⟩
    by_contra hc
    have h5 : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk inst ms
        = (if DualMSM.check d params = true then .ok ()
           else .error (Fault.error Error.opening)) := by
      unfold verifyMsgs
      rw [hd]
      rfl
    rw [h5] at hv
    simp [hc] at hv
  unfold ContractRefAcceptsAcc
  simp only [hinst, hd, ha]
  -- apply, not refine: the batching scalar is read off the goal by unification, and
  -- asking Lean to synthesise it positionally whnf's batchedCheck to death (measured:
  -- 200k heartbeats, timeout; apply closes in milliseconds).
  apply batched_complete
  · exact hWf d hd
  · exact hdcheck
  · exact hchk


/-! ### 7. Known-answer checks

    The toy point type below exists so these gates can RUN: decodeAcc, accWords,
    frOfWord? and negateByTable need no pairing, no group and no curve, only a
    G1Codec, so a two-element stand-in with the all-zero-bytes codec exercises the
    decoder's identity arm exactly the way accIdentityKats_ok exercises the Exec
    one. Midfall/Instances/ stays out (D-P17). -/

namespace Kats

/-- A two-element stand-in for a G1 group, with the codec that maps everything to
    the 128 zero bytes the contract uses for the identity and decodes only those.
    That is enough to drive decodeAcc's identity arm, which is where the R-25
    malleability lives. -/
inductive ToyPt | one | other deriving BEq

def toyCodec : G1Codec ToyPt where
  toEip := fun _ => natToBytesBE 0 128
  ofEip? := fun b => if b == natToBytesBE 0 128 then some .one else none
  toCompressed := fun _ => Bytes.empty
  ofCompressed? := fun _ => none

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The 12-word collapsed point-and-scalar tail at offset 0: x(2) y(2) flag,
    lhs scalar, x(2) y(2) flag, rhs scalar - the layout decodeAcc reads and the
    shape lowering/tests.rs:2051-2073 builds. -/
def tailA : Array Word256 :=
  #[BitVec.ofNat 256 12345, 0, BitVec.ofNat 256 54321, 0, 1, 2,
    BitVec.ofNat 256 999, 0, BitVec.ofNat 256 888, 0, 1, 3]

/-- The same tail with DIFFERENT coordinate words under both identity flags and the
    same scalars. This is the R-25 pair: distinct instance tails, one accumulator. -/
def tailB : Array Word256 :=
  #[BitVec.ofNat 256 7, BitVec.ofNat 256 8, BitVec.ofNat 256 9, BitVec.ofNat 256 10, 1, 2,
    BitVec.ofNat 256 11, BitVec.ofNat 256 12, BitVec.ofNat 256 13, BitVec.ofNat 256 14, 1, 3]

/-- Comparing two decoded accumulators component by component: KzgAcc carries no BEq
    (it is a structure over abstract groups), so the gate compares what it holds. -/
def accParts (a : KzgAcc (Midfall.Fr 17) ToyPt ToyPt ToyPt) :
    List ToyPt × List (Midfall.Fr 17) × List ToyPt × List (Midfall.Fr 17) ×
    List (String × Midfall.Fr 17) :=
  (a.lhs.bases.toList, a.lhs.scalars.toList, a.rhs.bases.toList,
   a.rhs.scalars.toList, a.rhs.fixedBaseScalars.toList)

/-- THE R-25 EVIDENCE. (1) the two tails are different arrays; (2) decodeAcc gives
    the same accumulator for both, so the UNPROJECTED injectivity the plan states is
    false; (3) accWords makes them equal, which is what decodeAcc_injective claims;
    (4) the flag words and the carried scalars survive the normalisation, so a scalar
    change is still visible - the projection is not "zero everything"; (5) with the
    flag cleared the coordinate words survive too, which is the positive control that
    the zeroing is keyed on the flag; (6) two arrays that differ only below enc.offset
    normalise equal but are not equal, which is the window clause earning its place. -/
def accWordsKats_ok : Bool :=
  let enc := AccumulatorEncoding.new 0 7 56
  (tailA != tailB) &&
  (match decodeAcc (p := 17) enc toyCodec (#[] : Array (AccFixedBase ToyPt)) tailA,
         decodeAcc (p := 17) enc toyCodec (#[] : Array (AccFixedBase ToyPt)) tailB with
   | some x, some y => accParts x == accParts y
   | _, _ => false) &&
  (accWords enc tailA == accWords enc tailB) &&
  (accWords enc tailA).size == 12 &&
  (accWords enc tailA).getD 4 0 == 1 && (accWords enc tailA).getD 10 0 == 1 &&
  (accWords enc tailA).getD 5 0 == 2 && (accWords enc tailA).getD 11 0 == 3 &&
  (accWords enc (arraySetD tailA 5 4) != accWords enc tailA) &&
  (let t := arraySetD (arraySetD tailA 4 0) 10 0
   accWords enc t == t) &&
  (accWords enc tailA != tailA) &&
  let enc2 := AccumulatorEncoding.new 2 7 56
  let pre1 := #[BitVec.ofNat 256 111, BitVec.ofNat 256 222]
  let pre2 := #[BitVec.ofNat 256 333, BitVec.ofNat 256 444]
  (accWords enc2 (pre1 ++ tailA) == accWords enc2 (pre2 ++ tailA)) &&
  (pre1 ++ tailA != pre2 ++ tailA)

#eval accWordsKats_ok   -- expect true

/-- frOfWord? / instOfWords?: the canonicality gate the contract applies to every
    instance word (TranscriptProofParser.yul:63-68). A word at or above p is none,
    NOT a reduction - that distinction is R-26.7 and it is what
    ContractRefAcceptsAcc's raw-word interface preserves. The negative control is the
    word equal to p, the smallest value a mod-p reduction would wrongly accept, and
    the last conjunct shows the rejection is whole-array. -/
def instOfWordsKats_ok : Bool :=
  (frOfWord? (p := 17) (BitVec.ofNat 256 16) == some 16) &&
  (frOfWord? (p := 17) (BitVec.ofNat 256 17) == none) &&
  (frOfWord? (p := 17) (BitVec.ofNat 256 0) == some 0) &&
  (instOfWords? (p := 17) #[BitVec.ofNat 256 1, BitVec.ofNat 256 2] == some #[1, 2]) &&
  (instOfWords? (p := 17) #[BitVec.ofNat 256 1, BitVec.ofNat 256 40] == none) &&
  (instOfWords? (p := 17) #[BitVec.ofNat 256 40, BitVec.ofNat 256 1] == none)

#eval instOfWordsKats_ok   -- expect true

/-- negateByTable: a negate base flips its tail scalar, a non-negated one does not,
    and the lhs is never touched (the contract's tail is an RHS-only structure). The
    two-name table with OPPOSITE flags is the perturbation: flipping the flags changes
    the result, so neither arm is decorative. -/
def negateByTableKats_ok : Bool :=
  let fb : Array (AccFixedBase ToyPt) :=
    #[{ name := "-G", base := .one, negate := true },
      { name := "a_com_0", base := .one, negate := false }]
  let a : KzgAcc (Midfall.Fr 17) ToyPt ToyPt ToyPt :=
    { lhs := { bases := #[.one], scalars := #[2],
               fixedBaseScalars := #[("-G", (5 : Midfall.Fr 17))] },
      rhs := { bases := #[.other], scalars := #[3],
               fixedBaseScalars := #[("-G", (5 : Midfall.Fr 17)),
                                      ("a_com_0", (6 : Midfall.Fr 17))] } }
  let n := negateByTable fb a
  ((n.rhs.fixedBaseScalars.toList.map Prod.snd) ==
      [(-5 : Midfall.Fr 17), (6 : Midfall.Fr 17)]) &&
  ((n.rhs.fixedBaseScalars.toList.map Prod.fst) == ["-G", "a_com_0"]) &&
  (n.lhs.fixedBaseScalars.toList == a.lhs.fixedBaseScalars.toList) &&
  (negateByTable (fb.map (fun b => { b with negate := false })) a).rhs.fixedBaseScalars.toList ==
      a.rhs.fixedBaseScalars.toList &&
  (negateByTable (fb.map (fun b => { b with negate := ! b.negate })) a).rhs.fixedBaseScalars.toList !=
      a.rhs.fixedBaseScalars.toList

#eval negateByTableKats_ok   -- expect true

/-- dropCarriedScalarWords removes exactly the two scalar slots and keeps the point
    blocks in order, which is what makes encodeAccPublicInput the inverse of what
    decodeAcc reads for a point-pair layout. The words are tagged by index so a slot
    shift is visible: dropping the wrong slot changes the result. -/
def dropCarriedScalarWordsKats_ok : Bool :=
  let enc := AccumulatorEncoding.new 0 7 56
  let pw := enc.pointWords
  let w := (List.range (2 * pw + 2)).map (fun i => BitVec.ofNat 256 i) |>.toArray
  let d := dropCarriedScalarWords enc w
  d.size == 2 * pw &&
  d.toList == (List.range pw).map (fun i => BitVec.ofNat 256 i) ++
                (List.range pw).map (fun i => BitVec.ofNat 256 (i + pw + 1)) &&
  ! d.toList.contains (BitVec.ofNat 256 pw) &&
  ! d.toList.contains (BitVec.ofNat 256 (2 * pw + 1)) &&
  pw == 5

#eval dropCarriedScalarWordsKats_ok   -- expect true

/-- The restriction decodeAcc_encode_pointPair has to state and the plan does not:
    for a point-pair encoding a NON-EMPTY fixed-base tail makes the decode none,
    because fixedScalarCount rejects any non-zero tail (api.rs:178-186, KAT at
    lowering/tests.rs:2096-2104). This is the counterexample to the sketch's
    inherited binders, as a gate. The last conjunct is the positive control: the
    point-and-scalar layout DOES read the two carried scalars verbatim. -/
def pointPairTailKats_ok : Bool :=
  let pp := AccumulatorEncoding.pointPair 0 7 56
  let noTail : Array Word256 := #[0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
  let withTail : Array Word256 := noTail ++ #[BitVec.ofNat 256 4]
  (AccumulatorEncoding.fixedScalarCount pp 10 == some 0) &&
  (AccumulatorEncoding.fixedScalarCount pp 11 == none) &&
  ((decodeAcc (p := 17) (G₂ := ToyPt) (Gₜ := ToyPt) pp toyCodec
        #[{ name := "-G", base := ToyPt.one, negate := false }] withTail).isNone) &&
  (match decodeAcc (p := 17) pp toyCodec (#[] : Array (AccFixedBase ToyPt)) noTail with
   | some a => accParts a == ([.one], [1], [.one], [1], [])
   | none => false) &&
  (match decodeAcc (p := 17) (AccumulatorEncoding.new 0 7 56) toyCodec
      (#[] : Array (AccFixedBase ToyPt)) tailA with
   | some a => accParts a == ([.one], [2], [.one], [3], [])
   | none => false)

#eval pointPairTailKats_ok   -- expect true

end Kats


/-! ### 8. D-P23 evidence for the holes this package closed

    Each claim below gets BOTH halves as theorems: a satisfiability witness and a
    falsification. They are stated over the abstract bundle, not at concrete bytes:
    Accumulator.lean is theorem-bearing and may not import Midfall/Instances/ (D-P17),
    so concrete-byte exhibits belong to Instances/ and are NOT claimed here.

    NOT CLAIMED, stated as a limit rather than hidden: the four pairing-level claims
    (dualMsm_check_iff_contract, batched_complete, batched_atMostOneRoot,
    contractRef_acc_complete) have NO witness/falsification pair in this change. The
    exhibits were drafted (empty DualMSM, trivial accumulator, params with one inverse
    pin broken) and each needs a chain of delta+iota reductions of constructor
    applications - DualMSM.init.left.eval, KzgAcc.trivial.lhs.eval - that this session
    ran out of room to finish; the drafts are not in the file. The reason they are not
    left in commented-out form is the standing rule that a comment is not a proof.
    And per the measured falsification-deletion gap: deleting any falsification
    theorem below leaves the build green and no gate catches it, so no coverage is
    claimed for the *persistence* of these theorems, only for their truth. -/

section Dp23
variable {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **eval_scale, witness.** On a one-term MSM the lemma computes to the scalar
    multiple of the base - the case the [1] shortcut in eval is about. -/
theorem eval_scale_witness (Q : G₁) (c : Fr p) :
    ((MSMKZG.fromBase (p := p) Q).scale c).eval = gsmul (p := p) c Q := by
  rw [MSMKZG.eval_scale, MSMKZG.eval_fromBase]

/-- **eval_scale, falsification.** The factor is not decoration: scaling a
    non-identity one-term MSM by 0 changes its value, so the tempting weakening
    '(m.scale c).eval = m.eval' is false for some m and c. -/
theorem eval_scale_falsifies (Q : G₁) (hQ : Q ≠ 1) :
    ∃ (m : MSMKZG (Fr p) G₁) (c : Fr p), (m.scale c).eval ≠ m.eval :=
  ⟨MSMKZG.fromBase (p := p) Q, 0, by
    rw [MSMKZG.eval_scale, MSMKZG.eval_fromBase, gsmul_zero]; exact fun hh => hQ hh.symm⟩

/-- **eval_addMsm, witness.** Two one-term channels add to the product of their
    bases - the shape prepareMsgs builds when it concatenates MSMs. -/
theorem eval_addMsm_witness (Q R : G₁) :
    ((MSMKZG.fromBase (p := p) Q).addMsm (MSMKZG.fromBase (p := p) R)).eval = Q * R := by
  rw [MSMKZG.eval_addMsm (hm := by simp [MSMKZG.fromBase]) (hn := by simp [MSMKZG.fromBase]),
      MSMKZG.eval_fromBase, MSMKZG.eval_fromBase]

/-- **eval_addMsm, falsification.** Without the lockstep lengths the statement is
    false: a channel whose scalars and bases disagree silently loses the other
    channel's term under the zip, and the sum law fails. -/
theorem eval_addMsm_falsifies (Q : G₁) (hQ : Q ≠ 1) :
    ∃ (m n : MSMKZG (Fr p) G₁),
      ¬ (m.scalars.size = m.bases.size ∧ n.scalars.size = n.bases.size) ∧
        (m.addMsm n).eval ≠ m.eval * n.eval := by
  refine ⟨⟨#[0], #[], #[]⟩, MSMKZG.fromBase (p := p) Q, ?_, ?_⟩
  · simp [MSMKZG.fromBase]
  · have hA : ((⟨#[0], #[], #[]⟩ : MSMKZG (Fr p) G₁).addMsm
          (MSMKZG.fromBase (p := p) Q)).eval = (1 : G₁) := by
      rw [MSMKZG.eval_eq_msmSpecific]
      show msmSpecific (p := p) (#[0] ++ #[1]) (#[] ++ #[Q]) = 1
      simp [msmSpecific]
    have hB : (⟨#[0], #[], #[]⟩ : MSMKZG (Fr p) G₁).eval = (1 : G₁) := by
      rw [MSMKZG.eval_eq_msmSpecific]
      show msmSpecific (p := p) (#[0] : Array (Fr p)) (#[] : Array G₁) = 1
      simp [msmSpecific]
    rw [hA, hB, MSMKZG.eval_fromBase, one_mul]
    exact fun hh => hQ hh.symm

/-- **exists_zmod_smul_generator, witness.** The generator itself is hit, by s = 1. -/
theorem exists_zmod_smul_witness : ∃ s : ZMod p, P.g₁ = gsmul (p := p) s P.g₁ :=
  ⟨1, by rw [gsmul_one]⟩

/-- **exists_zmod_smul_generator, falsification.** The claim is about a NONTRIVIAL
    base. Replace g₁ by the identity and the analogous statement collapses the whole
    group to one element - so hG₁, the field the statement consumes, is what makes it
    a theorem rather than a tautology about a one-element type. -/
theorem exists_zmod_smul_needs_nontrivial
    (h : ∀ Q : G₁, ∃ s : ZMod p, Q = gsmul (p := p) s (1 : G₁)) : Subsingleton G₁ :=
  ⟨fun a b => by
    obtain ⟨s, hs⟩ := h a
    obtain ⟨t, ht⟩ := h b
    rw [hs, ht, gsmul_one_pt, gsmul_one_pt]⟩

end Dp23

local instance factPrime17dp : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- **contractRefAcceptsAcc_none, witness.** The raw-word gate accepts a list of
    canonical scalars, so the existential on the right-hand side is inhabited and the
    equivalence is not vacuous. -/
theorem instOfWords_witness :
    instOfWords? (p := 17) #[BitVec.ofNat 256 1, BitVec.ofNat 256 2] =
      some #[1, 2] := by decide

/-- **contractRefAcceptsAcc_none, falsification.** The gate REJECTS rather than
    reduces (R-26.7): a word equal to r, or above it, makes the whole array none, in
    either position. Without this the raw-word interface of
    contractRefAcceptsAcc_none would be decorative, because every word list would
    decode. -/
theorem instOfWords_falsifies :
    instOfWords? (p := 17) #[BitVec.ofNat 256 1, BitVec.ofNat 256 40] = none ∧
      instOfWords? (p := 17) #[BitVec.ofNat 256 40, BitVec.ofNat 256 1] = none ∧
      frOfWord? (p := 17) (BitVec.ofNat 256 17) = none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! **contractRef_acc_complete: no D-P23 half is claimed for it here.** The reason is a
    confinement rule, not a missing lemma: its hypothesis bundle names a VerifierEnv, a
    VerifyingKey and a decodable instance array, and the only objects of those types in
    the tree live under Midfall/Instances/, which this file may not import (D-P17). What
    the lemma adds on top of that bundle is batched_complete, and no witness pair is
    claimed for that either (see the limit note at the head of this section). -/

/-! ### The `find?` readback lemmas (P-ACCENC step 3)

  `decodeAcc_injective` does NOT need the fold to be injective as a list equation -
  `accMapInsert_fold_inj` already has that for ascending lists - it needs to read ONE
  scalar back out of the map the decoder built, for a named base. That is a `find?`
  statement, and it splits in two: the key that was inserted, and a key that was not.
  Neither was in the tree before this package; P-LIMB named the pair and landed
  neither. Stated over `toList` because `Array.find?` is NOT `List.find?` on `toList`
  in this toolchain (probed: `l.toArray.find? p = l.find? p` is not rfl), and proved
  through the `go` helper because `accMapInsert.go k v []` does not reduce by `rfl` -
  the equation compiler put it behind `if`, so every arm needs `simp [go]`. -/

private theorem go_find?_inserted {F : Type} : ∀ (l : List (String × F)) (k : String) (v : F),
    (Midfall.Halo2.accMapInsert.go k v l).find? (fun e => e.1 == k) = some (k, v) := by
  intro l
  induction l with
  | nil => intro k v; simp [Midfall.Halo2.accMapInsert.go]
  | cons x xs ih =>
      intro k v
      cases x with
      | mk k' v' =>
          by_cases h : k = k'
          · subst h
            have hb : (k == k) = true := by simp
            simp only [Midfall.Halo2.accMapInsert.go, if_pos hb]
            rw [List.find?_cons]
            simp
          · have hne : ¬ (k == k') := by simp [h]
            have hne2 : ¬ (k' == k) := by simpa using Ne.symm h
            by_cases hlt : k < k'
            · simp only [Midfall.Halo2.accMapInsert.go, if_neg hne, ite_eq_left hlt]
              rw [List.find?_cons]
              simp
            · simp only [Midfall.Halo2.accMapInsert.go, if_neg hne, ite_eq_right hlt]
              rw [List.find?_cons]
              simp [hne2, ih]

private theorem go_find?_other {F : Type} : ∀ (l : List (String × F)) (k k' : String) (v : F),
    ¬ (k' == k) →
    (Midfall.Halo2.accMapInsert.go k v l).find? (fun e => e.1 == k') =
      l.find? (fun e => e.1 == k') := by
  intro l
  induction l with
  | nil =>
      intro k k' v h
      have hneq : ¬ (k = k') := fun g => h (by simp [g])
      simp [Midfall.Halo2.accMapInsert.go, hneq]
  | cons x xs ih =>
      intro k k' v h
      have hneq : ¬ (k = k') := fun g => h (by simp [g])
      have hc2 : (k == k') = false := by simp [hneq]
      cases x with
      | mk k'' v' =>
          by_cases h2 : k = k''
          · subst h2
            have hb : (k == k) = true := by simp
            simp only [Midfall.Halo2.accMapInsert.go, if_pos hb]
            rw [List.find?_cons, List.find?_cons, hc2]
          · have hne : ¬ (k == k'') := by simp [h2]
            by_cases hlt : k < k''
            · simp only [Midfall.Halo2.accMapInsert.go, if_neg hne, ite_eq_left hlt]
              rw [List.find?_cons, List.find?_cons, hc2]
            · simp only [Midfall.Halo2.accMapInsert.go, if_neg hne, ite_eq_right hlt]
              rw [List.find?_cons, List.find?_cons, ih k k' v h]

/-! ### P-TRUNK: D-P23 evidence for the two holes this package closed and the links it landed

  Both halves as THEOREMS, per D-P23. NOT CLAIMED: a satisfiability witness for the
  CONCLUSION of `decodeAcc_encode` needs a concrete `G1Codec` and a concrete curve,
  and those live under `Midfall/Instances/`, which this file may not import (D-P17) - the same
  limit P-ACCENC recorded for the codec-level exhibit. What IS exhibited here is the
  encoding-side bundle at the DEPLOYED shape, and every hypothesis that drives the decoder
  gets a falsification showing it is load-bearing. Per the measured falsification-deletion
  gap (25 times): deleting any of these leaves the build green and no gate catches it, so
  no persistence coverage is claimed here, only truth. -/

local instance factPrime17trunk : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- **Satisfiability witness for the trunk bundle.** The deployed accumulator shape - offset
    4, seven limbs of 56 bits (api.rs:75, layout/mod.rs:296) - satisfies the kind hypothesis,
    the limb-shape hypothesis and link (b) for a 12 + 2 word payload, all at once.
    `decodeAcc_encode` quantifies over exactly this bundle, so it is not vacuous. -/
theorem decodeAcc_encode_witness :
    Midfall.Generator.AccumulatorEncoding.kind
        (Midfall.Generator.AccumulatorEncoding.new 4 7 56) =
      Midfall.Generator.AccumulatorEncodingKind.pointAndScalar ∧
    (toExec (Midfall.Generator.AccumulatorEncoding.new 4 7 56)).limbShapeOk = true ∧
    (toExec (Midfall.Generator.AccumulatorEncoding.new 4 7 56)).fixedScalarCount
        (4 + (toExec (Midfall.Generator.AccumulatorEncoding.new 4 7 56)).fixedPayloadWords + 2)
        = some 2 := by
  refine ⟨rfl, rfl, ?_⟩
  exact AccumulatorEncoding.fixedScalarCount_exact _ 2 rfl rfl

/-- **Falsification: the kind hypothesis of `decodeAcc_encode` is load-bearing.** For a
    `.pointPair` encoding the decoder rejects ANY non-empty tail (api.rs:186) before it reads
    a word, so a round trip over a tail would be `none = some _`. This is why the sketch had
    to split `decodeAcc_encode` into the point-and-scalar and point-pair statements, and why
    `decodeAcc_encode_pointPair` carries `hfb : fb.size = 0`. -/
theorem fixedScalarCount_pointPair_rejects_tail :
    (Midfall.Halo2.AccumulatorEncoding.pointPair 4 7 56).fixedScalarCount (4 + 12 + 2) = none := by
  decide
/-- **Falsification: link (b) needs the limb shape.** The SAME payload length on a six-limb
    encoding answers `none`, so `fixedScalarCount_exact` is gated by `validFor` and not by
    arithmetic. -/
theorem fixedScalarCount_exact_needs_shape :
    (Midfall.Halo2.AccumulatorEncoding.new 4 6 56).fixedScalarCount (4 + 12 + 2) = none := by
  decide

/-- **Satisfiability witness: link (c) computes.** The scalar readback at a real prime. -/
theorem frWord_toNat_witness :
    (Midfall.Halo2.frWord (p := 17) 5).toNat = 5 ∧
    ((Midfall.Halo2.frWord (p := 17) 5).toNat : Midfall.Fr 17) = 5 := by decide

/-- **Falsification: `hneg` is what turns `negateByTable fb a` back into `a`.** With one negated
    table entry the relabelled scalar is `-1`, and `(-1 : Fr 17) ≠ 1`, so the literal
    conclusion of `decodeAcc_encode_noNeg` is false for that table. Stated over `Unit` because
    `negateByTable` needs no group structure, only a field to negate. -/
theorem negateByTable_needs_noNeg :
    ([(⟨("a" : String), (), true⟩ : AccFixedBase Unit)] : List (AccFixedBase Unit)).any
        (fun b => b.name == ("a" : String) && b.negate) = true ∧
    (-1 : Midfall.Fr 17) ≠ (1 : Midfall.Fr 17) := by
  refine ⟨by decide, ?_⟩
  decide
/-- **`find?` readback at the inserted key (P-ACCENC step 3, first of the pair).** Whatever
    the map was before, the entry stored under the key just inserted reads back exactly -
    and it is the only entry under that key, which is what makes the overwrite semantics
    of `accMapInsert` (BTreeMap::insert) safe here. -/
theorem accMapInsert_find?_inserted {F : Type} (m : Array (String × F)) (k : String) (v : F) :
    (accMapInsert m k v).toList.find? (fun e => e.1 == k) = some (k, v) := by
  show (Midfall.Halo2.accMapInsert.go k v m.toList).toArray.toList.find?
      (fun e => e.1 == k) = some (k, v)
  rw [List.toList_toArray]
  exact go_find?_inserted m.toList k v

/-- **`find?` readback at a different key (P-ACCENC step 3, second of the pair).** Inserting
    under one key leaves every OTHER key readback unchanged - the fact `decodeAcc_injective`
    consumes for the base whose word it is not currently looking at. -/
theorem accMapInsert_find?_other {F : Type} (m : Array (String × F)) (k k' : String) (v : F)
    (h : ¬ (k' == k)) :
    (accMapInsert m k v).toList.find? (fun e => e.1 == k') =
      m.toList.find? (fun e => e.1 == k') := by
  show (Midfall.Halo2.accMapInsert.go k v m.toList).toArray.toList.find?
      (fun e => e.1 == k') = m.toList.find? (fun e => e.1 == k')
  rw [List.toList_toArray]
  exact go_find?_other m.toList k k' v h

/-- **`accMapInsert_find?_inserted`, witness**: computed on a real two-name map, so the
    readback is not vacuous. -/
theorem accMapInsert_find?_inserted_witness :
    (accMapInsert #[("a", 1)] "b" 2).toList.find? (fun e => e.1 == "b") = some ("b", 2) :=
  by decide

/-- **`accMapInsert_find?_other`, falsification**: the distinctness hypothesis is
    load-bearing. At k' = k the insert OVERWRITES, so the readback changes and the
    equation of accMapInsert_find?_other fails. -/
theorem accMapInsert_find?_other_needs_ne :
    (accMapInsert #[("b", 1)] "b" 2).toList.find? (fun e => e.1 == "b") ≠
      (#[("b", 1)] : Array (String × Nat)).toList.find? (fun e => e.1 == "b") := by decide





end Midfall.Lowering
