-- |
-- Midfall.Generator.Quotient.VmRecognizers
--
-- THE QVM SHAPE RECOGNIZERS: the code that turns a generic 'QuotientExpr' tree into a
-- fused foreign-field limb shape, and the four hooks P-09c left standing in for it.
-- Ported from proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs
-- (4336 lines at git HEAD), cited below as QVM. Work package P-09f.
--
-- CITATION NOTATION. QVM is vm/mod.rs read through 'git show HEAD:<path>' (docs/plans/
-- README.md standing note 2); every range below was re-derived from that output, and the
-- brief's table is corrected in the table below rather than copied. VT is VmTypes.lean
-- (P-09a's vocabulary), VmReference.lean is P-09b's interpreter, VmBuilder.lean is P-09c's
-- emitter (imported, never re-implemented - hazard 5), VmValidator.lean is P-09e's validator
-- (imported for the same reason) and VmCertify.lean is P-09d's certifier (imported for
-- hazard 4's dual build).
--
--    CITATION CONVENTION. Every range below names the DOC-COMMENT line the Rust item opens
--    through its last body line, which is the convention the brief uses (its "3156-3227" is
--    quotient_limb_shape doc line through quotient_modarith7_shape opening). VmBuilder cites
--    fn-line to closing brace instead, so the same item reads 3157-3173 there: one line of
--    offset at each end, no difference in what is meant. Every statement-level cite was
--    re-checked against the content of the line it names.
--
-- WHAT THIS PACKAGE EXISTS TO DO. P-09a (hazard 4) established that the fallback-on-
-- misrecognition property is NOT carried by the type: a 6-term or 8-term Lin7 is
-- well-typed in Lean and in Rust alike, and what prevents mis-evaluation is the
-- recognizers' length guards (QVM:3667, 3714, 3753), the fixed-width encoding in
-- emit_limb_shape, and finish()'s build-time panic. P-09c (F-5) then found that two
-- recognizer POSTCONDITIONS - 'matched' is non-empty, and the residue is strictly
-- smaller than the input - are not enforced anywhere, and demonstrated the consequence:
-- a hook returning an empty 'matched' makes the builder report depth 0 and emit a program
-- the interpreter rejects (VmBuilder.lean:2415-2431). Both obligations are made real here
-- and gated: recognizersProduceWellFormedShapes_ok, subshapeMatchedNonEmpty_ok and
-- subshapeResidueShrinks_ok.
--
-- CORRECTED REFERENCE TABLE (the brief's four ranges, re-derived against HEAD).
--
--   brief 3156-3227 -> actual 3156-3237: quotient_limb_shape (3156-3172),
--     quotient_pow5_base (3175-3186), quotient_limb_subshape (3189-3226),
--     quotient_modarith7_shape (3230-3237). The brief's end line cut
--     quotient_modarith7_shape in half.
--   brief 3649-3813 -> actual 3653-3812: try_quotient_lin7_shape (3653-3676),
--     try_quotient_bilin7_row_shape (3682-3726), try_quotient_bilin7_pairwise_shape
--     (3735-3812). The brief's start line is the doc comment above the first item's doc.
--   brief 3440-3530 -> actual 3425-3529: the u16::try_from(..).ok()? producers P-09a
--     hazard 2 named, QVM:3445 (add_factored_affine_product_terms) and QVM:3506
--     (quotient_factored_bilin7_row_shape). The brief's range MISSES the third and most
--     load-bearing one: QVM:4024, inside quotient_product_mem_factors, which is the ONLY
--     u16 guard on the LIN7 / BILIN7 pointer path (hazard 3).
--   brief 3815-4083 -> actual 3815-4081: try_quotient_lin7_subshape (3815-3861),
--     try_quotient_bilin7_row_subshape (3864-3911), try_quotient_bilin7_pairwise_subshape
--     (3914-3985), quotient_mem_term (3988-3995), quotient_product_mem_pair (3999-4006),
--     quotient_product_mem_factors (4012-4029), add_grouped_limb_coeff (4032-4038),
--     limb7_base_candidates (4041-4055), limb7_index (4058-4066), quotient_fq_from_u256
--     (4072-4076), quotient_fq_to_u256 (4079-4081). QVM:4084 begins parse_mem, which is
--     P-09c's Yul parser, not a recognizer.
--   NOT IN THE BRIEF AT ALL: collect_product_expr_factors (3123-3136), quotient_sum_expr
--     (3139-3141), quotient_scaled_term_expr (3144-3153), quotient_condition_factor
--     (3241-3253), quotient_modarith7_affine_shape (3257-3397, the largest single item
--     here), remove_quotient_terms (3400-3408), add_grouped_product_coeff (3411-3421),
--     add_factored_affine_product_terms (3425-3473),
--     try_quotient_factored_bilin7_row_subshape (3476-3485),
--     quotient_factored_bilin7_row_shape (3488-3529), collect_quotient_affine_terms
--     (3553-3597), collect_quotient_sum_terms (3604-3646), and - required by
--     quotient_pow5_base and outside every range the brief names - quotient_expr_key
--     (2831-2843) with quotient_commutative_expr_key (2990-3002).
--
-- modarith7_coeffs (QVM:3532-3549) is the one cluster item NOT re-ported here: P-09c
-- already moved it into VmBuilder.lean:404-413 (its own WHAT MOVED 5) because the
-- preflight needs it, and hazard 5 says import rather than re-implement. This file uses
-- that copy and cites it at the site.
--
-- WHAT MOVED (Lean is order-sensitive; plans README standing note 3).
-- 1. The Fr helpers (QVM:4072-4081) move to the top: every collector uses them, and the
--    Rust's implicit 'Fq' import has no Lean counterpart.
-- 2. quotient_expr_key (QVM:2831) and quotient_commutative_expr_key (QVM:2990) move up
--    above quotient_pow5_base (QVM:3175), their only caller in this cluster. The Rust's two
--    are mutually recursive; Lean's structural checker will not use that (see the cite at
--    quotientCommutativeExprKey), so the keying happens at the call site and the helper takes
--    two strings. Same rendering, same order, one less mutual block.
-- 3. collect_product_expr_factors (QVM:3123) and the two term constructors (QVM:3139,
--    3144) move above their callers.
-- 4. quotient_mem_term / quotient_product_mem_pair / quotient_product_mem_factors
--    (QVM:3988-4029), add_grouped_limb_coeff (QVM:4032), limb7_base_candidates (QVM:4041)
--    and limb7_index (QVM:4058) move above the first shape matcher, which is where Rust
--    leaves them at the BOTTOM of the cluster.
-- 5. collect_quotient_sum_terms (QVM:3604) and collect_quotient_affine_terms (QVM:3553)
--    move above the matchers that consume them.
-- 6. The three whole-expression matchers (QVM:3653-3812) move above the three subshape
--    matchers (QVM:3815-3985); Rust needs no order because it is not scheduled.
-- 7. quotient_modarith7_affine_shape's accumulator loop (QVM:3273-3328) becomes a
--    fuelled recursion (R10, below) and is pulled above its only caller.
-- 8. Each of the six matcher bodies is split into a per-candidate helper (lin7SubshapeForBase,
--    bilin7RowSubshapeForCandidate, bilin7PairwiseSubshapeForBases, pairwiseDiagonals) plus a
--    firstSome scan over the candidates, because Lean cannot express Rust's early 'return'
--    from inside a nested loop any other way. firstSome is the one shape shared by all five
--    candidate loops.
--
-- R4, PANICS AND WIDTHS. The reference profile is release (BASELINE.md:143): arithmetic
-- overflow is NOT a panic and debug_assert! is compiled out, but indexing and division by
-- zero still panic. Four consequences are modelled explicitly rather than glossed.
-- (a) 'u16::try_from(x).ok()?' (QVM:3445, 3506, 4024) is a REJECTION, not a panic: that is
--     hazard 3's safety valve, ported as u16TryFrom.
-- (b) 'base + (limb as u16) * WORD_BYTES as u16' (QVM:3831) is plain u16 arithmetic, so in
--     release it WRAPS at 2^16 rather than panicking. Ported as u16Add with the modulus.
--     The wrap is faithful and not cosmetic: a base above 0xff3f can alias a low pointer and
--     make a limb look present. limb7_base_candidates' 'checked_add' (QVM:4048) and
--     limb7_index's 'checked_sub' (QVM:4060) are u16CheckedAdd / u16CheckedSub, which is what
--     the Rust actually calls at those two sites. The two differ, and the port keeps the
--     difference.
-- (c) The four unreachable!("... recognizer returned non-... shape") panics inside the
--     MODARITH7 accumulator (QVM:3286, 3298, 3310, 3322) are real build aborts. They are
--     ported as panicAt sites in the loop, which therefore lives in P-09c's M monad;
--     quotientModarith7AffineShape renders an error as "not recognized" because its return
--     type is Option, and portBoundsNeverBind_ok gates that neither the fuel nor the four
--     unreachable leg fires on any fixture. This is the one place where the port is WEAKER
--     than the Rust by construction, and it is stated here rather than buried: a future
--     recognizer that returned the wrong variant would fall back instead of aborting the
--     build.
-- (d) 'coeff.expect("pairwise sum coefficient")' (QVM:3805, 3976) is likewise a release
--     panic at an unreachable position: 'seen' is all true, so every i + j diagonal has been
--     written. Rendered as a rejection, same reasoning as (c).
--
-- R10, FUEL. The MODARITH7 accumulator is a Rust 'loop' that terminates because every
-- 'continue' removes at least one term (QVM:3288, 3300, 3312, 3324 each follow a non-empty
-- 'used' guard at QVM:3275/3292/3304/3316). Lean cannot see that, so the loop takes an
-- explicit fuel of terms.length + 1 and panics when it runs out - the same device
-- VmBuilder.lean:93 uses for emit_expr. portBoundsNeverBind_ok asserts the bound is never
-- reached, so the fuel is a totality crutch and not a behaviour.
--
-- NO THEOREM HERE, AND NOTHING UNDER Instances/ IS IMPORTED (D-P17). Everything below is
-- computable and every gate is a Bool or an IO Bool with a matching
-- '#eval ... -- expect true' line at the end of the file (R-38). D-P19 binds the artifact
-- gates: recognizerClusterHasNoLabelRead_ok opens vm/mod.rs while it evaluates and inspects
-- the recognizer cluster for label reads, and the reachability gate
-- recognizerArtifactReachable_ok runs FIRST so a wrong path is diagnosed rather than
-- silently matched (plans README, D-P19 standing note).

import Midfall.Common.Bytes
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmValidator
import Midfall.Generator.Quotient.VmCertify

namespace Midfall.Generator.QuotientRecognizers

open Midfall.Generator.QuotientBuilder

/-- The four unreachable! sites of the MODARITH7 accumulator, plus the port-only fuel site.
    Named here rather than inlined so no site text is split across lines (VmBuilder's own
    convention, its WHAT MOVED 6). -/
def sitePairwiseNotPairwise : String :=
  qvmPath ++ ":3286 (pairwise recognizer returned non-pairwise shape)"
def siteFactoredRowNotRow : String :=
  qvmPath ++ ":3298 (factored row recognizer returned non-row shape)"
def siteRowNotRow : String :=
  qvmPath ++ ":3310 (row recognizer returned non-row shape)"
def siteLinNotLin : String :=
  qvmPath ++ ":3322 (linear recognizer returned non-linear shape)"
def siteModarith7LoopFuel : String :=
  qvmPath ++ ":3273 (MODARITH7 accumulator fuel exhausted - port-only bound, see the header)"

/-! ## Fr helpers (rust: QVM:4072-4081) - MOVED; see WHAT MOVED 1 -/

/-- rust: QVM:4072-4076 (quotient_fq_from_u256). "Interpret a U256 as a canonical BLS12-381
    scalar field element. Values outside the field modulus are rejected; that is important
    when folding parsed Yul literals back into Fr coefficients for shape recognition."
    P-09b already ported the rejection as 'fqFromU256 : Word256 -> Except QVMFault QVMFr'
    (VmReference.lean:346) and gates it at the modulus boundary there; the Rust's signature
    here is Option, so the fault is discarded - every caller in this file turns it into a
    rejection anyway. -/
def quotientFqFromU256 (value : Word256) : Option QVMFr :=
  match fqFromU256 value with
  | .ok v => some v
  | .error _ => none

/-- rust: QVM:4079-4081 (quotient_fq_to_u256) = fe_to_u256::<Fq>. Every QVMFr this file
    hands it is already reduced: the type is Nat (VmReference.lean:252) and the only
    producers are quotientFqFromU256 (canonical by construction) and qvmFrAdd / qvmFrMul /
    qvmFrNeg, each of which reduces mod qvmFrModulus. So the encode is a plain 256-bit
    widening and cannot truncate. fqRoundTrip_ok re-checks that claim on the fixtures,
    including the largest value the field has. -/
def quotientFqToU256 (value : QVMFr) : Word256 := BitVec.ofNat 256 value

/-- Fr constants, spelled the way the Rust spells them. -/
def fqZero : QVMFr := qvmFrZero
def fqOne : QVMFr := 1

def fqIsZero (value : QVMFr) : Bool := value == fqZero

/-- rust: Fq addition / multiplication / negation, i.e. the '+=' and '*=' the collectors
    use. Not separate Rust items; R3's rendering of the arithmetic operators. -/
def fqAdd (lhs rhs : QVMFr) : QVMFr := qvmFrAdd lhs rhs
def fqMul (lhs rhs : QVMFr) : QVMFr := qvmFrMul lhs rhs
def fqNeg (value : QVMFr) : QVMFr := qvmFrNeg value

/-- rust: 'u8::MAX as usize' in the four count guards (QVM:3330-3332, 3359). -/
def u8Max : Nat := 255

/-! ## u16 modelling (R4) -/

/-- rust: 'u16::try_from(x).ok()?' at QVM:3445, 3506 and 4024. THE SAFETY VALVE (hazard 3):
    an oversized limb pointer is not a panic and not a truncation, it is a REJECTION, and the
    caller's '?' propagates it out of the recognizer so the builder falls back to generic Fr
    opcodes. The boundary is 0xffff accepted / 0x10000 rejected, and it is exactly the
    boundary emitU16 (QVM:1823-1827) panics past - which is why this guard is load-bearing
    and u16FallbackBoundary_ok pins both sides. -/
def u16TryFrom (n : Nat) : Option Nat := if n <= 0xffff then some n else none

/-- rust: 'base.checked_add(..)' (QVM:4048). -/
def u16CheckedAdd (lhs rhs : Nat) : Option Nat :=
  if lhs + rhs <= 0xffff then some (lhs + rhs) else none

/-- rust: 'ptr.checked_sub(base)' (QVM:4060). -/
def u16CheckedSub (lhs rhs : Nat) : Option Nat :=
  if rhs <= lhs then some (lhs - rhs) else none

/-- rust: plain u16 addition, QVM:3831 ('base + (limb as u16) * WORD_BYTES as u16'). Release
    profile (R4): this WRAPS at 2^16, it does not panic. See the header, R4 (b). -/
def u16Add (lhs rhs : Nat) : Nat := (lhs + rhs) % 65536

/-- rust: 'Vec<(Fq, &QuotientExpr)>' element: a coefficient and a term. The '&' is dropped
    (R3: Lean has no borrow), so a term is a subtree copy. -/
abbrev FrTerm := QVMFr × QuotientExpr

/-- rust: 'Vec<(u16, Fq)>' - grouped limb terms, pointer first (the accumulator's order).
    The shapes flip it to '(U256, u16)' on the way out, as the Rust does. -/
abbrev GroupedLimb := Nat × QVMFr

/-- rust: 'Vec<(u16, u16, Fq)>' - grouped memory-product pairs. -/
abbrev GroupedProduct := Nat × Nat × QVMFr

/-- First-argument-wins over Option, spelled out because Option.orElse's argument order has
    moved between Lean versions and this file must not depend on it. -/
def orElseOpt {α : Type} (head : Option α) (tail : Unit → Option α) : Option α :=
  match head with
  | some x => some x
  | none => tail ()

/-- rust: the 'for candidate in ... { if let Some(x) = recognise(candidate) { return Some(x) }
    }' shape every base / candidate loop in this cluster uses (QVM:3757-3809, 3826-3859,
    3879-3908, 3928-3982, 3479-3483): try each candidate in order, first success wins, and a
    candidate that fails does not stop the scan. Structural in the list (R10). -/
def firstSome {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | x :: rest => match f x with
    | some y => some y
    | none => firstSome f rest

/-- rust: 'Vec::retain(|(_, coeff)| *coeff != Fq::ZERO)' - order-preserving, so a plain filter
    is faithful. -/
def retainNonzero (grouped : List GroupedLimb) : List GroupedLimb :=
  grouped.filter fun (_, coeff) => !fqIsZero coeff

/-- Lean 4.35 core has no List.qsort (Kzg/Utils.lean:71 and VmBuilder.lean:1403 both record
    it), so the Rust's sort_by_key becomes this stable insertion sort: inserting x before the
    first y with x <= y preserves the order of equal keys, which is what sort_by_key does and
    what the two Kzg findings (Kzg.lean:338, 2425) say a hand-rolled sort must be checked for.
    -/
def insertionSortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insert x (insertionSortBy le xs)
where
  insert : α → List α → List α
  | x, [] => [x]
  | x, y :: ys => if le x y then x :: y :: ys else y :: insert x ys

/-- rust: 'Vec::sort_by_key(|(ptr, _)| *ptr)' (QVM:3356, 3670, 3715, 3849, 3898). After
    add_grouped_limb_coeff the keys are distinct anyway, so stability is not load-bearing
    here; it is stated because the Rust's sort is stable and a later caller may group twice.
    -/
def sortByPtr (grouped : List GroupedLimb) : List GroupedLimb :=
  insertionSortBy (fun a b => a.1 <= b.1) grouped

/-- rust: 'Vec::sort_by_key(|(lhs, rhs, _)| (*lhs, *rhs))' (QVM:3358), lexicographic on the
    pointer pair. -/
def sortByPair (grouped : List GroupedProduct) : List GroupedProduct :=
  insertionSortBy (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 <= b.2.1)) grouped

/-- rust: 'coeffs[idx] += coeff' / 'seen[idx] = true' on a fixed-length Vec (QVM:3771-3772,
    3940-3941). Indexing panics past the end in release too (R4); every caller here computes
    'i * QUOTIENT_VM_LIMBS + j' with i, j < 7, so idx < 49 and the bound is unreachable. Out of
    range is therefore rendered as "no change", which no reachable call observes, and
    pairwiseGridIndexStaysInBounds_ok checks the arithmetic instead. -/
def updateNth {α : Type} (xs : List α) (idx : Nat) (f : α → α) : List α :=
  (xs.take idx) ++ ((xs.drop idx).head?.map f).toList ++ (xs.drop (idx + 1))

def setNth {α : Type} (xs : List α) (idx : Nat) (v : α) : List α := updateNth xs idx (fun _ => v)

/-- Enumerate a list with its positions: the Rust's '.iter().enumerate()' that every subshape
    matcher starts from. -/
def enumerate {α : Type} (xs : List α) : List (α × Nat) :=
  (xs.zip (List.range xs.length)).map (fun (a, i) => (a, i))

/-! ## Canonical expression keys (rust: QVM:2831-2843, 2990-3002) - MOVED; WHAT MOVED 2 -/

/-- Lowercase hexadecimal with no '0x' and no leading zeros: the Rust's '{x:x}' on U256, u32
    and u8. Nat.toDigits 16 already yields lowercase and no padding. -/
def qvmHexLower (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- rust: QVM:2990-3002 (quotient_commutative_expr_key). "Canonical key helper for commutative
    binary operations." SHAPE CHANGE, recorded (WHAT MOVED 2): the Rust takes the two
    SUBEXPRESSIONS and keys them itself, which makes the pair mutually recursive with
    quotient_expr_key; Lean's structural checker cannot use that (it reports "failed to
    eliminate recursive application"), so the keying happens at the call site and this helper
    takes the two strings. The rendered text, and therefore the equality and the canonical
    order, are identical. The 'lhs <= rhs' is a String comparison in Rust and a String
    comparison here, so the canonical order is the same byte order (both compare the rendered
    text, and the rendering is ASCII). -/
def quotientCommutativeExprKey (op : String) (lhsKey rhsKey : String) : String :=
  if lhsKey <= rhsKey then op ++ ":" ++ lhsKey ++ ":" ++ rhsKey
  else op ++ ":" ++ rhsKey ++ ":" ++ lhsKey

/-- rust: QVM:2831-2843 (quotient_expr_key). "Canonical key for structural expression matching
    and deduplication. Addition and multiplication are keyed commutatively because all
    arithmetic is over Fr and these rewrites do not alter evaluation order side effects:
    QuotientExpr has no side effects."
    HAZARD 1, first evidence: every payload of this key comes out of the TREE. There is no
    name, no gate index and no circuit identifier anywhere in its definition, and
    recognizerClusterHasNoLabelRead_ok re-checks the same claim against the Rust source. -/
def quotientExprKey : QuotientExpr → String
  | .const value => "c:" ++ qvmHexLower value.toNat
  | .mem (.literal ptr) => "m:" ++ qvmHexLower ptr
  | .mem (.token token) => "t:" ++ qvmHexLower token
  | .mem (.tokenOffset token offset) =>
      "to:" ++ qvmHexLower token ++ ":" ++ qvmHexLower offset
  | .add lhs rhs => quotientCommutativeExprKey "a" (quotientExprKey lhs) (quotientExprKey rhs)
  | .mul lhs rhs => quotientCommutativeExprKey "u" (quotientExprKey lhs) (quotientExprKey rhs)
  | .neg inner => "n:" ++ quotientExprKey inner

/-! ## Product flattening and term constructors (rust: QVM:3123-3153) - MOVED; WHAT MOVED 3 -/

/-- rust: QVM:3123-3136 (collect_product_expr_factors). "Flatten multiplication nodes while
    keeping additive subexpressions whole." Infallible in Rust (it returns nothing and pushes
    into a &mut Vec), so the port returns the list. Note the asymmetry with
    collect_product_leaves (VmBuilder.lean:448, QVM:3101-3121), which REJECTS sums and
    negations: this one keeps them whole as factors. Both are used here, and mixing them up
    would silently widen or narrow every matcher. -/
def collectProductExprFactors : QuotientExpr → List QuotientExpr
  | .mul lhs rhs => collectProductExprFactors lhs ++ collectProductExprFactors rhs
  | e => [e]

/-- rust: QVM:3139-3141 (quotient_sum_expr). "Construct an addition node without applying
    algebraic simplification." -/
def quotientSumExpr (lhs rhs : QuotientExpr) : QuotientExpr := QuotientExpr.add lhs rhs

/-- rust: QVM:3144-3153 (quotient_scaled_term_expr). "Attach a scalar coefficient to a term,
    eliding multiplication by one." The elision matters for the key and for the emitted bytes:
    '1 * x' and 'x' must not be two different shapes. -/
def quotientScaledTermExpr (coeff : QVMFr) (expr : QuotientExpr) : QuotientExpr :=
  if coeff == fqOne then expr
  else QuotientExpr.mul (QuotientExpr.const (quotientFqToU256 coeff)) expr

/-! ## Memory-factor extraction (rust: QVM:3988-4066) - MOVED; WHAT MOVED 4 -/

/-- rust: QVM:4012-4029 (quotient_product_mem_factors). "Factor a product into its Fr
    coefficient and literal memory pointers. Token memory references are rejected because limb
    opcodes and fused product forms store compact literal u16 pointers." The rejection of
    Token / TokenOffset is the other half of hazard 3's fallback: a token pointer has no u16
    encoding at all, so it must not reach LIN7's operand list. QVM:4024 is the third
    u16::try_from(..).ok()? producer, the one the brief's table missed. -/
def quotientProductMemFactors (expr : QuotientExpr) : Option (QVMFr × List Nat) := do
  let leaves ← collectProductLeaves expr
  let step (acc : QVMFr × List Nat) (leaf : QuotientLeaf) : Option (QVMFr × List Nat) :=
    match leaf with
    | .const value =>
        match quotientFqFromU256 value with
        | some v => some (fqMul acc.1 v, acc.2)
        | none => none
    | .mem (.literal ptr) =>
        match u16TryFrom ptr with
        | some p => some (acc.1, acc.2 ++ [p])
        | none => none
    | .mem (.token _) => none
    | .mem (.tokenOffset _ _) => none
  let (coeff, ptrs) ← foldLeftOpt step (fqOne, []) leaves
  some (coeff, ptrs)

/-- rust: QVM:3988-3995 (quotient_mem_term). "Return (coefficient, ptr) for a product with
    exactly one memory factor." -/
def quotientMemTerm (expr : QuotientExpr) : Option (QVMFr × Nat) := do
  let (coeff, ptrs) ← quotientProductMemFactors expr
  match ptrs with
  | [ptr] => some (coeff, ptr)
  | _ => none

/-- rust: QVM:3999-4006 (quotient_product_mem_pair). "Return (coefficient, lhs_ptr, rhs_ptr)
    for a product with two memory factors." The Rust indexes ptrs[0] and ptrs[1] after the
    length test; the pattern match is the same test, and indexing past the end is unreachable
    either way. -/
def quotientProductMemPair (expr : QuotientExpr) : Option (QVMFr × Nat × Nat) := do
  let (coeff, ptrs) ← quotientProductMemFactors expr
  match ptrs with
  | [lhs, rhs] => some (coeff, lhs, rhs)
  | _ => none

/-- rust: QVM:4032-4038 (add_grouped_limb_coeff). "Add a coefficient into a grouped limb term."
    First match wins, which is what 'find' means in the Rust. -/
def addGroupedLimbCoeff (grouped : List GroupedLimb) (ptr : Nat) (coeff : QVMFr) :
    List GroupedLimb :=
  match grouped with
  | [] => [(ptr, coeff)]
  | (p, c) :: rest =>
      if p == ptr then (p, fqAdd c coeff) :: rest
      else (p, c) :: addGroupedLimbCoeff rest ptr coeff

/-- rust: QVM:3411-3421 (add_grouped_product_coeff). "Add a coefficient to an unordered
    memory-product pair." The 'if lhs <= rhs' normalisation is what makes the pair bucket
    insensitive to multiplication commutativity. -/
def addGroupedProductCoeff (grouped : List GroupedProduct) (lhs rhs : Nat) (coeff : QVMFr) :
    List GroupedProduct :=
  let (lhs, rhs) := if lhs <= rhs then (lhs, rhs) else (rhs, lhs)
  match grouped with
  | [] => [(lhs, rhs, coeff)]
  | (a, b, c) :: rest =>
      if a == lhs && b == rhs then (a, b, fqAdd c coeff) :: rest
      else (a, b, c) :: addGroupedProductCoeff rest lhs rhs coeff

/-- rust: QVM:4041-4055 (limb7_base_candidates). "Find all base pointers that cover a
    contiguous seven-limb vector." checked_add (QVM:4048) is the release-safe form: a base near
    the top of the u16 range does not wrap into a spurious hit here, the candidate is simply
    not a base. Sorted then deduped, exactly as the Rust writes it (natSortAsc is P-09c's
    ascending insertion sort, VmBuilder.lean:1405). -/
def limb7BaseCandidates (ptrs : List Nat) : List Nat :=
  let covers (base : Nat) : Bool :=
    (List.range quotientVmLimbs).all fun idx =>
      match u16CheckedAdd base (idx * qvmWordBytes) with
      | some p => ptrs.elem p
      | none => false
  natSortAsc (ptrs.filter covers) |>.dedup

/-- rust: QVM:4058-4066 (limb7_index). "Return the limb index of ptr relative to base, if it is
    in the vector." The '% WORD_BYTES' test is a division: R4 says division by zero panics in
    release, and WORD_BYTES is the literal 32 (LM:17, pinned by qvmWordBytes_isTheLimbStride_ok
    in P-09b), so the divisor is never zero here. -/
def limb7Index (base ptr : Nat) : Option Nat := do
  let diff ← u16CheckedSub ptr base
  if diff % qvmWordBytes != 0 then none
  else
    let idx := diff / qvmWordBytes
    if idx < quotientVmLimbs then some idx else none

/-! ## Sum collection (rust: QVM:3553-3646) - MOVED; WHAT MOVED 5 -/

/-- rust: QVM:3604-3646 (collect_quotient_sum_terms). "Collect additive terms as
    (coefficient, expression) pairs over Fr. Constant-only terms must reduce to zero for a limb
    shape to match; non-zero standalone constants would require an additional VM add and
    therefore are left to the generic emitter."
    The Rust returns bool and leaves a partial prefix in its &mut Vec; every caller discards
    the vector on false (QVM:3165-3167, 3523-3525), so Option observes the same behaviour - the
    same rendering P-09c used for collect_product_leaves (VmBuilder.lean:441-447). -/
def collectQuotientSumTerms (expr : QuotientExpr) (coeff : QVMFr) : Option (List FrTerm) :=
  if fqIsZero coeff then some []
  else
    match expr with
    | QuotientExpr.add lhs rhs => do
        let a ← collectQuotientSumTerms lhs coeff
        let b ← collectQuotientSumTerms rhs coeff
        some (a ++ b)
    | QuotientExpr.neg inner => collectQuotientSumTerms inner (fqNeg coeff)
    | QuotientExpr.mul lhs rhs =>
        match lhs with
        | QuotientExpr.const value =>
            match quotientFqFromU256 value with
            | some v => collectQuotientSumTerms rhs (fqMul coeff v)
            | none => none
        | _ =>
            match rhs with
            | QuotientExpr.const value =>
                match quotientFqFromU256 value with
                | some v => collectQuotientSumTerms lhs (fqMul coeff v)
                | none => none
            | _ => some [(coeff, QuotientExpr.mul lhs rhs)]
    | QuotientExpr.const value =>
        match quotientFqFromU256 value with
        | some v => if fqIsZero (fqMul coeff v) then some [] else none
        | none => none
    | e@(QuotientExpr.mem _) => some [(coeff, e)]

/-- rust: QVM:3553-3597 (collect_quotient_affine_terms). "Collect additive terms for subshape
    extraction, preserving constants as the residue instead of rejecting the whole affine
    identity." The only difference from its sibling above is the Const arm: here a non-zero
    constant folds into the accumulator instead of failing the match. The accumulator threads
    left to right exactly as the Rust's &mut Fq does. -/
def collectQuotientAffineTerms (expr : QuotientExpr) (coeff : QVMFr) :
    Option (List FrTerm × QVMFr) :=
  if fqIsZero coeff then some ([], fqZero)
  else
    match expr with
    | QuotientExpr.add lhs rhs => do
        let (t1, k1) ← collectQuotientAffineTerms lhs coeff
        let (t2, k2) ← collectQuotientAffineTerms rhs coeff
        some (t1 ++ t2, fqAdd k1 k2)
    | QuotientExpr.neg inner => collectQuotientAffineTerms inner (fqNeg coeff)
    | QuotientExpr.mul lhs rhs =>
        match lhs with
        | QuotientExpr.const value =>
            match quotientFqFromU256 value with
            | some v => do
                let (t, k) ← collectQuotientAffineTerms rhs (fqMul coeff v)
                some (t, k)
            | none => none
        | _ =>
            match rhs with
            | QuotientExpr.const value =>
                match quotientFqFromU256 value with
                | some v => do
                    let (t, k) ← collectQuotientAffineTerms lhs (fqMul coeff v)
                    some (t, k)
                | none => none
            | _ => some ([(coeff, QuotientExpr.mul lhs rhs)], fqZero)
    | QuotientExpr.const value =>
        match quotientFqFromU256 value with
        | some v => some ([], fqMul coeff v)
        | none => none
    | e@(QuotientExpr.mem _) => some ([(coeff, e)], fqZero)

/-- rust: QVM:3400-3408 (remove_quotient_terms). The Rust's closure counts positions in the
    list being filtered ('idx' increments once per element and retain visits each element of
    the ORIGINAL order exactly once), so 'used' indexes original positions - which is what its
    producers return. Recorded because the closure discards its argument and reads like a bug.
    -/
def removeQuotientTerms (terms : List FrTerm) (used : List Nat) : List FrTerm :=
  (enumerate terms).filterMap fun (term, idx) =>
    if used.elem idx then none else some term

/-- rust: QVM:3819-3824. The enumerate restricted to the terms whose expression is a single
    scaled memory load. -/
def memTermIndices (terms : List FrTerm) : List (Nat × Nat × QVMFr) :=
  (enumerate terms).filterMap fun (term, idx) =>
    let (coeff, expr) := term
    match quotientMemTerm expr with
    | some (innerCoeff, ptr) => some (idx, ptr, fqMul coeff innerCoeff)
    | none => none

/-- rust: QVM:3870-3876, 3920-3925. The same enumerate restricted to product pairs. -/
def productPairIndices (terms : List FrTerm) : List (Nat × QVMFr × Nat × Nat) :=
  (enumerate terms).filterMap fun (term, idx) =>
    let (coeff, expr) := term
    match quotientProductMemPair expr with
    | some (innerCoeff, lhs, rhs) => some (idx, fqMul coeff innerCoeff, lhs, rhs)
    | none => none

/-- The shape payload form the Rust writes on the way out of every matcher: '(U256, u16)' pairs
    sorted by pointer. -/
def groupedToShapeTerms (grouped : List GroupedLimb) : List (Word256 × Nat) :=
  (sortByPtr grouped).map fun (ptr, coeff) => (quotientFqToU256 coeff, ptr)

/-! ## The whole-expression matchers (rust: QVM:3653-3812) - MOVED; WHAT MOVED 6 -/

/-- rust: QVM:3653-3676 (try_quotient_lin7_shape). "Recognize a seven-limb linear combination.
    The resulting terms are sorted by memory pointer so equivalent expressions have
    deterministic bytecode even when the source expression tree orders additions differently."
    QVM:3667 is one of the three length guards P-09a hazard 4 named: 'grouped.len() !=
    QUOTIENT_VM_LIMBS' is the ONLY thing that stops a 6-term or 8-term Lin7 from being built,
    because the type does not (VmTypes.lean:401-406). -/
def tryQuotientLin7Shape (terms : List FrTerm) : Option QuotientLimbShape := do
  let grouped ← foldLeftOpt
    (fun (acc : List GroupedLimb) (term : FrTerm) => do
      let (coeff, expr) := term
      let (innerCoeff, ptr) ← quotientMemTerm expr
      some (addGroupedLimbCoeff acc ptr (fqMul coeff innerCoeff)))
    [] terms
  let grouped := retainNonzero grouped
  if grouped.length != quotientVmLimbs then none
  else some (QuotientLimbShape.lin7 (groupedToShapeTerms grouped))

/-- rust: QVM:3682-3726 (try_quotient_bilin7_row_shape). "Recognize one limb multiplied across
    a seven-limb vector. The recognizer tries both sides of the first pair as the repeated limb
    so it is insensitive to multiplication commutativity in the lowered expression." QVM:3714
    is the second length guard. The Rust 'break's out of the inner loop when a pair matches
    neither side; the port keeps folding with ok := false and discards the partial grouping,
    which is what the Rust's 'if ok && ..' does with it. -/
def tryQuotientBilin7RowShape (terms : List FrTerm) : Option QuotientLimbShape := do
  let pairs ← foldLeftOpt
    (fun (acc : List GroupedProduct) (term : FrTerm) => do
      let (coeff, expr) := term
      let (innerCoeff, lhs, rhs) ← quotientProductMemPair expr
      some (acc ++ [(fqMul coeff innerCoeff, lhs, rhs)]))
    [] terms
  if pairs.length != quotientVmLimbs then none
  else
    match pairs with
    | [] => none
    | (_, firstLhs, firstRhs) :: _ =>
        let tryCandidate (candidate : Nat) : Option QuotientLimbShape := do
          let state ← foldLeftOpt
            (fun (acc : Bool × List GroupedLimb) (p : GroupedProduct) =>
              let (coeff, lhs, rhs) := p
              if lhs == candidate then some (acc.1, addGroupedLimbCoeff acc.2 rhs coeff)
              else if rhs == candidate then some (acc.1, addGroupedLimbCoeff acc.2 lhs coeff)
              else some (false, acc.2))
            (true, []) pairs
          let grouped := retainNonzero state.2
          if state.1 && grouped.length == quotientVmLimbs then
            some (QuotientLimbShape.bilin7Row candidate (groupedToShapeTerms grouped))
          else none
        orElseOpt (tryCandidate firstLhs) fun _ => tryCandidate firstRhs

/-- rust: QVM:3779-3797 and QVM:3948-3966, the shared diagonal fold of the two pairwise
    matchers: accumulate each row-major slot into its i + j bucket and require every slot in a
    bucket to agree. Split out because the two Rust copies are character-for-character the same
    except for the 'expect' at the end, and a divergence between them would be invisible. -/
def pairwiseDiagonals (coeffs : List QVMFr) : Option (List Word256) := do
  let state ← foldLeftOpt
    (fun (acc : List (Option QVMFr) × Bool) (ij : Nat × Nat) =>
      let (i, j) := ij
      let coeff := coeffs.getD (i * quotientVmLimbs + j) fqZero
      match acc.1.getD (i + j) none with
      | some expected =>
          if expected != coeff then some (acc.1, false) else some acc
      | none => some (setNth acc.1 (i + j) (some coeff), acc.2))
    (List.replicate quotientVmPairwiseCoeffs none, true)
    (List.product (List.range quotientVmLimbs) (List.range quotientVmLimbs))
  if state.2 then some (state.1.map fun coeff =>
    -- rust: 'coeff.expect("pairwise sum coefficient")' (QVM:3805, 3976), a release panic at an
    -- unreachable position: 'seen' is all true, so every diagonal was written. Rendered as a
    -- rejection here; see the header, R4 (d).
    match coeff with
    | some c => quotientFqToU256 c
    | none => 0)
  else none

/-- rust: QVM:3735-3812 (try_quotient_bilin7_pairwise_shape). "Recognize a full seven-by-seven
    foreign-field product convolution. The memory pointers must contain two contiguous
    seven-word limb vectors. For each product term the coefficient is accumulated into its
    row-major slot and then checked to depend only on i + j, exactly matching the
    double_base_powers shape. If any slot is missing or coefficients disagree, the shape is
    rejected and the generic VM remains the source of truth." QVM:3753 is the third length
    guard ('pairs.len() != QUOTIENT_VM_PAIRWISE_TERMS') and QVM:3780 sizes the diagonal table
    at QUOTIENT_VM_PAIRWISE_COEFFS = 13. -/
def tryQuotientBilin7PairwiseShape (terms : List FrTerm) : Option QuotientLimbShape := do
  let collected ← foldLeftOpt
    (fun (acc : List GroupedProduct × List Nat) (term : FrTerm) => do
      let (coeff, expr) := term
      let (innerCoeff, lhs, rhs) ← quotientProductMemPair expr
      some (acc.1 ++ [(fqMul coeff innerCoeff, lhs, rhs)], acc.2 ++ [lhs, rhs]))
    ([], []) terms
  let pairs := collected.1
  if pairs.length != quotientVmPairwiseTerms then none
  else
    let grid (lhsBase rhsBase : Nat) : Option QuotientLimbShape := do
      let state ← foldLeftOpt
        (fun (acc : List QVMFr × List Bool × Bool) (p : GroupedProduct) =>
          let (coeffs, seen, ok) := acc
          let (coeff, lhs, rhs) := p
          let direct := do
            let i ← limb7Index lhsBase lhs
            let j ← limb7Index rhsBase rhs
            some (i, j)
          let swapped := do
            let i ← limb7Index lhsBase rhs
            let j ← limb7Index rhsBase lhs
            some (i, j)
          match orElseOpt direct (fun _ => swapped) with
          | none => some (coeffs, seen, false)
          | some (i, j) =>
              let idx := i * quotientVmLimbs + j
              some ( updateNth coeffs idx (fun c => fqAdd c coeff)
                   , setNth seen idx true
                   , ok))
        (List.replicate quotientVmPairwiseTerms fqZero,
         List.replicate quotientVmPairwiseTerms false, true) pairs
      let (gridCoeffs, gridSeen, gridOk) := state
      if !gridOk || gridSeen.any (!·) then none
      else
        match pairwiseDiagonals gridCoeffs with
        | none => none
        | some coeffs => some (QuotientLimbShape.bilin7Pairwise lhsBase rhsBase coeffs)
    let bases := limb7BaseCandidates collected.2
    firstSome (fun b => grid b.1 b.2) (List.product bases bases)

/-- rust: QVM:3815-3861 (try_quotient_lin7_subshape). "Find a complete seven-limb linear
    subshape inside a larger affine sum." Note QVM:3831's plain u16 addition (the wrapping one,
    R4 (b)) and the 'used.len() >= QUOTIENT_VM_LIMBS' conjunct at QVM:3848, which the package
    report records as UNOBSERVABLE: every found limb pushes one grouped entry and at least one
    used index, so the arity conjunct already implies it. -/
def lin7SubshapeForBase (base : Nat) (memTerms : List (Nat × Nat × QVMFr)) :
    Option (QuotientLimbShape × List Nat) :=
  let attempt :=
    foldLeftOpt
      (fun (acc : List GroupedLimb × List Nat × Bool) (limb : Nat) =>
        let (grouped, used, ok) := acc
        let ptr := u16Add base (limb * qvmWordBytes)
        let hits := memTerms.filter fun m => m.2.1 == ptr
        if hits.isEmpty then some (grouped, [], false)
        else
          let coeff := hits.foldl (fun (c : QVMFr) m => fqAdd c m.2.2) fqZero
          some (grouped ++ [(ptr, coeff)], used ++ hits.map (fun m => m.1), ok))
      ([], [], true) (List.range quotientVmLimbs)
  match attempt with
  | none => none
  | some (grouped, used, ok) =>
      let grouped := retainNonzero grouped
      if ok && grouped.length == quotientVmLimbs && used.length >= quotientVmLimbs then
        some (QuotientLimbShape.lin7 (groupedToShapeTerms grouped), used)
      else none

def tryQuotientLin7Subshape (terms : List FrTerm) : Option (QuotientLimbShape × List Nat) :=
  let memTerms := memTermIndices terms
  firstSome (fun base => lin7SubshapeForBase base memTerms)
    (limb7BaseCandidates (memTerms.map (fun m => m.2.1)))

/-- rust: QVM:3864-3911 (try_quotient_bilin7_row_subshape). "Find terms sharing one
    multiplicand with a complete seven-limb row." The candidate list here is the sorted pointer
    set WITHOUT a dedup pass (QVM:3878-3879) because a HashSet is already distinct; the port
    dedups to model the set. -/
def bilin7RowSubshapeForCandidate (candidate : Nat) (pairs : List (Nat × QVMFr × Nat × Nat)) :
    Option (QuotientLimbShape × List Nat) := do
  let attempt ← foldLeftOpt
    (fun (acc : List GroupedLimb × List Nat) (p : Nat × QVMFr × Nat × Nat) =>
      let (idx, coeff, lhs, rhs) := p
      if lhs == candidate then some (addGroupedLimbCoeff acc.1 rhs coeff, acc.2 ++ [idx])
      else if rhs == candidate then some (addGroupedLimbCoeff acc.1 lhs coeff, acc.2 ++ [idx])
      else some acc)
    ([], []) pairs
  let grouped := retainNonzero attempt.1
  if grouped.length == quotientVmLimbs && attempt.2.length >= quotientVmLimbs then
    some (QuotientLimbShape.bilin7Row candidate (groupedToShapeTerms grouped), attempt.2)
  else none

def tryQuotientBilin7RowSubshape (terms : List FrTerm) :
    Option (QuotientLimbShape × List Nat) :=
  let pairs := productPairIndices terms
  let candidates := (natSortAsc (pairs.flatMap fun (_, _, lhs, rhs) => [lhs, rhs])).dedup
  firstSome (fun candidate => bilin7RowSubshapeForCandidate candidate pairs) candidates

/-- rust: QVM:3914-3985 (try_quotient_bilin7_pairwise_subshape). "Find a full 7x7 pairwise
    product grid inside a larger affine sum." The difference from the whole-expression version
    is the point: an unmappable pair is SKIPPED here ('continue', QVM:3937-3939) rather than
    failing the grid, because a larger sum legitimately contains terms that are not part of
    this grid. 'used' therefore collects only the mapped indices, and QVM:3968 re-checks
    'used.len() >= QUOTIENT_VM_PAIRWISE_TERMS'. -/
def bilin7PairwiseSubshapeForBases (lhsBase rhsBase : Nat)
    (pairs : List (Nat × QVMFr × Nat × Nat)) : Option (QuotientLimbShape × List Nat) := do
  let state ← foldLeftOpt
    (fun (acc : List QVMFr × List Bool × List Nat) (p : Nat × QVMFr × Nat × Nat) =>
      let (coeffs, seen, used) := acc
      let (idx, coeff, lhs, rhs) := p
      let direct := do
        let i ← limb7Index lhsBase lhs
        let j ← limb7Index rhsBase rhs
        some (i, j)
      let swapped := do
        let i ← limb7Index lhsBase rhs
        let j ← limb7Index rhsBase lhs
        some (i, j)
      match orElseOpt direct (fun _ => swapped) with
      | none => some (coeffs, seen, used)
      | some (i, j) =>
          let termIdx := i * quotientVmLimbs + j
          some ( updateNth coeffs termIdx (fun c => fqAdd c coeff)
               , setNth seen termIdx true
               , used ++ [idx]))
    (List.replicate quotientVmPairwiseTerms fqZero,
     List.replicate quotientVmPairwiseTerms false, []) pairs
  let (gridCoeffs, gridSeen, gridUsed) := state
  if gridSeen.any (!·) then none
  else
    match pairwiseDiagonals gridCoeffs with
    | none => none
    | some coeffs =>
        if gridUsed.length >= quotientVmPairwiseTerms then
          some (QuotientLimbShape.bilin7Pairwise lhsBase rhsBase coeffs, gridUsed)
        else none

def tryQuotientBilin7PairwiseSubshape (terms : List FrTerm) :
    Option (QuotientLimbShape × List Nat) :=
  let pairs := productPairIndices terms
  let bases := limb7BaseCandidates (pairs.flatMap fun (_, _, lhs, rhs) => [lhs, rhs])
  firstSome (fun b => bilin7PairwiseSubshapeForBases b.1 b.2 pairs) (List.product bases bases)

/-! ## Factored row forms (rust: QVM:3425-3529) -/

/-- rust: QVM:3488-3529 (quotient_factored_bilin7_row_shape). "Recognize lhs_limb *
    lin7(rhs_limbs) as a row bilinear limb shape." This is the matcher for the FACTORED
    spelling of a row - one limb times a whole sum - which is how the lowered ECC identities
    appear, as opposed to try_quotient_bilin7_row_shape's flat sum of products. QVM:3506 is the
    second u16::try_from(..).ok()? producer. -/
def quotientFactoredBilin7RowShape (termCoeff : QVMFr) (expr : QuotientExpr) :
    Option QuotientLimbShape :=
  let factors := collectProductExprFactors expr
  if factors.length < 2 then none
  else do
    let state ← foldLeftOpt
      (fun (acc : QVMFr × Option Nat × Option QuotientExpr) (factor : QuotientExpr) =>
        let (coeff, lhs, lin) := acc
        match factor with
        | QuotientExpr.const value =>
            match quotientFqFromU256 value with
            | some v => some (fqMul coeff v, lhs, lin)
            | none => none
        | QuotientExpr.mem (.literal ptr) =>
            match u16TryFrom ptr with
            | some p => if lhs.isSome then none else some (coeff, some p, lin)
            | none => none
        | QuotientExpr.mem (.token _) => none
        | QuotientExpr.mem (.tokenOffset _ _) => none
        | QuotientExpr.add _ _ => if lin.isSome then none else some (coeff, lhs, some factor)
        | QuotientExpr.mul _ _ => if lin.isSome then none else some (coeff, lhs, some factor)
        | QuotientExpr.neg _ => if lin.isSome then none else some (coeff, lhs, some factor))
      (termCoeff, none, none) factors
    match state with
    | (coeff, some lhs, some linExpr) =>
        match collectQuotientSumTerms linExpr coeff with
        | none => none
        | some linTerms =>
            match tryQuotientLin7Shape linTerms with
            | some (QuotientLimbShape.lin7 terms) => some (QuotientLimbShape.bilin7Row lhs terms)
            | _ => none
    | _ => none

/-- rust: QVM:3476-3485 (try_quotient_factored_bilin7_row_subshape). "Find one factored
    row-shaped limb term inside a larger affine sum." Note the 'used' list is exactly one index
    - the ONLY recognizer in this cluster that can return a single-element 'used'. It is
    reachable only from the MODARITH7 accumulator, never from quotient_limb_subshape, and that
    is why hazard 2's 'matched' non-empty obligation still holds: see
    subshapeMatchedNonEmpty_ok. -/
def tryQuotientFactoredBilin7RowSubshape (terms : List FrTerm) :
    Option (QuotientLimbShape × List Nat) :=
  firstSome
    (fun pair =>
      let ((coeff, expr), idx) := pair
      match quotientFactoredBilin7RowShape coeff expr with
      | some shape => some (shape, [idx])
      | none => none)
    (enumerate terms)

/-- rust: QVM:3425-3473 (add_factored_affine_product_terms). "Recognize mem * (affine mem sum)
    and fold it into sparse product/memory buckets for MODARITH7." QVM:3445 is the first
    u16::try_from(..).ok()? producer. The Rust mutates both buckets and returns Option<()>; the
    port threads them and returns the pair, so a rejection discards the partial work exactly as
    the caller's '?' does (QVM:3344-3353). -/
def addFactoredAffineProductTerms (groupedMem : List GroupedLimb)
    (groupedProducts : List GroupedProduct) (termCoeff : QVMFr) (expr : QuotientExpr) :
    Option (List GroupedLimb × List GroupedProduct) :=
  let factors := collectProductExprFactors expr
  if factors.length < 2 then none
  else do
    let state ← foldLeftOpt
      (fun (acc : QVMFr × Option Nat × Option QuotientExpr) (factor : QuotientExpr) =>
        let (coeff, lhs, affine) := acc
        match factor with
        | QuotientExpr.const value =>
            match quotientFqFromU256 value with
            | some v => some (fqMul coeff v, lhs, affine)
            | none => none
        | QuotientExpr.mem (.literal ptr) =>
            match u16TryFrom ptr with
            | some p => if lhs.isSome then none else some (coeff, some p, affine)
            | none => none
        | QuotientExpr.mem (.token _) => none
        | QuotientExpr.mem (.tokenOffset _ _) => none
        | QuotientExpr.add _ _ => if affine.isSome then none else some (coeff, lhs, some factor)
        | QuotientExpr.mul _ _ => if affine.isSome then none else some (coeff, lhs, some factor)
        | QuotientExpr.neg _ => if affine.isSome then none else some (coeff, lhs, some factor))
      (termCoeff, none, none) factors
    match state with
    | (coeff, some lhs, some affineExpr) =>
        match collectQuotientAffineTerms affineExpr fqOne with
        | none => none
        | some (terms, constant) =>
            let groupedMem :=
              if !fqIsZero constant
                then addGroupedLimbCoeff groupedMem lhs (fqMul coeff constant)
                else groupedMem
            foldLeftOpt
              (fun (acc : List GroupedLimb × List GroupedProduct) (term : FrTerm) =>
                let (innerCoeff, e) := term
                match quotientMemTerm e with
                | none => none
                | some (memCoeff, rhs) =>
                    some (acc.1,
                      addGroupedProductCoeff acc.2 lhs rhs (fqMul (fqMul coeff innerCoeff) memCoeff)))
              (groupedMem, groupedProducts) terms
    | _ => none

/-! ## MODARITH7 (rust: QVM:3230-3397) -/

/-- rust: QVM:3241-3253 (quotient_condition_factor). "Split cond * inner when cond is a
    literal memory load, moving any scalar factor attached to cond into inner." -/
def quotientConditionFactor (expr : QuotientExpr) : Option (Nat × QuotientExpr) :=
  match expr with
  | QuotientExpr.mul lhs rhs =>
      match quotientMemTerm lhs with
      | some (coeff, ptr) => some (ptr, quotientScaledTermExpr coeff rhs)
      | none =>
          match quotientMemTerm rhs with
          | some (coeff, ptr) => some (ptr, quotientScaledTermExpr coeff lhs)
          | none => none
  | _ => none

/-- The accumulator state of QVM:3273-3328's loop: the three block lists plus the terms still
    unclaimed. Not a Rust type; it is the loop's locals reified so the recursion can return
    them. -/
structure Modarith7Accum where
  lin : List (List (Word256 × Nat))
  rows : List (Nat × List (Word256 × Nat))
  pairwise : List (Nat × Nat × List Word256)
  terms : List FrTerm

/-- rust: QVM:3273-3328, the MODARITH7 accumulator loop, ported as a fuelled recursion (header,
    R10). Each arm is tried in the Rust's order - pairwise, factored row, row, lin - and each
    arm that fires with a non-empty 'used' removes those terms and continues; an arm that fires
    with an EMPTY 'used' breaks the loop (QVM:3275-3277 and its three siblings), which is a
    different thing from an arm that returns None, and the port keeps that distinction because
    it is the loop's only exit besides exhaustion. The four unreachable! panics are panicAt
    sites (header, R4 (c)). -/
def modarith7Loop : Nat → Modarith7Accum → M Modarith7Accum
  | 0, _ => panicAt siteModarith7LoopFuel
  | fuel + 1, acc =>
      match tryQuotientBilin7PairwiseSubshape acc.terms with
      | some (shape, used) =>
          if used.isEmpty then .ok acc
          else match shape with
            | .bilin7Pairwise lhsBase rhsBase coeffs =>
                modarith7Loop fuel
                  { acc with pairwise := acc.pairwise ++ [(lhsBase, rhsBase, coeffs)]
                             , terms := removeQuotientTerms acc.terms used }
            | .lin7 _ | .bilin7Row _ _ => panicAt sitePairwiseNotPairwise
      | none =>
          match tryQuotientFactoredBilin7RowSubshape acc.terms with
          | some (shape, used) =>
              if used.isEmpty then .ok acc
              else match shape with
                | .bilin7Row lhs terms =>
                    modarith7Loop fuel
                      { acc with rows := acc.rows ++ [(lhs, terms)]
                                 , terms := removeQuotientTerms acc.terms used }
                | .lin7 _ | .bilin7Pairwise _ _ _ => panicAt siteFactoredRowNotRow
          | none =>
              match tryQuotientBilin7RowSubshape acc.terms with
              | some (shape, used) =>
                  if used.isEmpty then .ok acc
                  else match shape with
                    | .bilin7Row lhs terms =>
                        modarith7Loop fuel
                          { acc with rows := acc.rows ++ [(lhs, terms)]
                                     , terms := removeQuotientTerms acc.terms used }
                    | .lin7 _ | .bilin7Pairwise _ _ _ => panicAt siteRowNotRow
              | none =>
                  match tryQuotientLin7Subshape acc.terms with
                  | some (shape, used) =>
                      if used.isEmpty then .ok acc
                      else match shape with
                        | .lin7 terms =>
                            modarith7Loop fuel
                              { acc with lin := acc.lin ++ [terms]
                                         , terms := removeQuotientTerms acc.terms used }
                        | .bilin7Row _ _ | .bilin7Pairwise _ _ _ => panicAt siteLinNotLin
                  | none => .ok acc

/-- rust: QVM:3257-3397 (quotient_modarith7_affine_shape). "Recognize a mixed affine form after
    any outer condition factor has been separated." The largest single item in the cluster: the
    accumulator loop, then the leftover terms are bucketed into grouped memory and grouped
    product terms, then five count guards and two shape guards decide whether the fused opcode
    is worth emitting at all. The lin/rows/pairwise 'len() > u8::MAX' guards (QVM:3330-3332)
    and the two bucket guards (QVM:3359) are the byte widths of the MODARITH7 encoding, so they
    are part of the ABI, not optimisations. -/
def quotientModarith7AffineShape (cond : Option Nat) (expr : QuotientExpr) :
    Option QuotientModarith7Shape := do
  let collected ← collectQuotientAffineTerms expr fqOne
  let terms0 := collected.1.filter fun (coeff, _) => !fqIsZero coeff
  let constant := collected.2
  let acc ← match modarith7Loop (terms0.length + 1)
      { lin := [], rows := [], pairwise := [], terms := terms0 } with
    | .ok acc => some acc
    | .error _ => none
  if acc.lin.length > u8Max || acc.rows.length > u8Max || acc.pairwise.length > u8Max then none
  else
    let bucketed ← foldLeftOpt
      (fun (acc : List GroupedLimb × List GroupedProduct) (term : FrTerm) =>
        let (coeff, expr) := term
        match quotientMemTerm expr with
        | some (innerCoeff, ptr) =>
            some (addGroupedLimbCoeff acc.1 ptr (fqMul coeff innerCoeff), acc.2)
        | none =>
            match quotientProductMemPair expr with
            | some (innerCoeff, lhs, rhs) =>
                some (acc.1, addGroupedProductCoeff acc.2 lhs rhs (fqMul coeff innerCoeff))
            | none =>
                match addFactoredAffineProductTerms acc.1 acc.2 coeff expr with
                | none => none
                | some (gm, gp) => some (gm, gp))
      ([], []) acc.terms
    let groupedMem := sortByPtr (bucketed.1.filter fun (_, coeff) => !fqIsZero coeff)
    let groupedProducts := sortByPair (bucketed.2.filter fun (_, _, coeff) => !fqIsZero coeff)
    if groupedMem.length > u8Max || groupedProducts.length > u8Max then none
    else
      let nonzeroConstant := if fqIsZero constant then 0 else 1
      let componentCount :=
        acc.lin.length + acc.rows.length + acc.pairwise.length +
          groupedMem.length + groupedProducts.length + nonzeroConstant
      if componentCount == 0 then none
      else
        let hasLimbComponent := !acc.lin.isEmpty || !acc.rows.isEmpty || !acc.pairwise.isEmpty
        let hasSparseConditionalProducts :=
          cond.isSome && !groupedProducts.isEmpty && componentCount >= 2
        if !hasLimbComponent && !hasSparseConditionalProducts then none
        else if cond.isNone && componentCount < 2 then none
        else
          some { cond := cond
                 constant := quotientFqToU256 constant
                 lin := acc.lin
                 rows := acc.rows
                 pairwise := acc.pairwise
                 memTerms := groupedMem.map fun (ptr, coeff) => (quotientFqToU256 coeff, ptr)
                 productTerms := groupedProducts.map fun (lhs, rhs, coeff) =>
                   (quotientFqToU256 coeff, lhs, rhs) }

/-- rust: QVM:3230-3237 (quotient_modarith7_shape). "Recognize a whole affine
    foreign-field/ECC identity that can be evaluated by the dynamic MODARITH7 opcode." Try it
    with the condition factor split off first; if that fails, try the whole expression with no
    condition. -/
def quotientModarith7Shape (expr : QuotientExpr) : Option QuotientModarith7Shape :=
  match quotientConditionFactor expr with
  | some (cond, inner) =>
      orElseOpt (quotientModarith7AffineShape (some cond) inner) fun _ =>
        quotientModarith7AffineShape none expr
  | none => quotientModarith7AffineShape none expr

/-! ## The four public recognizers (rust: QVM:3156-3226) -/

/-- rust: QVM:3156-3172 (quotient_limb_shape). "Recognize any supported seven-limb
    foreign-field quotient shape." The doc comment inside it is hazard 1's text and is quoted
    in VmTypes.lean:388-395: "This deliberately does not look at gate names: the Rust verifier
    source of truth remains
    proofs/src/plonk/mod.rs::partially_evaluate_identities, which evaluates vk.cs.gates
    expression trees in order. The recognizer only changes how obvious sum_exprs / pair_wise_prod
    shapes are encoded for Solidity." The three-way or_else chain is the precedence: the most
    specific shape wins. -/
def quotientLimbShape (expr : QuotientExpr) : Option QuotientLimbShape := do
  let terms ← collectQuotientSumTerms expr fqOne
  let terms := terms.filter fun (coeff, _) => !fqIsZero coeff
  orElseOpt (tryQuotientBilin7PairwiseShape terms) fun _ =>
    orElseOpt (tryQuotientBilin7RowShape terms) fun _ =>
      tryQuotientLin7Shape terms

/-- rust: QVM:3175-3186 (quotient_pow5_base). "Return the repeated base for a structural fifth
    power." Five flattened factors that key equal. Because the key is commutative for Add and
    Mul, x^5 written with the factors in any order - and with each factor's own additions
    commuted - still recognises; pow5CommutativeKey_ok is that claim, and it is the clearest
    demonstration in the cluster that recognition is structural and not textual. -/
def quotientPow5Base (expr : QuotientExpr) : Option QuotientExpr :=
  let factors := collectProductExprFactors expr
  if factors.length != 5 then none
  else
    match factors with
    | [] => none
    | first :: _ =>
        let firstKey := quotientExprKey first
        if factors.all (fun factor => quotientExprKey factor == firstKey) then some first
        else none

/-- rust: QVM:3189-3226 (quotient_limb_subshape). "Extract one limb shape from a larger affine
    sum and return the residue." The two guards are the whole contract P-09c could not check:
    QVM:3199 ('terms.len() <= QUOTIENT_VM_LIMBS && constant == ZERO') refuses a sum with
    nothing left over, and QVM:3206 ('used.is_empty() || (used.len() == terms.len() && constant
    == ZERO)') refuses a match that consumes everything or nothing. The comment at QVM:3210-3214
    states what 'matched' is FOR: "the panic-free fallback for emit_limb_shape: their sum equals
    the fused opcode's value, but each is a single scaled load/product that uses u16-capable
    constant loads." -/
def quotientLimbSubshape (expr : QuotientExpr) :
    Option (QuotientLimbShape × QuotientExpr × List QuotientExpr) := do
  let collected ← collectQuotientAffineTerms expr fqOne
  let terms := collected.1.filter fun (coeff, _) => !fqIsZero coeff
  let constant := collected.2
  if terms.length <= quotientVmLimbs && fqIsZero constant then none
  else
    let (shape, used) ←
      orElseOpt (tryQuotientBilin7PairwiseSubshape terms) fun _ =>
        orElseOpt (tryQuotientBilin7RowSubshape terms) fun _ =>
          tryQuotientLin7Subshape terms
    if used.isEmpty || (used.length == terms.length && fqIsZero constant) then none
    else
      let split :=
        (enumerate terms).foldl
          (fun (acc : QuotientExpr × List QuotientExpr) (pair : FrTerm × Nat) =>
            let ((coeff, term), idx) := pair
            let scaled := quotientScaledTermExpr coeff term
            if used.elem idx then (acc.1, acc.2 ++ [scaled])
            else (quotientSumExpr acc.1 scaled, acc.2))
          (QuotientExpr.const (quotientFqToU256 constant), [])
      some (shape, split.1, split.2)

/-! ## The hooks P-09c left standing in (rust: the builder's four recognizer calls) -/

/-- THE REAL HOOKS. This is what QuotientShapeRecognizers (VmBuilder.lean:221-229) was written
    to receive: four function fields, each bound to the Rust fn of the same name.
    noShapeRecognizers stays what it was - the conservative instantiation - and nothing in
    VmBuilder.lean had to change, exactly as P-09c promised at :44-47. -/
def shapeRecognizers : QuotientShapeRecognizers :=
  { pow5Base := quotientPow5Base
    limbShape := quotientLimbShape
    limbSubshape := quotientLimbSubshape
    modarith7Shape := quotientModarith7Shape }

end Midfall.Generator.QuotientRecognizers

/-! ## Known-answer tests

    Every gate below is a Bool or an IO Bool with a matching '#eval ... -- expect true' line
    at the end of the file, so scripts/kat_gate.py turns each one into a CI obligation
    (docs/REVIEW.md R-38). Each doc names the concrete wrong implementation it rules out, and
    the package report carries the perturbation actually run inside each stated scope (R-41).
    D-P19 binds the artifact gates: recognizerClusterHasNoLabelRead_ok opens vm/mod.rs while
    it evaluates and slices the recognizer cluster out by its own doc anchors rather than by
    line numbers, and the reachability gate recognizerArtifactReachable_ok runs FIRST so a
    wrong path is diagnosed rather than silently matched (plans README, D-P19 standing note).
    R-48: the fixture non-degeneracy gate runs before any gate that compares numbers. -/

namespace Midfall.Generator.QuotientVmRecognizersKats

open Midfall Midfall.Generator
open Midfall.Generator.QuotientRecognizers
open Midfall.Generator.QuotientBuilder
open Midfall.Generator.QuotientValidator
open Midfall.Generator.QuotientCertify
open Midfall.Generator.QuotientVmKats (readFileOrEmpty hasDuplicateNat lin7Short lin7Long)
open Midfall.Generator.QuotientVmBuilderKats

/-! ### Fixtures. R-48: these are THIS package's own - different coefficients and different
    bases from VmBuilder's - and rFixturesNonDegenerate_ok asserts distinctness before any
    comparison relies on it. -/

/-- The seven pointers this package recognises on: base 0x200, not the builder's 0x100, so a
    gate that confuses the two fixtures cannot pass. -/
def rPtrs : List Nat := [0x200, 0x220, 0x240, 0x260, 0x280, 0x2a0, 0x2c0]

/-- Distinct from lin7Coeffs (2,3,5,7,11,13,17) as a list and at every index. -/
def rCoeffs : List Word256 := [3, 5, 7, 11, 13, 17, 19]

/-- A seven-limb linear form: what sum_exprs(base_powers, limbs) lowers to. -/
def rLin7 : QuotientExpr :=
  sumLeft (QuotientExpr.const 0) ((rCoeffs.zip rPtrs).map fun (c, p) => scaled c (lit p))
def rLin7Shape : QuotientLimbShape := QuotientLimbShape.lin7 (rCoeffs.zip rPtrs)

/-- The flat bilinear row: sum_i c_i * (m(lhs) * m(rhs_i)). This is what
    try_quotient_bilin7_row_shape matches; the FACTORED spelling (lhs * sum_i c_i m(rhs_i),
    which is VmBuilder's own rowExpr fixture) is matched only by the factored row recognizer
    inside MODARITH7 - see rowSpellingMatters_ok. -/
def rRowLhs : Nat := 0x300
def rRowTerms : List QuotientExpr :=
  (rCoeffs.zip rPtrs).map fun (c, p) =>
    QuotientExpr.mul (QuotientExpr.const c) (QuotientExpr.mul (lit rRowLhs) (lit p))
def rRow7 : QuotientExpr := sumLeft (QuotientExpr.const 0) rRowTerms
def rRowShape : QuotientLimbShape := QuotientLimbShape.bilin7Row rRowLhs (rCoeffs.zip rPtrs)

/-- The 7x7 convolution over two fresh bases, with diagonal coefficients no two of which are
    equal, so a wrong i + j mapping cannot hide behind a repeated number. -/
def rPwLhsBase : Nat := 0x400
def rPwRhsBase : Nat := 0x500
def rPwCoeffs : List Word256 := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
def rPwTerms : List QuotientExpr :=
  (List.range quotientVmLimbs).flatMap fun i =>
    (List.range quotientVmLimbs).map fun j =>
      QuotientExpr.mul (QuotientExpr.const (rPwCoeffs.getD (i + j) 0))
        (QuotientExpr.mul (lit (rPwLhsBase + i * 0x20)) (lit (rPwRhsBase + j * 0x20)))
def rPw7 : QuotientExpr := sumLeft (QuotientExpr.const 0) rPwTerms
def rPwShape : QuotientLimbShape :=
  QuotientLimbShape.bilin7Pairwise rPwLhsBase rPwRhsBase rPwCoeffs

/-- Decomposition targets: each shape plus one term that is NOT part of it. -/
def rDecompLin : QuotientExpr := sumLeft rLin7 [scaled 23 (lit 0x2e0)]
def rDecompRow : QuotientExpr := sumLeft rRow7 [scaled 29 (lit 0x2e0)]
def rDecompPw : QuotientExpr := sumLeft rPw7 [scaled 31 (lit 0x700)]

/-- A fifth power of a non-trivial base, and the same five factors in a different order. The
    base is a SUM, not a product: collect_product_expr_factors (QVM:3123) flattens nested
    Muls, so a product base would make the tree ten factors rather than five and it would not
    recognise - which pow5Recognition_ok pins as its own clause. -/
def rPow5Base : QuotientExpr := QuotientExpr.add (lit 0x200) (QuotientExpr.const 5)
def rPow5 : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.mul rPow5Base rPow5Base)
    (QuotientExpr.mul (QuotientExpr.mul rPow5Base rPow5Base) rPow5Base)
def rPow5Commuted : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.mul rPow5Base (QuotientExpr.mul rPow5Base rPow5Base))
    (QuotientExpr.mul rPow5Base rPow5Base)
def rPow4 : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.mul rPow5Base rPow5Base)
    (QuotientExpr.mul rPow5Base rPow5Base)
def rPow5Mixed : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.mul rPow5Base rPow5Base)
    (QuotientExpr.mul (QuotientExpr.mul (QuotientExpr.add (lit 0x220) (QuotientExpr.const 5))
      rPow5Base) rPow5Base)
/-- Five copies of a PRODUCT base: the flattener sees ten factors, so this is not a fifth power
    as far as QVM:3179 is concerned. -/
def rPow5ProductBase : QuotientExpr :=
  let b := QuotientExpr.mul (lit 0x200) (QuotientExpr.const 5)
  QuotientExpr.mul (QuotientExpr.mul b b) (QuotientExpr.mul (QuotientExpr.mul b b) b)

/-- A MODARITH7 identity with a condition: cond * (const + lin + flat row + one load). -/
def rMaInner : QuotientExpr :=
  sumLeft (QuotientExpr.const 7) [rLin7, rRow7, scaled 43 (lit 0x600)]
def rMaCond : Nat := 0x620
def rMaExpr : QuotientExpr := QuotientExpr.mul (lit rMaCond) rMaInner

/-- The u16 boundary pair: seven limbs whose LAST pointer is 0xffe0 (fits) and 0x10000 (does
    not). -/
def rPtrsAt (base : Nat) : List Nat := (List.range quotientVmLimbs).map fun i => base + i * 0x20
def rLinAt (base : Nat) : QuotientExpr :=
  sumLeft (QuotientExpr.const 0) ((rCoeffs.zip (rPtrsAt base)).map fun (c, p) => scaled c (lit p))
def rLinU16Max : QuotientExpr := rLinAt 0xff20
def rLinU16Over : QuotientExpr := rLinAt 0xff40

/-- A seven-limb sum with ONE token pointer: hazard 3's other rejection. -/
def rLinWithToken : QuotientExpr :=
  sumLeft (QuotientExpr.const 0)
    ((((rCoeffs.zip rPtrs).drop 1).map fun (c, p) => scaled c (lit p)) ++
      [scaled 19 (QuotientExpr.mem (.token qMemBeta))])

/-- Every expression the gates sweep. -/
def rExprs : List (String × QuotientExpr) :=
  [("rLin7", rLin7), ("rRow7", rRow7), ("rPw7", rPw7), ("rDecompLin", rDecompLin),
   ("rDecompRow", rDecompRow), ("rDecompPw", rDecompPw), ("rPow5", rPow5),
   ("rPow4", rPow4), ("rPow5Mixed", rPow5Mixed), ("rMaExpr", rMaExpr),
   ("rLinU16Max", rLinU16Max), ("rLinU16Over", rLinU16Over),
   ("rLinWithToken", rLinWithToken), ("eCert", eCert), ("lin7Expr", lin7Expr),
   ("rowExpr", rowExpr), ("pwExpr", pwExpr), ("maExpr", maExpr), ("eRunLin4", eRunLin4)]

/-- The four nominal contexts hazard 1 is about: the SAME tree, four different identities.
    Nothing in QuotientExpr sees any of this, which is the point. -/
structure RContext where
  gateIndex : Nat
  gateName : String
  constraintName : String
  var : String
  deriving BEq

/-- A default for the getD-style lookups, so no gate depends on an Inhabited instance for a
    record whose fields are all meaningful. -/
def rDefaultCtx : RContext :=
  { gateIndex := 0, gateName := "foreign_norm", constraintName := "norm", var := "t0" }

/-- List.getD's argument order is (index, fallback) in this Lean; spelled as a helper so no gate
    gets it backwards. -/
def nthOf {α : Type} (xs : List α) (i : Nat) (fallback : α) : α := (xs.drop i).head?.getD fallback

def rContexts : List RContext :=
  [ { gateIndex := 0, gateName := "foreign_norm", constraintName := "norm", var := "t0" },
    { gateIndex := 41, gateName := "foreign_mul", constraintName := "mul_z", var := "t7" },
    { gateIndex := 7, gateName := "ecc_slope", constraintName := "slope", var := "q2" },
    { gateIndex := 41, gateName := "foreign_norm", constraintName := "norm", var := "t0" } ]

/-- One identity record for a tree under a nominal context. -/
def rIdentityOf (ctx : RContext) (e : QuotientExpr) : QuotientIdentity :=
  { meta_ := { globalIndex := ctx.gateIndex,
               source := QuotientIdentitySource.gate ctx.gateIndex ctx.gateName 0
                 ctx.constraintName 0 }
    lines := [ctx.var ++ " := add(1, 2)"]
    var := ctx.var
    target := QuotientTarget.main
    expr := e }

def rPlanOf (exprs : List QuotientExpr) : QuotientProgramPlan :=
  { inlineIdentities := []
    items := (exprs.zip (List.range exprs.length)).map
      (fun (e, i) => QuotientProgramItem.identity (rIdentityOf (nthOf rContexts i rDefaultCtx) e))
    nativeIdentities := []
    nativePermutationIdentities := []
    nativeLookupIdentities := []
    structuredTailIdentities := []
    sortedSimple := []
    hasNativePermutation := false
    hasNativeLookup := false
    selectorFold := selectorFoldPlanDefault }

def rG1 (a b c d : Nat) : G1Words := { xHi := a, xLo := b, yHi := c, yLo := d }

/-- A VK whose ten payload words are pairwise distinct and non-zero (R-48), and which is NOT the
    certifier's own certVk. -/
def rVk : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0x80
    constants := [("r0", 101), ("r1", 103)]
    fixedComms := [rG1 107 109 113 127]
    permutationComms := [rG1 131 137 139 149]
    quotientConstOffsetWords := none
    quotientConstWords := 0
    quotientProgramOffsetWords := none
    quotientProgramWords := 0
    quotientConstLabels := []
    quotientConstHeaders := [] }

/-- Emit one identity through a given hook set and finalize. -/
def rEmit (r : QuotientShapeRecognizers) (e : QuotientExpr) : M QuotientProgramBuild :=
  identityExpr r builderDefault e QuotientTarget.main none >>= finish

/-- The projections of a build, with the failure case rendered as nothing rather than as a panic
    the gate would have to pattern-match. -/
def rOptBytes (x : M QuotientProgramBuild) : Option Bytes :=
  match x with | .ok b => some b.bytes | .error _ => none
def rBytes (x : M QuotientProgramBuild) : List Nat :=
  match x with | .ok b => qvmBytesToNats b.bytes | .error _ => []
def rConsts (x : M QuotientProgramBuild) : List Word256 :=
  match x with | .ok b => b.consts | .error _ => []
def rSegment (x : M QuotientProgramBuild) : List Nat :=
  match x with
  | .ok b => (finalizedIdentitySegment (qvmBytesToNats b.bytes)).getD []
  | .error _ => []

/-- Emit a whole stream through a given hook set and finalize: the dual-build pair. -/
def rEmitStream (r : QuotientShapeRecognizers) :
    List QuotientExpr → QuotientProgramBuilder → M QuotientProgramBuilder
  | [], s => .ok s
  | e :: rest, s => do
      let s ← identityExpr r s e QuotientTarget.main none
      rEmitStream r rest s

def rDualExprs : List QuotientExpr := [rLin7, rRow7, rPw7, rDecompLin, rMaExpr]
def rDualPlan : QuotientProgramPlan := rPlanOf rDualExprs
def rOptimizedBuild : M QuotientProgramBuild :=
  rEmitStream shapeRecognizers rDualExprs builderDefault >>= finish
def rBaselineBuild : M QuotientProgramBuild :=
  rEmitStream noShapeRecognizers rDualExprs builderDefault >>= finish

def patchByteAt (bs : List Nat) (idx : Nat) (v : Nat) : List Nat :=
  (bs.take idx) ++ [v] ++ (bs.drop (idx + 1))
def patchBuild (build : QuotientProgramBuild) (idx : Nat) (v : Nat) : QuotientProgramBuild :=
  { build with bytes := qvmBytesOfNats (patchByteAt (qvmBytesToNats build.bytes) idx v) }

def certifyOk (x : Except String Unit) : Bool :=
  match x with | .ok _ => true | .error _ => false
def certifyErr (x : Except String Unit) : String :=
  match x with | .ok _ => "<ok>" | .error e => e
def validIsOk (bytes : List Nat) : Bool :=
  match validateQuotientProgram bytes with | .ok _ => true | .error _ => false
def exceptIsOk {α : Type} (x : Except QVMFault α) : Bool :=
  match x with | .ok _ => true | .error _ => false

/-- Every shape a limb recognizer returns over the sweep. -/
def rAllShapes : List QuotientLimbShape :=
  (rExprs.map (fun (_, e) => quotientLimbShape e)).filterMap id ++
    (rExprs.map (fun (_, e) => (quotientLimbSubshape e).map (fun s => s.1))).filterMap id

/-- Every MODARITH7 shape over the sweep. -/
def rAllModarith7 : List QuotientModarith7Shape :=
  (rExprs.map (fun (_, e) => quotientModarith7Shape e)).filterMap id

/-! ### GATE 0 - D-P19 reachability, FIRST -/

/-- The recognizer cluster's artifact, read from disk at #eval time. Two candidates so the gate
    resolves from formal/ (where lake and checks.sh run) and from the repo root. -/
def recognizerVmPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"]

/-- The cluster, sliced OUT BY DOC ANCHOR rather than by line number: from the item that opens
    quotient_limb_shape to the first non-recognizer item after it, parse_mem. A line-number
    slice drifts silently the moment the Rust file changes; this one fails loudly because both
    anchors have to be present. -/
def recognizerClusterSource (src : String) : Option String :=
  let lines := src.splitOn "\n"
  let start? := lines.findIdx? (fun l => l.contains "fn quotient_limb_shape")
  let stop? := lines.findIdx? (fun l => l.contains "fn parse_mem")
  match start?, stop? with
  | some st, some sp =>
      if sp > st then some (String.intercalate "\n" ((lines.drop st).take (sp - st))) else none
  | _, _ => none

/-- Reachability, plus the slice's own sanity: the cluster must be large and must contain the
    public entry points. Rules out: a wrong path (the slice is none), a renamed anchor, and a
    slice so short it contains nothing worth checking. -/
def recognizerArtifactReachable_ok : IO Bool := do
  let mut got := ""
  for cand in recognizerVmPathCandidates do
    if got.length == 0 then got ← readFileOrEmpty cand
  match recognizerClusterSource got with
  | none => return false
  | some cluster =>
      return cluster.length > 20000 &&
        cluster.contains "fn quotient_pow5_base" &&
        cluster.contains "fn quotient_limb_subshape" &&
        cluster.contains "fn try_quotient_bilin7_pairwise_shape" &&
        cluster.contains "fn quotient_modarith7_affine_shape"

/-! ### GATE 1 - hazard 1: recognition cannot depend on a name -/

/-- HAZARD 1'S GATE. The doc at QVM:966-971 says shapes are "recognized from the expression tree
    alone" and that "adding a limb opcode must never make correctness depend on a gate label or
    on a hand-maintained list of circuit gadgets". Three clauses, all inside that scope: (a) the
    same tree under four different nominal contexts - different gate index, gate name,
    constraint name and Yul variable - recognises identically, for all four recognizers and for
    the canonical key; (b) the emitted program is byte-identical across those contexts, which is
    the operational form of the claim; and (c) the identity record really does carry a label and
    the four contexts really differ, so (a) is not comparing four identical contexts. Rules out:
    a recognizer that consults identity metadata, a label-keyed dispatch table, and a builder
    path that lets the label reach the encoder. -/
def labelIndependence_ok : Bool :=
  rExprs.all fun (_, e) =>
    let perCtx := rContexts.map fun ctx =>
      (quotientLimbShape (rIdentityOf ctx e).expr,
       quotientLimbSubshape (rIdentityOf ctx e).expr,
       quotientModarith7Shape (rIdentityOf ctx e).expr,
       quotientPow5Base (rIdentityOf ctx e).expr,
       quotientExprKey (rIdentityOf ctx e).expr,
       rOptBytes (rEmit shapeRecognizers (rIdentityOf ctx e).expr))
    perCtx.all (fun s => s == perCtx.head!) &&
      (rContexts.length == 4 &&
        (rIdentityOf (nthOf rContexts 0 rDefaultCtx) e).meta_.source !=
          (rIdentityOf (nthOf rContexts 3 rDefaultCtx) e).meta_.source)

/-- The artifact half of hazard 1: the recognizer cluster in the Rust reads no label. The tokens
    are the ones a label-dependent recognizer would have to use - identity metadata fields, the
    gate-name accessors, the api.rs source enum - and the scan strips line comments first,
    because the prose DOES mention "gate names" and "circuit gadgets", as a prohibition. If a
    future recognizer reads a label, this reddens. Rules out: the design constraint being
    honoured only by the current file and nothing checking it. -/
def recognizerClusterHasNoLabelRead_ok : IO Bool := do
  let mut got := ""
  for cand in recognizerVmPathCandidates do
    if got.length == 0 then got ← readFileOrEmpty cand
  match recognizerClusterSource got with
  | none => return false
  | some cluster =>
      let code := String.intercalate "\n"
        ((cluster.splitOn "\n").filter fun l =>
          !((l.dropWhile (fun c => c == ' ')).startsWith "//"))
      let forbidden := ["meta.", "gate_name", "constraint_name", "identity.meta",
        "QuotientIdentitySource", "QuotientTarget", "label", "fixed_column", "selector_name",
        "gadgets", "columns"]
      -- Positive control (R-40/R-41): the same contains machinery must find tokens that ARE in
      -- the region, so an empty or mis-sliced buffer cannot pass the negative half.
      return code.length > 20000 && (forbidden.all fun tok => !code.contains tok) &&
        (code.contains "quotient_mem_term" && code.contains "u16::try_from" &&
          code.contains "QUOTIENT_VM_LIMBS")

/-- The commutative-key claim quotient_pow5_base rests on: two trees that differ only by
    commuting an addition or a multiplication key equal, and a tree with a different leaf does
    not. This is hazard 1 in miniature - the key is a function of the tree's shape and the only
    strings in it come from node tags and pointers. Rules out: a key that is sensitive to operand
    order (which would make x^5 written the other way round fall off the fused path), and a key
    that loses a node tag so two different leaves collide. -/
def pow5CommutativeKey_ok : Bool :=
  quotientExprKey (QuotientExpr.add (lit 0x100) (lit 0x120)) ==
    quotientExprKey (QuotientExpr.add (lit 0x120) (lit 0x100)) &&
  quotientExprKey (QuotientExpr.mul (lit 0x100) (lit 0x120)) ==
    quotientExprKey (QuotientExpr.mul (lit 0x120) (lit 0x100)) &&
  quotientExprKey (QuotientExpr.add (lit 0x100) (lit 0x120)) !=
    quotientExprKey (QuotientExpr.add (lit 0x100) (lit 0x140)) &&
  quotientExprKey (QuotientExpr.neg (lit 0x100)) == "n:m:100" &&
  quotientExprKey (QuotientExpr.const 255) == "c:ff" &&
  quotientExprKey (QuotientExpr.mem (.tokenOffset qMemBeta 32)) == "to:4:20"

/-! ### GATE 2 - hazard 2: the two postconditions P-09c could not enforce -/

/-- HAZARD 2 (a). P-09c's F-5 said emit_affine_terms' claim that the matched slice "is always
    non-empty" is a recognizer POSTCONDITION the type does not carry, and that a hook returning
    an empty matched list makes the builder emit a program whose trailing ADD pops a stack
    holding only the residue (VmBuilder.lean:2415-2431). For the REAL recognizers it follows
    from the construction - every subshape matcher requires used.len() >= 7 (QVM:3848), >= 7
    (QVM:3897) or >= 49 (QVM:3968) before it returns, and quotient_limb_subshape rejects an
    empty used at QVM:3206 - and this gate checks it over every fixture, including the ones that
    do NOT recognise. Rules out: a subshape matcher whose used list can come back empty, and a
    split that drops every matched index. -/
def subshapeMatchedNonEmpty_ok : Bool :=
  rExprs.all fun (_, e) =>
    match quotientLimbSubshape e with
    | none => true
    | some (_, _, matched) => !matched.isEmpty

/-- HAZARD 2 (b). The other postcondition: the residue the decomposition path re-enters emit_expr
    on is STRICTLY SMALLER than the input, which is what makes the Rust's recursion terminate
    and what P-09c could only assume behind the hook (its R10 note, VmBuilder.lean:85-88).
    Measured with nodeCount, the same proxy P-09c used for the emitter's fuel. Rules out: a
    residue that reproduces the whole input (which would make the builder recurse on itself,
    bounded only by the port's fuel), and a residue that is the input with one term ADDED. -/
def subshapeResidueShrinks_ok : Bool :=
  rExprs.all fun (_, e) =>
    match quotientLimbSubshape e with
    | none => true
    | some (_, residue, _) => residue.nodeCount < e.nodeCount

/-- HAZARD 2 (c), and P-09a hazard 4 made real. VmTypes.lean:401-406 records that the arity is
    NOT part of the type - a 6-term or 8-term Lin7 is well-typed - and that what enforces it is
    the recognizers' length guards at QVM:3667, 3714 and 3753. This gate checks the enforcement:
    every shape the recognizers produce is wellFormed, and so is every block inside every
    MODARITH7 shape. The negative half pins that the predicate is not vacuous: VmTypes'
    hand-built 6-term and 8-term Lin7 fixtures are well-typed and NOT wellFormed, so a
    recognizer that skipped its guard would produce one of those and redden this gate. Rules
    out: a matcher whose length guard was dropped, and one that compares the length before the
    zero-coefficient retain instead of after. -/
def recognizersProduceWellFormedShapes_ok : Bool :=
  !rAllShapes.isEmpty &&
  rAllShapes.all QuotientLimbShape.wellFormed &&
  rAllModarith7.all fun s =>
    (s.lin.all fun block => block.length == quotientVmLimbs) &&
    (s.rows.all fun (_, block) => block.length == quotientVmLimbs) &&
    (s.pairwise.all fun (_, _, coeffs) => coeffs.length == quotientVmPairwiseCoeffs) &&
  !lin7Short.wellFormed && !lin7Long.wellFormed &&
  (match quotientLimbShape rLin7 with
   | some sh => sh.wellFormed
   | none => false)

/-- The frontier P-09c named, re-checked against the real hooks: with a hook that returns an
    empty matched list the builder still emits the broken program (so the contract is real, not
    decorative), and with the REAL recognizers no fixture can produce that shape. Rules out:
    this package quietly making the builder's guard unnecessary in a way the next hook author
    cannot see. -/
def emptyMatchedStillABoundary_ok : Bool :=
  (match emitExprTop emptyMatchedHooks (stateWithConsts 249) decompTarget with
   | .ok s => s.stackDepth == 0 && ! exceptIsOk (runProg s.bytes s.consts)
   | .error _ => false) &&
  (rExprs.all fun (_, e) =>
    match quotientLimbSubshape e with
    | none => true
    | some (_, _, matched) => !matched.isEmpty)

/-- The matched list really is the shape's own terms: for every decomposition the recognizer
    returns, the residue plus the matched terms evaluates to the same field element as the whole
    input. This is the property QVM:3210-3214 claims for the panic-free fallback path, and it is
    what makes the double preflight in try_emit_limb_decomposition (QVM:1361-1387) safe rather
    than hopeful. Rules out: a matched list that omits a term the shape uses, which would make
    the fallback evaluate a different polynomial from the fused opcode. -/
def matchedReconstructsTheShape_ok : Bool :=
  rExprs.all fun (_, e) =>
    match quotientLimbSubshape e with
    | none => true
    | some (_, residue, matched) =>
        let rebuilt := matched.foldl QuotientExpr.add residue
        rebuilt.nodeCount > 0 && oracle rebuilt == oracle e && !matched.isEmpty

/-- Two near-miss grids, so the pairwise matcher's two rejection clauses each have a fixture that
    can reach them: a 7x7 grid whose coefficients do NOT depend only on i + j (the
    diagonal-consistency check, QVM:3784-3788), and a 49-term list in which two products land in
    the same row-major slot so another slot is never seen (the completeness check, QVM:3776).
    Both must be rejected, and both must still lower to a valid program. -/
def rPwSkewedTerms : List QuotientExpr :=
  (List.range quotientVmLimbs).flatMap fun i =>
    (List.range quotientVmLimbs).map fun j =>
      let c := rPwCoeffs.getD (i + j) 0
      QuotientExpr.mul (QuotientExpr.const (if i == 3 && j == 2 then c + 100 else c))
        (QuotientExpr.mul (lit (rPwLhsBase + i * 0x20)) (lit (rPwRhsBase + j * 0x20)))
def rPwSkewed : QuotientExpr := sumLeft (QuotientExpr.const 0) rPwSkewedTerms

/-- The duplicate-and-drop grid: slot (6,6) is replaced by a second copy of slot (0,0), so 49
    pairs are present but one diagonal slot is never seen. -/
def rPwDuplicateTerms : List QuotientExpr :=
  (List.range quotientVmLimbs).flatMap fun i =>
    (List.range quotientVmLimbs).map fun j =>
      if i == 6 && j == 6
        then QuotientExpr.mul (QuotientExpr.const 97)
          (QuotientExpr.mul (lit rPwLhsBase) (lit rPwRhsBase))
        else QuotientExpr.mul (QuotientExpr.const (rPwCoeffs.getD (i + j) 0))
          (QuotientExpr.mul (lit (rPwLhsBase + i * 0x20)) (lit (rPwRhsBase + j * 0x20)))
def rPwDuplicate : QuotientExpr := sumLeft (QuotientExpr.const 0) rPwDuplicateTerms

/-- PAIRWISE REJECTION BOUNDARIES. The pairwise matcher has three ways to say no after the length
    guard passes, and each gets its own fixture here because none of them was reachable before:
    the diagonal-consistency check (QVM:3784-3788, "coefficients disagree" in the doc), the
    slot-completeness check (QVM:3776, "if any slot is missing"), and the base-pair scan finding
    no consistent grid at all. The doc's own promise is what is being pinned: "If any slot is
    missing or coefficients disagree, the shape is rejected and the generic VM remains the source
    of truth" - so each near-miss must be rejected AND must still lower to a program that
    validates and evaluates correctly through the fallback. The subshape path is NOT expected to
    reject a near-miss grid: a 49-term grid still contains a legal seven-term row, and
    QVM:3864-3911 is entitled to extract it, so those clauses assert only what must hold of
    whatever is returned - a well-formed shape, a non-empty matched list and a strictly smaller
    residue. Rules out: a diagonal check that only ever compares equal numbers, a seen-check that
    was dropped, and a rejection that leaves the builder with no path at all. -/
def pairwiseRejectionBoundaries_ok : Bool :=
  (quotientLimbShape rPw7).isSome &&
  (quotientLimbShape rPwSkewed).isNone &&
  (quotientLimbShape rPwDuplicate).isNone &&
  (match quotientLimbSubshape rPwSkewed with
   | none => true
   | some (sh, residue, matched) =>
       sh.wellFormed && !matched.isEmpty && residue.nodeCount < rPwSkewed.nodeCount) &&
  (match rEmit shapeRecognizers rPwSkewed with
   | .error _ => false
   | .ok b => validIsOk (qvmBytesToNats b.bytes) &&
       okIs (runProg (rSegment (rEmit shapeRecognizers rPwSkewed)) b.consts) (oracle rPwSkewed)) &&
  (match rEmit shapeRecognizers rPwDuplicate with
   | .error _ => false
   | .ok b => okIs (runProg (rSegment (rEmit shapeRecognizers rPwDuplicate)) b.consts)
        (oracle rPwDuplicate))

/-- The two guards in quotient_limb_subshape that decide whether a decomposition is worth taking
    at all, each pinned at its own boundary. QVM:3199 refuses a sum with nothing left over
    ('terms.len() <= QUOTIENT_VM_LIMBS && constant == ZERO'): seven terms and no constant is the
    WHOLE shape, which is quotient_limb_shape's job, not a subshape's. QVM:3206's second disjunct
    refuses the same thing reached a different way - eight terms whose pointers duplicate one
    limb, so the seven-limb window consumes all eight indices and the residue would be a bare
    zero. The third clause is the boundary from the other side: a constant makes a full consume
    legal, because the residue is then the constant and the emitted program is still one value
    plus a fused opcode. Rules out: a subshape that fires on a shape with no residue (which makes
    the builder emit a redundant zero-and-add), and one that refuses a decomposition whose residue
    is a constant. -/
def rDupFullWindow : QuotientExpr :=
  sumLeft (QuotientExpr.const 0)
    [scaled 3 (lit 0x200), scaled 5 (lit 0x200), scaled 7 (lit 0x220), scaled 11 (lit 0x240),
      scaled 13 (lit 0x260), scaled 17 (lit 0x280), scaled 19 (lit 0x2a0),
      scaled 23 (lit 0x2c0)]
def rConstResidue : QuotientExpr :=
  sumLeft (QuotientExpr.const 5) ((rCoeffs.zip rPtrs).map fun (c, p) => scaled c (lit p))

def subshapeGuardBoundaries_ok : Bool :=
  (quotientLimbSubshape lin7Expr).isNone &&
  (quotientLimbSubshape rLin7).isNone &&
  (quotientLimbSubshape rDupFullWindow).isNone &&
  (quotientLimbSubshape rDecompLin).isSome &&
  (match quotientLimbSubshape rConstResidue with
   | none => false
   | some (sh, residue, matched) =>
       sh.wellFormed && matched.length == quotientVmLimbs &&
         residue == QuotientExpr.const 5) &&
  (quotientLimbShape rDupFullWindow).isSome

/-! ### GATE 3 - hazard 3: the u16 safety valve -/

/-- The u16 modelling itself, pinned at the widths: try_from accepts 0xffff and rejects 0x10000,
    checked_add refuses where plain addition wraps, and limb7_index rejects a pointer below its
    base and one that is not word-aligned. These are the three helpers every guard in the cluster
    is built from, so a mistake here propagates everywhere. Rules out: modelling u16::try_from as
    a truncation ('as u16' instead of try_from), which is the single most likely port error in
    this file. -/
def u16Modelling_ok : Bool :=
  u16TryFrom 0xffff == some 0xffff && u16TryFrom 0x10000 == none && u16TryFrom 0 == some 0 &&
  u16CheckedAdd 0xffe0 0x20 == none && u16CheckedAdd 0xffdf 0x20 == some 0xffff &&
  u16CheckedAdd 0x100 0x20 == some 0x120 &&
  u16Add 0xffe0 0x20 == 0 && u16Add 0x100 0x20 == 0x120 &&
  u16CheckedSub 0x100 0x120 == none && u16CheckedSub 0x120 0x100 == some 0x20 &&
  limb7Index 0x100 0x100 == some 0 && limb7Index 0x100 0x120 == some 1 &&
  limb7Index 0x100 0x110 == none && limb7Index 0x100 0xe0 == none &&
  limb7Index 0x100 0x240 == none && limb7Index 0x100 0x1c0 == some 6

/-- HAZARD 3. The boundary is 0xffff / 0x10000 and it is a REJECTION, not a panic:
    u16::try_from(..).ok()? at QVM:4024 propagates out of quotient_product_mem_factors, so the
    whole recognizer returns None and the builder takes the generic Fr path. Four clauses: the
    last limb at 0xffe0 recognises; the last limb at 0x10000 does not; a token pointer does not
    (QVM:4025-4026); and the guard is LOAD-BEARING - feeding the oversized shape straight to
    emit_limb_shape panics at QVM:1824, which is the build abort the recognizer prevents. Rules
    out: a recognizer that truncates the pointer instead of rejecting, and one that lets a token
    reach a limb opcode. -/
def u16FallbackBoundary_ok : Bool :=
  (rPtrsAt 0xff20).getLast! == 0xffe0 && (rPtrsAt 0xff40).getLast! == 0x10000 &&
  (quotientLimbShape rLinU16Max).isSome &&
  (quotientLimbShape rLinU16Over).isNone &&
  (quotientLimbShape rLinWithToken).isNone &&
  (quotientLimbSubshape rLinU16Over).isNone &&
  (quotientMemTerm (lit 0x10000)).isNone &&
  quotientMemTerm (lit 0xffff) == some (1, 0xffff) &&
  (match emitLimbShape builderDefault
      (QuotientLimbShape.lin7 (rCoeffs.zip (rPtrsAt 0xff40))) with
   | .ok _ => false
   | .error _ => isPanicAt (emitLimbShape builderDefault
       (QuotientLimbShape.lin7 (rCoeffs.zip (rPtrsAt 0xff40)))) siteU16Overflow)

/-- HAZARD 3's other half, and the part P-09a could not check: the fallback is a VALID,
    DIFFERENTLY ENCODED program, not a rejected one. For the oversized-pointer tree the builder
    emits through the generic path: the finalized program passes P-09e's structural validator,
    the identity segment executes to the same field element as the oracle, and the encoding
    differs from the recognised build - LIN7 (0x1c) with PUSH_MEM_U16 (0x05) operands on the
    fused side, PUSH_MEM_LITERAL (0x02) with a four-byte pointer on the fallback side. The last
    clause pins that the fallback is what noShapeRecognizers would have produced anyway, i.e. the
    recognizer's rejection and the hook being absent are the same code path. Rules out: a
    fallback that emits a program the interpreter rejects, a fallback that silently produces the
    SAME bytes (which would mean the recognizer never fired), and a fallback whose constant table
    disagrees with its bytes. -/
def fallbackProgramIsValidAndDifferentlyEncoded_ok : Bool :=
  let over := rEmit shapeRecognizers rLinU16Over
  let fused := rEmit shapeRecognizers rLinU16Max
  let overGeneric := rEmit noShapeRecognizers rLinU16Over
  let overBytes := rBytes over
  let fusedBytes := rBytes fused
  overBytes != [] && fusedBytes != [] &&
    validIsOk overBytes &&
    okIs (runProg (rSegment over) (rConsts over)) (oracle rLinU16Over) &&
    okIs (runProg (rSegment fused) (rConsts fused)) (oracle rLinU16Max) &&
    overBytes != fusedBytes &&
    fusedBytes.any (· == qOpLin7) &&
    !overBytes.any (· == qOpLin7) &&
    overBytes.any (· == qOpPushMemLiteral) &&
    fusedBytes.any (· == qOpPushMemU16) &&
    overBytes == rBytes overGeneric

/-! ### GATE 4 - hazard 4: the real hooks, end to end -/

/-- THE ACCEPTANCE GATE. P-09c's dual-build comparison (VmCertify.lean:1849-1873) had to be run
    with a hand-supplied hook that recognised exactly one expression, and it said so: "that
    exercises the comparison and the seed binding; it is NOT the Rust's claim about recognizers
    on a real circuit". This is the same comparison with the REAL recognizers wired in: five
    identities (LIN7, flat row, 7x7 pairwise, a decomposition, and a conditional MODARITH7),
    optimized through shapeRecognizers and baseline through noShapeRecognizers, certifying as
    identical under P-09d's own driver, with the two programs differing byte-wise and in their
    constant tables, and the seed absorbing both. The negative control is the one-byte patch: it
    must produce the Rust's disagreement message, which is what makes the accept clause a check
    rather than a tautology. Rules out: a recognizer that changes the value of an identity (the
    soundness claim QVC:291-332 exists to catch), a dual build that is secretly the same program,
    and a comparison that cannot fail. -/
def dualBuildWithRealRecognizers_ok : Bool :=
  match rOptimizedBuild, rBaselineBuild with
  | .ok o, .ok b =>
      let ob := qvmBytesToNats o.bytes
      let bb := qvmBytesToNats b.bytes
      ob != bb && o.consts != b.consts &&
        certifyOk (certifyQuotientBuildsAgree rDualPlan o b rVk) &&
        certifyOk (certifyQuotientProgram rDualPlan o rVk) &&
        certifyOk (certifyQuotientProgram rDualPlan b rVk) &&
        (certifyErr (certifyQuotientBuildsAgree rDualPlan o (patchBuild b 1 0x01) rVk)).contains
          "changed the value of interpreted identity at stream position" &&
        (certifyErr (certifyQuotientBuildsAgree rDualPlan o (patchBuild b 1 0x01) rVk)).contains
          "One of the shape recognizers is unsound for this gate shape."
  | _, _ => false

/-- Every fixture, emitted with the REAL hooks, finalized, and run through P-09b's interpreter
    against the oracle: the same certification P-09c's headline gate makes with
    noShapeRecognizers, now with the recognizers that actually fire. This is the leg that would
    catch a shape whose fused encoding evaluates differently from the tree it was recognised from
    - including a shape whose arity is wrong, which is P-09a hazard 4's scenario. Rules out: an
    operand written in the wrong width or order for a fused opcode, a residue/matched split that
    does not sum back to the input, and a MODARITH7 block order the interpreter reads differently
    from the way the recognizer wrote it. -/
def realHooks_endToEnd_ok : Bool :=
  rExprs.all fun (_, e) =>
    match rEmit shapeRecognizers e with
    | .error _ => false
    | .ok b =>
        let bytes := qvmBytesToNats b.bytes
        match finalizedIdentitySegment bytes with
        | none => false
        | some seg => seg != [] && okIs (runProg seg b.consts) (oracle e) && validIsOk bytes

/-- The real recognizers reproduce, shape for shape, what P-09c hand-supplied: the builder's own
    lin7Expr and pwExpr trees lower to exactly its lin7Shape and pwShape fixtures. This is what
    makes P-09c's gate-8 evidence transfer instead of having to be redone. Rules out: a
    recognizer that produces the same shape up to ordering (the Rust sorts by pointer for exactly
    this reason, QVM:3651-3653), and one that picks a different base for the pairwise grid. -/
def realHooksReproduceP09cFixtureShapes_ok : Bool :=
  quotientLimbShape lin7Expr == some lin7Shape &&
  quotientLimbShape pwExpr == some pwShape &&
  quotientLimbShape rLin7 == some rLin7Shape &&
  quotientLimbShape rRow7 == some rRowShape &&
  quotientLimbShape rPw7 == some rPwShape

/-- QVM:3651-3653's own claim: "The resulting terms are sorted by memory pointer so equivalent
    expressions have deterministic bytecode even when the source expression tree orders additions
    differently." Three orderings of the same seven terms - ascending, descending, and
    right-associated - must give the same shape and the same bytes, and the same must hold for
    the pairwise grid written row-major versus column-major. Rules out: a matcher that emits
    terms in source order, which would make bytecode depend on the lowering's association and
    break the certifier's byte-for-byte comparisons. -/
def determinismUnderPermutation_ok : Bool :=
  let rTerms := (rCoeffs.zip rPtrs).map fun (c, p) => scaled c (lit p)
  let desc := sumLeft (QuotientExpr.const 0)
    ((rCoeffs.zip rPtrs).reverse.map fun (c, p) => scaled c (lit p))
  let rightNested := rTerms.foldr (fun t acc => QuotientExpr.add t acc) (QuotientExpr.const 0)
  let colMajor := sumLeft (QuotientExpr.const 0)
    ((List.range quotientVmLimbs).flatMap fun j =>
      (List.range quotientVmLimbs).map fun i =>
        QuotientExpr.mul (QuotientExpr.const (rPwCoeffs.getD (i + j) 0))
          (QuotientExpr.mul (lit (rPwLhsBase + i * 0x20)) (lit (rPwRhsBase + j * 0x20))))
  quotientLimbShape rLin7 == quotientLimbShape desc &&
    rOptBytes (rEmit shapeRecognizers rLin7) == rOptBytes (rEmit shapeRecognizers desc) &&
    quotientLimbShape rPw7 == quotientLimbShape colMajor &&
    quotientLimbShape rightNested == some rLin7Shape

/-- The two spellings of a bilinear row are NOT interchangeable, and this is a finding rather than
    a bug: the flat sum of products is a limb shape (BILIN7_ROW, one opcode), while the factored
    lhs * sum form - which is what VmBuilder's own rowExpr fixture is - is recognised only inside
    MODARITH7, by quotient_factored_bilin7_row_shape. Pinning it here because the brief's hazard
    list and VmBuilder's fixture both call the second one "the row shape", and a reader who
    assumes the flat matcher covers it will be wrong. Rules out: a factored row being silently
    recognised as BILIN7_ROW by the flat matcher. -/
def rowSpellingMatters_ok : Bool :=
  quotientLimbShape rRow7 == some rRowShape &&
  quotientLimbShape rowExpr == none &&
  (quotientModarith7Shape rowExpr).isSome &&
  (quotientModarith7Shape rRow7).isNone

/-- The MODARITH7 recognizer's own output, pinned structurally: condition pointer, the constant,
    one lin block and one row block, and the leftover scalar memory term bucketed into mem_terms.
    The counts are what the encoding's five one-byte length fields carry, so a recognizer that
    produced a 256th component would be caught here before the preflight ever ran. Rules out: the
    cond factor being swallowed into the sum, the constant landing in mem_terms, and a block
    being emitted twice by the accumulator loop. -/
def modarith7Recognition_ok : Bool :=
  match quotientModarith7Shape rMaExpr with
  | some s => s.cond == some rMaCond && s.constant.toNat == 7 && s.lin.length == 1 &&
      (nthOf s.lin 0 []).length == quotientVmLimbs && s.rows.length == 1 &&
      (nthOf s.rows 0 (0, [])).1 == rRowLhs && s.pairwise.isEmpty &&
      s.memTerms.length == 1 && s.productTerms.isEmpty &&
      (modarith7Coeffs s).length == 16
  | none => false

/-- pow5: five equal factors recognise, four do not, five with one different factor does not, and
    a commuted spelling does (the key is commutative). A fifth power of a PRODUCT base does not,
    because the flattener sees ten factors. The base returned is the first factor, which is what
    try_emit_pow5 re-enters emit_expr on. Rules out: a matcher that counts Mul nodes instead of
    flattened factors, and one that compares trees structurally instead of by key (which would
    reject rPow5Commuted). -/
def pow5Recognition_ok : Bool :=
  quotientPow5Base rPow5 == some rPow5Base &&
  quotientPow5Base rPow5Commuted == some rPow5Base &&
  quotientPow5Base rPow4 == none &&
  quotientPow5Base rPow5Mixed == none &&
  quotientPow5Base rLin7 == none &&
  quotientPow5Base ePow5 == some ePow5Base &&
  quotientPow5Base rPow5ProductBase == none

/-- The hooks are the four functions, not a copy: each field of shapeRecognizers agrees with its
    recognizer on every fixture, and noShapeRecognizers still recognises nothing. This is the
    wiring gate - if a field were bound to the wrong recognizer (say limbShape to
    quotientLimbSubshape) the types would still check. Rules out: a mis-wired hook and a hook
    that fires on a tree the recognizer rejects. -/
def hooksBoundToTheRecognizers_ok : Bool :=
  rExprs.all fun (_, e) =>
    shapeRecognizers.pow5Base e == quotientPow5Base e &&
      shapeRecognizers.limbShape e == quotientLimbShape e &&
      shapeRecognizers.limbSubshape e == quotientLimbSubshape e &&
      shapeRecognizers.modarith7Shape e == quotientModarith7Shape e &&
    noShapeRecognizers.limbShape e == none && noShapeRecognizers.modarith7Shape e == none

/-- The port-only bounds stay bounds: the MODARITH7 accumulator's fuel never runs out and its
    four unreachable! legs never fire on any fixture, and the emitter's own fuel is never reached
    with the real hooks either. These are the places where the port is not a literal
    transcription (header, R4 (c) and R10), so each is asserted rather than assumed. Rules out: a
    loop that actually needs its fuel, which would mean the Rust's termination argument is wrong,
    and a recognizer returning the wrong variant. -/
def portBoundsNeverBind_ok : Bool :=
  rExprs.all fun (_, e) =>
    (match collectQuotientAffineTerms e fqOne with
     | none => true
     | some (raw, _) =>
         let terms := raw.filter (fun t => !fqIsZero t.1)
         exceptIsOk (modarith7Loop (terms.length + 1)
           { lin := [], rows := [], pairwise := [], terms := terms})) &&
    exceptIsOk (emitExprTop shapeRecognizers builderDefault e)

/-- R-48. The fixtures this package compares are not degenerate: the pointer sets are pairwise
    distinct and disjoint between the lin, row, pairwise and MODARITH7 fixtures; the coefficient
    lists differ from VmBuilder's; the four nominal contexts really differ from each other; and
    the dual-build expression list has five distinct trees. Rules out: every comparison gate above
    being satisfied by one value. -/
def rFixturesNonDegenerate_ok : Bool :=
  !hasDuplicateNat rPtrs && rPtrs.length == 7 &&
    !hasDuplicateNat (rCoeffs.map (fun c => c.toNat)) &&
    rCoeffs != lin7Coeffs && rPwCoeffs != pwCoeffs &&
    rPtrs != bPtrs && !rPtrs.elem rRowLhs && !rPtrs.elem rPwLhsBase &&
    !rPtrs.elem rPwRhsBase && rPwLhsBase != rPwRhsBase &&
    (rContexts.zip (List.range rContexts.length)).all fun (ctx, i) =>
      (rContexts.zip (List.range rContexts.length)).all fun (ctx', j) =>
        i == j || (ctx.gateIndex, ctx.gateName, ctx.constraintName, ctx.var) !=
          (ctx'.gateIndex, ctx'.gateName, ctx'.constraintName, ctx'.var) &&
    rDualExprs.length == 5 &&
    (rDualExprs.zip (List.range rDualExprs.length)).all fun (e, i) =>
      (rDualExprs.zip (List.range rDualExprs.length)).all fun (e', j) =>
        i == j || e != e' &&
    rExprs.length == 19 && (rAllShapes.length + rAllModarith7.length) > 4

/-- The Fr encode/decode pair the shapes are built from: quotient_fq_to_u256 round-trips every
    coefficient the recognizers emit, including the largest value the field has, and
    quotient_fq_from_u256 rejects a non-canonical one (which is what makes a Const node outside
    the field a rejection rather than a silent reduction). Rules out: a shape whose coefficient
    is the wrapped value rather than the field element, and a collector that accepts a
    non-canonical constant. -/
def fqRoundTrip_ok : Bool :=
  (rCoeffs.map (fun c => c.toNat)).all (fun n =>
    quotientFqFromU256 (quotientFqToU256 n) == some n) &&
  quotientFqFromU256 (quotientFqToU256 (qvmFrModulus - 1)) == some (qvmFrModulus - 1) &&
  quotientFqFromU256 (BitVec.ofNat 256 qvmFrModulus) == none &&
  quotientFqToU256 (qvmFrModulus - 1) == BitVec.ofNat 256 (qvmFrModulus - 1) &&
  fqAdd (qvmFrModulus - 1) 1 == 0 && fqNeg 0 == 0

/-- The pairwise grid's index arithmetic stays inside the 49-slot table the Rust allocates, which
    is the precondition for updateNth's "out of range is a no-op" rendering being unobservable.
    The last two clauses are the boundary itself: the eighth limb of a vector is not an index,
    the seventh is. Rules out: an i or j escaping 0..6, which in the Rust would be an
    index-out-of-bounds panic in release too. -/
def pairwiseGridIndexStaysInBounds_ok : Bool :=
  (List.product (List.range quotientVmLimbs) (List.range quotientVmLimbs)).all
    (fun (ij : Nat × Nat) => ij.1 * quotientVmLimbs + ij.2 < quotientVmPairwiseTerms &&
      ij.1 + ij.2 < quotientVmPairwiseCoeffs) &&
  quotientVmPairwiseTerms == quotientVmLimbs * quotientVmLimbs &&
  quotientVmPairwiseCoeffs == 2 * quotientVmLimbs - 1 &&
  limb7Index 0x100 (0x100 + 7 * qvmWordBytes) == none &&
  limb7Index 0x100 (0x100 + 6 * qvmWordBytes) == some 6

/-- The recognizer sweep does not recognise everything: most of the generic fixtures are rejected
    by every recognizer, so the gates above are not passing because everything matches. Rules out:
    a recognizer that returns Some for any tree, which would make the fallback path dead code and
    every fallback gate vacuous. -/
def recognizersDoNotRecogniseEverything_ok : Bool :=
  (quotientLimbShape eCert).isNone && (quotientLimbShape eRunLin4).isNone &&
    (quotientModarith7Shape eCert).isNone && (quotientLimbSubshape lin7Expr).isNone &&
    (quotientPow5Base rLin7).isNone &&
    (rExprs.filter (fun (_, e) => (quotientLimbShape e).isNone)).length >= 5 &&
    (rExprs.filter (fun (_, e) => (quotientLimbShape e).isSome)).length >= 4

#eval Midfall.Generator.QuotientVmRecognizersKats.pairwiseRejectionBoundaries_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.recognizerArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.recognizerClusterHasNoLabelRead_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.rFixturesNonDegenerate_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.labelIndependence_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.pow5CommutativeKey_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.subshapeMatchedNonEmpty_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.subshapeResidueShrinks_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.recognizersProduceWellFormedShapes_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.emptyMatchedStillABoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.matchedReconstructsTheShape_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.subshapeGuardBoundaries_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.u16Modelling_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.u16FallbackBoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.fallbackProgramIsValidAndDifferentlyEncoded_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.hooksBoundToTheRecognizers_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.realHooksReproduceP09cFixtureShapes_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.determinismUnderPermutation_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.rowSpellingMatters_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.modarith7Recognition_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.pow5Recognition_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.realHooks_endToEnd_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.dualBuildWithRealRecognizers_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.portBoundsNeverBind_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.fqRoundTrip_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.pairwiseGridIndexStaysInBounds_ok -- expect true
#eval Midfall.Generator.QuotientVmRecognizersKats.recognizersDoNotRecogniseEverything_ok -- expect true

end Midfall.Generator.QuotientVmRecognizersKats
