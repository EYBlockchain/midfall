-- |
-- Midfall.Generator.Quotient.Evaluator
--
-- THE BATCHED-IDENTITY NUMERATOR EMITTER. Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/yul_emit.rs
-- (1,176 lines, 32 items at git HEAD - two structs and thirty fns, not the fifteen the
-- brief states; cited below as YE, per the standing note that line
-- numbers come from 'git show HEAD:<path>' and never from wc -l on a dirty checkout).
-- Work package P-09h.
--
-- THE FILE IS NOT AN EMITTER, IT IS THE EVALUATOR. YE:49 is 'pub(crate) struct
-- Evaluator<'a>' and all 31 items are methods of it or free helpers of its emission.
-- P-10b (FoldCompute.lean:39-57) and P-11 (LoweringPlan.lean:43-66, :325, :629) both
-- named this struct as the reason quotient_identity_parts (QRS:804),
-- compact_quotient_computation_blocks (QRS:2000) and the three structured_*_loop_block
-- emitters (QRS:1471, :1688, :1941) could not be ported. This file is that unblock; the
-- package report names item by item what is now reachable and what is not.
--
-- HAZARD 1, AND THE SHAPE THE PORT HAD TO TAKE. The Rust struct carries interior
-- mutability: Cell<bool> pow5_used (YE:59), RefCell<usize> var_counter (YE:61) and
-- RefCell<HashMap<String,String>> var_cache (YE:63), and the methods that mutate them
-- take &self - reset_locals(&self) (YE:111), evaluate_expression(&self, ..) (YE:116),
-- compress_expressions_with_challenge_var(&self, ..) (YE:124),
-- lookup_shared_prefix_f_plus_beta(&self, ..) (YE:138). Lean has no mutable borrow, so
-- the whole struct IS the threaded state: Evaluator F carries the three immutable
-- borrows (cs, meta, data) and the three mutable cells as plain fields, and every &self
-- method becomes a member of E F, i.e. StateT (Evaluator F) (Except Fault). A port that
-- made these pure and dropped the cache would change the emitted text, because the cache
-- is what makes two structurally equal subexpressions share one let. varCacheReuse_ok and
-- varCacheNamedSlot_ok gate that; pow5UsedFlipsExactlyOnQPow5_ok gates the Cell.
--
-- A DOC-VS-CODE DIVERGENCE FOUND WHILE DOING THIS. YE:115 says evaluate_expression emits
-- "without changing caller state". It does change caller state: it calls self.evaluate,
-- which bumps var_counter and inserts into var_cache through the RefCells. What it does
-- NOT do is RESET them - unlike evaluate_and_reset (YE:879), which is the only reason the
-- four emitters still produce independent variable numbering. The port keeps the
-- behaviour and records the comment as wrong, because a reader who trusted it would
-- conclude the public entry point is pure and drop the threading here too.
--
-- HAZARD 2: var_cache ITERATION ORDER IS NOT OBSERVABLE. The map is written at YE:1134
-- (insert) and read at YE:1130 (contains_key) and YE:1131 ([&value]). Those three lines
-- are its whole API surface in this file: grep var_cache returns exactly YE:63 (the
-- field), :875 (the reset assignment to Default), :1130, :1131 and :1134. Nothing
-- iterates it, keys it, or reads its length. So an assoc list is R6-legal, and
-- hashMapGet/hashMapInsert (Encoding.lean:179, :187) are reused rather than a second
-- model being invented. varCacheReadSites_ok re-pins the site set against the source file
-- at #eval time (D-P19), so a future iteration in the Rust reddens a gate instead of
-- silently desyncing the port.
--
-- HAZARD 5: THE EXPRESSION VISITOR IS REUSED, NOT RE-DERIVED. evaluate_basic
-- (YE:1025-1108) is one instantiation of halo2's Expression::evaluate ten-closure
-- visitor, which Exec/Circuit.lean already ports as Expression.Callbacks +
-- Expression.evaluate (Circuit.lean:498-535) in the Rust's own variant order. This file
-- supplies the ten closures and calls that traversal; it does not write a second one.
-- CORRECTION TO THE BRIEF: the brief says Circuit's evaluator comes "including the
-- virtual-selector panic (R4)". It must not be used for that. Expression.verifierCallbacks
-- (Circuit.lean:1736-1762) is the VERIFIER's instantiation and its selector arm panics at
-- proofs/src/plonk/mod.rs:532. The codegen instantiation here has its OWN panic at
-- YE:1041 with a different message ("virtual selectors must be removed before codegen").
-- Two different panics at two different sites for the same variant;
-- virtualSelectorPanic_site_ok pins that this file's site is the codegen one.
--
-- R9 DEVIATION, RECORDED: THE FIELD DICTIONARY IS A PARAMETER. The Rust is concrete to
-- midnight_curves::Fq and reaches for Fq::ZERO, Fq::ONE, is_zero_vartime, Fq::DELTA
-- (YE:330, :379) and fe_to_u256::<Fq> as associated items of a trait. Lean has no trait
-- dictionary to reach through, so the eight operations this file actually uses are one
-- explicit record, FieldCtx F, per PLAN R9 ("traits become structures of functions").
-- delta is a field of it rather than an associated constant, which is what the rest of the
-- tree already does for the same constant (Native.lean:45 delta : Fr p; Permutation.lean:336
-- records that FieldConsts carries zeta but NOT delta) - and it is what the reference
-- itself insists on: lowering/tests.rs:3467-3474 computes
-- u256_string(fe_to_u256::<Fq>(&Fq::DELTA)) and then asserts that the codegen source does
-- NOT contain the literal. So nothing here hard-codes DELTA either;
-- deltaLiteral_computedNotHardcoded_ok gates that the emitted permutation literal is a
-- function of the parameter and of no literal in this file.
--
-- R2/R6 DEVIATIONS, each recorded at its site:
-- * Vec -> List throughout (the Generator row; plans README standing note 4).
-- * meta is a Lean reserved word, so the field and every parameter is meta_ - the same
--   forced rename Encoding.lean:610 records for Data::new.
-- * Evaluator::pow5_used() (YE:106) collides with the pow5_used FIELD projection, which
--   Lean generates automatically. The method is ported as pow5Flag; the collision is the
--   reason and this sentence is the record.
-- * The Evaluator's private evaluate (YE:885) is a top-level def named evaluate in this
--   namespace; Expression.evaluate (Circuit.lean:525) is a different fully-qualified name
--   and both are used in this file.
-- * `prefix` is ALSO a Lean keyword (the notation modifier), so `column_eval_var`'s
--   parameter is `prefixName` and the shared-prefix local is `sharedPrefix`. Third
--   reserved-word collision after `meta` and `instance`; plans/README.md standing note 3
--   lists only `meta`.
-- * HashMap<String,String> -> assoc list (hazard 2 above).
-- * Lean 4.35's `List.range'` is INCLUSIVE of its second argument, so Rust's `1..n` must
--   be `(List.range n).drop 1` and NOT `List.range' 1 n`. Three sites here. This is not
--   hypothetical: FoldTypes.lean:504 has the bug in inherited work - see the report.
-- * `List.zipIdx` yields `(element, index)` and not `(index, element)`, the opposite of
--   Rust's `.enumerate()`. Every `.enumerate()` port has to swap.
--
-- WHAT MOVED (Lean is order-sensitive; plans README standing note 3). Rust needs no order
-- inside an impl; this file needs:
-- 1. FieldCtx and Evaluator before everything, since E names the state type.
-- 2. nextVar (YE:1140), initVar (YE:1128) and reset (YE:873) before their first callers,
--    which in the Rust sit ABOVE them (YE:176 and :189 already call fresh_var).
-- 3. collectProductFactors (YE:1166) and collectSumTerms (YE:945) before pow5BaseExpr and
--    evaluateSumWithCoeffAndConst, which call them.
-- 4. instanceEvalAt (YE:1112) before evalAt (YE:843) and before evaluateBasicCore.
-- 5. expressionMemoryPtr (YE:782) before lookupSharedPrefixFPlusBeta (YE:138).
-- 6. compressExpressions (YE:753) before compressExpressionsWithTheta (YE:735) and before
--    lookupSharedPrefixFPlusBeta, both of which call it.
-- 7. evaluateBasicCore/evaluateBasic (YE:1025) before evaluateScaledTerm (YE:970) before
--    evaluateSumWithCoeffAndConst (YE:897) before evaluate (YE:885), and all of them
--    before the four public emitters.
-- None of these moves changes a line of emitted text; they are declaration order only.
--
-- R10: NO partial, NO termination_by. evaluate_basic's pow5 arm recurses into
-- evaluate_basic(base) in the Rust (YE:1027), which would be a non-structural call in
-- Lean because pow5_base_expr hands back an Option (Expression F) and Lean cannot see it
-- is a subterm. It is provably never a re-entry: collect_product_factors pushes only
-- NON-Product nodes (YE:1170-1174), so every factor it yields is a non-product, and
-- pow5_base_expr on a non-product collects exactly one factor and fails the
-- factors.len() != 5 test at YE:828. The Rust's recursion is therefore always exactly one
-- level deep. The port splits the function at that seam - evaluateBasicCore is the
-- visitor, evaluateBasic is the pow5 guard plus a call to the core - which is the same
-- program with the dead recursion removed, and says so at the site.
--
-- THE NEGATION D-P20 ASKED ABOUT IS NOT IN THIS FILE. The module doc (YE:13-16) says the
-- generated verifier "stores -nu_y(x) as the expected opening scalar", and the brief asks
-- whether this is where that negation lives. It is not. Grepping this file for the
-- negation finds only per-identity subtractions: left-minus-right at YE:405, 1 - z_0 at
-- :283, h*P - sum at :564, compressed - (1-q)*trash at :717. The batch-level negation is
-- one line of Yul in the template,
-- templates/partials/quotient_numerator/QuotientNumeratorBlock.yul:1439,
--   let linearization_expected_eval := addmod(0, sub(r, quotient_eval_numer), r)
-- which is P-13's row and is modelled by nothing in this tree. The only Lean model of it
-- is the test-module oracle FoldCompute ported (T:4288-4321, quotient_expected_eval =
-- -main_numerator). So D-P20 item 1's "the negation ... is Yul-side" SURVIVES this
-- package: P-09h does not close it, and the brief's hypothesis is wrong. See the report.
--
-- WHAT THIS FILE DOES NOT IMPORT (hazard 6). No direct/{mod,emit,layout,validate}.rs,
-- nothing from Generator.Vk, and nothing from Midfall/Instances/ (D-P17). The halo2
-- ConstraintSystem it walks is Midfall.Halo2.ConstraintSystem from Exec/Circuit.lean,
-- the ported L0 record, not a new one.

import Midfall.Common.Bytes
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Generator.Encoding
import Midfall.Generator.Filters
import Midfall.Generator.Layout
import Midfall.Generator.Models
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.FoldCompute

namespace Midfall.Generator.QuotientEvaluator

open Midfall Midfall.Halo2 Midfall.Generator

/-- The Rust file, so every R4 site string reads out fully. -/
def yePath : String :=
  "proofs/solidity-verifier/src/lowering/quotient_numerator/yul_emit.rs"

/-- R4 site helper: an expect or an out-of-range index carries the file and the line it
    aborts at. -/
def site (line : Nat) (msg : String) : String :=
  yePath ++ ":" ++ toString line ++ " (" ++ msg ++ ")"

/-! ## The state (rust: YE:49-78) -/

/-- The subset of ff::Field + ff::PrimeField that yul_emit.rs actually reaches for, as an
    explicit record of functions (rule R9). repr is PrimeField::to_repr and is composed
    with the ported feToU256 (Encoding.lean:1008) exactly as the Rust composes
    fe_to_u256::<Fq>; delta is PrimeField::DELTA, a parameter here for the reason the
    header gives. -/
structure FieldCtx (F : Type) where
  /-- rust: Fq::ZERO, read at YE:902. -/
  zero : F
  /-- rust: Fq::ONE, read at YE:903, :909, :975. -/
  one : F
  /-- rust: Field::add, YE:953 (*constant += coeff * value). -/
  add : F -> F -> F
  /-- rust: Field::mul, YE:953 and :963. -/
  mul : F -> F -> F
  /-- rust: Neg at YE:956 (-coeff). -/
  neg : F -> F
  /-- rust: PartialEq at YE:909 (*coeff != Fq::ONE) and :975 (coeff == Fq::ONE). -/
  eqF : F -> F -> Bool
  /-- rust: is_zero_vartime, YE:905 and :906. -/
  isZero : F -> Bool
  /-- rust: pow_vartime([(n : u64)]), YE:379. One limb, so a plain Nat exponent. -/
  powNat : F -> Nat -> F
  /-- rust: PrimeField::to_repr, the first half of every fe_to_u256::<Fq>(&x). -/
  repr : F -> List Nat
  /-- rust: PrimeField::DELTA, read at YE:330 and YE:379. -/
  delta : F

/-- rust: YE:49-66 (pub(crate) struct Evaluator<'a>), all seven fields in source order
    (rule R1). The three &'a borrows become values - Lean has no lifetimes and copying a
    ConstraintSystem is free in a pure language - and the three interior-mutable cells
    become plain fields of the SAME record, which is what makes &self mutation
    expressible: a method is Evaluator -> (result, Evaluator). field is not a Rust field;
    it is the R9 materialisation of the Fq dictionary the Rust reaches through the type. -/
structure Evaluator (F : Type) where
  /-- rust: YE:51 (cs: &'a ConstraintSystem<Fq>) -/
  cs : ConstraintSystem F
  /-- rust: YE:53 (meta: &'a ConstraintSystemMeta). R2: meta is a Lean reserved word. -/
  meta_ : ConstraintSystemMeta
  /-- rust: YE:55 (data: &'a Data) -/
  data : Data
  /-- rust: YE:57 (use_pow5_helper: bool) - immutable, set by with_pow5_helper. -/
  usePow5Helper : Bool
  /-- rust: YE:59 (pow5_used: Cell<bool>) -/
  pow5Used : Bool
  /-- rust: YE:61 (var_counter: RefCell<usize>) -/
  varCounter : Nat
  /-- rust: YE:63 (var_cache: RefCell<HashMap<String, String>>) - hazard 2: get and
      insert only, never iterated, so an assoc list observes everything. -/
  varCache : List (String × String)
  /-- Not a Rust field: the Fq dictionary (rule R9). -/
  field : FieldCtx F

/-- The method type. Every &self fn in YE:80-1145 becomes a member of this: it reads the
    immutable borrows, mutates the three cells, and may abort at an expect or an index
    (rule R4). -/
abbrev E (F : Type) (alpha : Type) := StateT (Evaluator F) (Except Fault) alpha

/-- One emitted identity: the Yul lines, then the variable holding the value. This is the
    Rust's (Vec<String>, String) pair, which YE:33-35 documents as the module's whole
    contract with lowering/quotient.rs. -/
abbrev Lines := List String
abbrev Var := String

/-- rust: YE:68-78 (pub(crate) struct GateComputation), field order preserved. The four
    index fields are usize -> Nat (R5) and Option<usize> -> Option Nat. -/
structure GateComputation (F : Type) where
  /-- rust: YE:70 (lines: Vec<String>) -/
  lines : List String
  /-- rust: YE:71 (var: String) -/
  var : String
  /-- rust: YE:72 (simple_selector_index: Option<usize>) -/
  simpleSelectorIndex : Option Nat
  /-- rust: YE:73 (gate_index: usize) -/
  gateIndex : Nat
  /-- rust: YE:74 (gate_name: String) -/
  gateName : String
  /-- rust: YE:75 (constraint_index: usize) -/
  constraintIndex : Nat
  /-- rust: YE:76 (constraint_name: String) -/
  constraintName : String
  /-- rust: YE:77 (polynomial_index: usize) -/
  polynomialIndex : Nat
  deriving BEq

/-- Lean scaffolding, not a Rust item: the two line shapes every emitter pushes. -/
def letLine (v rhs : String) : String := "let " ++ v ++ " := " ++ rhs
def assignLine (v rhs : String) : String := v ++ " := " ++ rhs

/-- Lean scaffolding, not a Rust item: xs[i] = v, the slice assignment the Rust does
    directly at YE:532 and :540. -/
def setIdx {alpha : Type} (xs : List alpha) (i : Nat) (v : alpha) : List alpha :=
  xs.take i ++ [v] ++ xs.drop (i + 1)

/-! ## Free helpers (rust: YE:1148-1176) - MOVED ahead of their callers -/

/-- rust: YE:1148-1154 (u256_string). "Render a U256 as the shortest stable hexadecimal
    Yul literal." The bit_len() < 64 arm and the general arm render the SAME text, so the
    branch is documentation dressed as a case split - the same guard-that-cannot-bind
    FoldCompute.lean:153-159 records for the byte-identical copy at QVM:4122-4128.
    FINDING: yul_emit.rs and vm/mod.rs each carry their own u256_string; this is the
    yul_emit one, ported because R1 wants one Lean def per Rust fn, and
    u256String_matchesFoldComputeCopy_ok gates that the two copies cannot drift. -/
def u256String (value : Word256) : String :=
  if value.toNat < 2^64 then "0x" ++ hexDigits value.toNat
  else "0x" ++ hexDigits value.toNat

/-- rust: YE:1157-1163 (column_eval_var). "Stable variable name for a column evaluation
    and rotation." rotation.cmp(&0) is a three-way split and the negative arm prints
    rotation.abs(), so f_0_prev_1 and not f_0_prev_-1. The i32 -> Int widening is
    lossless (R5). R2 FORCED RENAME, RECORDED: the Rust parameter is `prefix`, and
    `prefix` is a Lean keyword (the notation modifier), so it is `prefixName` here - the
    same class of collision Encoding.lean:610 records for `meta`. -/
def columnEvalVar (prefixName : String) (columnIndex : Nat) (rotation : Int) : String :=
  if rotation < 0 then
    prefixName ++ "_" ++ toString columnIndex ++ "_prev_" ++ toString (Int.natAbs rotation)
  else if rotation == 0 then prefixName ++ "_" ++ toString columnIndex
  else prefixName ++ "_" ++ toString columnIndex ++ "_next_" ++ toString (Int.natAbs rotation)

/-- rust: YE:1166-1176 (collect_product_factors). "Flatten a product tree into leaf
    expressions." Left subtree first, then right, so the factor order is the in-order walk
    of the tree - which is what makes ((a*a)*a)*(a*a) and (a*(a*(a*(a*a)))) both five a's.
    Every element it returns is a NON-Product: that is the fact R10 leans on. -/
def collectProductFactors {F : Type} (expression : Expression F) : List (Expression F) :=
  match expression with
  | .product lhs rhs => collectProductFactors lhs ++ collectProductFactors rhs
  | _ => [expression]

/-- Word::to_string(), i.e. the Display impl at ENC:764-775 that every .to_string() call
    in this file routes through. Reuses wordKey (Encoding.lean:318), which is already that
    Display and is documented there as "the EMITTED YUL text, not a structural key".
    yul_emit.rs is the reach site Encoding.lean:44 does not name. -/
def wordString (w : Word) : String := wordKey w

/-- u256_string(fe_to_u256::<Fq>(&x)), the pair every field literal in this file emits.
    feToU256 can only fault on a repr that is not 32 bytes (ENC:914), which no
    PrimeField::to_repr produces; the fault is kept rather than assumed away (R4). -/
def feToU256String {F : Type} (x : F) : E F String := do
  let ctx <- (fun s => s.field) <$> get
  pure (u256String (<- StateT.lift (feToU256 (ctx.repr x))))

/-- expect on an Option, as the Rust writes it at YE:317, :365, :687, :850, :859, :1054,
    :1066 and :1117. -/
def expectOpt {F : Type} {alpha : Type} (o : Option alpha) (line : Nat) (msg : String) :
    E F alpha :=
  match o with
  | some v => pure v
  | none => throw (Fault.panic (site line msg))

/-- Vec/slice indexing, which panics out of range in BOTH profiles (R4). Reuses listGetMut
    (Encoding.lean:193), whose comment already records that the panic belongs to the
    expect/index line and not to a get. -/
def atIndex {F : Type} {alpha : Type} (xs : List alpha) (i : Nat) (line : Nat) (msg : String) :
    E F alpha :=
  StateT.lift (listGetMut xs i (site line msg))

/-! ## Variable allocation (rust: YE:868-882, :1128-1144) - MOVED ahead of every caller -/

/-- rust: YE:1140-1144 (next_var). "Return the next varN local name." The Rust reads the
    counter THEN bumps it, so the first name is var0. R5: usize bump; reaching 2^64 locals
    inside one identity is not a program the generator can build, so no wrapping is
    emulated. -/
def nextVar {F : Type} : E F String := do
  let e <- get
  modify fun s => { s with varCounter := s.varCounter + 1 }
  pure ("var" ++ toString e.varCounter)

/-- rust: YE:868-870 (fresh_var). A one-line alias of next_var; kept as its own def because
    R1 wants one Lean def per Rust fn and because the two names mark which call sites are
    "allocate a scratch variable" in the Rust source. -/
def freshVar {F : Type} : E F String := nextVar

/-- rust: YE:873-876 (reset). *var_counter.borrow_mut() = Default::default() and the same
    for the cache: usize's Default is 0 and HashMap's is empty, so both cells go back to
    their new values and nothing else changes - notably NOT use_pow5_helper and NOT
    pow5_used, which no reset touches. -/
def reset {F : Type} : E F Unit :=
  modify fun s => { s with varCounter := 0, varCache := [] }

/-- rust: YE:1128-1137 (init_var). "Bind a Yul expression to a local variable, reusing
    cached variables." THE CACHE IS THE HAZARD. The key is the rendered VALUE text, not
    the requested name: a hit emits NO line and returns the earlier variable even when the
    caller asked for a different name. So Some("f_0") on a second identical fixed query is
    discarded and f_0 comes back from the cache - invisible the first time, observable the
    second. A miss takes the caller's name if it supplied one and otherwise allocates varN,
    and the allocation happens BEFORE the insert, matching unwrap_or_else. The Rust does
    two lookups (contains_key then [&value]) where the port does one; nothing mutates the
    map between them, so the two are the same program. -/
def initVar {F : Type} (value : String) (name : Option String) : E F (Lines × Var) := do
  let e <- get
  match hashMapGet e.varCache value with
  | some cached => pure ([], cached)
  | none => do
      let v <- match name with
        | some nm => pure nm
        | none => nextVar
      modify fun s => { s with varCache := hashMapInsert value v s.varCache }
      pure ([letLine v value], v)

/-- Lean scaffolding, not a Rust item: the Rust's 'let v = self.fresh_var();
    lines.push(format!("let {v} := {rhs}"))' idiom, which appears ~60 times in the four
    emitters. It is deliberately NOT init_var: it does not consult or update the cache, so
    two calls with the same right-hand side emit two identical lines. freshLetBypassesCache_ok
    gates that difference, because it is the whole of hazard 1. -/
def freshLet {F : Type} (rhs : String) : E F (Lines × Var) := do
  let v <- freshVar
  pure ([letLine v rhs], v)

/-! ## Expression emission (rust: YE:885-1108) - MOVED ahead of the emitters -/

/-- rust: YE:821-838 (pow5_base_expr). "Recognize a * a * a * a * a when the Yul pow5
    helper is enabled." Three rejections in the Rust's order: the peephole is off, the
    flattened factor count is not five, and the factors after the first are not all equal
    to it. *factor == base is Expression's derived PartialEq, i.e. structural equality
    including the field payloads, so a * a * a * a * a matches and a * a * a * a * b does
    not. -/
def pow5BaseExpr {F : Type} [BEq F] (expression : Expression F) :
    E F (Option (Expression F)) := do
  let e <- get
  if ! e.usePow5Helper then pure none
  else do
    let factors := collectProductFactors expression
    if factors.length != 5 then pure none
    else
      match factors.head? with
      | none => pure none
      | some base =>
          if (factors.drop 1).all (fun factor => factor == base) then pure (some base)
          else pure none

/-- rust: YE:945-967 (collect_sum_terms). "Recursively collect additive terms with their
    accumulated coefficient." The two &mut accumulators become an explicit pair, which is
    the only Lean rendering; the arm order and the _ => terms.push fall-through are the
    Rust's. Note what is NOT a term: a Constant, and anything under Negated/Sum/Scaled that
    bottoms out at a Constant. Everything else - every query, and every Product - is a leaf
    of the additive walk, which is why a * a * a * a * a stays one term. -/
def collectSumTerms {F : Type} (field : FieldCtx F) (expression : Expression F)
    (coeff : F) : (F × List (F × Expression F)) -> (F × List (F × Expression F))
  | (constant, terms) =>
      match expression with
      | .constant value => (field.add constant (field.mul coeff value), terms)
      | .negated inner => collectSumTerms field inner (field.neg coeff) (constant, terms)
      | .sum lhs rhs =>
          collectSumTerms field rhs coeff
            (collectSumTerms field lhs coeff (constant, terms))
      | .scaled inner scale =>
          collectSumTerms field inner (field.mul coeff scale) (constant, terms)
      | _ => (constant, terms ++ [(coeff, expression)])

/-- rust: YE:1112-1125 (instance_eval_at). "Resolve an instance query either from proof
    evals or local interpolation." The split is on num_committed_instances, and the public
    branch ignores the column index and the rotation entirely: there is exactly one
    non-committed instance column and its Lagrange-combined value already sits at
    INSTANCE_EVAL_MPTR (YE:1120-1122). -/
def instanceEvalAt {F : Type} (columnIndex : Nat) (rotation : Int) : E F String := do
  let e <- get
  if columnIndex < e.meta_.numCommittedInstances then
    let w <- expectOpt (hashMapGet e.data.committedInstanceEvals (columnIndex, rotation))
      1117 "committed instance eval present"
    pure (wordString w)
  else pure (wordString e.data.instanceEval)

/-- rust: YE:1025-1108 (evaluate_basic), the visitor half. "Emit an expression through the
    native Expression::evaluate visitor." The ten closures are the Rust's ten closures in
    the Rust's argument order, handed to the ported Expression.evaluate (Circuit.lean:525)
    rather than re-derived (hazard 5). The Selector arm is the CODEGEN panic at YE:1041,
    not the verifier's at plonk/mod.rs:532. The Fixed arm is the one to read twice: a
    simple-selector column emits the literal 0x1 and is never looked up (YE:1045-1048). -/
def evaluateBasicCore {F : Type} [BEq F] (expression : Expression F) : E F (Lines × Var) :=
  expression.evaluate
    { constant := fun scalar => do initVar (<- feToU256String scalar) none
      selectorColumn := fun _ =>
        throw (Fault.panic (site 1041 "virtual selectors must be removed before codegen"))
      fixedColumn := fun query => do
        let e <- get
        let columnIndex := query.columnIndex
        let rotation := query.rotation.int
        if e.meta_.simpleSelectorCols.contains columnIndex then
          initVar "0x1" none
        else
          let eval <- expectOpt (hashMapGet e.data.fixedEvals (columnIndex, rotation))
            1054 "fixed eval present"
          initVar (wordString eval) (some (columnEvalVar "f" columnIndex rotation))
      adviceColumn := fun query => do
        let e <- get
        let columnIndex := query.columnIndex
        let rotation := query.rotation.int
        let eval <- expectOpt (hashMapGet e.data.adviceEvals (columnIndex, rotation))
          1066 "advice eval present"
        initVar (wordString eval) (some (columnEvalVar "a" columnIndex rotation))
      instanceColumn := fun query => do
        let eval <- instanceEvalAt query.columnIndex query.rotation.int
        initVar eval (some (columnEvalVar "i" query.columnIndex query.rotation.int))
      challenge := fun ch => do
        let e <- get
        let w <- atIndex e.data.challenges ch.index 1078 "challenges index"
        initVar (wordString w) (some ("c_" ++ toString ch.index))
      negated := fun inner => do
        let (lines, var) <- inner
        let (addLines, addVar) <- initVar ("addmod(0, sub(r, " ++ var ++ "), r)") none
        pure (lines ++ addLines, addVar)
      sum := fun lhs rhs => do
        let (lhsLines, lhsVar) <- lhs
        let (rhsLines, rhsVar) <- rhs
        let (lines, var) <- initVar ("addmod(" ++ lhsVar ++ ", " ++ rhsVar ++ ", r)") none
        pure (lhsLines ++ rhsLines ++ lines, var)
      product := fun lhs rhs => do
        let (lhsLines, lhsVar) <- lhs
        let (rhsLines, rhsVar) <- rhs
        let (lines, var) <- initVar ("mulmod(" ++ lhsVar ++ ", " ++ rhsVar ++ ", r)") none
        pure (lhsLines ++ rhsLines ++ lines, var)
      scaled := fun inner scalar => do
        let (lines, var) <- inner
        let (scalarLines, scalarVar) <- initVar (<- feToU256String scalar) none
        let (mulLines, mulVar) <-
          initVar ("mulmod(" ++ var ++ ", " ++ scalarVar ++ ", r)") none
        pure (lines ++ scalarLines ++ mulLines, mulVar) }

/-- rust: YE:1026-1032 (evaluate_basic), the pow5 guard. See the header's R10 note: the
    Rust recurses here but the recursion can never fire a second time, so the port calls
    the core directly and the two are the same program. pow5_used.set(true) sits AFTER the
    base has been emitted (YE:1028), which is what makes the flag's flip order observable in
    the line list. -/
def evaluateBasic {F : Type} [BEq F] (expression : Expression F) : E F (Lines × Var) := do
  match <- pow5BaseExpr expression with
  | some base => do
      let (lines, baseVar) <- evaluateBasicCore base
      modify fun s => { s with pow5Used := true }
      let (powLines, powVar) <- initVar ("q_pow5(" ++ baseVar ++ ")") none
      pure (lines ++ powLines, powVar)
  | none => evaluateBasicCore expression

/-- rust: YE:970-1022 (evaluate_scaled_term). "Emit one term multiplied by a known Fr
    coefficient." Three arms in the Rust's order: the pow5 peephole (with its own
    coefficient scaling), a top-level Product (fused into one mulmod, or
    mulmod(mulmod(..), coeff, r) when the coefficient is not one), and the general
    fallback. Every arm returns the term UNSCALED when coeff_is_one, which is why a
    coefficient of exactly ONE changes the emitted text and not just the value. -/
def evaluateScaledTerm {F : Type} [BEq F] (expression : Expression F) (coeff : F) :
    E F (Lines × Var) := do
  let e <- get
  let coeffIsOne := e.field.eqF coeff e.field.one
  match <- pow5BaseExpr expression with
  | some base => do
      let (lines, baseVar) <- evaluateBasicCore base
      modify fun s => { s with pow5Used := true }
      let (powLines, powVar) <- initVar ("q_pow5(" ++ baseVar ++ ")") none
      let lines := lines ++ powLines
      if coeffIsOne then pure (lines, powVar)
      else
        let (coeffLines, coeffVar) <- initVar (<- feToU256String coeff) none
        let (scaleLines, outVar) <-
          initVar ("mulmod(" ++ powVar ++ ", " ++ coeffVar ++ ", r)") none
        pure (lines ++ coeffLines ++ scaleLines, outVar)
  | none =>
      match expression with
      | .product lhs rhs => do
          let (lhsLines, lhsVar) <- evaluateBasic lhs
          let (rhsLines, rhsVar) <- evaluateBasic rhs
          let lines := lhsLines ++ rhsLines
          if coeffIsOne then
            let (outLines, outVar) <-
              initVar ("mulmod(" ++ lhsVar ++ ", " ++ rhsVar ++ ", r)") none
            pure (lines ++ outLines, outVar)
          else
            let (coeffLines, coeffVar) <- initVar (<- feToU256String coeff) none
            let (outLines, outVar) <- initVar
              ("mulmod(mulmod(" ++ lhsVar ++ ", " ++ rhsVar ++ ", r), " ++ coeffVar ++ ", r)") none
            pure (lines ++ coeffLines ++ outLines, outVar)
      | _ => do
          let (lines, var) <- evaluateBasic expression
          if coeffIsOne then pure (lines, var)
          else
            let (coeffLines, coeffVar) <- initVar (<- feToU256String coeff) none
            let (scaleLines, outVar) <-
              initVar ("mulmod(" ++ var ++ ", " ++ coeffVar ++ ", r)") none
            pure (lines ++ coeffLines ++ scaleLines, outVar)

/-- rust: YE:897-942 (evaluate_sum_with_coeff_and_const). "Try to flatten a sum into
    constants and scaled terms before emission." The predicate at YE:907-909 is the whole
    function's reason to exist and it is asymmetric in a way that is easy to lose: a single
    term with coefficient exactly ONE is NOT fused (so it falls through to the visitor),
    but a single term with any other coefficient IS, and any sum with a non-zero constant
    part is. terms.retain drops zero-coefficient terms AFTER the walk, so a - a fuses to
    the constant zero and emits let var0 := 0x0. -/
def evaluateSumWithCoeffAndConst {F : Type} [BEq F] (expression : Expression F) :
    E F (Option (Lines × Var)) := do
  let e <- get
  let field := e.field
  let (constant0, terms0) := collectSumTerms field expression field.one (field.zero, [])
  let terms := terms0.filter fun (coeff, _) => ! field.isZero coeff
  let hasConstant := ! field.isZero constant0
  let firstCoeffNotOne := match terms.head? with
    | some (coeff, _) => ! field.eqF coeff field.one
    | none => false
  let shouldFuse := hasConstant || terms.length > 1 || firstCoeffNotOne
  if ! shouldFuse then pure none
  else do
    let (lines0, acc0) <-
      if hasConstant then do
        let (cl, cv) <- initVar (<- feToU256String constant0) none
        pure (cl, some cv)
      else pure ([], none)
    let (lines, acc) <- terms.foldlM
        fun (acc : Lines × Option Var) (pair : F × Expression F) => do
          let (termLines, termVar) <- evaluateScaledTerm pair.2 pair.1
          match acc with
          | (ls, some accVar) =>
              let (addLines, addVar) <-
                initVar ("addmod(" ++ accVar ++ ", " ++ termVar ++ ", r)") none
              pure (ls ++ termLines ++ addLines, some addVar)
          | (ls, none) => pure (ls ++ termLines, some termVar)
        (lines0, acc0)
    match acc with
    | some var => pure (some (lines, var))
    | none => do let r <- initVar "0x0" none; pure (some r)

/-- rust: YE:885-891 (evaluate). "Emit an expression, first trying additive-term fusion."
    Two lines: try the fusion, else the visitor. -/
def evaluate {F : Type} [BEq F] (expression : Expression F) : E F (Lines × Var) := do
  match <- evaluateSumWithCoeffAndConst expression with
  | some result => pure result
  | none => evaluateBasic expression

/-- rust: YE:879-882 (evaluate_and_reset). Reset, then evaluate: this is what gives each
    GATE polynomial its own var0-rooted numbering. -/
def evaluateAndReset {F : Type} [BEq F] (expression : Expression F) : E F (Lines × Var) := do
  reset
  evaluate expression

/-! ## Column resolution (rust: YE:782-818, :843-865, :1112-1125) -/

/-- rust: YE:843-865 (eval_at). "Resolve a Column<Any> evaluation at a rotation. Used by
    the permutation emitter (which works in Column<Any> form rather than Expression<F>)."
    The three arms are Any's three variants. The Fixed arm is the one to read twice: a
    simple selector column renders as the LITERAL "0x1" and is not looked up at all, the
    same rule evaluate_basic's fixedColumn closure applies at YE:1045. -/
def evalAt {F : Type} (column : Column) (rotation : Int) : E F String := do
  let e <- get
  let colIdx := column.index
  match column.columnType with
  | .advice _ =>
      let w <- expectOpt (hashMapGet e.data.adviceEvals (colIdx, rotation))
        850 "advice eval present in permutation chunk"
      pure (wordString w)
  | .fixed =>
      if e.meta_.simpleSelectorCols.contains colIdx then pure "0x1"
      else
        let w <- expectOpt (hashMapGet e.data.fixedEvals (colIdx, rotation))
          859 "fixed eval present in permutation chunk"
        pure (wordString w)
  | .instance => instanceEvalAt colIdx rotation

/-- rust: YE:782-818 (expression_memory_ptr). "Return the concrete memory pointer for a
    simple query expression." Three rejections after the match: a non-query variant, a
    simple-selector fixed column (YE:791-793, which returns None rather than falling
    through to the eval map), and a pointer that is not in memory or not a non-negative
    integer offset. The 0x20 adjacency test in lookup_shared_prefix_f_plus_beta is built on
    this, so the returned number is a BYTE offset - Value::Integer is in bytes
    (Encoding.lean:240-252 records that the WORD_BYTES multiplication happens in Value.add). -/
def expressionMemoryPtr {F : Type} (expression : Expression F) : E F (Option Nat) := do
  let e <- get
  let word? <- match expression with
    | .advice query =>
        pure (hashMapGet e.data.adviceEvals (query.columnIndex, query.rotation.int))
    | .fixed query =>
        if e.meta_.simpleSelectorCols.contains query.columnIndex then pure none
        else pure (hashMapGet e.data.fixedEvals (query.columnIndex, query.rotation.int))
    | .instance query =>
        if query.columnIndex < e.meta_.numCommittedInstances then
          pure (hashMapGet e.data.committedInstanceEvals (query.columnIndex, query.rotation.int))
        else pure (some e.data.instanceEval)
    | _ => pure none
  match word? with
  | none => pure none
  | some word =>
      -- Location carries no BEq (the queued F5 in plans/README.md), so the Rust
      -- `word.loc() != Location::Memory` becomes a match on the location here.
      match word.loc with
      | .calldata => pure none
      | .memory => match word.ptr.value with
        | .integer offset => if offset >= 0 then pure (some offset.toNat) else pure none
        | _ => pure none

/-! ## Compression (rust: YE:124-196, :735-776) -/

/-- rust: YE:753-776 (compress_expressions). "Fold expressions as
    acc = acc * challenge + expr." The fold starts from the literal 0 and NOT from a
    variable, which is why the first line is addmod(mulmod(0, <tau>, r), <e0>, r) and not a
    copy. An empty list emits let var0 := 0 and returns it (YE:770-774) - note that is a
    fresh_var plus a raw push, not init_var, so it is NOT cached. -/
def compressExpressions {F : Type} [BEq F] (expressions : List (Expression F))
    (challengeVar : String) : E F (Lines × Var) := do
  let (lines, acc) <- expressions.foldlM
      fun (acc : Lines × Option Var) (expr : Expression F) => do
        let (eLines, eVar) <- evaluate expr
        let next <- freshVar
        let prev := match acc.2 with | some v => v | none => "0"
        pure (acc.1 ++ eLines ++
          [letLine next ("addmod(mulmod(" ++ prev ++ ", " ++ challengeVar ++ ", r), "
            ++ eVar ++ ", r)")], some next)
      ([], none)
  match acc with
  | some var => pure (lines, var)
  | none => do
      let zero <- freshVar
      pure ([letLine zero "0"], zero)

/-- rust: YE:735-750 (compress_expressions_with_theta). "theta-compress a slice of
    expressions ... Uses a fresh theta mload at the start; relies on the caller's reset
    cycle to deduplicate within a constraint." The empty case is NOT the same as
    compressExpressions []: it returns init_var("0x0", None), i.e. let var0 := 0x0, and
    emits no mload(THETA_MPTR) at all. Two spellings of zero one line apart, and a port
    that collapses them changes the text. -/
def compressExpressionsWithTheta {F : Type} [BEq F] (expressions : List (Expression F)) :
    E F (Lines × Var) := do
  if expressions.isEmpty then initVar "0x0" none
  else do
    let theta <- freshVar
    let (lines, finalVar) <- compressExpressions expressions theta
    pure ([letLine theta "mload(THETA_MPTR)"] ++ lines, finalVar)

/-- rust: YE:124-134 (compress_expressions_with_challenge_var). Public wrapper: "used by
    structured lookup/trash paths that hoist theta or the trash challenge once and then
    reuse the variable across loop bodies." -/
def compressExpressionsWithChallengeVar {F : Type} [BEq F]
    (expressions : List (Expression F)) (challengeVar : String) : E F (Lines × Var) :=
  compressExpressions expressions challengeVar

/-- rust: YE:138-196 (lookup_shared_prefix_f_plus_beta). "Emit a shared-prefix
    optimization for parallel lookup inputs." Five rejections before any line is emitted,
    in the Rust's order: fewer than three parallel inputs, an empty first input, a prefix
    of length zero, any input whose length or prefix differs from the first's, and a tail
    pointer that is not base + idx * 0x20. The {base_ptr:#x} rendering is minimal lowercase
    hex with a 0x prefix, i.e. NOT hexFilter's even-nibble padding (FoldTypes.lean:104
    records the same distinction for {:#x} in folds.rs). R5: base_ptr + idx * 0x20 is
    usize arithmetic on byte offsets; no wrapping is emulated because no layout the
    generator builds reaches 2^64. -/
def lookupSharedPrefixFPlusBeta {F : Type} [BEq F] (inputChunk : List (List (Expression F)))
    (challengeVar : String) (betaVar : String) (fPlusBetaMptr : String) :
    E F (Option (List String)) := do
  if inputChunk.length < 3 then pure none
  else match inputChunk.head? with
    | none => pure none
    | some first =>
        if first.isEmpty then pure none
        else
          -- YE:164 checked_sub(1): an empty input has no prefix, and a one-element input
          -- has an EMPTY prefix, which the next arm rejects.
          let prefixLen := first.length - 1
          if prefixLen == 0 then pure none
          else
            -- R2 FORCED RENAME: `prefix` is a Lean keyword; the Rust is `prefix_len` /
            -- `exprs[..prefix_len]`.
            let sharedPrefix := first.take prefixLen
            let mismatch := inputChunk.any fun exprs =>
              exprs.length != first.length || exprs.take prefixLen != sharedPrefix
            if mismatch then pure none
            else do
              let basePtr? <- match first.getLast? with
                | none => pure none
                | some last => expressionMemoryPtr last
              match basePtr? with
              | none => pure none
              | some basePtr => do
                  let ptrOf (exprs : List (Expression F)) : E F (Option Nat) :=
                    match exprs.getLast? with
                    | none => pure none
                    | some q => expressionMemoryPtr q
                  let adjacent <- inputChunk.zipIdx.mapM fun (exprs, idx) => do
                    let p <- ptrOf exprs
                    pure (match p with
                      | some v => v == basePtr + idx * 0x20
                      | none => false)
                  if ! (adjacent.all id) then pure none
                  else do
                    let (prefixLines, prefixVar) <- compressExpressions sharedPrefix challengeVar
                    let (scaledLines, prefixScaled) <-
                      freshLet ("mulmod(" ++ prefixVar ++ ", " ++ challengeVar ++ ", r)")
                    let header := "for { let q_lookup_shared_i := 0 } lt(q_lookup_shared_i, "
                      ++ toString inputChunk.length
                      ++ ") { q_lookup_shared_i := add(q_lookup_shared_i, 1) }} {"
                    let body : List String :=
                      [ "let q_lookup_shared_off := shl(5, q_lookup_shared_i)",
                        "let q_lookup_shared_tail := mload(add(0x" ++ hexDigits basePtr
                          ++ ", q_lookup_shared_off))",
                        "let q_lookup_shared_compressed := addmod(" ++ prefixScaled
                          ++ ", q_lookup_shared_tail, r)",
                        "mstore(add(" ++ fPlusBetaMptr ++ ", q_lookup_shared_off), addmod("
                          ++ "q_lookup_shared_compressed, " ++ betaVar ++ ", r))",
                        "}" ]
                    pure (some (prefixLines ++ scaledLines ++ [header] ++ body))

/-! ## Public entry points (rust: YE:83-118) -/

/-- rust: YE:83-97 (Evaluator::new). use_pow5_helper: false, Cell::new(false), and both
    RefCells Default::default(): counter 0, cache empty. The field argument is the R9
    dictionary and is not a Rust parameter. -/
def Evaluator.new {F : Type} (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (data : Data) : Evaluator F :=
  { cs := cs, meta_ := meta_, data := data, usePow5Helper := false,
    pow5Used := false, varCounter := 0, varCache := [], field := field }

/-- rust: YE:100-104 (with_pow5_helper). Takes mut self by value and returns Self, so this
    is a plain field update and not a stateful method. -/
def Evaluator.withPow5Helper {F : Type} (self : Evaluator F) (enabled : Bool) : Evaluator F :=
  { self with usePow5Helper := enabled }

/-- rust: YE:106-108 (pow5_used). "Whether any emitted line so far calls the q_pow5
    helper." R2 COLLISION, RECORDED: the structure already generates the projection
    Evaluator.pow5Used, so the method is ported under a distinct name. -/
def pow5Flag {F : Type} (self : Evaluator F) : Bool := self.pow5Used

/-- rust: YE:111-113 (reset_locals). Public alias of reset. -/
def resetLocals {F : Type} : E F Unit := reset

/-- rust: YE:116-118 (evaluate_expression). See the header: the Rust doc's "without
    changing caller state" is false about the two RefCells and true only of the reset. -/
def evaluateExpression {F : Type} [BEq F] (expression : Expression F) : E F (Lines × Var) :=
  evaluate expression

/-! ## The four emitters (rust: YE:211-723) -/

/-- rust: YE:211-238 (gate_computations_tagged). "Emit each gate polynomial and tag it with
    its simple-selector fixed-column index (if any)." flat_map over gates then over each
    gate's polynomials, with evaluate_and_reset per polynomial - so the gate's
    simple-selector index is computed ONCE per gate (YE:217-218, find, i.e. the first simple
    selector in queried_selectors order) and copied onto every one of its identities.
    gate.constraint_name(i) is the circuit.rs:1637 index panic. -/
def gateComputationsTagged {F : Type} [BEq F] : E F (List (GateComputation F)) := do
  let e <- get
  let perGate <- e.cs.gates.toList.zipIdx.mapM fun (gate, gateIndex) => do
    let simpleSel := gate.queriedSelectors.toList.find? fun s => s.isSimple
    let simpleIdx := simpleSel.map fun s => s.index
    let polys := (Gate.polynomials gate).toList
    polys.zipIdx.mapM fun (poly, polynomialIndex) => do
      let (lines, var) <- evaluateAndReset poly
      let constraintName <- Gate.constraintName gate polynomialIndex
      let g : GateComputation F :=
        { lines := lines, var := var, simpleSelectorIndex := simpleIdx,
          gateIndex := gateIndex, gateName := gate.name, constraintIndex := polynomialIndex,
          constraintName := constraintName, polynomialIndex := polynomialIndex }
      pure g
  pure (perGate.flatten)

/-- rust: YE:264-412 (permutation_computations). The four families the block comment at
    YE:240-256 enumerates: first-set boundary, last-set boundary, set-to-set continuity for
    1..num_permutation_zs, and the per-set product equality. Two things to keep: the delta
    ladder literal is fe_to_u256(Fq::DELTA) (YE:330) and the INITIAL power is
    DELTA^(set_idx * chunk_len) (YE:379), both rendered as minimal hex; and the ladder is
    NOT multiplied after the last column of a chunk (YE:396, col_pos != last_col_idx with
    saturating_sub), so a one-column chunk emits no delta_pow reassignment line at all. -/
def permutationComputations {F : Type} [BEq F] : E F (List (Lines × Var)) := do
  let e <- get
  if e.meta_.numPermutationZs == 0 then pure []
  else do
    let chunkLen := e.meta_.permutationChunkLen
    let columns := e.meta_.permutationColumns
    let zEvals := e.data.permutationZEvals
    -- 1. First-set boundary: l_0 * (1 - z_0_cur)
    let fam1 <- do
      reset
      let (z0, _, _) <- expectOpt zEvals.head? 279 "perm sets non-empty"
      let z0s := wordString z0
      let (l1, l0) <- freshLet "mload(L_0_MPTR)"
      let (l2, omz) <- freshLet ("addmod(1, sub(r, " ++ z0s ++ "), r)")
      let (l3, bnd) <- freshLet ("mulmod(" ++ l0 ++ ", " ++ omz ++ ", r)")
      pure (l1 ++ l2 ++ l3, bnd)
    -- 2. Last-set boundary: l_last * (z_n^2 - z_n)
    let fam2 <- do
      reset
      let (zn, _, _) <- expectOpt zEvals.getLast? 295 "perm sets non-empty"
      let zns := wordString zn
      let (l1, llast) <- freshLet "mload(L_LAST_MPTR)"
      let (l2, sq) <- freshLet ("mulmod(" ++ zns ++ ", " ++ zns ++ ", r)")
      let (l3, sqm) <- freshLet ("addmod(" ++ sq ++ ", sub(r, " ++ zns ++ "), r)")
      let (l4, bnd) <- freshLet ("mulmod(" ++ llast ++ ", " ++ sqm ++ ", r)")
      pure (l1 ++ l2 ++ l3 ++ l4, bnd)
    -- 3. Set-to-set continuity: l_0 * (z_i_cur - z_{i-1}_last)
    let fam3 <- ((List.range e.meta_.numPermutationZs).drop 1).mapM fun i => do
      reset
      let (zi, _, _) <- atIndex zEvals i 315 "z_evals index"
      let zi := wordString zi
      let (_, _, prevLast) <- atIndex zEvals (i - 1) 317 "z_evals index"
      let zPrevLast <- match prevLast with
        | some w => pure (wordString w)
        | none => throw (Fault.panic (site 317 "non-last set has last eval"))
      let (l1, l0) <- freshLet "mload(L_0_MPTR)"
      let (l2, diff) <- freshLet ("addmod(" ++ zi ++ ", sub(r, " ++ zPrevLast ++ "), r)")
      let (l3, cont) <- freshLet ("mulmod(" ++ l0 ++ ", " ++ diff ++ ", r)")
      pure (l1 ++ l2 ++ l3, cont)
    -- 4. Per-set product equality.
    let delta <- StateT.lift (feToU256 (e.field.repr e.field.delta))
    let chunkss <- StateT.lift (rustChunks chunkLen (site 332 "permutation chunk length")
      columns.toArray)
    let fam4 <- (List.zip zEvals chunkss.toList).zipIdx.mapM fun (pair, setIdx) => do
      let ((zCur, zNext, _), chunkColsA) := pair
      let chunkCols := chunkColsA.toList
      reset
      let (a1, lLast) <- freshLet "mload(L_LAST_MPTR)"
      let (a2, lBlind) <- freshLet "mload(L_BLIND_MPTR)"
      let (a3, lSum) <- freshLet ("addmod(" ++ lLast ++ ", " ++ lBlind ++ ", r)")
      let (a4, active) <- freshLet ("addmod(1, sub(r, " ++ lSum ++ "), r)")
      let (a5, beta) <- freshLet "mload(BETA_MPTR)"
      let (a6, gamma) <- freshLet "mload(GAMMA_MPTR)"
      let (a7, left) <- freshLet (wordString zNext)
      let leftBlock <- chunkCols.mapM fun col => do
        let colEval <- evalAt col 0
        let sEval <- expectOpt (hashMapGet e.data.permutationEvals col) 365
          "permutation eval present"
        let (b1, betaS) <- freshLet ("mulmod(" ++ beta ++ ", " ++ wordString sEval ++ ", r)")
        let (b2, term) <- freshLet
          ("addmod(addmod(" ++ colEval ++ ", " ++ betaS ++ ", r), " ++ gamma ++ ", r)")
        pure (b1 ++ b2 ++ [assignLine left ("mulmod(" ++ left ++ ", " ++ term ++ ", r)")])
      let initialDeltaPower <- StateT.lift (feToU256 (e.field.repr
        (e.field.powNat e.field.delta (setIdx * chunkLen))))
      let (c1, deltaPow) <- freshLet
        ("mulmod(mulmod(" ++ beta ++ ", mload(X_MPTR), r), "
          ++ u256String initialDeltaPower ++ ", r)")
      let (c2, right) <- freshLet (wordString zCur)
      let lastColIdx := chunkCols.length - 1
      let rightBlock <- chunkCols.zipIdx.mapM fun (col, colPos) => do
        let colEval <- evalAt col 0
        let (d1, term) <- freshLet
          ("addmod(addmod(" ++ colEval ++ ", " ++ deltaPow ++ ", r), " ++ gamma ++ ", r)")
        let d2 := [assignLine right ("mulmod(" ++ right ++ ", " ++ term ++ ", r)")]
        if colPos != lastColIdx then
          pure (d1 ++ d2 ++ [assignLine deltaPow
            ("mulmod(" ++ deltaPow ++ ", " ++ u256String delta ++ ", r)")])
        else pure (d1 ++ d2)
      let (e1, diff) <- freshLet ("addmod(" ++ left ++ ", sub(r, " ++ right ++ "), r)")
      let (e2, constraint) <- freshLet ("mulmod(" ++ active ++ ", " ++ diff ++ ", r)")
      pure (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7
        ++ leftBlock.flatten ++ c1 ++ c2 ++ rightBlock.flatten ++ e1 ++ e2, constraint)
    pure ([fam1, fam2] ++ fam3 ++ fam4)

/-- rust: YE:439-632 (lookup_computations). Per lookup: the boundary, one helper identity
    per input chunk, and the accumulator. The helper is the prefix/suffix product
    construction at YE:509-557 - partial[j] = prefix[j] * suffix[j], NO inversion - which is
    the divergence P-SE's attack pass records against proofs/src/plonk/logup.rs:457-459
    (product * f.invert().unwrap(), which panics at f_j(x) + beta = 0). The k == 0 arm at
    YE:494-500 emits let varN := 0 and continues, so an empty chunk still produces an
    identity. -/
def lookupComputations {F : Type} [BEq F] : E F (List (Lines × Var)) := do
  let e <- get
  if e.meta_.numLookups == 0 then pure []
  else do
    let csDegree <- StateT.lift (ConstraintSystem.degree e.cs)
    let perLookup <- e.cs.lookups.toList.zipIdx.mapM fun (lookup, lookupIdx) => do
      let (mEval, hEvals, zEval, zNextEval) <-
        atIndex e.data.lookupEvals lookupIdx 449 "lookup evals index"
      let chunked <- StateT.lift (LogupBatchedArgument.chunkByDegree lookup csDegree)
      -- Boundary: (l_0 + l_last) * z_eval
      let boundary <- do
        reset
        let (b1, l0) <- freshLet "mload(L_0_MPTR)"
        let (b2, lLast) <- freshLet "mload(L_LAST_MPTR)"
        let (b3, lSum) <- freshLet ("addmod(" ++ l0 ++ ", " ++ lLast ++ ", r)")
        let (b4, bnd) <- freshLet ("mulmod(" ++ lSum ++ ", " ++ wordString zEval ++ ", r)")
        pure (b1 ++ b2 ++ b3 ++ b4, bnd)
      let selectorExpr := chunked.selector
      let helpers <- (chunked.inputExpressionChunks.toList.zip hEvals).mapM
          fun (inputChunk, hEval) => do
        reset
        let (h0, beta) <- freshLet "mload(BETA_MPTR)"
        let compressed <- inputChunk.toList.mapM fun parallelInput => do
          let (cl, cv) <- compressExpressionsWithTheta parallelInput.toList
          let (fl, fv) <- freshLet ("addmod(" ++ cv ++ ", " ++ beta ++ ", r)")
          pure (cl ++ fl, fv)
        let fVars := compressed.map Prod.snd
        let preLines := compressed.flatMap Prod.fst        let k := fVars.length
        if k == 0 then
          let zero <- freshVar
          pure (h0 ++ preLines ++ [letLine zero "0"], zero)
        else do
          let f0 <- atIndex fVars 0 504 "f_plus_beta_vars index"
          let (pLines, pv) <- freshLet f0
          let pFold := (fVars.drop 1).map fun fb =>
            assignLine pv ("mulmod(" ++ pv ++ ", " ++ fb ++ ", r)")
          let (pre0Lines, pre0) <- freshLet "1"
          let prefixRes <- ((List.range k).drop 1).foldlM
            (fun (st : List Var × List String) (j : Nat) => do
              let prevP <- atIndex st.1 (j - 1) 522 "prefix_vars index"
              let prevF <- atIndex fVars (j - 1) 523 "f_plus_beta_vars index"
              let (ls, pj) <- freshLet ("mulmod(" ++ prevP ++ ", " ++ prevF ++ ", r)")
              pure (st.1 ++ [pj], st.2 ++ ls))
            ([pre0], pre0Lines)
          let (suf0Lines, suf0) <- freshLet "1"
          let suffixRes <- (List.range (k - 1)).reverse.foldlM
            (fun (st : List Var × List String) (j : Nat) => do
              let nextS <- atIndex st.1 (j + 1) 537 "suffix_vars index"
              let nextF <- atIndex fVars (j + 1) 538 "f_plus_beta_vars index"
              let (ls, sj) <- freshLet ("mulmod(" ++ nextS ++ ", " ++ nextF ++ ", r)")
              pure (setIdx st.1 j sj, st.2 ++ ls))
            (List.replicate (k - 1) "" ++ [suf0], suf0Lines)
          let preVars := prefixRes.1
          let sufVars := suffixRes.1
          let preFirst <- atIndex preVars 0 548 "prefix_vars index"
          let sufFirst <- atIndex sufVars 0 548 "suffix_vars index"
          let (sumLines0, sumVar) <-
            freshLet ("mulmod(" ++ preFirst ++ ", " ++ sufFirst ++ ", r)")
          let sumRest <- ((List.range k).drop 1).foldlM
            (fun (st : List String) (j : Nat) => do
              let preJ <- atIndex preVars j 554 "prefix_vars index"
              let sufJ <- atIndex sufVars j 554 "suffix_vars index"
              let (tl, term) <- freshLet ("mulmod(" ++ preJ ++ ", " ++ sufJ ++ ", r)")
              pure (st ++ tl ++ [assignLine sumVar
                ("addmod(" ++ sumVar ++ ", " ++ term ++ ", r)")]))
            sumLines0
          let (hpLines, hp) <- freshLet
            ("mulmod(" ++ wordString hEval ++ ", " ++ pv ++ ", r)")
          let (hcLines, helperC) <- freshLet
            ("addmod(" ++ hp ++ ", sub(r, " ++ sumVar ++ "), r)")
          pure (h0 ++ preLines ++ pLines ++ pFold ++ prefixRes.2 ++ suffixRes.2
            ++ sumRest ++ hpLines ++ hcLines, helperC)
      -- Accumulator constraint: active * ((z_next - z - s * sum h) * (t + beta) + m)
      let accumulator <- do
        reset
        let (x1, lLast) <- freshLet "mload(L_LAST_MPTR)"
        let (x2, lBlind) <- freshLet "mload(L_BLIND_MPTR)"
        let (x3, active) <- freshLet
          ("addmod(1, sub(r, addmod(" ++ lLast ++ ", " ++ lBlind ++ ", r)), r)")
        let (x4, beta) <- freshLet "mload(BETA_MPTR)"
        let hFirst <- atIndex hEvals 0 589 "h_evals index"
        let (x5, sumH) <- freshLet (wordString hFirst)
        let hFold := (hEvals.drop 1).map fun h =>
          assignLine sumH ("addmod(" ++ sumH ++ ", " ++ wordString h ++ ", r)")
        let (selLines, selVar) <- evaluate selectorExpr
        let (x6, sSumH) <- freshLet ("mulmod(" ++ selVar ++ ", " ++ sumH ++ ", r)")
        let (x7, diff) <- freshLet
          ("addmod(" ++ wordString zNextEval ++ ", sub(r, addmod(" ++ wordString zEval
            ++ ", " ++ sSumH ++ ", r)), r)")
        let (tLines, tVar) <- compressExpressionsWithTheta chunked.tableExpressions.toList
        let (x8, tPlusBeta) <- freshLet ("addmod(" ++ tVar ++ ", " ++ beta ++ ", r)")
        let (x9, core) <- freshLet
          ("addmod(mulmod(" ++ diff ++ ", " ++ tPlusBeta ++ ", r), " ++ wordString mEval ++ ", r)")
        let (x10, accC) <- freshLet ("mulmod(" ++ active ++ ", " ++ core ++ ", r)")
        pure (x1 ++ x2 ++ x3 ++ x4 ++ x5 ++ hFold ++ selLines ++ x6 ++ x7 ++ tLines ++ x8
          ++ x9 ++ x10, accC)
      pure ([boundary] ++ helpers ++ [accumulator])
    pure (perLookup.flatten)

/-- rust: YE:654-723 (trashcan_computations). Per trash argument:
    compressed - (1 - selector) * trash_eval, compressed by the TRASH challenge and not by
    theta (YE:644-647 says so explicitly). The lazy challenge load at YE:671-677 is the
    detail a port loses: with no constraint expressions the mload(TRASH_CHALLENGE_MPTR)
    line is never emitted, so an empty trashcan's block has no unused let. -/
def trashcanComputations {F : Type} [BEq F] : E F (List (Lines × Var)) := do
  let e <- get
  if e.meta_.numTrashcans == 0 then pure []
  else
    e.cs.trashcans.toList.zipIdx.mapM fun (argument, idx) => do
      reset
      let constraintExprs := argument.constraintExpressions.toList
      let (headLines, trashChallenge) <-
        if constraintExprs.isEmpty then pure ([], none)
        else do
          let var <- freshVar
          pure ([letLine var "mload(TRASH_CHALLENGE_MPTR)"], some var)
      let foldRes <- constraintExprs.foldlM
        (fun (st : Lines × Option Var) (expr : Expression F) => do
          let (eLines, eVar) <- evaluate expr
          let next <- freshVar
          let prev := match st.2 with | some v => v | none => "0"
          let tau <- match trashChallenge with
            | some t => pure t
            | none => throw (Fault.panic
                (site 687 "trash_challenge present when expressions non-empty"))
          pure (st.1 ++ eLines ++
            [letLine next ("addmod(mulmod(" ++ prev ++ ", " ++ tau ++ ", r), " ++ eVar
              ++ ", r)")], some next))
        (headLines, none)
      let (lines1, compressed) <- match foldRes.2 with
        | some v => pure (foldRes.1, v)
        | none => do
            let zero <- freshVar
            pure (foldRes.1 ++ [letLine zero "0"], zero)
      let (selLines, selVar) <- evaluate argument.selector
      let (y1, oneMinusQ) <- freshLet ("addmod(1, sub(r, " ++ selVar ++ "), r)")
      let trashEval <- atIndex e.data.trashcanEvals idx 708 "trashcan evals index"
      let (y2, scaled) <- freshLet
        ("mulmod(" ++ oneMinusQ ++ ", " ++ wordString trashEval ++ ", r)")
      let (y3, c) <- freshLet ("addmod(" ++ compressed ++ ", sub(r, " ++ scaled ++ "), r)")
      pure (lines1 ++ selLines ++ y1 ++ y2 ++ y3, c)

end Midfall.Generator.QuotientEvaluator
/-! # Known-answer checks

Executable booleans, no theorems (D-P17: nothing here imports Midfall/Instances/). The
concrete field is the QVM's own model of BLS12-381 Fr - QVMFr, i.e. Nat reduced at
qvmFrModulus - so that hazard 4's cross-check compares the emitter against the QVM
reference interpreter over ONE field and ONE memory rather than two lookalikes. -/

namespace Midfall.Generator.QuotientEvaluatorKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientEvaluator
  Midfall.Generator.QuotientBuilder

/-! ## Fixtures -/

/-- The field dictionary for the gates. DELTA is a parameter and not a literal (see the
    header); 7 is chosen because it is neither 0 nor 1 nor a small power of two, so a
    permutation literal that came from a different constant is visible. -/
def qFrCtx (delta : QVMFr) : FieldCtx QVMFr where
  zero := 0
  one := 1
  add := qvmFrAdd
  mul := qvmFrMul
  neg := qvmFrNeg
  eqF := fun a b => a == b
  isZero := fun v => v == 0
  powNat := fun b e => (List.range e).foldl (fun acc _ => qvmFrMul acc b) 1
  repr := fun v => bytesToNats (natToBytesLE v 32)
  delta := delta

/-- The permutation delta used by every fixture in this section. -/
def qDelta : QVMFr := 7

/-- A memory Word at an absolute byte address - the shape every Data eval slot has, since
    Data::new builds them from Ptr::memory(...) advanced by an integer offset. -/
def wmem (addr : Nat) : Word := Word.fromPtr (ptrMemory (valueFromNat addr))

/-- The eval addresses. All distinct and all multiples of 0x20, so a wrong column or a
    wrong rotation shows up as a different mload and not as an off-by-one that reads like
    the right one (R-48: own fixture, distinctness asserted by pointerDistinct_ok). -/
def aAddr (i : Nat) : Nat := 0x2000 + i * 0x20
def fAddr (i : Nat) : Nat := 0x2400 + i * 0x20
def iAddr (i : Nat) : Nat := 0x2800 + i * 0x20
def zAddr (i : Nat) : Nat := 0x2c00 + i * 0x20
def znAddr (i : Nat) : Nat := 0x2e00 + i * 0x20
def zlAddr (i : Nat) : Nat := 0x3000 + i * 0x20
def sAddr (i : Nat) : Nat := 0x3200 + i * 0x20
def mAddr : Nat := 0x3400
def hAddr (i : Nat) : Nat := 0x3480 + i * 0x20
def instEvalAddr : Nat := 0x3800
def trashAddr (i : Nat) : Nat := 0x3a00 + i * 0x20
def challengeAddr (i : Nat) : Nat := 0x3c00 + i * 0x20

def colA (i : Nat) : Column := { index := i, columnType := .advice Advice.default }
def colF (i : Nat) : Column := { index := i, columnType := .fixed }
def colI (i : Nat) : Column := { index := i, columnType := .instance }

def eA (i : Nat) : Expression QVMFr := Expression.advice { index := none, columnIndex := i, rotation := Rotation.cur, phase := { val := 0 } }
def eAn (i : Nat) : Expression QVMFr := Expression.advice { index := none, columnIndex := i, rotation := Rotation.next, phase := { val := 0 } }
def eF (i : Nat) : Expression QVMFr := Expression.fixed { index := none, columnIndex := i, rotation := Rotation.cur }
def eI (i : Nat) : Expression QVMFr := Expression.instance { index := none, columnIndex := i, rotation := Rotation.cur }
def eC (n : QVMFr) : Expression QVMFr := Expression.constant n
def eMul (a b : Expression QVMFr) : Expression QVMFr := Expression.product a b
def eAdd (a b : Expression QVMFr) : Expression QVMFr := Expression.sum a b
def eNeg (a : Expression QVMFr) : Expression QVMFr := Expression.negated a
def eScale (a : Expression QVMFr) (s : QVMFr) : Expression QVMFr := Expression.scaled a s
def eSel (i : Nat) : Expression QVMFr := Expression.selector { index := i, isSimple := true }

/-- Column 0 is a converted simple selector; columns 1.. are ordinary fixed. Instance
    column 0 is committed, column 1 is the public one whose Lagrange value sits at
    INSTANCE_EVAL_MPTR. -/
def qMeta : ConstraintSystemMeta := { constraintSystemMetaDefault with numFixeds := 3, permutationColumns := [colA 0, colA 1, colF 1, colI 0], permutationChunkLen := 3, numLookups := 1, lookupChunks := [1], numTrashcans := 1, numPermutationZs := 2, numQuotients := 1, simpleSelectorCols := [0], numCommittedInstances := 1 }

def qDataEmpty : Data := { challengeMptr := ptrMemory (valueFromNat 0), thetaMptr := ptrMemory (valueFromNat 0), fixedComms := [], permutationComms := [], adviceComms := [], committedInstanceComms := [], permutationZComms := [], lookupMComms := [], lookupHelperComms := [], lookupZComms := [], trashcanComms := [], challenges := [], instanceEval := wmem 0, committedInstanceEvals := [], adviceEvals := [], fixedEvals := [], permutationEvals := [], permutationZEvals := [], lookupEvals := [], trashcanEvals := [], computedQuotientComm := EcPoint.new (ptrMemory (valueFromNat 0)), computedQuotientEval := wmem 0, commsMptrBase := ptrMemory (valueFromNat 0), reversedEvalsMptr := ptrMemory (valueFromNat 0), dummyEvalWords := [] }

def qData : Data := { qDataEmpty with challenges := [wmem (challengeAddr 0), wmem (challengeAddr 1)], instanceEval := wmem instEvalAddr, committedInstanceEvals := [((0, 0), wmem (iAddr 0))], adviceEvals := [((0, 0), wmem (aAddr 0)), ((1, 0), wmem (aAddr 1)), ((2, 0), wmem (aAddr 2)), ((3, 0), wmem (aAddr 3)), ((4, 0), wmem (aAddr 4)), ((0, 1), wmem (aAddr 5))], fixedEvals := [((1, 0), wmem (fAddr 1)), ((2, 0), wmem (fAddr 2))], permutationEvals := [(colA 0, wmem (sAddr 0)), (colA 1, wmem (sAddr 1)), (colF 1, wmem (sAddr 2)), (colI 0, wmem (sAddr 3))], permutationZEvals := [(wmem (zAddr 0), wmem (znAddr 0), some (wmem (zlAddr 0))), (wmem (zAddr 1), wmem (znAddr 1), none)], lookupEvals := [(wmem mAddr, [wmem (hAddr 0), wmem (hAddr 1)], wmem (zAddr 9), wmem (znAddr 9))], trashcanEvals := [wmem (trashAddr 0)] }

def qGate (name : String) (polys : List (Expression QVMFr)) (sels : List Selector) : Gate QVMFr := { name := name, constraintNames := ((List.range polys.length).map (fun i => name ++ "_c" ++ toString i)).toArray, polys := polys.toArray, queriedSelectors := sels.toArray, queriedCells := #[] }

def qCs : ConstraintSystem QVMFr := { (ConstraintSystem.default : ConstraintSystem QVMFr) with gates := #[qGate "g0" [eMul (eA 0) (eA 1)] [{ index := 0, isSimple := true }], qGate "g1" [eAdd (eScale (eA 2) 3) (eC 5), eA 3] []], numFixedColumns := 3, numAdviceColumns := 5, numInstanceColumns := 2, fixedQueries := #[(colF 1, Rotation.cur)], adviceQueries := #[(colA 0, Rotation.cur), (colA 1, Rotation.cur), (colA 2, Rotation.cur), (colA 3, Rotation.cur), (colA 4, Rotation.cur)], instanceQueries := #[(colI 0, Rotation.cur), (colI 1, Rotation.cur)], lookups := #[{ name := "lk", selector := eF 1, inputExpressions := #[#[eA 0], #[eA 1]], tableExpressions := #[eF 2] }], trashcans := #[{ name := "tr", selector := eF 1, constraintExpressions := #[eMul (eA 3) (eA 4)] }] }

/-- A fresh evaluator over the fixtures, pow5 peephole off (the Rust's default). -/
def ev : Evaluator QVMFr := Evaluator.new (qFrCtx qDelta) qCs qMeta qData

/-- The same with the peephole on: with_pow5_helper consumes and returns the struct, so
    this is the one Rust method in the file that is not an &self mutation. -/
def evPow5 : Evaluator QVMFr := (Evaluator.new (qFrCtx qDelta) qCs qMeta qData).withPow5Helper true

/-- Run an emission against a fixture; keep the value, or none if it faulted. -/
def runOpt {alpha : Type} (x : E QVMFr alpha) (e : Evaluator QVMFr) : Option alpha :=
  match x e with
  | .ok (v, _) => some v
  | .error _ => none

/-- The emitted lines of an (Lines, Var) emission, or [] if it faulted. A gate that gets
    [] is a gate that goes red, which is the point. -/
def runLines (x : E QVMFr (Lines × Var)) (e : Evaluator QVMFr) : List String :=
  match x e with
  | .ok ((ls, _), _) => ls
  | .error _ => []

/-- The final variable name of an emission, or "" if it faulted. -/
def runVar (x : E QVMFr (Lines × Var)) (e : Evaluator QVMFr) : String :=
  match x e with
  | .ok ((_, v), _) => v
  | .error _ => ""

/-- The panic site an emission faults at, or "" if it succeeds. -/
def runSite {alpha : Type} (x : E QVMFr alpha) (e : Evaluator QVMFr) : String :=
  match x e with
  | .ok _ => ""
  | .error (Fault.panic s) => s
  | .error _ => "?"

/-- The observable residue of the interior mutability: the counter, the cache size and the
    pow5 flag AFTER the emission. -/
def runState (x : E QVMFr (Lines × Var)) (e : Evaluator QVMFr) : Nat × Nat × Bool :=
  match x e with
  | .ok (_, s) => (s.varCounter, s.varCache.length, s.pow5Used)
  | .error _ => (0, 0, false)

/-! ## The Yul reader the cross-check needs (Lean scaffolding, not a Rust item)

HAZARD 4. The QVM reference interpreter evaluates QuotientExpr trees over a PRNG memory;
this Evaluator emits Yul TEXT for the same identities by a different route. To compare
them the text has to be executed, and the emitted subset is small enough to interpret
directly: let-assignments and reassignments over addmod / mulmod / sub / mload / q_pow5 /
literals / variables - exactly the grammar VmBuilder.lean:1169 already documents as "the
Evaluator's" shape. The parsers are reused from the builder (callArgs, parseU256,
isLiteral, trimStr) rather than written again. -/

/-- The symbolic memory symbols the emitters print bare (mload(L_0_MPTR) and friends),
    mapped to absolute addresses so the QVM side can name the same slot with
    QuotientMem.literal. None of these collides with the eval addresses above. -/
def symSymbols : List (String × Nat) :=
  [ ("L_0_MPTR", 0x1000), ("L_LAST_MPTR", 0x1020), ("L_BLIND_MPTR", 0x1040),
    ("BETA_MPTR", 0x1060), ("GAMMA_MPTR", 0x1080), ("X_MPTR", 0x10a0),
    ("THETA_MPTR", 0x10c0), ("TRASH_CHALLENGE_MPTR", 0x10e0) ]

def symAddr (name : String) : Option Nat :=
  (symSymbols.find? fun (n, _) => n == name).map Prod.snd

inductive YulTerm
  | lit (n : Nat)
  | mload (addr : Nat)
  | var (name : String)
  | add (a b : YulTerm)
  | mul (a b : YulTerm)
  | neg (a : YulTerm)
  | pow5 (a : YulTerm)
  deriving BEq, Inhabited

/-- Resolve one mload argument: a literal address, a symbolic prologue symbol, or a
    symbolic symbol offset by add/sub of a word. -/
def yulAddr (arg : String) : Except QVMFault Nat := do
  let a := trimStr arg
  if isLiteral a then pure (← parseU256 a).toNat
  else match symAddr a with
    | some n => pure n
    | none =>
        match callArgs a "add" with
        | .ok (some [base, off]) =>
            let b := match symAddr (trimStr base) with | some n => n | none => 0
            pure (b + (← parseU256 (trimStr off)).toNat)
        | _ =>
            match callArgs a "sub" with
            | .ok (some [base, off]) =>
                let b := match symAddr (trimStr base) with | some n => n | none => 0
                pure (b - (← parseU256 (trimStr off)).toNat)
            | _ => .error (QVMFault.panic ("unresolved yul pointer: " ++ a))

/-- Parse one right-hand side of an emitted assignment. The Rust's own grammar, read off
    the format strings of the four emitters. -/
partial def yulParse (text : String) : Except QVMFault YulTerm :=
    let t := trimStr text
    match callArgs t "addmod" with
    | .ok (some [a, b, "r"]) => do pure (YulTerm.add (← yulParse a) (← yulParse b))
    | _ => match callArgs t "mulmod" with
      | .ok (some [a, b, "r"]) => do pure (YulTerm.mul (← yulParse a) (← yulParse b))
      | _ => match callArgs t "sub" with
        | .ok (some ["r", a]) => do pure (YulTerm.neg (← yulParse a))
        | _ => match callArgs t "mload" with
          | .ok (some [a]) => do pure (YulTerm.mload (← yulAddr a))
          | _ => match callArgs t "q_pow5" with
            | .ok (some [a]) => do pure (YulTerm.pow5 (← yulParse a))
            | _ => if isLiteral t then do pure (YulTerm.lit (← parseU256 t).toNat)
                   else pure (YulTerm.var t)

structure YSt where
  mem : QuotientRefMemory
  vars : List (String × QVMFr)

def yulLookup (st : YSt) (name : String) : Except QVMFault QVMFr :=
  match st.vars.find? fun (n, _) => n == name with
  | some (_, v) => .ok v
  | none => .error (QVMFault.panic ("unbound yul variable: " ++ name))

def yulValue (st : YSt) (t : YulTerm) : Except QVMFault (QVMFr × YSt) :=
  match t with
  | .lit n => do let v ← fqFromU256 (BitVec.ofNat 256 n); pure (v, st)
  | .mload addr => let (v, m) := st.mem.literal addr; .ok (v, { st with mem := m })
  | .var name => do let v ← yulLookup st name; pure (v, st)
  | .add a b => do
      let (x, s1) ← yulValue st a
      let (y, s2) ← yulValue s1 b
      .ok (qvmFrAdd x y, s2)
  | .mul a b => do
      let (x, s1) ← yulValue st a
      let (y, s2) ← yulValue s1 b
      .ok (qvmFrMul x y, s2)
  | .neg a => do let (x, s1) ← yulValue st a; .ok (qvmFrNeg x, s1)
  | .pow5 a => do
      let (x, s1) ← yulValue st a
      .ok (qvmFrMul (qvmFrMul (qvmFrMul (qvmFrMul x x) x) x) x, s1)

/-- Split 'let v := e' or 'v := e'. -/
def yulSplit (line : String) : Except QVMFault (String × String) := do
  let l0 := trimStr line
  let l := if l0.startsWith "let " then (l0.drop 4).toString else l0
  match String.splitOn l " := " with
  | [dst, rhs] => .ok (trimStr dst, trimStr rhs)
  | _ => .error (QVMFault.panic ("not an assignment: " ++ line))

/-- Run a whole emitted block and return the value of its final variable. -/
def yulRun (lines : List String) (finalVar : String) (st : YSt) :
    Except QVMFault (QVMFr × YSt) := do
  let st ← lines.foldlM
    (fun (st : YSt) (line : String) => do
      let (dst, rhs) ← yulSplit line
      let t ← yulParse rhs
      let (v, st') ← yulValue st t
      pure { st' with vars := (dst, v) :: st'.vars })
    st
  let v <- yulLookup st finalVar
  .ok (v, st)

/-- The shared memory both routes read. -/
def xMem : QuotientRefMemory := quotientRefMemoryNew (qvmBytesOfNats (List.range 32))

def cMemAt (ptr : Nat) : QuotientExpr := QuotientExpr.mem (QuotientMem.literal ptr)
def cLit (n : Nat) : QuotientExpr := QuotientExpr.const (BitVec.ofNat 256 n)
def cAdd (a b : QuotientExpr) : QuotientExpr := QuotientExpr.add a b
def cMul (a b : QuotientExpr) : QuotientExpr := QuotientExpr.mul a b
def cNeg (a : QuotientExpr) : QuotientExpr := QuotientExpr.neg a

/-- The cross-check itself: emit Yul for an expression, run the Yul, evaluate the hand
    written QuotientExpr for the same identity over the same memory, and require the same
    field element. True only when BOTH routes succeed and agree. -/
def agree (lines : List String) (finalVar : String) (qexpr : QuotientExpr) : Bool :=
  match yulRun lines finalVar { mem := xMem, vars := [] } with
  | .error _ => false
  | .ok (yv, _) =>
      match evalQuotientExpr qexpr xMem with
      | .error _ => false
      | .ok (qv, _) => yv == qv

/-! ## Gates -/

/-- GATE 0 (D-P19 reachability, FIRST #eval). Rules out every cite in this file being
    checked against a file that is not there. -/
def yePathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/yul_emit.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/yul_emit.rs"]

def readYeArtifact : IO String :=
  yePathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got
        else Midfall.Generator.QuotientVmKats.readFileOrEmpty path)
    (pure "")

def evaluatorArtifactReachable_ok (src : String) : Bool :=
  src.length > 30000 && src.contains "pub(crate) struct Evaluator<'a>"

/-- R-48 distinctness: every eval address in the fixture is different, so no gate below can
    pass because two slots accidentally read the same mload. -/
def pointerDistinct_ok : Bool :=
  let addrs := [aAddr 0, aAddr 1, aAddr 2, aAddr 3, aAddr 4, aAddr 5, fAddr 1, fAddr 2,
    iAddr 0, zAddr 0, zAddr 1, zAddr 9, znAddr 0, znAddr 1, znAddr 9, zlAddr 0,
    sAddr 0, sAddr 1, sAddr 2, sAddr 3, mAddr, hAddr 0, hAddr 1, instEvalAddr,
    trashAddr 0, challengeAddr 0, challengeAddr 1]
  addrs.Nodup && (addrs.all fun a => a % 0x20 == 0) &&
    (symSymbols.all fun (_, a) => ! addrs.contains a)

/-- HAZARD 1, part 1: the counter really is threaded state. var0, var1, var2 in call order
    and the counter left at 3. PERTURBATION RUN: making nextVar bump before reading (so the
    first name is var1) reddens this gate and every exact-line gate below. -/
def nextVarAndReset_ok : Bool :=
  match ((nextVar >>= fun a => nextVar >>= fun b => nextVar >>= fun c => pure (a, b, c)) ev) with
  | .ok ((v0, v1, v2), s) =>
      v0 == "var0" && v1 == "var1" && v2 == "var2" && s.varCounter == 3
  | _ => false

/-- HAZARD 1, part 2 (THE CACHE GATE). Two structurally equal expressions inside one
    identity share ONE variable and the second emits NO line. Dropping the cache - the
    tempting pure port - makes the second call emit a second let and return var1, and this
    goes red. It also pins the key: the rendered VALUE, so a differently spelled but
    semantically identical expression is a MISS, exactly the class P-09f's
    rowSpellingMatters_ok pins. -/
def varCacheReuse_ok : Bool :=
  let x := do
    let (l1, v1) ← evaluate (eAdd (eA 0) (eA 1))
    let (l2, v2) ← evaluate (eAdd (eA 0) (eA 1))
    let (l3, v3) ← evaluate (eAdd (eA 0) (eC 5))
    pure (l1, v1, l2, v2, l3, v3)
  match x ev with
  | .ok ((l1, v1, l2, v2, l3, v3), s) =>
      l1 == ["let a_0 := mload(0x2000)", "let a_1 := mload(0x2020)",
             "let var0 := addmod(a_0, a_1, r)"]
        && v1 == "var0" && l2 == [] && v2 == "var0"
        && l3 == ["let var1 := 0x5", "let var2 := addmod(var1, a_0, r)"] && v3 == "var2"
        && s.varCache.length == 5 && s.varCounter == 3
  | _ => false

/-- HAZARD 1, part 3: the cache is keyed on the value and NOT on the requested name, so a
    second identical query returns the FIRST name even when the caller asked for a
    different one, and an unnamed request reuses it too. -/
def varCacheNamedSlot_ok : Bool :=
  let x := do
    let (l1, v1) ← initVar "mload(0x2000)" (some "a_0")
    let (l2, v2) ← initVar "mload(0x2000)" (some "renamed")
    let (l3, v3) ← initVar "mload(0x2000)" none
    pure (l1, v1, l2, v2, l3, v3)
  match x ev with
  | .ok ((l1, v1, l2, v2, l3, v3), s) =>
      l1 == ["let a_0 := mload(0x2000)"] && v1 == "a_0"
        && l2 == [] && v2 == "a_0" && l3 == [] && v3 == "a_0"
        && s.varCounter == 0
  | _ => false

/-- HAZARD 1, part 4: the emitters' own 'let v = fresh_var(); lines.push(..)' idiom does
    NOT go through the cache, so two identical freshLets emit two identical lines. If a
    future port routed everything through init_var the permutation and lookup blocks would
    collapse, and this reddens. -/
def freshLetBypassesCache_ok : Bool :=
  let x := do
    let (l1, v1) ← freshLet "mload(L_0_MPTR)"
    let (l2, v2) ← freshLet "mload(L_0_MPTR)"
    pure (l1, v1, l2, v2)
  match x ev with
  | .ok ((l1, v1, l2, v2), s) =>
      l1 == ["let var0 := mload(L_0_MPTR)"] && l2 == ["let var1 := mload(L_0_MPTR)"]
        && v1 == "var0" && v2 == "var1" && s.varCache == []
  | _ => false

/-- HAZARD 1, part 5 (THE pow5 CELL GATE). pow5_used starts false, stays false when the
    peephole is off even for a five-fold product, and flips to true EXACTLY when a q_pow5
    line is emitted - not before, and not for four or six factors. -/
def pow5UsedFlipsExactlyOnQPow5_ok : Bool :=
  let a5 := eMul (eMul (eMul (eMul (eA 0) (eA 0)) (eA 0)) (eA 0)) (eA 0)
  let a4 := eMul (eMul (eMul (eA 0) (eA 0)) (eA 0)) (eA 0)
  let a6 := eMul a5 (eA 0)
  let off := runState (evaluate a5) ev
  let on := runState (evaluate a5) evPow5
  let off4 := runState (evaluate a4) evPow5
  let off6 := runState (evaluate a6) evPow5
  let plain := runState (evaluate (eA 0)) evPow5
  off == (4, 5, false) && on.2.2 == true && on.2.1 == 2
    && runLines (evaluate a5) evPow5
        == ["let a_0 := mload(0x2000)", "let var0 := q_pow5(a_0)"]
    && runLines (evaluate a5) ev
        == ["let a_0 := mload(0x2000)", "let var0 := mulmod(a_0, a_0, r)",
            "let var1 := mulmod(var0, a_0, r)", "let var2 := mulmod(var1, a_0, r)",
            "let var3 := mulmod(var2, a_0, r)"]
    && off4.2.2 == false && off6.2.2 == false && plain.2.2 == false

/-- YE:821-838 in isolation: five factors, all equal, and the flattening is
    associativity-blind, so a right-nested tree is recognised as readily as a left-nested
    one. A five-fold product under a Sum is NOT a single term's factor list. -/
def pow5BaseRecognition_ok : Bool :=
  let a := eA 0
  let left5 := eMul (eMul (eMul (eMul a a) a) a) a
  let right5 := eMul a (eMul a (eMul a (eMul a a)))
  let mixed := eMul (eMul (eMul (eMul a a) a) a) (eA 1)
  let underSum := eAdd left5 (eA 1)
  (match pow5BaseExpr left5 evPow5 with | .ok (some _, _) => true | _ => false)
    && (match pow5BaseExpr right5 evPow5 with | .ok (some _, _) => true | _ => false)
    && (match pow5BaseExpr mixed evPow5 with | .ok (none, _) => true | _ => false)
    && (match pow5BaseExpr underSum evPow5 with | .ok (none, _) => true | _ => false)
    && (match pow5BaseExpr left5 ev with | .ok (none, _) => true | _ => false)
    && (match pow5BaseExpr (eA 0) evPow5 with | .ok (none, _) => true | _ => false)

/-- YE:1148-1154 and YE:1157-1163, the two free renderers. The u256_string branch cannot
    bind (both arms render the same text) and column_eval_var's negative arm prints the
    ABSOLUTE rotation. FINDING: yul_emit.rs and vm/mod.rs each carry their own
    u256_string; this gate pins that FoldCompute's port of the QVM copy and this port of
    the yul_emit copy agree, so the duplicate cannot drift silently. -/
def u256String_and_columnEvalVar_ok : Bool :=
  u256String 0 == "0x0" && u256String 1 == "0x1"
    && u256String (BitVec.ofNat 256 (2^64)) == "0x10000000000000000"
    && (List.range 40).all (fun n => u256String (BitVec.ofNat 256 n)
        == Midfall.Generator.QuotientFoldCompute.u256String (BitVec.ofNat 256 n))
    && columnEvalVar "f" 0 0 == "f_0"
    && columnEvalVar "f" 0 (-1) == "f_0_prev_1"
    && columnEvalVar "a" 12 3 == "a_12_next_3"
    && columnEvalVar "i" 1 0 == "i_1"

/-- YE:782-818: the rejections, each reachable from a hand-built Data. The simple-selector
    arm is the one a port forgets, because the eval map CAN have an entry for a converted
    selector column and the Rust refuses to read it. -/
def expressionMemoryPtr_rejections_ok : Bool :=
  let calldata := Evaluator.new (qFrCtx qDelta) qCs qMeta
    { qData with adviceEvals := ((0, 0), Word.fromPtr (ptrCalldata (valueFromNat 0x44)))
        :: qData.adviceEvals }
  let negative := Evaluator.new (qFrCtx qDelta) qCs qMeta
    { qData with adviceEvals := ((0, 0), Word.fromPtr (ptrMemory (Value.integer (-32))))
        :: qData.adviceEvals }
  let symbolic := Evaluator.new (qFrCtx qDelta) qCs qMeta
    { qData with adviceEvals := ((0, 0), Word.fromPtr (ptrMemory (Value.identifier "p" 0)))
        :: qData.adviceEvals }
  let simpleSel := Evaluator.new (qFrCtx qDelta) qCs qMeta
    { qData with fixedEvals := ((0, 0), wmem 0x9000) :: qData.fixedEvals }
  (match expressionMemoryPtr (eA 0) ev with | .ok (some 0x2000, _) => true | _ => false)
    && (match expressionMemoryPtr (eC 5) ev with | .ok (none, _) => true | _ => false)
    && (match expressionMemoryPtr (eSel 0) ev with | .ok (none, _) => true | _ => false)
    && (match expressionMemoryPtr (eA 0) calldata with | .ok (none, _) => true | _ => false)
    && (match expressionMemoryPtr (eA 0) negative with | .ok (none, _) => true | _ => false)
    && (match expressionMemoryPtr (eA 0) symbolic with | .ok (none, _) => true | _ => false)
    && (match expressionMemoryPtr (eF 0) simpleSel with | .ok (none, _) => true | _ => false)
    && (match expressionMemoryPtr (eI 1) ev with | .ok (some 0x3800, _) => true | _ => false)

/-- YE:843-865: the three Any arms, including the two that do not read an eval map at all
    (a simple selector column is the literal 0x1; a public instance column is
    INSTANCE_EVAL_MPTR whatever its index and rotation), and the advice expect. -/
def evalAt_threeArms_ok : Bool :=
  (match evalAt (colA 1) 0 ev with | .ok ("mload(0x2020)", _) => true | _ => false)
    && (match evalAt (colF 0) 0 ev with | .ok ("0x1", _) => true | _ => false)
    && (match evalAt (colF 1) 0 ev with | .ok ("mload(0x2420)", _) => true | _ => false)
    && (match evalAt (colI 0) 0 ev with | .ok ("mload(0x2800)", _) => true | _ => false)
    && (match evalAt (colI 7) 5 ev with | .ok ("mload(0x3800)", _) => true | _ => false)
    && (runSite (evalAt (colA 9) 0 ev) ev).contains "yul_emit.rs:850"
    && (runSite (evalAt (colF 3) 0 ev) ev).contains "yul_emit.rs:859"

/-- HAZARD 5: the virtual-selector panic here is the CODEGEN one at YE:1041, not the
    verifier's at proofs/src/plonk/mod.rs:532 that Circuit.lean's verifierCallbacks uses.
    A port that reused verifierCallbacks would report the wrong file to whoever generates a
    verifier from a circuit that still has virtual selectors. -/
def virtualSelectorPanic_site_ok : Bool :=
  let s := runSite (evaluate (eSel 0)) ev
  s.contains "yul_emit.rs:1041"
    && s.contains "virtual selectors must be removed before codegen"
    && ! s.contains "mod.rs:532"

/-- YE:897-942's fuse predicate, arm by arm. The asymmetry is the point: ONE term with
    coefficient exactly ONE is not fused and goes through the visitor, and the third
    disjunct - a single term whose coefficient is NOT one - is what makes a scaled PRODUCT
    fuse into one nested mulmod instead of two lets. That disjunct is INVISIBLE for a
    scaled LEAF (both routes emit a_0 / 0x3 / mulmod(a_0, var0, r) in the same order), so
    the first version of this gate did not redden when the perturbation deleted it; the
    scaled-product pair is what pins it, and it also shows the fusion is an emission-SHAPE
    optimisation and not an arithmetic one. Second finding, pinned rather than assumed:
    a - a does NOT cancel, because terms.retain drops only ZERO coefficients and -1 is not
    zero, so the emitter spends three lines on 1*a + (r-1)*a. -/
def sumFusionPredicate_ok : Bool :=
  runLines (evaluate (eA 0)) ev == ["let a_0 := mload(0x2000)"]
    && runLines (evaluate (eScale (eA 0) 3)) ev
        == ["let a_0 := mload(0x2000)", "let var0 := 0x3", "let var1 := mulmod(a_0, var0, r)"]
    && runLines (evaluate (eScale (eMul (eA 0) (eA 1)) 3)) ev
        == ["let a_0 := mload(0x2000)", "let a_1 := mload(0x2020)", "let var0 := 0x3",
            "let var1 := mulmod(mulmod(a_0, a_1, r), var0, r)"]
    && runLines (evaluateBasic (eScale (eMul (eA 0) (eA 1)) 3)) ev
        == ["let a_0 := mload(0x2000)", "let a_1 := mload(0x2020)",
            "let var0 := mulmod(a_0, a_1, r)", "let var1 := 0x3",
            "let var2 := mulmod(var0, var1, r)"]
    && runLines (evaluate (eC 5)) ev == ["let var0 := 0x5"]
    && runLines (evaluate (eAdd (eA 0) (eA 1))) ev
        == ["let a_0 := mload(0x2000)", "let a_1 := mload(0x2020)",
            "let var0 := addmod(a_0, a_1, r)"]
    && runLines (evaluate (eAdd (eA 0) (eNeg (eA 0)))) ev
        == ["let a_0 := mload(0x2000)",
            "let var0 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000",
            "let var1 := mulmod(a_0, var0, r)", "let var2 := addmod(a_0, var1, r)"]
    && runVar (evaluate (eAdd (eA 0) (eNeg (eA 0)))) ev == "var2"
    && runLines (evaluate (eAdd (eA 0) (eNeg (eA 0)))) ev != ["let var0 := 0x0"]

/-- YE:735-776: the two spellings of an empty compression. compressExpressions [] pushes a
    RAW 'let var0 := 0' (fresh_var plus push, uncached); compressExpressionsWithTheta []
    returns init_var("0x0"), which IS cached and renders 0x0. Collapsing them changes the
    text of every empty lookup chunk. -/
def compressTwoZeros_ok : Bool :=
  runLines (compressExpressions [] "var0") ev == ["let var0 := 0"]
    && runLines (compressExpressionsWithTheta []) ev == ["let var0 := 0x0"]
    && runLines (compressExpressionsWithChallengeVar [] "tau") ev == ["let var0 := 0"]
    && runLines (compressExpressionsWithTheta [eA 0]) ev
        == ["let var0 := mload(THETA_MPTR)", "let a_0 := mload(0x2000)",
            "let var1 := addmod(mulmod(0, var0, r), a_0, r)"]
    && runLines (compressExpressions [eA 0, eA 1] "tau") ev
        == ["let a_0 := mload(0x2000)", "let var0 := addmod(mulmod(0, tau, r), a_0, r)",
            "let a_1 := mload(0x2020)",
            "let var1 := addmod(mulmod(var0, tau, r), a_1, r)"]

/-- YE:138-196: the five rejections and then the exact loop text. The adjacency test is
    what makes this an optimisation and not a rewrite: three inputs whose tails are not
    0x20 apart must fall back to the caller's generic path. -/
def lookupSharedPrefix_ok : Bool :=
  let tail (i : Nat) : List (Expression QVMFr) := [eA 0, eA i]
  let okChunk := [tail 1, tail 2, tail 3]
  let two := [tail 1, tail 2]
  let ragged := [tail 1, [eA 0], tail 3]
  let badPrefix := [tail 1, [eA 1, eA 2], tail 3]
  let nonAdjacent := [tail 1, tail 2, [eA 0, eA 5]]
  (match lookupSharedPrefixFPlusBeta two "v" "b" "p" ev with | .ok (none, _) => true | _ => false)
    && (match lookupSharedPrefixFPlusBeta [] "v" "b" "p" ev with | .ok (none, _) => true | _ => false)
    && (match lookupSharedPrefixFPlusBeta [[], [], []] "v" "b" "p" ev with | .ok (none, _) => true | _ => false)
    && (match lookupSharedPrefixFPlusBeta ragged "v" "b" "p" ev with | .ok (none, _) => true | _ => false)
    && (match lookupSharedPrefixFPlusBeta badPrefix "v" "b" "p" ev with | .ok (none, _) => true | _ => false)
    && (match lookupSharedPrefixFPlusBeta nonAdjacent "v" "b" "p" ev with | .ok (none, _) => true | _ => false)
    && (match lookupSharedPrefixFPlusBeta okChunk "tau" "beta" "0x9000" ev with
        | .ok (some ls, _) =>
            ls == [ "let a_0 := mload(0x2000)",
              "let var0 := addmod(mulmod(0, tau, r), a_0, r)",
              "let var1 := mulmod(var0, tau, r)",
              "for { let q_lookup_shared_i := 0 } lt(q_lookup_shared_i, 3) { q_lookup_shared_i := add(q_lookup_shared_i, 1) }} {",
              "let q_lookup_shared_off := shl(5, q_lookup_shared_i)",
              "let q_lookup_shared_tail := mload(add(0x2020, q_lookup_shared_off))",
              "let q_lookup_shared_compressed := addmod(var1, q_lookup_shared_tail, r)",
              "mstore(add(0x9000, q_lookup_shared_off), addmod(q_lookup_shared_compressed, beta, r))",
              "}" ]
        | _ => false)

def emptyGC : GateComputation QVMFr :=
  { lines := [], var := "", simpleSelectorIndex := none, gateIndex := 0, gateName := "",
    constraintIndex := 0, constraintName := "", polynomialIndex := 0 }

/-- HAZARD 3 (exact product, gates): the whole gate list of the fixture, line for line,
    with the four tag fields. Note g1_c1's variable is a_3 and not a varN: a bare column
    query is a NAMED slot, and the per-polynomial reset means the second polynomial of the
    second gate starts from a clean cache. -/
def gateComputations_exact_ok : Bool :=
  match runOpt gateComputationsTagged ev with
  | some gs =>
      gs.length == 3
        && gs.map (fun g => (g.gateIndex, g.constraintIndex, g.polynomialIndex))
            == [(0, 0, 0), (1, 0, 0), (1, 1, 1)]
        && gs.map (fun g => g.gateName) == ["g0", "g1", "g1"]
        && gs.map (fun g => g.constraintName) == ["g0_c0", "g1_c0", "g1_c1"]
        && gs.map (fun g => g.simpleSelectorIndex) == [some 0, none, none]
        && (gs.getD 0 emptyGC).lines
            == ["let a_0 := mload(0x2000)", "let a_1 := mload(0x2020)",
                "let var0 := mulmod(a_0, a_1, r)"]
        && ((gs.drop 1).getD 0 emptyGC).lines
            == ["let var0 := 0x5", "let a_2 := mload(0x2040)", "let var1 := 0x3",
                "let var2 := mulmod(a_2, var1, r)", "let var3 := addmod(var0, var2, r)"]
        && ((gs.drop 2).getD 0 emptyGC).lines == ["let a_3 := mload(0x2060)"]
  | none => false

/-- HAZARD 3 (exact product, permutation): all four families. The parts a port loses are
    pinned here: the delta ladder multiplies by 0x7 AFTER each column except the last (so
    a one-column chunk has no ladder line at all), the initial power is
    DELTA^(set_idx * chunk_len) = 7^3 = 0x157 for the second set, and the left/right
    products are REASSIGNMENTS and not lets. -/
def permutationComputations_exact_ok : Bool :=
  match runOpt permutationComputations ev with
  | some ps =>
      ps.length == 5
        && (ps.getD 0 ([], "")).1
            == ["let var0 := mload(L_0_MPTR)",
                "let var1 := addmod(1, sub(r, mload(0x2c00)), r)",
                "let var2 := mulmod(var0, var1, r)"]
        && (ps.getD 1 ([], "")).1
            == ["let var0 := mload(L_LAST_MPTR)",
                "let var1 := mulmod(mload(0x2c20), mload(0x2c20), r)",
                "let var2 := addmod(var1, sub(r, mload(0x2c20)), r)",
                "let var3 := mulmod(var0, var2, r)"]
        && (ps.getD 2 ([], "")).1
            == ["let var0 := mload(L_0_MPTR)",
                "let var1 := addmod(mload(0x2c20), sub(r, mload(0x3000)), r)",
                "let var2 := mulmod(var0, var1, r)"]
        && ((ps.getD 3 ([], "")).1).length == 28
        && ((ps.getD 4 ([], "")).1).length == 16
        && ((ps.getD 3 ([], "")).1.filter (fun l => l == "var13 := mulmod(var13, 0x7, r)")).length == 2
        && ((ps.getD 3 ([], "")).1).any (fun l =>
              l == "let var13 := mulmod(mulmod(var4, mload(X_MPTR), r), 0x1, r)")
        && ((ps.getD 4 ([], "")).1).any (fun l =>
              l == "let var9 := mulmod(mulmod(var4, mload(X_MPTR), r), 0x157, r)")
        && !((ps.getD 4 ([], "")).1).any (fun l => l.startsWith "var9 := mulmod(var9,")
        && ps.map (fun q => q.2) == ["var2", "var3", "var2", "var19", "var13"]
  | none => false

/-- YE:265-267: no permutation z slots means no permutation identities at all, and the
    emitter must not even reset. -/
def permutationComputations_empty_ok : Bool :=
  let e := Evaluator.new (qFrCtx qDelta) qCs { qMeta with numPermutationZs := 0 } qData
  runOpt permutationComputations e == some []
    && runOpt lookupComputations
        (Evaluator.new (qFrCtx qDelta) qCs { qMeta with numLookups := 0 } qData) == some []
    && runOpt trashcanComputations
        (Evaluator.new (qFrCtx qDelta) qCs { qMeta with numTrashcans := 0 } qData) == some []

/-- HAZARD 3 (exact product, lookup): boundary, one helper block for the single chunk of
    two parallel inputs, and the accumulator. The helper is the prefix/suffix construction
    with NO inversion anywhere - the divergence attack.md records against
    proofs/src/plonk/logup.rs:457-459 - and the duplicate-line class is pinned here: each
    'let varN := 1' appears exactly once. -/
def lookupComputations_exact_ok : Bool :=
  match runOpt lookupComputations ev with
  | some ls =>
      ls.length == 3
        && (ls.getD 0 ([], "")).1
            == ["let var0 := mload(L_0_MPTR)", "let var1 := mload(L_LAST_MPTR)",
                "let var2 := addmod(var0, var1, r)",
                "let var3 := mulmod(var2, mload(0x2d20), r)"]
        && ((ls.getD 1 ([], "")).1.filter (fun l => l == "let var8 := 1")).length == 1
        && ((ls.getD 1 ([], "")).1.filter (fun l => l == "let var10 := 1")).length == 1
        && ((ls.getD 1 ([], "")).1.filter (fun l => l == "let var12 := mulmod(var8, var11, r)")).length == 1
        && (ls.getD 1 ([], "")).1
            == ["let var0 := mload(BETA_MPTR)", "let var1 := mload(THETA_MPTR)",
                "let a_0 := mload(0x2000)",
                "let var2 := addmod(mulmod(0, var1, r), a_0, r)",
                "let var3 := addmod(var2, var0, r)", "let var4 := mload(THETA_MPTR)",
                "let a_1 := mload(0x2020)",
                "let var5 := addmod(mulmod(0, var4, r), a_1, r)",
                "let var6 := addmod(var5, var0, r)", "let var7 := var3",
                "var7 := mulmod(var7, var6, r)", "let var8 := 1",
                "let var9 := mulmod(var8, var3, r)", "let var10 := 1",
                "let var11 := mulmod(var10, var6, r)",
                "let var12 := mulmod(var8, var11, r)",
                "let var13 := mulmod(var9, var10, r)",
                "var12 := addmod(var12, var13, r)",
                "let var14 := mulmod(mload(0x3480), var7, r)",
                "let var15 := addmod(var14, sub(r, var12), r)"]
        && (ls.getD 2 ([], "")).1
            == ["let var0 := mload(L_LAST_MPTR)", "let var1 := mload(L_BLIND_MPTR)",
                "let var2 := addmod(1, sub(r, addmod(var0, var1, r)), r)",
                "let var3 := mload(BETA_MPTR)", "let var4 := mload(0x3480)",
                "var4 := addmod(var4, mload(0x34a0), r)", "let f_1 := mload(0x2420)",
                "let var5 := mulmod(f_1, var4, r)",
                "let var6 := addmod(mload(0x2f20), sub(r, addmod(mload(0x2d20), var5, r)), r)",
                "let var7 := mload(THETA_MPTR)", "let f_2 := mload(0x2440)",
                "let var8 := addmod(mulmod(0, var7, r), f_2, r)",
                "let var9 := addmod(var8, var3, r)",
                "let var10 := addmod(mulmod(var6, var9, r), mload(0x3400), r)",
                "let var11 := mulmod(var2, var10, r)"]
  | none => false

/-- HAZARD 3 (exact product, trash): the whole block for one trash argument. -/
def trashcanComputations_exact_ok : Bool :=
  match runOpt trashcanComputations ev with
  | some ts =>
      ts.length == 1
        && (ts.getD 0 ([], "")).1
            == ["let var0 := mload(TRASH_CHALLENGE_MPTR)", "let a_3 := mload(0x2060)",
                "let a_4 := mload(0x2080)", "let var1 := mulmod(a_3, a_4, r)",
                "let var2 := addmod(mulmod(0, var0, r), var1, r)",
                "let f_1 := mload(0x2420)", "let var3 := addmod(1, sub(r, f_1), r)",
                "let var4 := mulmod(var3, mload(0x3a00), r)",
                "let var5 := addmod(var2, sub(r, var4), r)"]
  | none => false

/-- The empty-trashcan arm of YE:671-697, its own gate so a port that always emits the
    challenge load fails here and not by changing the non-empty block above. -/
def trashcanEmptyNoChallengeLoad_ok : Bool :=
  let cs : ConstraintSystem QVMFr :=
    { qCs with trashcans := #[{ name := "tr0", selector := eF 1, constraintExpressions := #[] }] }
  let e := Evaluator.new (qFrCtx qDelta) cs qMeta qData
  match runOpt trashcanComputations e with
  | some ts =>
      ((ts.getD 0 ([], "")).1).any (fun l => l == "let var0 := 0")
        && !((ts.getD 0 ([], "")).1).any (fun l => l.contains "TRASH_CHALLENGE_MPTR")
  | none => false

/-- HAZARD 2, read at #eval time (D-P19): var_cache is touched at exactly six lines in the
    Rust - the field, the new() initialiser, the reset, contains_key, the index and the
    insert. If a future commit
    adds an iteration, a keys(), a values() or a len(), this gate reddens and the
    assoc-list rendering has to be re-argued. -/
def varCacheReadSites_ok (src : String) : Bool :=
  let hits := (src.splitOn "\n").filterMap (fun (l : String) =>
    if l.contains "var_cache" then some (trimStr l) else none)
  hits.length == 6
    && (hits.filter (fun l => l.contains "Default::default()")).length == 2
    && (hits.all fun l => ! (l.contains ".iter()" || l.contains ".keys()"
      || l.contains ".values()" || l.contains ".len()" || l.contains "for "))
    && src.contains "self.var_cache.borrow().contains_key(&value)"
    && src.contains "self.var_cache.borrow()[&value].clone()"
    && src.contains "self.var_cache.borrow_mut().insert(value.clone(), var.clone())"

/-- The DELTA literal is COMPUTED from the field constant and never hard-coded, which is
    what lowering/tests.rs:3467-3474 asserts of the Rust and what the R9 parameterisation
    has to preserve. Two directions: changing the parameter changes the emitted literal,
    and the literal for delta = 7 is not a token in the Rust source. -/
def deltaLiteral_computedNotHardcoded_ok (src : String) : Bool :=
  src.contains "Fq::DELTA.pow_vartime([(set_idx * chunk_len) as u64])"
    && src.contains "let delta = fe_to_u256::<Fq>(&Fq::DELTA);"
    && (match runOpt permutationComputations (Evaluator.new (qFrCtx 5) qCs qMeta qData) with
        | some ps => ((ps.getD 3 ([], ""))).1.any (fun l => l.endsWith ", 0x5, r)")
        | none => false)
    && (match runOpt permutationComputations (Evaluator.new (qFrCtx 9) qCs qMeta qData) with
        | some ps => ((ps.getD 3 ([], ""))).1.any (fun l => l.endsWith ", 0x9, r)")
        | none => false)
    && ! src.contains "0x157"

/-- THE NEGATION IS NOT HERE. The brief asks whether yul_emit.rs is where the verifier's
    -nu_y(x) lives, which would close D-P20's "Yul-side and modelled nowhere". It is not:
    this file only DOCUMENTS the fact (YE:13-16) and emits per-identity differences. The
    batch negation is one template line, and this gate pins both halves against the
    artifacts at #eval time. -/
def negationNotInThisFile_ok (ye : String) : Bool :=
  ye.contains "The generated verifier later stores "
    && ! ye.contains "linearization_expected_eval"
    && ! ye.contains "sub(r, quotient_eval_numer)"

/-- HAZARD 4 (the second-implementation check), case 1: a gate product. The Emitter walks
    a halo2 Expression and prints Yul; the QVM route evaluates a QuotientExpr. Same memory,
    same field, same answer. -/
def qvmAgree_gateProduct_ok : Bool :=
  let (ls, v) := match evaluate (eMul (eA 0) (eA 1)) ev with
    | .ok (r, _) => r
    | .error _ => ([], "")
  agree ls v (cMul (cMemAt (aAddr 0)) (cMemAt (aAddr 1)))

/-- Case 2: the sum-fusion path, which is the emitter's own optimisation and has no QVM
    counterpart at all - so agreement here checks the fused arithmetic (5 + 3*a2) rather
    than a shared traversal. -/
def qvmAgree_sumFusion_ok : Bool :=
  let (ls, v) := match evaluate (eAdd (eScale (eA 2) 3) (eC 5)) ev with
    | .ok (r, _) => r
    | .error _ => ([], "")
  agree ls v (cAdd (cLit 5) (cMul (cMemAt (aAddr 2)) (cLit 3)))

/-- Case 3: the permutation boundary identities, straight out of permutationComputations
    rather than hand-written, so the whole emitter is in the loop. -/
def qvmAgree_permBoundary_ok : Bool :=
  match runOpt permutationComputations ev with
  | some ps =>
      agree (ps.getD 0 ([], "")).1 (ps.getD 0 ([], "")).2
        (cMul (cMemAt 0x1000) (cAdd (cLit 1) (cNeg (cMemAt (zAddr 0)))))
        && agree (ps.getD 1 ([], "")).1 (ps.getD 1 ([], "")).2
          (cMul (cMemAt 0x1020)
            (cAdd (cMul (cMemAt (zAddr 1)) (cMemAt (zAddr 1))) (cNeg (cMemAt (zAddr 1)))))
        && agree (ps.getD 2 ([], "")).1 (ps.getD 2 ([], "")).2
          (cMul (cMemAt 0x1000)
            (cAdd (cMemAt (zAddr 1)) (cNeg (cMemAt (zlAddr 0)))))
  | none => false

/-- Case 4: the per-set product equality, the largest identity in the file - both product
    ladders, the beta*x*DELTA^(set*chunk) seed and the delta ladder. This is the closest
    thing in the tree to qvm_yul_refines: two independent implementations of one identity,
    one a text emitter and one a bytecode reference interpreter. -/
def qvmAgree_permProduct_ok : Bool :=
  match runOpt permutationComputations ev with
  | some ps =>
      let (ls, v) := ps.getD 3 ([], "")
      let c0 := cMemAt (aAddr 0)
      let c1 := cMemAt (aAddr 1)
      let c2 := cMemAt (fAddr 1)
      let beta := cMemAt 0x1060
      let gamma := cMemAt 0x1080
      let x := cMemAt 0x10a0
      let left := cMul (cMemAt (znAddr 0))
        (cMul (cMul (cAdd (cAdd c0 (cMul beta (cMemAt (sAddr 0)))) gamma)
          (cAdd (cAdd c1 (cMul beta (cMemAt (sAddr 1)))) gamma))
          (cAdd (cAdd c2 (cMul beta (cMemAt (sAddr 2)))) gamma))
      let d0 := cMul (cMul beta x) (cLit 1)
      let d1 := cMul d0 (cLit 7)
      let d2 := cMul d1 (cLit 7)
      let right := cMul (cMemAt (zAddr 0))
        (cMul (cMul (cAdd (cAdd c0 d0) gamma) (cAdd (cAdd c1 d1) gamma))
          (cAdd (cAdd c2 d2) gamma))
      let active := cAdd (cLit 1) (cNeg (cAdd (cMemAt 0x1020) (cMemAt 0x1040)))
      agree ls v (cMul active (cAdd left (cNeg right)))
  | none => false

/-- Case 5: the trash identity, including the theta fold whose first step multiplies by
    zero and the (1 - q) * trash subtraction. -/
def qvmAgree_trash_ok : Bool :=
  match runOpt trashcanComputations ev with
  | some ts =>
      let (ls, v) := ts.getD 0 ([], "")
      agree ls v (cAdd (cMul (cMemAt (aAddr 3)) (cMemAt (aAddr 4)))
        (cNeg (cMul (cAdd (cLit 1) (cNeg (cMemAt (fAddr 1)))) (cMemAt (trashAddr 0)))))
  | none => false

/-- Case 6: the lookup helper block - the prefix/suffix product with no inversion anywhere. -/
def qvmAgree_lookupHelper_ok : Bool :=
  match runOpt lookupComputations ev with
  | some ls =>
      let (block, v) := ls.getD 1 ([], "")
      let f0 := cAdd (cMemAt (aAddr 0)) (cMemAt 0x1060)
      let f1 := cAdd (cMemAt (aAddr 1)) (cMemAt 0x1060)
      let sum := cAdd (cMul (cLit 1) f1) (cMul f0 (cLit 1))
      agree block v (cAdd (cMul (cMemAt (hAddr 0)) (cMul f0 f1)) (cNeg sum))
  | none => false

/-- Case 7, and the sharpest one: the q_pow5 peephole against the QVM's own repeated
    multiplication. The emitter prints a call to a Yul helper; the reference interpreter
    has no pow opcode at all, so agreement means the helper's CONTRACT (x^5 mod r) is what
    the emitted call claims. This is also the gate that would catch a q_pow5 that meant x^4
    or x^6. -/
def qvmAgree_pow5_ok : Bool :=
  let a := eA 0
  let expr := eMul (eMul (eMul (eMul a a) a) a) a
  let (ls, v) := match evaluate expr evPow5 with
    | .ok (r, _) => r
    | .error _ => ([], "")
  ls == ["let a_0 := mload(0x2000)", "let var0 := q_pow5(a_0)"]
    && agree ls v (cMul (cMul (cMul (cMul (cMemAt (aAddr 0)) (cMemAt (aAddr 0)))
      (cMemAt (aAddr 0))) (cMemAt (aAddr 0))) (cMemAt (aAddr 0)))

/-- The cross-check is not vacuous: a deliberately wrong QuotientExpr (x^4 instead of x^5,
    and the same power at the wrong slot) must NOT agree. Without this the gate could be
    satisfied by a reader that ignores its input. -/
def qvmCrossCheck_notVacuous_ok : Bool :=
  let a := eA 0
  let expr := eMul (eMul (eMul (eMul a a) a) a) a
  let (ls, v) := match evaluate expr evPow5 with
    | .ok (r, _) => r
    | .error _ => ([], "")
  let p5 := fun x => cMul (cMul (cMul (cMul x x) x) x) x
  ! agree ls v (p5 (cMemAt (aAddr 0)) |> fun t => cNeg t)
    && ! agree ls v (p5 (cMemAt (aAddr 1)))
    && ! agree ls v (cMul (cMul (cMul (cMemAt (aAddr 0)) (cMemAt (aAddr 0)))
      (cMemAt (aAddr 0))) (cMemAt (aAddr 0)))
    && agree ls v (p5 (cMemAt (aAddr 0)))

/-- The Yul reader is itself a second implementation, so it gets pinned before anything
    leans on it: literals, mload of a literal and of a symbol, addmod, mulmod, sub(r, _),
    nesting and q_pow5. -/
def yulReader_ok : Bool :=
  (match yulRun ["let a := 0x7", "let b := mload(0x2000)", "let c := addmod(a, b, r)",
                 "let d := mulmod(c, 0x2, r)", "c := sub(r, d)", "let e := q_pow5(0x3)"]
      "d" { mem := xMem, vars := [] } with
    | .ok (v, _) => v == qvmFrMul (qvmFrAdd 7 (xMem.literal 0x2000).1) 2
    | .error _ => false)
    && (match yulRun ["let e := q_pow5(0x3)"] "e" { mem := xMem, vars := [] } with
        | .ok (v, _) => v == 243
        | .error _ => false)
    && (match yulRun ["let a := mload(L_0_MPTR)"] "a" { mem := xMem, vars := [] } with
        | .ok (v, _) => v == (xMem.literal 0x1000).1
        | .error _ => false)

/-- The reader rejects what the emitter never produces, so a malformed line cannot be
    silently read as zero. -/
def yulReaderRejects_ok : Bool :=
  (match yulRun ["let a := mload(NOT_A_SYMBOL)"] "a" { mem := xMem, vars := [] } with
    | .error _ => true | .ok _ => false)
    && (match yulRun ["let a := 7"] "b" { mem := xMem, vars := [] } with
      | .error _ => true | .ok _ => false)
    && (match yulRun ["not an assignment"] "a" { mem := xMem, vars := [] } with
      | .error _ => true | .ok _ => false)
    && (match yulRun ["let a := mload(0x2000)"] "a" { mem := xMem, vars := [] } with
      | .ok _ => true | .error _ => false)

/-- R-41 non-vacuity of the cross-check: the two routes differ in TEXT while agreeing in
    VALUE. If a future change made the emitter produce the QVM's own shape it would stop
    being a second implementation, and this is what says so. -/
def twoRoutes_differInTextAgreeInValue_ok : Bool :=
  let (ls, v) := match evaluate (eMul (eA 0) (eA 1)) ev with
    | .ok (r, _) => r
    | .error _ => ([], "")
  ls.length == 3 && v == "var0"
    && (ls.all fun l => ! (l.contains "PUSH" || l.contains "q_pow5"))
    && agree ls v (cMul (cMemAt (aAddr 0)) (cMemAt (aAddr 1)))

#eval Midfall.Generator.QuotientEvaluatorKats.evaluatorArtifactReachable_ok <$> Midfall.Generator.QuotientEvaluatorKats.readYeArtifact -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.pointerDistinct_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.nextVarAndReset_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.varCacheReuse_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.varCacheNamedSlot_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.freshLetBypassesCache_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.pow5UsedFlipsExactlyOnQPow5_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.pow5BaseRecognition_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.u256String_and_columnEvalVar_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.expressionMemoryPtr_rejections_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.evalAt_threeArms_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.virtualSelectorPanic_site_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.sumFusionPredicate_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.compressTwoZeros_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.lookupSharedPrefix_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.gateComputations_exact_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.permutationComputations_exact_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.permutationComputations_empty_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.lookupComputations_exact_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.trashcanComputations_exact_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.trashcanEmptyNoChallengeLoad_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.varCacheReadSites_ok <$> Midfall.Generator.QuotientEvaluatorKats.readYeArtifact -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.deltaLiteral_computedNotHardcoded_ok <$> Midfall.Generator.QuotientEvaluatorKats.readYeArtifact -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.negationNotInThisFile_ok <$> Midfall.Generator.QuotientEvaluatorKats.readYeArtifact -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.yulReader_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.yulReaderRejects_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_gateProduct_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_sumFusion_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_permBoundary_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_permProduct_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_trash_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_lookupHelper_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmAgree_pow5_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.qvmCrossCheck_notVacuous_ok -- expect true
#eval Midfall.Generator.QuotientEvaluatorKats.twoRoutes_differInTextAgreeInValue_ok -- expect true

end Midfall.Generator.QuotientEvaluatorKats
