-- |
-- Midfall.Generator.Quotient.QuotientBlocks
--
-- THE THREE STRUCTURED FAMILY BLOCKS, the compact assembly point, and the Yul-to-AST bridge
-- that P-10 named as blocked on the Evaluator. Ported from
-- proofs/solidity-verifier/src/lowering/quotient.rs (2147 lines at git HEAD, cited as Q)
-- with the vm/mod.rs items it needs (4336 lines at HEAD, cited as QVM) and one item from
-- lowering/diagnostics.rs (cited as DIAG). Work package P-10c.
--
-- ITEMS, all six, with their real HEAD ranges (the brief's are corrected in the report):
-- structured_permutation_loop_block (Q:1471-1680), structured_lookup_loop_block
-- (Q:1688-1934), structured_trash_loop_block (Q:1941-1993),
-- compact_quotient_computation_blocks (Q:2000-2099), the three-function bridge
-- quotient_identity_expr / quotient_yul_expr / quotient_expr_from_plonk_expr
-- (Q:972-974, Q:978-984, Q:987-993), and quotient_identity_parts (Q:804-969).
--
-- WHY THIS WAS BLOCKED AND WHAT UNBLOCKED IT. FoldCompute.lean:39-57 declined the first
-- five because they need the Evaluator's four &self methods (reset_locals,
-- evaluate_expression, compress_expressions_with_challenge_var,
-- lookup_shared_prefix_f_plus_beta) and Data's permutation_z_evals / lookup_evals /
-- trashcan_evals read through it. P-09h landed those in Evaluator.lean, so the blocks are
-- now writable. Nothing here needed a new record except QuotientIdentityParts
-- (QVM:228-244), which VmTypes.lean:56 lists as unported and which is declared below.
--
-- UNOWNED ITEMS PICKED UP (hazard 5's second half; the FoldCompute.lean:72-81 precedent).
-- Nine items outside the six named by the brief are ported because the six cannot be
-- written without them. None is in direct/{mod,emit,layout,validate}.rs, none is in the VK
-- row, none is in the template row:
--   * QVM:4131-4133 fr_delta_literal - the permutation block's 'let delta :=' literal.
--   * Q:1117-1204 push_mstore_mload_literal_runs - the permutation block stages six eval
--     tables through it. FoldCompute.lean:62 lists it as unported; it needs nothing the
--     tree lacks (yulMloadLiteralExpr is FoldCompute's own, QVM:4236-4244).
--   * Q:1420-1439 structured_lookup_max_parallel - the lookup block's scratch layout.
--     THE BRIEF MIS-FILES THIS: its table row puts 1419-1464 under "memory-layout, not
--     Evaluator", but max_parallel is a direct callee of structured_lookup_loop_block
--     (Q:1701), so the lookup block cannot be ported without it. The other two items of
--     that range (structured_lookup_scratch_words Q:1442-1445, native_callback_scratch_words
--     Q:1448-1464) are NOT ported here: nothing in this package calls them, and they are
--     the memory-layout row's, exactly as the brief says.
--   * QVM:2965-2987 ptr_to_quotient_mem, QVM:2955-2962 word_to_quotient_expr,
--     QVM:2856-2867 trait QuotientExpressionEnv, QVM:2870-2891 quotient_expr_from_expression,
--     QVM:2894-2952 DataQuotientExpressionEnv and its impl - the whole chain under
--     quotient_expr_from_plonk_expr. VmTypes.lean:104-108 already names QVM:2904-2979 as
--     panic sites of the unported builder.
--   * DIAG:225-247 trash_manifest_name - the trash arm of quotient_identity_parts (Q:924).
--     FINDING: this is a diagnostics.rs item, and diagnostics is P-14, which PLAN 14.8 CUT.
--     The brief's table says quotient_identity_parts "needs the bridge above" and stops
--     there; it also needs this. Its observable content is two lookups into
--     vk.cs().gates() and vk.cs().trashcans(), both of which the Evaluator already carries,
--     so it is ported over the ConstraintSystem with the receiver deviation recorded at the
--     site. If the orchestrator would rather not own a diagnostics.rs item, the trash arm of
--     quotient_identity_parts is the only thing that stops, and nothing else here does.
--
-- WHAT HAZARD 3 ASKS, ANSWERED AT THE SITE AND IN THE REPORT. The three loop blocks are
-- the PRODUCERS of the family fold sites and NOT the populator of the function names.
-- push_structured_fold (Q:1364-1397) builds every Weighted FoldSite with
-- 'function: String::new()' (Q:1372, Q:1381) and this file changes nothing about that:
-- FoldTypes.lean:226-230 already records the split and it is still exactly right. The
-- names are stamped by direct/emit.rs:925-930 (family sites, 'function: name.to_string()')
-- and built whole by direct/emit.rs:431-442 (gate sites, 'identity_function_name(j)'), and
-- the only shipped caller that passes StructuredFold::Weighted at all is
-- quotient_direct.rs:313-390 (direct_quotient_rendering), which is M10 by P-09's own row
-- (plans/P-09-quotient-vm.md:14 lists quotient_direct.rs with quotient_numerator/direct/*).
-- So the M10 deferral is NOT narrowed in the way the brief hypothesises. What IS newly
-- reachable is one step short of it: the site LIST - labels, weights, buckets, trace lines
-- - is now computable from a real circuit, so emit.rs's remaining job is a rename and a
-- calls map, not an enumeration. compact_quotient_computation_blocks, the one assembly
-- point this file does port, passes StructuredFold::Horner at all three call sites (Q:2039,
-- Q:2057, Q:2074), so it records NO sites at all - compactBlocksHornerRecordsNoSites_ok.
--
-- WHAT MOVED (Lean is order-sensitive; plans README standing note 3).
-- 1. The bridge (Q:972-993 and its QVM chain) comes first: quotient_identity_parts (Q:804)
--    calls all three bridge functions, which in the Rust sit 170 lines BELOW it.
-- 2. push_mstore_mload_literal_runs (Q:1117) and structured_lookup_max_parallel (Q:1420)
--    come before the blocks that call them.
-- 3. The three blocks come before compact_quotient_computation_blocks (Q:2000), which
--    calls all three. Rust order preserved.
-- 4. QuotientIdentityParts (QVM:228) is declared before quotient_identity_parts (Q:804),
--    which returns it; in the Rust it is 575 lines earlier in a different file.
-- None of these moves changes a line of emitted text.
--
-- R2/R4/R5/R6/R9 DEVIATIONS, each recorded at its site.
-- * Vec -> List throughout (the Generator row; plans README standing note 4).
-- * R9: the trait QuotientExpressionEnv (QVM:2856) becomes a record of five functions, and
--   the Fq dictionary reaches quotient_expr_from_expression as an explicit 'repr'
--   projection because Lean has no associated items to reach through - the treatment P-09h
--   gave FieldCtx (Evaluator.lean:63-75). DataQuotientExpressionEnv keeps the Rust's two
--   fields and gains nothing.
-- * R4: the panics in this range are real release-profile aborts and all of them are
--   observable: the assert_eq! at Q:827-831 and the four at Q:941-960 (assert_eq! is NOT
--   compiled out; only debug_assert! is), the .expect at Q:848, Q:901, Q:1518, the direct
--   indices at Q:1728, Q:1776, Q:1885, Q:1974, and the five in the QVM chain. 'meta' is a
--   Lean reserved word, so every parameter the Rust calls 'meta' is 'meta_' (plans README
--   standing note 3); 'instance' is too, so the env's fourth method is 'instance_'.
-- * The two fault taxonomies of this tree meet here for the first time. The Evaluator row
--   aborts with Midfall.Halo2.Fault (Exec/Error.lean:56); the VM row aborts with QVMFault
--   (VmReference.lean:284). The only place they touch is compact_quotient_computation_blocks,
--   which calls the Evaluator and FoldCompute's direct_quotient_block (an M) in one
--   expression: liftQVM renders the QVMFault through its own message and re-wraps it as a
--   Halo2 panic, so the site string survives and neither file's taxonomy has to widen. The
--   panic class is the only class direct_quotient_block can produce, and
--   liftQVMPreservesSite_ok says so.
-- * R5: usize -> Nat. '(num_sets - 1) * 0x20' (Q:1491, Q:1587) is a plain usize subtraction
--   guarded by the num_permutation_zs == 0 early return, so it cannot wrap; '(k - 1) * 0x20'
--   (Q:1841) is guarded by k != 0 (Q:1760). weight_of's checked_sub stays FoldCompute's.
-- * R3: the two 'continue' statements in the lookup block (Q:1770, Q:1790) are the two
--   early arms of an if/else chain, which is the same control flow; the 'while' loops of
--   push_mstore_mload_literal_runs (Q:1127, Q:1160) become index-free list recursion.
-- * 'List.zipIdx' yields (element, index), the reverse of Rust's '.enumerate()' (plans
--   README standing note; hazard 2 of this package). Every one of the ten enumerate sites in
--   this range swaps: Q:1512, Q:1539, Q:1726, Q:1750 (a zip THEN an enumerate, so the
--   element is a PAIR), Q:1802, Q:1957, Q:854, Q:878, Q:895, Q:921. Each is annotated at the
--   point of use and zipIdxSites_ok re-pins the swap against the reference source at #eval
--   time (D-P19).
-- * 'List.range'' is NOT used anywhere in this file. It takes a COUNT, not an inclusive end
--   (plans README standing note 1 - the false defect claim P-09h made and the orchestrator
--   measured away). The two Rust loop ranges here go through FoldLoop.header, which P-10a
--   already pins, or through hand-written Yul loop headers, which are text and not indices.

import Midfall.Common.Bytes
import Midfall.Generator.Api
import Midfall.Generator.Encoding
import Midfall.Generator.Filters
import Midfall.Generator.Layout
import Midfall.Generator.Models
import Midfall.Generator.Protocol
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.FoldTypes
import Midfall.Generator.Quotient.FoldCompute
import Midfall.Generator.Quotient.Evaluator

namespace Midfall.Generator.QuotientBlocks

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientFold
  Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientEvaluator
  Midfall.Generator.QuotientBuilder

/-! ## Sites (R4) -/

/-- R4 site helper for quotient.rs. P-09h's 'site' (Evaluator.lean:165) hard-codes the
    yul_emit path, so a Q panic needs its own constructor or the cite would name the wrong
    file. -/
def siteQ (line : Nat) (msg : String) : String :=
  qPath ++ ":" ++ toString line ++ " (" ++ msg ++ ")"

/-- The same for vm/mod.rs, whose items this package picks up. -/
def siteQVM (line : Nat) (msg : String) : String :=
  QuotientFoldCompute.qvmPath ++ ":" ++ toString line ++ " (" ++ msg ++ ")"

/-- R4: an abort as a Halo2 panic. -/
def panicF {α : Type} (site : String) : Except Fault α := .error (Fault.panic site)

/-- R4: 'Option' + '.expect(msg)' at a Q line. -/
def expectQ {α : Type} (o : Option α) (line : Nat) (msg : String) : Except Fault α :=
  match o with | some v => .ok v | none => panicF (siteQ line msg)

/-- R4: a 'Vec' index '[i]' at a Q line: out of range aborts in BOTH profiles. -/
def atQ {α : Type} (xs : List α) (i : Nat) (line : Nat) (msg : String) : Except Fault α :=
  listGetMut xs i (siteQ line msg)

/-- R4: the same two, cited to vm/mod.rs, for the picked-up bridge items. -/
def expectQVM {α : Type} (o : Option α) (line : Nat) (msg : String) : Except Fault α :=
  match o with | some v => .ok v | none => panicF (siteQVM line msg)

def atQVM {α : Type} (xs : List α) (i : Nat) (line : Nat) (msg : String) : Except Fault α :=
  listGetMut xs i (siteQVM line msg)

/-- The two fault taxonomies, joined. See the header: the only thing this does is carry the
    site string across, because QVMFault.message renders '.panic site' as 'site' itself
    (VmReference.lean:334), so nothing is lost for the class that can actually occur. -/
def liftQVM {α : Type} (x : Except QVMFault α) : Except Fault α :=
  match x with
  | .ok v => .ok v
  | .error f => .error (Fault.panic (QVMFault.message f))

/-! ## The state the family blocks thread (Lean scaffolding, not a Rust item)

HAZARD 3'S PLUMBING. Each of the three blocks has four things moving through it in the
Rust: the '&Evaluator' (whose three RefCells survive the call), the local
'block: Vec<String>', the '&RefCell<Vec<FoldSite>>' carried inside
'StructuredFold::Weighted' (Q:82), and the StructuredFold itself. P-10b turned the second
and third into return values (pushStructuredFold returns 'List String × List FoldSite',
FoldCompute.lean:387); this file threads all four, because a family block is a hundred
pushes deep and returning pairs at every step would hide what is being threaded. 'fold'
stays an explicit parameter of every block: it is one in the Rust too. -/

structure FamilyState (F : Type) where
  /-- The '&Evaluator<'_>' parameter (Q:1474, Q:1692, Q:1945). -/
  ev : Evaluator F
  /-- The '&mut Vec<String>' the block pushes into. -/
  block : List String
  /-- The '&RefCell<Vec<FoldSite>>' inside the Weighted arm (Q:82). -/
  sites : List FoldSite

abbrev FM (F : Type) (α : Type) := StateT (FamilyState F) (Except Fault) α

/-- One 'block.push(line)'. -/
def emit {F : Type} (line : String) : FM F Unit :=
  modify fun st => { st with block := st.block ++ [line] }

/-- Several pushes in order, i.e. 'block.append(&mut other)'. -/
def emitAll {F : Type} (lines : List String) : FM F Unit :=
  modify fun st => { st with block := st.block ++ lines }

/-- Run an Evaluator action: the Rust's 'evaluator.method(..)' through the shared borrow. -/
def evRun {F : Type} {α : Type} (x : E F α) : FM F α := do
  let st ← get
  let (a, ev) ← StateT.lift (x.run st.ev)
  modify fun st => { st with ev := ev }
  pure a

/-- Lift a plain 'Except Fault' computation (the Q/QVM panic helpers) into the family state. -/
def liftF {F : Type} {α : Type} (x : Except Fault α) : FM F α := StateT.lift x

/-- Run a plain 'Except Fault' computation against an explicit evaluator: the shape
    quotient_identity_parts needs, because in the Rust it CONSTRUCTS its Evaluator (Q:817)
    rather than borrowing one. -/
def evRunOn {F : Type} {α : Type} (x : E F α) (ev : Evaluator F) :
    Except Fault (α × Evaluator F) := x.run ev

/-- rust: Q:1353-1399 (push_structured_fold) as the three family blocks call it. The
    recorder is the state, so the Rust's 'sites.borrow_mut().push(site)' (Q:1396) and the
    two 'block.push' calls (Q:1393, Q:1395) both land here. The fold itself is FoldCompute's
    pushStructuredFold and is NOT re-derived (hazard 5's reuse rule). -/
def pushFold {F : Type} (fold : StructuredFold) (value : String) (pos : FoldPos) : FM F Unit := do
  let st ← get
  let (block, sites) := pushStructuredFold st.block st.sites fold value pos
  modify fun st => { st with block := block, sites := sites }

/-- Lean scaffolding: run one family block. The three results are the Rust's three shared
    objects - the local block, the site recorder, and the evaluator whose cells survive the
    call, which is why the caller threads the third into the next block. -/
def runFamilyBlock {F : Type} (ev : Evaluator F) (x : FM F (Option (List String))) :
    Except Fault (Option (List String) × List FoldSite × Evaluator F) :=
  match (x.run { ev := ev, block := [], sites := [] }) with
  | .ok (r, st) => .ok (r, st.sites, st.ev)
  | .error e => .error e

/-! ## The Yul-to-AST bridge (rust: Q:972-993 and the QVM chain under it) -/

/-- rust: Q:972-974 (quotient_identity_expr). "Return the typed quotient expression." One
    clone in the Rust; Lean has no borrow and no clone, so it is a projection. -/
def quotientIdentityExpr (identity : QuotientIdentity) : QuotientExpr := identity.expr

/-- rust: QVM:2965-2987 (ptr_to_quotient_mem) @formal-baseline. "Convert a generated memory
    pointer into the compact VM pointer form." UNOWNED ITEM PICKED UP. Four aborts, in the
    Rust's order: the loc assert (:2967), the negative integer (:2973), the negative token
    offset (:2977) BEFORE the token lookup, and the unsupported token name (:2979). The two
    'as u32' truncations are NOT emulated: VmTypes.lean:196-207 already records that
    QuotientMem's payloads are unbounded Nat and that out-of-width is a silent truncation
    rather than an abort, and quotientMem_noTruncation_ok pins that stance. -/
def ptrToQuotientMem (ptr : Ptr) : Except Fault QuotientMem :=
  match ptr.loc with
  | .calldata =>
      panicF (siteQVM 2967 "quotient expressions can only load memory-backed words")
  | .memory => match ptr.value with
    | .integer offset =>
        if offset >= 0 then .ok (QuotientMem.literal offset.toNat)
        else panicF (siteQVM 2973 "negative quotient memory pointer")
    | .identifier name off =>
        if off < 0 then panicF (siteQVM 2977 "negative quotient memory token offset")
        else match quotientMemTokenFromName name with
          | none => panicF (siteQVM 2979 ("unsupported quotient memory token: " ++ name))
          | some token =>
              .ok (if off == 0 then QuotientMem.token token
                   else QuotientMem.tokenOffset token off.toNat)

/-- rust: QVM:2955-2962 (word_to_quotient_expr) @formal-baseline. "Convert a memory-backed
    Word into a quotient memory load expression." UNOWNED ITEM PICKED UP. The assert_eq! on
    the location is a release abort (R4), and note it is checked TWICE - here and again
    inside ptr_to_quotient_mem - which the port keeps as two distinct sites rather than
    collapsing them into one guard. -/
def wordToQuotientExpr (word : Word) : Except Fault QuotientExpr :=
  match word.loc with
  | .calldata =>
      panicF (siteQVM 2957 "quotient expressions can only load memory-backed words")
  | .memory => do .ok (QuotientExpr.mem (← ptrToQuotientMem word.ptr))

/-- rust: QVM:2856-2867 (trait QuotientExpressionEnv) @formal-baseline. "Environment needed
    to lower Halo2 Expression<Fq> leaves." UNOWNED ITEM PICKED UP. R9: a trait becomes a
    record of functions. DEVIATION, RECORDED: the Rust's five methods return QuotientExpr
    and abort; these return 'Except Fault QuotientExpr', because R4 makes an abort
    observable and a Lean function that aborts must say so in its type. The usize/i32 pairs
    become Nat/Int (R5). -/
structure QuotientExpressionEnv where
  /-- rust: QVM:2858 ('fn selector') -/
  selector : Selector → Except Fault QuotientExpr
  /-- rust: QVM:2860 ('fn fixed') -/
  fixed : Nat → Int → Except Fault QuotientExpr
  /-- rust: QVM:2862 ('fn advice') -/
  advice : Nat → Int → Except Fault QuotientExpr
  /-- rust: QVM:2864 ('fn instance'). R2: 'instance' is a Lean reserved word, so the field
      is 'instance_' - the convention Protocol.lean:378-380 sets. -/
  instance_ : Nat → Int → Except Fault QuotientExpr
  /-- rust: QVM:2866 ('fn challenge') -/
  challenge : Nat → Except Fault QuotientExpr

/-- rust: QVM:2870-2891 (quotient_expr_from_expression) @formal-baseline. "Lower a Halo2
    expression into the compact quotient AST." UNOWNED ITEM PICKED UP.
    HAZARD 5'S REUSE RULE: this is the SECOND instantiation of the ported Expression.evaluate
    visitor (Circuit.lean:525) and not a third traversal. The ten closures are the Rust's ten
    arguments in the Rust's order, and the recursive arms combine AFTER both children, which
    is what makes the left-to-right abort order of a Sum whose left leaf is missing match the
    reference. DEVIATION, RECORDED: 'fe_to_u256::<Fq>' reaches through the type in the Rust;
    here the dictionary fragment is the explicit 'repr' parameter, the same R9 treatment
    P-09h gave FieldCtx (Evaluator.lean:175-195). -/
def quotientExprFromExpression {F : Type} (repr : F → List Nat)
    (env : QuotientExpressionEnv) (expression : Expression F) :
    Except Fault QuotientExpr :=
  Expression.evaluate
    { constant := fun scalar => do
        let w ← feToU256 (repr scalar)
        .ok (QuotientExpr.const w)
      selectorColumn := fun s => env.selector s
      fixedColumn := fun q => env.fixed q.columnIndex q.rotation.int
      adviceColumn := fun q => env.advice q.columnIndex q.rotation.int
      instanceColumn := fun q => env.instance_ q.columnIndex q.rotation.int
      challenge := fun c => env.challenge c.index
      negated := fun inner => do
        let x ← inner
        .ok (QuotientExpr.neg x)
      sum := fun a b => do
        let x ← a
        let y ← b
        .ok (QuotientExpr.add x y)
      product := fun a b => do
        let x ← a
        let y ← b
        .ok (QuotientExpr.mul x y)
      scaled := fun inner scalar => do
        let x ← inner
        let w ← feToU256 (repr scalar)
        .ok (QuotientExpr.mul x (QuotientExpr.const w)) }
    expression

/-- rust: QVM:2894-2899 (struct DataQuotientExpressionEnv) @formal-baseline. "Production
    expression environment backed by generated verifier data." UNOWNED ITEM PICKED UP. The
    two &'a borrows become values (Lean has no lifetimes), and 'meta' is a reserved word. -/
structure DataQuotientExpressionEnv where
  /-- rust: QVM:2896 ('meta: &ConstraintSystemMeta') -/
  meta_ : ConstraintSystemMeta
  /-- rust: QVM:2898 ('data: &Data') -/
  data : Data

/-- rust: QVM:2901-2952 ('impl QuotientExpressionEnv for DataQuotientExpressionEnv')
    @formal-baseline. UNOWNED ITEM PICKED UP. R9: the trait implementation is a function
    producing the record of closures. Five abort sites, all real (R4): the virtual-selector
    panic (:2904), the fixed expect (:2917), the advice expect (:2929), the committed
    instance expect (:2941) and the 'challenges[index]' direct index (:2950). The simple
    selector arm synthesises 'U256::from(1u64)' and does NOT look anything up (:2909-2910),
    the same rule evalAt applies at YE:855. -/
def DataQuotientExpressionEnv.env (self : DataQuotientExpressionEnv) : QuotientExpressionEnv :=
  { selector := fun _ =>
      panicF (siteQVM 2904 "virtual selectors must be removed before quotient lowering")
    fixed := fun columnIndex rotation =>
        if self.meta_.simpleSelectorCols.contains columnIndex then
          .ok (QuotientExpr.const (BitVec.ofNat 256 1))
        else do
          let w ← expectQVM (hashMapGet self.data.fixedEvals (columnIndex, rotation))
            2917 "fixed eval present"
          wordToQuotientExpr w
    advice := fun columnIndex rotation => do
        let w ← expectQVM (hashMapGet self.data.adviceEvals (columnIndex, rotation))
          2929 "advice eval present"
        wordToQuotientExpr w
    instance_ := fun columnIndex rotation =>
        if columnIndex < self.meta_.numCommittedInstances then do
          let w ← expectQVM (hashMapGet self.data.committedInstanceEvals (columnIndex, rotation))
            2941 "committed instance eval present"
          wordToQuotientExpr w
        else wordToQuotientExpr self.data.instanceEval
    challenge := fun index => do
        let w ← atQVM self.data.challenges index 2950 "challenges index"
        wordToQuotientExpr w }

/-- rust: Q:987-993 (quotient_expr_from_plonk_expr). "Lower a Halo2 expression into the
    quotient AST using generated data." THE BRIDGE'S THIRD LEG, and the reason the QVM chain
    above had to come with it: this is a two-word function in the Rust and six items in
    Lean. The 'repr' parameter is the R9 dictionary fragment the Rust reaches through Fq. -/
def quotientExprFromPlonkExpr {F : Type} (repr : F → List Nat)
    (meta_ : ConstraintSystemMeta) (data : Data) (expression : Expression F) :
    Except Fault QuotientExpr :=
  quotientExprFromExpression repr
    (DataQuotientExpressionEnv.env { meta_ := meta_, data := data }) expression

/-- rust: Q:978-984 (quotient_yul_expr). "Parse an evaluator-emitted Yul identity into the
    quotient AST once at plan-construction time." THE BRIDGE'S SECOND LEG: a fresh builder,
    one 'assignment' per line, then 'parse_expr(var)'. The builder is P-09c's
    (VmBuilder.lean:1232, :1224) and is reused, not re-derived. assignment aborts on a line
    the shallow Yul grammar does not accept (QVM:1240), so this is an Except and not a
    total function - which is exactly the hazard P-09h's two-routes gate is about. -/
def quotientYulExpr (lines : List String) (var : String) : Except Fault QuotientExpr := do
  let parser ← liftQVM
    (lines.foldlM (fun p line => QuotientBuilder.assignment p line) builderDefault)
  liftQVM (parseExprTop parser var)

/-! ## The picked-up emitters the family blocks call -/

/-- rust: QVM:4131-4133 (fr_delta_literal) @formal-baseline. "Render BLS12-381 Fr DELTA for
    legacy/direct Yul paths." = u256_string(fe_to_u256::<Fq>(&Fq::DELTA)). UNOWNED ITEM
    PICKED UP: it lives in vm/mod.rs, which no P-09 package ported, and Q:1494 is its only
    shipped caller outside the Evaluator. R9: Fq::DELTA is an associated constant of a
    trait, so it is read from the field dictionary the Evaluator carries - exactly what
    P-09h did at YE:330 - and NOTHING here hard-codes it, which is the property the
    reference's own test enforces (lowering/tests.rs:3467-3474 asserts the codegen source
    does not contain the literal). deltaFrLiteralIsNotHardcoded_ok re-pins that here. -/
def frDeltaLiteral {F : Type} : E F String := do
  let e ← get
  feToU256String e.field.delta

/-- rust: Q:1117-1204 (push_mstore_mload_literal_runs) @formal-baseline. "Compact runs of
    adjacent 'mstore(dst+i, mload(src+i*stride))' lines." UNOWNED ITEM PICKED UP -
    FoldCompute.lean:62 lists it as unported, and the permutation block stages six tables
    through it. The shape a port loses is the FIVE single-line rejections before any loop is
    emitted, in the Rust's order: the expression is not an mload literal; there is no next
    entry; the next destination is not dst_base + 0x20; the next expression is not an mload
    literal; the source stride underflows or is zero. Then a second gate: a run shorter than
    THREE entries is left as single lines (Q:1170), so a pair never compacts. The two
    src_stride arms differ: 0x20 reuses the destination offset variable, anything else
    multiplies by the stride literal. -/
def pushMstoreMloadLiteralRuns (block : List String) (dst : String)
    (entries : List (Nat × String)) (loopPrefix : String) : List String :=
  let single (b : List String) (dstBase : Nat) (expr : String) : List String :=
    b ++ ["mstore(add(" ++ dst ++ ", " ++ rustHashHex dstBase ++ "), " ++ expr ++ ")"]
  -- Q:1159-1168's inner 'while let'. It walks FORWARD from the third entry of a candidate
  -- run, so it is written as a recursion over the remaining list (R10: structural, no fuel
  -- needed here) rather than over the index the Rust uses.
  let rec extend (dstBase srcBase srcStride : Nat) : List (Nat × String) → Nat → Nat
    | [], count => count
    | (candDst, candExpr) :: rest, count =>
        match yulMloadLiteralExpr candExpr with
        | none => count
        | some candSrc =>
            if candDst == dstBase + count * 0x20 && candSrc == srcBase + count * srcStride
            then extend dstBase srcBase srcStride rest (count + 1)
            else count
  -- Q:1127's outer 'while idx < entries.len()'. Fuel is the entry count plus one: every arm
  -- advances idx by at least one, so the walk cannot outlast the fuel (R10, the
  -- specializeLimb7Chains precedent at FoldCompute.lean:311).
  let rec go (b : List String) : Nat → Nat → List String
    | 0, _ => b
    | fuel + 1, idx =>
        if idx >= entries.length then b
        else
          let (dstBase, expr) := entries.getD idx (0, "")
          let singleStep := single b dstBase expr
          match yulMloadLiteralExpr expr with
          | none => go singleStep fuel (idx + 1)
          | some srcBase =>
              match (entries.drop (idx + 1)).head? with
              | none => go singleStep fuel (idx + 1)
              | some (nextDst, nextExpr) =>
                  if nextDst != dstBase + 0x20 then go singleStep fuel (idx + 1)
                  else match yulMloadLiteralExpr nextExpr with
                    | none => go singleStep fuel (idx + 1)
                    | some nextSrc => match natSubOpt nextSrc srcBase with
                      | none => go singleStep fuel (idx + 1)
                      | some srcStride =>
                          if srcStride == 0 then go singleStep fuel (idx + 1)
                          else
                            let count := extend dstBase srcBase srcStride
                              (entries.drop (idx + 2)) 2
                            if count < 3 then go singleStep fuel (idx + 1)
                            else
                              let header := "for { let " ++ loopPrefix ++ "_i := 0 } lt("
                                ++ loopPrefix ++ "_i, " ++ toString count
                                ++ ") { " ++ loopPrefix ++ "_i := add(" ++ loopPrefix
                                ++ "_i, 1) } {"
                              let srcOff := if srcStride == 0x20
                                then "let " ++ loopPrefix ++ "_src_off := "
                                  ++ loopPrefix ++ "_dst_off"
                                else "let " ++ loopPrefix ++ "_src_off := mul(" ++ loopPrefix
                                  ++ "_i, " ++ rustHashHex srcStride ++ ")"
                              let store := "mstore(add(add(" ++ dst ++ ", "
                                ++ rustHashHex dstBase ++ "), " ++ loopPrefix
                                ++ "_dst_off), mload(add(" ++ rustHashHex srcBase ++ ", "
                                ++ loopPrefix ++ "_src_off)))"
                              go (b ++ ["{", header,
                                "let " ++ loopPrefix ++ "_dst_off := shl(5, " ++ loopPrefix
                                  ++ "_i)", srcOff, store, "}", "}"]) fuel (idx + count)
  go block (entries.length + 1) 0

/-- rust: Q:1419-1439 (structured_lookup_max_parallel) @formal-baseline. "Maximum parallel
    input width across LogUp lookup chunks." UNOWNED ITEM PICKED UP, and the brief's table
    mis-files it (header). THE '.max().unwrap_or(1)' IS NOT '.max().unwrap_or(0)': a
    constraint system whose every lookup has zero chunks yields 1, and the scratch layout
    the caller computes from it (Q:1707-1708) is three words wide and not zero. The Rust's
    flat_map collects per-lookup Vecs and then takes the global max; the port keeps the
    flatten and the Option. 'chunk_by_degree' aborts on a zero chunk count (logup.rs:329),
    which the port propagates rather than swallowing. -/
def structuredLookupMaxParallel {F : Type} (meta_ : ConstraintSystemMeta) : E F Nat := do
  let e ← get
  if meta_.numLookups == 0 then pure 0
  else do
    let csDegree ← StateT.lift (ConstraintSystem.degree e.cs)
    let widths ← e.cs.lookups.toList.mapM fun lookup => do
      let chunked ← StateT.lift (LogupBatchedArgument.chunkByDegree lookup csDegree)
      pure (chunked.inputExpressionChunks.toList.map fun inputChunk => inputChunk.size)
    pure (((widths.flatten).foldl
      (fun acc x => match acc with | none => some x | some m => some (max m x)) none).getD 1)


/-! ## structured_permutation_loop_block (rust: Q:1466-1680) -/

/-- rust: Q:1471-1680 (structured_permutation_loop_block) @formal-baseline. "Emit a native
    structured loop for the full permutation identity block." THE FIRST OF THE THREE
    PRODUCERS hazard 3 asks about.
    DEVIATION, RECORDED (R1 arity): the Rust takes meta, data and the evaluator as three
    separate parameters, but Q:817 and Q:2010 both build the Evaluator FROM that same meta
    and data, so the Lean port reads them from the threaded Evaluator and takes only the two
    parameters that are not already in it - scratch_mptr and base - plus fold. Nothing is
    lost: evalAt reads e.meta_ and e.data, which is what the Rust's 'meta' and 'data'
    arguments are. The scratch base and the stream base stay parameters because they are
    call-site facts, not circuit facts.
    The six mptrs are the layout the native callback promises (Q:1486-1491) and the
    delta_base slot is sized by 'num_sets.saturating_sub(1)' (Q:1491), NOT num_sets: the
    last set has no z_last, so the spill slot sits one word earlier than a naive port puts
    it. The two loop folds use FoldLoop.header (P-10a) while the lookup block's loops are
    hand-written strings - a divergence inside the reference itself, and
    permLoopsUseFoldHeaderNotHandWritten_ok pins which is which. -/
def structuredPermutationLoopBlock {F : Type} [BEq F] (scratchMptr : Nat)
    (fold : StructuredFold) (base : Nat) : FM F (Option (List String)) := do
  modify fun st => { st with block := [] }
  let st0 ← get
  let meta_ := st0.ev.meta_
  if meta_.numPermutationZs == 0 then pure none
  else do
    let numCols := meta_.permutationColumns.length
    let numSets := meta_.numPermutationZs
    let chunkLen := meta_.permutationChunkLen
    let valsMptr := scratchMptr
    let sigmasMptr := valsMptr + numCols * 0x20
    let zCurMptr := sigmasMptr + numCols * 0x20
    let zNextMptr := zCurMptr + numSets * 0x20
    let zLastMptr := zNextMptr + numSets * 0x20
    let deltaBaseMptr := zLastMptr + (numSets - 1) * 0x20
    -- Q:1492-1494: DELTA^chunk_len and DELTA, both rendered as minimal hex, both computed
    -- from the field dictionary and never written as literals here.
    let deltaChunk ← evRun (feToU256String (st0.ev.field.powNat st0.ev.field.delta chunkLen))
    let delta ← evRun frDeltaLiteral
    emit "{"
    emit ("let delta := " ++ delta)
    emit ("let q_perm_vals := " ++ rustHashHex valsMptr)
    emit ("let q_perm_sigmas := " ++ rustHashHex sigmasMptr)
    emit ("let q_perm_z_cur := " ++ rustHashHex zCurMptr)
    emit ("let q_perm_z_next := " ++ rustHashHex zNextMptr)
    emit ("let q_perm_z_last := " ++ rustHashHex zLastMptr)
    emit ("let q_perm_delta_base_ptr := " ++ rustHashHex deltaBaseMptr)
    emit ("let q_perm_num_cols := " ++ toString numCols)
    emit ("let q_perm_num_sets := " ++ toString numSets)
    emit ("let q_perm_chunk_len := " ++ toString chunkLen)
    emit ("let q_perm_delta_chunk := " ++ deltaChunk)
    -- Q:1512 '.enumerate()' -> zipIdx, which yields (element, index).
    let pairs ← meta_.permutationColumns.zipIdx.mapM fun (column, idx) => do
      let value ← evRun (evalAt column 0)
      let st ← get
      let sigma ← liftF (expectQ (hashMapGet st.ev.data.permutationEvals column)
        1518 "permutation sigma eval present")
      pure ((idx * 0x20, value), (idx * 0x20, wordString sigma))
    modify fun st => { st with
      block := pushMstoreMloadLiteralRuns st.block "q_perm_vals" (pairs.map Prod.fst)
        "q_perm_val_load" }
    modify fun st => { st with
      block := pushMstoreMloadLiteralRuns st.block "q_perm_sigmas" (pairs.map Prod.snd)
        "q_perm_sigma_load" }
    let st1 ← get
    let zTriples := st1.ev.data.permutationZEvals
    -- Q:1539 '.enumerate()' -> zipIdx. The z_last table skips the None slots but keeps the
    -- index-derived offset, so a gap in the middle would leave a hole in the table.
    let zCur := (zTriples.zipIdx).map fun ((c, _, _), idx) => (idx * 0x20, wordString c)
    let zNext := (zTriples.zipIdx).map fun ((_, n, _), idx) => (idx * 0x20, wordString n)
    let zLast := (zTriples.zipIdx).filterMap fun t => match t with
      | ((_, _, some l), idx) => some (idx * 0x20, wordString l)
      | _ => none
    modify fun st => { st with
      block := pushMstoreMloadLiteralRuns st.block "q_perm_z_cur" zCur "q_perm_z_cur_load" }
    modify fun st => { st with
      block := pushMstoreMloadLiteralRuns st.block "q_perm_z_next" zNext "q_perm_z_next_load" }
    modify fun st => { st with
      block := pushMstoreMloadLiteralRuns st.block "q_perm_z_last" zLast "q_perm_z_last_load" }
    -- Identity order (Q:1566-1568, permutation.rs::expressions): first-set boundary,
    -- last-set boundary, continuity for i >= 1, then one product identity per set.
    emit "let q_perm_eval := 0"
    emit "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)"
    pushFold fold "q_perm_eval"
      (FoldPos.fixed base FoldLabel.permutationFirstBoundary)
    let finalZOffset := (numSets - 1) * 0x20
    emit ("let q_perm_zn := mload(add(q_perm_z_cur, " ++ rustHashHex finalZOffset ++ "))")
    emit "q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)"
    pushFold fold "q_perm_eval"
      (FoldPos.fixed (base + 1) FoldLabel.permutationLastBoundary)
    if numSets > 1 then do
      let continuity : FoldLoop := { var := "q_perm_i", start := 1, end_ := numSets }
      emit (FoldLoop.header continuity)
      emit "let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))"
      emit "let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))"
      emit "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)"
      pushFold fold "q_perm_eval"
        (FoldPos.loop (base + 1) continuity (fun set => FoldLabel.permutationContinuity set))
      emit "}"
    emit "mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))"
    let products : FoldLoop := { var := "q_perm_set", start := 0, end_ := numSets }
    emit (FoldLoop.header products)
    emit "let q_perm_start := mul(q_perm_set, q_perm_chunk_len)"
    emit "let q_perm_end := add(q_perm_start, q_perm_chunk_len)"
    emit "if gt(q_perm_end, q_perm_num_cols) { q_perm_end := q_perm_num_cols }"
    emit "let q_perm_left := mload(add(q_perm_z_next, shl(5, q_perm_set)))"
    emit "let q_perm_right := mload(add(q_perm_z_cur, shl(5, q_perm_set)))"
    emit "let q_perm_delta_pow := mload(q_perm_delta_base_ptr)"
    emit "for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {"
    emit "let q_perm_off := shl(5, q_perm_j)"
    emit "let q_perm_v := mload(add(q_perm_vals, q_perm_off))"
    emit "let q_perm_s := mload(add(q_perm_sigmas, q_perm_off))"
    emit "q_perm_left := mulmod(q_perm_left, addmod(addmod(q_perm_v, mulmod(mload(BETA_MPTR), q_perm_s, r), r), mload(GAMMA_MPTR), r), r)"
    emit "q_perm_right := mulmod(q_perm_right, addmod(addmod(q_perm_v, q_perm_delta_pow, r), mload(GAMMA_MPTR), r), r)"
    emit "q_perm_delta_pow := mulmod(q_perm_delta_pow, delta, r)"
    emit "}"
    emit "q_perm_eval := mulmod(addmod(1, sub(r, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r)), r), addmod(q_perm_left, sub(r, q_perm_right), r), r)"
    pushFold fold "q_perm_eval"
      (FoldPos.loop (base + 1 + numSets) products (fun set => FoldLabel.permutationProduct set))
    emit "mstore(q_perm_delta_base_ptr, mulmod(mload(q_perm_delta_base_ptr), q_perm_delta_chunk, r))"
    emit "}"
    emit "}"
    let st ← get
    pure (some st.block)


/-! ## structured_lookup_loop_block (rust: Q:1682-1934) -/

/-- rust: Q:1688-1934 (structured_lookup_loop_block) @formal-baseline. "Emit a native
    structured loop for all LogUp lookup identities." THE SECOND PRODUCER.
    The same arity deviation as the permutation block: 'self' contributes only
    'self.vk.cs()' and 'structured_lookup_max_parallel', both of which read the Evaluator's
    own cs, and meta/data are the Evaluator's (Q:2010).
    THREE THINGS A PORT LOSES. (1) The chunk loop's iterator is a zip and THEN an enumerate
    (Q:1750), so the element is the PAIR '(input_chunk, h_eval)' and the index is 'chunk';
    zip truncates to the shorter side, which is why the helper count is
    'min(chunks, h_evals)' and why 'j' has to be counted from the zip and not from the chunk
    list. (2) The k == 0 and k == 1 arms 'continue' (Q:1770, Q:1790) and so never reach the
    staging loops, the prefix/suffix products or the shared-prefix attempt - and the k == 1
    arm is the only place the reference writes 'sub(r, 1)' instead of a sum. (3) The three
    staging loops are hand-written Yul strings, NOT FoldLoop.header: the permutation block
    uses the header and this one does not, and a port that "unifies" them changes the text.
    The scratch layout is 'max_parallel * 3' words (Q:1444 via Q:1701), staged as f+beta,
    prefix, suffix at 0x20 per parallel input. -/
def structuredLookupLoopBlock {F : Type} [BEq F] (scratchMptr : Nat)
    (fold : StructuredFold) (base : Nat) : FM F (Option (List String)) := do
  modify fun st => { st with block := [] }
  let st0 ← get
  let meta_ := st0.ev.meta_
  if meta_.numLookups == 0 then pure none
  else do
    let maxParallel ← evRun (structuredLookupMaxParallel meta_)
    let fPlusBetaMptr := scratchMptr
    let prefixMptr := fPlusBetaMptr + maxParallel * 0x20
    let suffixMptr := prefixMptr + maxParallel * 0x20
    emit "{"
    emit ("let q_lookup_f := " ++ rustHashHex fPlusBetaMptr)
    emit ("let q_lookup_prefix := " ++ rustHashHex prefixMptr)
    emit ("let q_lookup_suffix := " ++ rustHashHex suffixMptr)
    emit "let q_lookup_l0 := mload(L_0_MPTR)"
    emit "let q_lookup_llast := mload(L_LAST_MPTR)"
    emit "let q_lookup_lblind := mload(L_BLIND_MPTR)"
    emit "let q_lookup_lsum := addmod(q_lookup_l0, q_lookup_llast, r)"
    emit "let q_lookup_active := addmod(1, sub(r, addmod(q_lookup_llast, q_lookup_lblind, r)), r)"
    emit "let q_lookup_beta := mload(BETA_MPTR)"
    emit "let q_lookup_theta := mload(THETA_MPTR)"
    let st1 ← get
    let csDegree ← liftF (ConstraintSystem.degree st1.ev.cs)
    -- Q:1726 '.enumerate()' -> zipIdx: (element, index).
    let _ ← st1.ev.cs.lookups.toList.zipIdx.foldlM
        (fun (j : Nat) (lookup, lookupIdx) => do
          let chunked ← liftF (LogupBatchedArgument.chunkByDegree lookup csDegree)
          let st ← get
          -- Q:1728: a direct Vec index, so an out-of-range lookup index aborts (R4).
          let (mEval, hEvals, zEval, zNextEval) ←
            liftF (atQ st.ev.data.lookupEvals lookupIdx 1728 "lookup evals index")
          emit "{"
          -- boundary = (l_0 + l_last) * Z_lookup(x)   (Q:1732-1748)
          emit "{"
          emit ("let q_lookup_eval := mulmod(q_lookup_lsum, " ++ wordString zEval ++ ", r)")
          pushFold fold "q_lookup_eval" (FoldPos.fixed j (FoldLabel.lookupBoundary lookupIdx))
          emit "}"
          -- one helper identity per input chunk (Q:1750-1876). The zip is INSIDE the
          -- enumerate, so zipIdx hands back ((chunk_list, h_eval), index).
          let jAfter ← (chunked.inputExpressionChunks.toList.zip hEvals).zipIdx.foldlM
              (fun (j : Nat) (elem, chunk) => do
                let inputChunk := elem.fst.toList
                let hEval := elem.snd
                let helper := FoldLabel.lookupHelper lookupIdx chunk
                let k := inputChunk.length
                emit "{"
                if k == 0 then do
                  emit "let q_lookup_eval := 0"
                  pushFold fold "q_lookup_eval" (FoldPos.fixed j helper)
                  emit "}"
                  pure (j + 1)
                else if k == 1 then do
                  evRun resetLocals
                  -- Q:1776 'input_chunk[0]': unreachable here because k == 1, but the site
                  -- is a real index and is ported as one (R4).
                  let first ← liftF (atQ inputChunk 0 1776 "input chunk index")
                  let (compressedLines, compressedVar) ←
                    evRun (compressExpressionsWithChallengeVar first.toList "q_lookup_theta")
                  emitAll compressedLines
                  emit ("let q_lookup_eval := addmod(mulmod(" ++ wordString hEval
                    ++ ", addmod(" ++ compressedVar ++ ", q_lookup_beta, r), r), sub(r, 1), r)")
                  pushFold fold "q_lookup_eval" (FoldPos.fixed j helper)
                  emit "}"
                  pure (j + 1)
                else do
                  evRun resetLocals
                  let shared ← evRun (lookupSharedPrefixFPlusBeta
                    (inputChunk.map fun parallelInput => parallelInput.toList)
                    "q_lookup_theta" "q_lookup_beta" "q_lookup_f")
                  match shared with
                  | some ls => emitAll ls
                  | none =>
                    -- Q:1802 '.enumerate()' -> zipIdx.
                    let _ ← inputChunk.zipIdx.mapM fun (parallelInput, inputIdx) => do
                      let (compressedLines, compressedVar) ←
                        evRun (compressExpressionsWithChallengeVar parallelInput.toList
                          "q_lookup_theta")
                      emitAll compressedLines
                      emit ("mstore(add(q_lookup_f, " ++ rustHashHex (inputIdx * 0x20)
                        ++ "), addmod(" ++ compressedVar ++ ", q_lookup_beta, r))")
                  emit "let q_lookup_product := 1"
                  emit ("for { let q_lookup_prod_i := 0 } lt(q_lookup_prod_i, " ++ toString k
                    ++ ") { q_lookup_prod_i := add(q_lookup_prod_i, 1) } {")
                  emit "q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)"
                  emit "}"
                  emit "mstore(q_lookup_prefix, 1)"
                  if k > 1 then do
                    emit ("for { let q_lookup_pref_i := 1 } lt(q_lookup_pref_i, " ++ toString k
                      ++ ") { q_lookup_pref_i := add(q_lookup_pref_i, 1) } {")
                    emit "let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)"
                    emit "mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))"
                    emit "}"
                  -- Q:1841 '(k - 1) * 0x20': guarded by k != 0 above, so no underflow (R5).
                  emit ("mstore(add(q_lookup_suffix, " ++ rustHashHex ((k - 1) * 0x20)
                    ++ "), 1)")
                  if k > 1 then do
                    emit ("for { let q_lookup_suf_i := sub(" ++ toString k
                      ++ ", 1) } gt(q_lookup_suf_i, 0) { q_lookup_suf_i := sub(q_lookup_suf_i, 1) } {")
                    emit "let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)"
                    emit "mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))"
                    emit "}"
                  emit "let q_lookup_sum := 0"
                  emit ("for { let q_lookup_sum_i := 0 } lt(q_lookup_sum_i, " ++ toString k
                    ++ ") { q_lookup_sum_i := add(q_lookup_sum_i, 1) } {")
                  emit "q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)"
                  emit "}"
                  emit ("let q_lookup_eval := addmod(mulmod(" ++ wordString hEval
                    ++ ", q_lookup_product, r), sub(r, q_lookup_sum), r)")
                  pushFold fold "q_lookup_eval" (FoldPos.fixed j helper)
                  emit "}"
                  pure (j + 1))
              (j + 1)
          -- accumulator = active * ((Z_next - Z - selector * sum(h)) * (table + beta) + m)
          emit "{"
          -- Q:1885 'h_evals[0]' is a direct index; the arm is only entered when non-empty.
          let sumHExpr ← match hEvals with
            | [] => pure "0"
            | first :: rest => do
                emit ("let q_lookup_sum_h := " ++ wordString first)
                emitAll (rest.map fun h =>
                  "q_lookup_sum_h := addmod(q_lookup_sum_h, " ++ wordString h ++ ", r)")
                pure "q_lookup_sum_h"
          evRun resetLocals
          let (selectorLines, selectorVar) ← evRun (evaluateExpression chunked.selector)
          emitAll selectorLines
          let (tableLines, tableVar) ←
            evRun (compressExpressionsWithChallengeVar chunked.tableExpressions.toList
              "q_lookup_theta")
          emitAll tableLines
          emit ("let q_lookup_s_sum_h := mulmod(" ++ selectorVar ++ ", " ++ sumHExpr ++ ", r)")
          emit ("let q_lookup_diff := addmod(" ++ wordString zNextEval
            ++ ", sub(r, addmod(" ++ wordString zEval ++ ", q_lookup_s_sum_h, r)), r)")
          emit ("let q_lookup_t_beta := addmod(" ++ tableVar ++ ", q_lookup_beta, r)")
          emit ("let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), "
            ++ wordString mEval ++ ", r)")
          emit "let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)"
          pushFold fold "q_lookup_eval"
            (FoldPos.fixed jAfter (FoldLabel.lookupAccumulator lookupIdx))
          emit "}"
          emit "}"
          pure (jAfter + 1))
        base
    emit "}"
    let st ← get
    pure (some st.block)

/-! ## structured_trash_loop_block (rust: Q:1936-1993) -/

/-- rust: Q:1941-1993 (structured_trash_loop_block) @formal-baseline. "Emit a native
    structured loop for the trash identity suffix." THE THIRD PRODUCER, and the shortest:
    one block per trash argument, compressed by TRASH_CHALLENGE_MPTR and not by theta (the
    same distinction the Evaluator's trashcan_computations documents at YE:644-647). Note
    the two resets this function does NOT do: 'q_trash_tau' is loaded ONCE outside the loop
    (Q:1955) while the Evaluator loads the challenge per argument, so the two paths differ
    in exactly one mload - and both are correct because the value cannot change mid-render.
    Q:1957 '.enumerate()' -> zipIdx. Q:1974 'data.trashcan_evals[idx]' is a direct index
    (R4). -/
def structuredTrashLoopBlock {F : Type} [BEq F] (fold : StructuredFold) (base : Nat) :
    FM F (Option (List String)) := do
  modify fun st => { st with block := [] }
  let st0 ← get
  let meta_ := st0.ev.meta_
  if meta_.numTrashcans == 0 then pure none
  else do
    emit "{"
    emit "let q_trash_tau := mload(TRASH_CHALLENGE_MPTR)"
    let _ ← st0.ev.cs.trashcans.toList.zipIdx.mapM fun (argument, idx) => do
      emit "{"
      evRun resetLocals
      let (compressedLines, compressedVar) ←
        evRun (compressExpressionsWithChallengeVar argument.constraintExpressions.toList
          "q_trash_tau")
      emitAll compressedLines
      let (selectorLines, selectorVar) ← evRun (evaluateExpression argument.selector)
      emitAll selectorLines
      let st ← get
      let trashEval ← liftF (atQ st.ev.data.trashcanEvals idx 1974 "trashcan evals index")
      emit ("let q_trash_one_minus_selector := addmod(1, sub(r, " ++ selectorVar ++ "), r)")
      emit ("let q_trash_scaled := mulmod(q_trash_one_minus_selector, "
        ++ wordString trashEval ++ ", r)")
      emit ("let q_trash_eval := addmod(" ++ compressedVar
        ++ ", sub(r, q_trash_scaled), r)")
      pushFold fold "q_trash_eval" (FoldPos.fixed (base + idx) (FoldLabel.trash idx))
      emit "}"
    emit "}"
    let st ← get
    pure (some st.block)


/-! ## compact_quotient_computation_blocks (rust: Q:1995-2099) -/

/-- rust: Q:2000-2099 (compact_quotient_computation_blocks) @formal-baseline. "Emit all
    template blocks for the compact quotient VM representation." HAZARD 4: P-10 declined
    this as Evaluator-blocked and it now ports, which is the clearest evidence the unblock
    was real.
    THE ORDER IS THE SEMANTICS. A Rust struct literal evaluates its fields top to bottom, so
    the six families are emitted in source order: inline, eval_numer (a literal Vec::new at
    Q:2032), post_vm (the trash block), native permutation, native lookup, native identity.
    That matters because ONE Evaluator is shared by the three family calls (Q:2010) and its
    var_counter and var_cache are RefCells: a port that reordered the fields, or built a
    fresh evaluator per family, would change the varN names in the emitted text. The port
    threads the evaluator through in the Rust's order and nothing else.
    THE FOLD IS ALWAYS HORNER HERE (Q:2039-2042, Q:2057-2060, Q:2074-2077), so this function
    records NO fold sites at all: the Weighted recorder is only reachable from the direct
    lowering's caller, which is quotient_direct.rs (M10). The returned pair still carries the
    site list so that the fact is visible in the type and gated, rather than assumed.
    The three stream bases come from the PROTOCOL plan (Q:2013-2015) and not from the
    identity lists, which is what makes them a cross-check and not a restatement. -/
def compactQuotientComputationBlocks {F : Type} [BEq F] (field : FieldCtx F)
    (cs : ConstraintSystem F) (meta_ : ConstraintSystemMeta) (data : Data)
    (quotientPlan : QuotientProgramPlan) (quotientStackMptr : Nat)
    (quotientStateSlots : QuotientStateSlots) (trace : Bool) :
    Except Fault (QuotientComputationBlocks × List FoldSite) := do
  let evalScratchSlot := quotientStackMptr
  let evaluator := (Evaluator.new field cs meta_ data).withPow5Helper true
  let permutationBase := meta_.protocol.quotient.gates
  let lookupBase := permutationBase + meta_.protocol.quotient.permutation
  let trashBase := lookupBase + meta_.protocol.quotient.lookup
  let horner := StructuredFold.horner quotientStateSlots trace
  -- Q:2017-2031: inline_computations, a map of direct_quotient_block over the plan's
  -- inline prefix. FoldCompute's directQuotientBlock is reused (hazard 5); its selector-gap
  -- abort is a QVMFault and crosses through liftQVM.
  let inline ← quotientPlan.inlineIdentities.mapM fun identity =>
    liftQVM (directQuotientBlock identity.lines identity.var identity.target
      (quotientPlan.selectorFold.gapFor identity) evalScratchSlot quotientStateSlots trace)
  -- Q:2032: eval_numer_computations is Vec::new(). Not an omission - the reference emits
  -- nothing there in compact mode, because the fold advance lives inside each block.
  -- Q:2033-2048: post_vm_computations, the trash suffix, gated on num_trashcans.
  let (postVm, sites1, ev2) ←
    if meta_.numTrashcans > 0 then do
      let (r, s, ev) ← runFamilyBlock evaluator (structuredTrashLoopBlock horner trashBase)
      pure (match r with | some b => [b] | none => [], s, ev)
    else pure ([], [], evaluator)
  -- Q:2049-2065: native_permutation_computation, gated on the plan's flag.
  let (permBlock, sites2, ev3) ←
    if quotientPlan.hasNativePermutation then do
      let (r, s, ev) ←
        runFamilyBlock ev2 (structuredPermutationLoopBlock quotientStackMptr horner
          permutationBase)
      pure (match r with | some b => b | none => [], s, ev)
    else pure ([], [], ev2)
  -- Q:2066-2082: native_lookup_computation.
  let (lookupBlock, sites3, _ev4) ←
    if quotientPlan.hasNativeLookup then do
      let (r, s, ev) ←
        runFamilyBlock ev3 (structuredLookupLoopBlock quotientStackMptr horner lookupBase)
      pure (match r with | some b => b | none => [], s, ev)
    else pure ([], [], ev3)
  -- Q:2083-2097: native_identity_computations, the same direct_quotient_block map as the
  -- inline prefix, over the plan's native bodies.
  let nativeIds ← quotientPlan.nativeIdentities.mapM fun identity =>
    liftQVM (directQuotientBlock identity.lines identity.var identity.target
      (quotientPlan.selectorFold.gapFor identity) evalScratchSlot quotientStateSlots trace)
  pure ({ inlineComputations := inline, evalNumerComputations := [],
          postVmComputations := postVm, nativePermutationComputation := permBlock,
          nativeLookupComputation := lookupBlock,
          nativeIdentityComputations := nativeIds },
        sites1 ++ sites2 ++ sites3)

/-! ## quotient_identity_parts (rust: Q:796-969) and its bridge items -/

/-- rust: QVM:228-244 (struct QuotientIdentityParts) @formal-baseline. The five families of
    the identity stream, in global y-batch order. UNOWNED ITEM PICKED UP: VmTypes.lean:56
    lists QVM:228-297 as unported, and quotient_identity_parts returns this record. The
    manifest method (QVM:258-282) is #[cfg(test)] and is NOT ported; all_identities
    (QVM:246-256) is shipped and is. -/
structure QuotientIdentityParts where
  /-- rust: QVM:232 (gates: Vec<QuotientIdentity>) -/
  gates : List QuotientIdentity
  /-- rust: QVM:234 (permutation: Vec<QuotientIdentity>) -/
  permutation : List QuotientIdentity
  /-- rust: QVM:236 (lookup: Vec<QuotientIdentity>) -/
  lookup : List QuotientIdentity
  /-- rust: QVM:238 (trash: Vec<QuotientIdentity>) -/
  trash : List QuotientIdentity
  /-- rust: QVM:243 (sorted_simple: Vec<usize>) -/
  sortedSimple : List Nat

/-- rust: QVM:248-256 (QuotientIdentityParts::all_identities). "Return every identity in
    global y-batch order." Four chained iterators, in the Rust's order. -/
def QuotientIdentityParts.allIdentities (self : QuotientIdentityParts) :
    List QuotientIdentity :=
  self.gates ++ self.permutation ++ self.lookup ++ self.trash

/-- Rust's 'slice::position' (Q:847): the index of the first equal element, or None. Lean
    scaffolding, not a Rust item - written out rather than using List.findIdx? because that
    function's argument order puts the HAYSTACK second and dot notation would silently read
    backwards here. -/
def positionOf {α : Type} [BEq α] (xs : List α) (a : α) : Option Nat :=
  go xs a 0 where
  go : List α → α → Nat → Option Nat
    | [], _, _ => none
    | x :: rest, a, i => if x == a then some i else go rest a (i + 1)

/-- rust: DIAG:225-247 (VerifierBuildInputs::trash_manifest_name) @formal-baseline.
    "Best-effort human label for a trash identity." UNOWNED ITEM PICKED UP, and a scope
    finding: diagnostics.rs is P-14, which PLAN 14.8 CUT, and the brief's table does not
    list this dependency at all. RECEIVER DEVIATION, RECORDED: the Rust is a method on
    VerifierBuildInputs and reaches the constraint system through 'self.vk.cs()'; the port
    takes the ConstraintSystem directly, because that is the only thing the body reads and
    the Evaluator already carries it. Nothing about VerifierBuildInputs, the VK row or the
    build pipeline is imported. 'nth(trash_index)' is a positional skip and not an index, so
    the filter changes what the position means - the port keeps the filter first. Total:
    every arm has a fallback, so there is no abort site here. -/
def trashManifestName {F : Type} (cs : ConstraintSystem F) (trashIndex : Nat) : String :=
  match ((cs.gates.toList.filter
        fun (gate : Gate F) => (Gate.polynomials gate).isEmpty).drop trashIndex).head? with
  | some gate => Gate.name gate
  | none => match (cs.trashcans.toList.drop trashIndex).head? with
    | some trash => TrashArgument.name trash
    | none => "trash_" ++ toString trashIndex

/-- rust: Q:804-969 (quotient_identity_parts) @formal-baseline. "Split the quotient identity
    stream into gate/permutation/lookup/trash parts." THE ITEM P-10 NAMED LAST and the one
    the bridge exists for: the gate arm lowers the typed Expression through
    quotient_expr_from_plonk_expr and the three family arms parse the emitted Yul through
    quotient_yul_expr, so one identity stream ends up with BOTH representations of every
    identity - which is the point of the assert_eq! at Q:827-831 ("gate Yul expressions and
    typed expressions must stay aligned") and of the four count asserts at Q:941-960 that
    tie the stream to the protocol plan. All five are release aborts (R4): assert_eq! is not
    compiled out, only debug_assert! is.
    The four bases (Q:839-842) are computed from the ITEM COUNTS and not from the protocol
    plan - the plan is only checked against them at the end, which is what makes the four
    asserts a cross-check rather than a restatement. 'sorted_simple' (Q:836-837) is a
    sort_unstable of the BTreeSet's ascending order: a no-op on an already-sorted input, and
    the port sorts anyway because R1 says transcribe and simpleSelectorCols is documented as
    ascending (Encoding.lean:390-394) rather than guaranteed so.
    Q:854, Q:878, Q:895 and Q:921 are four more '.enumerate()' sites: zipIdx swaps. -/
def quotientIdentityParts {F : Type} [BEq F] (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault QuotientIdentityParts := do
  -- Q:817: the Evaluator is CONSTRUCTED here, not borrowed, so the state is threaded by hand.
  let ev0 := Evaluator.new field cs meta_ data
  let (gateItems, ev1) ← evRunOn gateComputationsTagged ev0
  -- Q:819-826: flat_map over gates then polynomials, each lowered through the bridge.
  -- mapM short-circuits at the first abort, which is the Rust's left-to-right order.
  let gateExprs ← (cs.gates.toList.flatMap fun gate => gate.polynomials.toList).mapM
    (fun poly => quotientExprFromPlonkExpr field.repr meta_ data poly)
  -- Q:827-831
  unless gateItems.length == gateExprs.length do
    panicF (siteQ 830 "gate Yul expressions and typed expressions must stay aligned")
  let (permItems, ev2) ← evRunOn permutationComputations ev1
  let (lookupItems, ev3) ← evRunOn lookupComputations ev2
  let (trashItems, _ev4) ← evRunOn trashcanComputations ev3
  -- Q:836-837
  let sortedSimple := sortedNats meta_.simpleSelectorCols
  -- Q:839-842
  let permutationBase := gateItems.length
  let lookupBase := permutationBase + permItems.length
  let trashBase := lookupBase + lookupItems.length
  -- Q:844-850: the selector_target closure. '.expect' is a release abort (R4).
  let selectorTarget (col : Nat) : Except Fault QuotientTarget := do
    .ok (QuotientTarget.selector (← expectQ (positionOf sortedSimple col) 848
      "selector column present"))
  -- Q:851-875: gates. zip THEN enumerate, so zipIdx yields ((item, expr), index).
  let gates ← (gateItems.zip gateExprs).zipIdx.mapM fun ((item, expr), globalIndex) => do
    let target ← match item.simpleSelectorIndex with
      | some col => selectorTarget col
      | none => .ok QuotientTarget.main
    let m : QuotientIdentityMetadata :=
      { globalIndex := globalIndex,
        source := QuotientIdentitySource.gate item.gateIndex item.gateName
          item.constraintIndex item.constraintName item.polynomialIndex }
    pure ({ meta_ := m, lines := item.lines, var := item.var, target := target,
            expr := expr } : QuotientIdentity)
  -- Q:876-892: permutation. The expr is PARSED from the emitted lines (the bridge).
  let permutation ← permItems.zipIdx.mapM fun ((lines, var), identityIndex) => do
    let expr ← quotientYulExpr lines var
    let m : QuotientIdentityMetadata :=
      { globalIndex := permutationBase + identityIndex,
        source := QuotientIdentitySource.permutation identityIndex }
    pure ({ meta_ := m, lines := lines, var := var, target := QuotientTarget.main,
            expr := expr } : QuotientIdentity)
  -- Q:893-918: lookup, plus the protocol chunk map and the synthesized name.
  let lookup ← lookupItems.zipIdx.mapM fun ((lines, var), identityIndex) => do
    let expr ← quotientYulExpr lines var
    let (lookupIndex, _) ← expectQ (meta_.protocol.lookupIdentitySource identityIndex)
      901 "lookup identity index covered by protocol lookup chunks"
    let lookupName := "lookup_" ++ toString lookupIndex
    let m : QuotientIdentityMetadata :=
      { globalIndex := lookupBase + identityIndex,
        source := QuotientIdentitySource.lookup identityIndex lookupIndex lookupName }
    pure ({ meta_ := m, lines := lines, var := var, target := QuotientTarget.main,
            expr := expr } : QuotientIdentity)
  -- Q:919-939: trash, named by the diagnostics helper.
  let trash ← trashItems.zipIdx.mapM fun ((lines, var), trashIndex) => do
    let expr ← quotientYulExpr lines var
    let trashName := trashManifestName cs trashIndex
    let m : QuotientIdentityMetadata :=
      { globalIndex := trashBase + trashIndex,
        source := QuotientIdentitySource.trash trashIndex trashName }
    pure ({ meta_ := m, lines := lines, var := var, target := QuotientTarget.main,
            expr := expr } : QuotientIdentity)
  -- Q:941-960: the four protocol-plan cross-checks.
  unless gates.length == meta_.protocol.quotient.gates do
    panicF (siteQ 944 "gate identity count must match protocol plan")
  unless permutation.length == meta_.protocol.quotient.permutation do
    panicF (siteQ 949 "permutation identity count must match protocol plan")
  unless lookup.length == meta_.protocol.quotient.lookup do
    panicF (siteQ 954 "lookup identity count must match protocol plan")
  unless trash.length == meta_.protocol.quotient.trash do
    panicF (siteQ 959 "trash identity count must match protocol plan")
  pure ({ gates := gates, permutation := permutation, lookup := lookup, trash := trash,
          sortedSimple := sortedSimple } : QuotientIdentityParts)

end Midfall.Generator.QuotientBlocks

/-! # Known-answer checks (P-10c)

The fixtures here are the Evaluator's QVMFr field dictionary and column/expression sugar
(reused from Evaluator.lean's KAT namespace, the precedent Evaluator.lean:1322 and
LoweringPlan.lean:814 already set for reading another package's KAT vocabulary) but a NEW
constraint system, meta and data with their own address map, so nothing here can silently
inherit P-09h's expectations. blocksFixturesNonDegenerate_ok (R-48) asserts the internal
distinctness AND that the fixture differs from qMeta/qData where it has to.

The three exact-line pins below are the P-09h standard: the whole emitted block, line for
line, not a "something was produced" smoke test. pinnedLinesTraceToReference_ok is the
anti-circularity half - it counts how many pinned lines appear VERBATIM in the reference
and requires the rest to match named format-string skeletons, so a pin that drifted from Q
reddens even though both sides of the main comparison are Lean. -/

namespace Midfall.Generator.QuotientBlocksKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientFold
  Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientEvaluator
  Midfall.Generator.QuotientBlocks
  Midfall.Generator.QuotientEvaluatorKats

/-- The reference file, read at #eval time (D-P19). -/
def qPathCandidates : List String :=
  ["proofs/solidity-verifier/src/lowering/quotient.rs",
   "../proofs/solidity-verifier/src/lowering/quotient.rs"]

def readQArtifact : IO String :=
  qPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got
        else Midfall.Generator.QuotientVmKats.readFileOrEmpty path)
    (pure "")

/-- Long enough that a wrong path cannot pass: quotient.rs is ~78 KB at HEAD. -/
def qReadOk (src : String) : Bool := src.length > 60000

def qvmPathCandidates : List String :=
  ["proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs",
   "../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"]

def readQVMArtifact : IO String :=
  qvmPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got
        else Midfall.Generator.QuotientVmKats.readFileOrEmpty path)
    (pure "")

def faultSite {α : Type} (x : Except Fault α) : String :=
  match x with
  | .error (Fault.panic s) => s
  | .error _ => "?"
  | .ok _ => ""

def isFault {α : Type} (x : Except Fault α) : Bool :=
  match x with | .error _ => true | .ok _ => false

/-! ## The fixture -/

/-- The address map. All multiples of 0x20, all distinct, and deliberately DISJOINT from
    P-09h's 0x2000-0x3c00 range so a gate cannot read the other fixture by accident. The
    permutation columns sit 0x20 apart (so the value table compacts with stride 0x20) and
    the sigmas 0x40 apart (so the sigma table compacts with the mul arm) - that is the only
    reason those two strides differ, and blocksFixtureStrides_ok pins it. -/
def pA (i : Nat) : Nat := 0x4000 + i * 0x20
def pS (i : Nat) : Nat := 0x5000 + i * 0x40
def pZc (i : Nat) : Nat := 0x6000 + i * 0x20
def pZn (i : Nat) : Nat := 0x6100 + i * 0x20
def pZl (i : Nat) : Nat := 0x6200 + i * 0x20
def pM : Nat := 0x7000
def pH (i : Nat) : Nat := 0x7100 + i * 0x20
def pLz : Nat := 0x7200
def pLzn : Nat := 0x7300
def pT (i : Nat) : Nat := 0x8000 + i * 0x20
def pCh (i : Nat) : Nat := 0x9000 + i * 0x20
def pIe : Nat := 0x9100
def pCi (i : Nat) : Nat := 0x9200 + i * 0x20

def bLk : LogupBatchedArgument QVMFr :=
  { name := "blk", selector := eF 1,
    inputExpressions := #[#[eA 0], #[eA 1], #[eA 2], #[eA 3], #[eA 4]],
    tableExpressions := #[eF 1] }

/-- The shared-prefix lookup: three parallel inputs of two expressions each, sharing
    [eA 0], with tails at 0x4020, 0x4040, 0x4060 - adjacent, so
    lookup_shared_prefix_f_plus_beta (YE:138) fires and the block gets the
    q_lookup_shared_i loop instead of three staged mstores. -/
def bLk2 : LogupBatchedArgument QVMFr :=
  { name := "blk2", selector := eF 1,
    inputExpressions := #[#[eA 0, eA 1], #[eA 0, eA 2], #[eA 0, eA 3]],
    tableExpressions := #[eF 1] }

def bTr : TrashArgument QVMFr :=
  { name := "trb", selector := eF 1, constraintExpressions := #[eMul (eA 3) (eA 4)] }

/-- The empty trashcan: constraint_expressions is empty, so compress emits its
    'let varN := 0' and the selector is an ADVICE column, which is what makes the
    one_minus_selector line read a_5 and not f_1. -/
def bTr2 : TrashArgument QVMFr :=
  { name := "trc", selector := eA 5, constraintExpressions := #[] }

/-- "gev" has NO polynomials, which is the only way trash_manifest_name's first arm
    (DIAG:233-240, the empty-polynomial gate filter) can ever fire. -/
def bCs : ConstraintSystem QVMFr :=
  { (ConstraintSystem.default : ConstraintSystem QVMFr) with
      gates := #[qGate "g0" [eMul (eA 0) (eA 1)] [{ index := 0, isSimple := true }],
                qGate "g1" [eAdd (eScale (eA 2) 3) (eC 5), eA 3] [],
                qGate "g2" [eMul (eMul (eA 0) (eA 1)) (eMul (eA 2) (eA 3))] [],
                qGate "gev" [] []],
      numFixedColumns := 3, numAdviceColumns := 6, numInstanceColumns := 2,
      fixedQueries := #[(colF 1, Rotation.cur)],
      adviceQueries := #[(colA 0, Rotation.cur), (colA 1, Rotation.cur), (colA 2, Rotation.cur),
        (colA 3, Rotation.cur), (colA 4, Rotation.cur), (colA 5, Rotation.cur)],
      instanceQueries := #[(colI 0, Rotation.cur)],
      lookups := #[bLk, bLk2],
      trashcans := #[bTr, bTr2] }

def bData : Data :=
  { qDataEmpty with
      challenges := [wmem (pCh 0), wmem (pCh 1)],
      instanceEval := wmem pIe,
      committedInstanceEvals := [((0, 0), wmem (pCi 0))],
      adviceEvals := [((0, 0), wmem (pA 0)), ((1, 0), wmem (pA 1)),
        ((2, 0), wmem (pA 2)), ((3, 0), wmem (pA 3)), ((4, 0), wmem (pA 4)),
        ((5, 0), wmem (pA 5))],
      fixedEvals := [((1, 0), wmem 0x4800)],
      permutationEvals := [(colA 0, wmem (pS 0)), (colA 1, wmem (pS 1)),
        (colA 2, wmem (pS 2)), (colA 3, wmem (pS 3))],
      permutationZEvals := [(wmem (pZc 0), wmem (pZn 0), some (wmem (pZl 0))),
        (wmem (pZc 1), wmem (pZn 1), some (wmem (pZl 1))),
        (wmem (pZc 2), wmem (pZn 2), none)],
      lookupEvals := [(wmem pM, [wmem (pH 0), wmem (pH 1)], wmem pLz, wmem pLzn),
        (wmem 0x7040, [wmem (pH 2)], wmem 0x7240, wmem 0x7340)],
      trashcanEvals := [wmem (pT 0), wmem (pT 1)] }

/-- The protocol plan is set to what the Evaluator ACTUALLY produces for this circuit:
    4 gate identities, 6 permutation identities (the Evaluator zips z_evals with
    columns.chunks(chunk_len), so 3 sets x 2 columns = 2 product identities, not 3 - see
    permProductCountDivergesFromEvaluator_ok), 4 + 3 lookup identities and 2 trash. The
    four assert_eq! at Q:941-960 are what makes this a cross-check and not a guess: get any
    count wrong and quotientIdentityParts aborts. -/
def bProto : ProtocolPlan :=
  { protocolPlanDefault with
      lookupChunks := [2, 1],
      quotient := { quotientIdentityPlanDefault with
        gates := 4, permutation := 6, lookup := 7, trash := 2 } }

def bMeta : ConstraintSystemMeta :=
  { constraintSystemMetaDefault with
      protocol := bProto, numFixeds := 3,
      permutationColumns := [colA 0, colA 1, colA 2, colA 3], permutationChunkLen := 2,
      numLookups := 2, lookupChunks := [2, 1], numTrashcans := 2, numPermutationZs := 3,
      numQuotients := 1, simpleSelectorCols := [0], numCommittedInstances := 1 }

def bField : FieldCtx QVMFr := qFrCtx qDelta
def bEv : Evaluator QVMFr := Evaluator.new bField bCs bMeta bData
def bSlots : QuotientStateSlots := QuotientStateSlots.new 0xb000
def bHorner : StructuredFold := StructuredFold.horner bSlots false
def bHornerTrace : StructuredFold := StructuredFold.horner bSlots true
/-- m = 19, so weight_of j = 18 - j: the same m the FoldTypes fixture folds with, chosen so
    the two packages' weights are comparable. trace = true so the trace lines are visible. -/
def bWeighted : StructuredFold := StructuredFold.weighted 19 true
def bScratch : Nat := 0xa000

def runBlocks {α : Type} (x : FM QVMFr α) : Except Fault α :=
  (x.run { ev := bEv, block := [], sites := [] }).map Prod.fst

def blockOf (x : Except Fault (Option (List String) × List FoldSite × Evaluator QVMFr)) :
    List String :=
  match x with | .ok (some b, _, _) => b | _ => []

def sitesOf (x : Except Fault (Option (List String) × List FoldSite × Evaluator QVMFr)) :
    List FoldSite :=
  match x with | .ok (_, s, _) => s | _ => []

/-- A FoldSite has no BEq (SiteLabel carries a function, FoldTypes.lean:217-224), so sites
    are compared through this rendering: function name, label, weight, bucket. The function
    name is the FIRST thing it shows, because hazard 3 is about that field being empty. -/
def siteKey (s : FoldSite) : String :=
  let lbl := match s.label with
    | SiteLabel.fixed l => FoldLabel.display l
    | SiteLabel.loop lp l =>
        "loop " ++ lp.var ++ " " ++ toString lp.start ++ ".." ++ toString lp.end_ ++ ": "
          ++ FoldLabel.display (l 0)
  let w := match s.weight with
    | FoldWeight.fixed k => "w=" ++ toString k
    | FoldWeight.loopDown k v => "wdn=" ++ toString k ++ "/" ++ v
  "fn[" ++ s.function ++ "] " ++ lbl ++ " " ++ w ++ " bucket=" ++ s.bucket.name

def memKey : QuotientMem -> String
  | .literal p => "lit" ++ toString p
  | .token t => "tok" ++ toString t
  | .tokenOffset t o => "tok" ++ toString t ++ "+" ++ toString o

def exprKey : QuotientExpr -> String
  | .const w => "c" ++ toString w.toNat
  | .mem m => "m(" ++ memKey m ++ ")"
  | .add a b => "(" ++ exprKey a ++ "+" ++ exprKey b ++ ")"
  | .mul a b => "(" ++ exprKey a ++ "*" ++ exprKey b ++ ")"
  | .neg a => "-" ++ exprKey a

def identKey (i : QuotientIdentity) : String :=
  "j=" ++ toString i.meta_.globalIndex ++ " src=" ++ sourceName i.meta_.source
    ++ " var=" ++ i.var ++ " tgt="
    ++ (match i.target with | .main => "main" | .selector k => "sel" ++ toString k)
    ++ " nl=" ++ toString i.lines.length ++ " expr=" ++ exprKey i.expr



/-- A plan with one inline identity on each target and one native identity, so all six
    families are exercised at once. The selector identity needs a gap (Q:1031's expect). -/
def kIdentity (j : Nat) (target : QuotientTarget) : QuotientIdentity :=
  { meta_ := { globalIndex := j, source := QuotientIdentitySource.permutation j },
    lines := ["let var0 := mload(0x4000)", "let var1 := addmod(var0, 1, r)"],
    var := "var1", target := target,
    expr := QuotientExpr.add (QuotientExpr.mem (QuotientMem.literal 0x4000))
      (QuotientExpr.const (BitVec.ofNat 256 1)) }

def kFold : SelectorFoldPlan :=
  { gapsByIdentity := [none, some 3], tailExponents := [], maxPower := 3 }

def kPlan : QuotientProgramPlan :=
  { inlineIdentities := [kIdentity 0 QuotientTarget.main, kIdentity 1 (QuotientTarget.selector 0)],
    items := [], nativeIdentities := [kIdentity 5 QuotientTarget.main],
    nativePermutationIdentities := [], nativeLookupIdentities := [],
    structuredTailIdentities := [], sortedSimple := [0],
    hasNativePermutation := true, hasNativeLookup := true, selectorFold := kFold }

/-- The two direct_quotient_block shapes, pinned here so the compact gate is not circular
    about the inline arm: open brace, the identity's own lines, the scratch store, the fold
    advance, then either the main addmod or the selector bucket with its gap power. The gap
    power is Y_POW[3] at 0xb040 + 3*0x20 = 0xb0a0, rendered as add(0xb040, 0x60). -/
def kInlineMain : List String :=
  [ "{", "let var0 := mload(0x4000)", "let var1 := addmod(var0, 1, r)",
    "mstore(0xa000, var1)", "}",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), mload(0xa000), r))" ]

def kInlineSelector : List String :=
  [ "{", "let var0 := mload(0x4000)", "let var1 := addmod(var0, 1, r)",
    "mstore(0xa000, var1)", "}",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "{", "let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x0)",
    "let q_selector_acc := mload(q_selector_ptr)",
    "q_selector_acc := mulmod(q_selector_acc, mload(add(0xb040, 0x60)), r)",
    "mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa000), r))", "}" ]

/-- The seven pinned identity keys of GATE 22, rendered by identKey. -/
def kIdent0 : String :=
  "j=0 src=cs.gates()[0] \"g0\" polynomial[0] var=var0 tgt=sel0 nl=3 expr=(m(lit16384)*m(lit16416))"
def kIdent1 : String :=
  "j=1 src=cs.gates()[1] \"g1\" polynomial[0] var=var3 tgt=main nl=5 expr=((m(lit16448)*c3)+c5)"
def kIdent3 : String :=
  "j=3 src=cs.gates()[2] \"g2\" polynomial[0] var=var2 tgt=main nl=7 expr=((m(lit16384)*m(lit16416))*(m(lit16448)*m(lit16480)))"
def kIdent4 : String :=
  "j=4 src=permutation identity 0 var=var2 tgt=main nl=3 expr=(m(tok1)*(c1+-m(lit24576)))"
def kIdent10 : String :=
  "j=10 src=lookup 0 identity 0 var=var3 tgt=main nl=4 expr=((m(tok1)+m(tok2))*m(lit29184))"
def kIdent13 : String :=
  "j=13 src=lookup 0 identity 3 var=var11 tgt=main nl=14 expr=((c1+-(m(tok2)+m(tok3)))*(((m(lit29440)+-(m(lit29184)+(m(lit18432)*(m(lit28928)+m(lit28960)))))*(((c0*m(tok7))+m(lit18432))+m(tok4)))+m(lit28672)))"
def kIdent14 : String :=
  "j=14 src=lookup 1 identity 4 var=var3 tgt=main nl=4 expr=((m(tok1)+m(tok2))*m(lit29248))"
/-! ## The pins -/

/-- The whole permutation block, Horner, trace off (GATE 3). -/
def kPermBlock : List String :=
  [ "{",
    "let delta := 0x7",
    "let q_perm_vals := 0xa000",
    "let q_perm_sigmas := 0xa080",
    "let q_perm_z_cur := 0xa100",
    "let q_perm_z_next := 0xa160",
    "let q_perm_z_last := 0xa1c0",
    "let q_perm_delta_base_ptr := 0xa200",
    "let q_perm_num_cols := 4",
    "let q_perm_num_sets := 3",
    "let q_perm_chunk_len := 2",
    "let q_perm_delta_chunk := 0x31",
    "{",
    "for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 4) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {",
    "let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)",
    "let q_perm_val_load_src_off := q_perm_val_load_dst_off",
    "mstore(add(add(q_perm_vals, 0x0), q_perm_val_load_dst_off), mload(add(0x4000, q_perm_val_load_src_off)))",
    "}",
    "}",
    "{",
    "for { let q_perm_sigma_load_i := 0 } lt(q_perm_sigma_load_i, 4) { q_perm_sigma_load_i := add(q_perm_sigma_load_i, 1) } {",
    "let q_perm_sigma_load_dst_off := shl(5, q_perm_sigma_load_i)",
    "let q_perm_sigma_load_src_off := mul(q_perm_sigma_load_i, 0x40)",
    "mstore(add(add(q_perm_sigmas, 0x0), q_perm_sigma_load_dst_off), mload(add(0x5000, q_perm_sigma_load_src_off)))",
    "}",
    "}",
    "{",
    "for { let q_perm_z_cur_load_i := 0 } lt(q_perm_z_cur_load_i, 3) { q_perm_z_cur_load_i := add(q_perm_z_cur_load_i, 1) } {",
    "let q_perm_z_cur_load_dst_off := shl(5, q_perm_z_cur_load_i)",
    "let q_perm_z_cur_load_src_off := q_perm_z_cur_load_dst_off",
    "mstore(add(add(q_perm_z_cur, 0x0), q_perm_z_cur_load_dst_off), mload(add(0x6000, q_perm_z_cur_load_src_off)))",
    "}",
    "}",
    "{",
    "for { let q_perm_z_next_load_i := 0 } lt(q_perm_z_next_load_i, 3) { q_perm_z_next_load_i := add(q_perm_z_next_load_i, 1) } {",
    "let q_perm_z_next_load_dst_off := shl(5, q_perm_z_next_load_i)",
    "let q_perm_z_next_load_src_off := q_perm_z_next_load_dst_off",
    "mstore(add(add(q_perm_z_next, 0x0), q_perm_z_next_load_dst_off), mload(add(0x6100, q_perm_z_next_load_src_off)))",
    "}",
    "}",
    "mstore(add(q_perm_z_last, 0x0), mload(0x6200))",
    "mstore(add(q_perm_z_last, 0x20), mload(0x6220))",
    "let q_perm_eval := 0",
    "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_perm_eval, r))",
    "let q_perm_zn := mload(add(q_perm_z_cur, 0x40))",
    "q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_perm_eval, r))",
    "for { let q_perm_i := 1 } lt(q_perm_i, 3) { q_perm_i := add(q_perm_i, 1) } {",
    "let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))",
    "let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))",
    "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_perm_eval, r))",
    "}",
    "mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))",
    "for { let q_perm_set := 0 } lt(q_perm_set, 3) { q_perm_set := add(q_perm_set, 1) } {",
    "let q_perm_start := mul(q_perm_set, q_perm_chunk_len)",
    "let q_perm_end := add(q_perm_start, q_perm_chunk_len)",
    "if gt(q_perm_end, q_perm_num_cols) { q_perm_end := q_perm_num_cols }",
    "let q_perm_left := mload(add(q_perm_z_next, shl(5, q_perm_set)))",
    "let q_perm_right := mload(add(q_perm_z_cur, shl(5, q_perm_set)))",
    "let q_perm_delta_pow := mload(q_perm_delta_base_ptr)",
    "for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {",
    "let q_perm_off := shl(5, q_perm_j)",
    "let q_perm_v := mload(add(q_perm_vals, q_perm_off))",
    "let q_perm_s := mload(add(q_perm_sigmas, q_perm_off))",
    "q_perm_left := mulmod(q_perm_left, addmod(addmod(q_perm_v, mulmod(mload(BETA_MPTR), q_perm_s, r), r), mload(GAMMA_MPTR), r), r)",
    "q_perm_right := mulmod(q_perm_right, addmod(addmod(q_perm_v, q_perm_delta_pow, r), mload(GAMMA_MPTR), r), r)",
    "q_perm_delta_pow := mulmod(q_perm_delta_pow, delta, r)",
    "}",
    "q_perm_eval := mulmod(addmod(1, sub(r, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r)), r), addmod(q_perm_left, sub(r, q_perm_right), r), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_perm_eval, r))",
    "mstore(q_perm_delta_base_ptr, mulmod(mload(q_perm_delta_base_ptr), q_perm_delta_chunk, r))",
    "}",
    "}" ]

/-- The whole permutation block, Weighted m = 19, trace on (GATE 4). -/
def kPermWBlock : List String :=
  [ "{",
    "let delta := 0x7",
    "let q_perm_vals := 0xa000",
    "let q_perm_sigmas := 0xa080",
    "let q_perm_z_cur := 0xa100",
    "let q_perm_z_next := 0xa160",
    "let q_perm_z_last := 0xa1c0",
    "let q_perm_delta_base_ptr := 0xa200",
    "let q_perm_num_cols := 4",
    "let q_perm_num_sets := 3",
    "let q_perm_chunk_len := 2",
    "let q_perm_delta_chunk := 0x31",
    "{",
    "for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 4) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {",
    "let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)",
    "let q_perm_val_load_src_off := q_perm_val_load_dst_off",
    "mstore(add(add(q_perm_vals, 0x0), q_perm_val_load_dst_off), mload(add(0x4000, q_perm_val_load_src_off)))",
    "}",
    "}",
    "{",
    "for { let q_perm_sigma_load_i := 0 } lt(q_perm_sigma_load_i, 4) { q_perm_sigma_load_i := add(q_perm_sigma_load_i, 1) } {",
    "let q_perm_sigma_load_dst_off := shl(5, q_perm_sigma_load_i)",
    "let q_perm_sigma_load_src_off := mul(q_perm_sigma_load_i, 0x40)",
    "mstore(add(add(q_perm_sigmas, 0x0), q_perm_sigma_load_dst_off), mload(add(0x5000, q_perm_sigma_load_src_off)))",
    "}",
    "}",
    "{",
    "for { let q_perm_z_cur_load_i := 0 } lt(q_perm_z_cur_load_i, 3) { q_perm_z_cur_load_i := add(q_perm_z_cur_load_i, 1) } {",
    "let q_perm_z_cur_load_dst_off := shl(5, q_perm_z_cur_load_i)",
    "let q_perm_z_cur_load_src_off := q_perm_z_cur_load_dst_off",
    "mstore(add(add(q_perm_z_cur, 0x0), q_perm_z_cur_load_dst_off), mload(add(0x6000, q_perm_z_cur_load_src_off)))",
    "}",
    "}",
    "{",
    "for { let q_perm_z_next_load_i := 0 } lt(q_perm_z_next_load_i, 3) { q_perm_z_next_load_i := add(q_perm_z_next_load_i, 1) } {",
    "let q_perm_z_next_load_dst_off := shl(5, q_perm_z_next_load_i)",
    "let q_perm_z_next_load_src_off := q_perm_z_next_load_dst_off",
    "mstore(add(add(q_perm_z_next, 0x0), q_perm_z_next_load_dst_off), mload(add(0x6100, q_perm_z_next_load_src_off)))",
    "}",
    "}",
    "mstore(add(q_perm_z_last, 0x0), mload(0x6200))",
    "mstore(add(q_perm_z_last, 0x20), mload(0x6220))",
    "let q_perm_eval := 0",
    "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)",
    "trace_u256(30003, q_perm_eval)",
    "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(YP_15), q_perm_eval, r), r))",
    "let q_perm_zn := mload(add(q_perm_z_cur, 0x40))",
    "q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)",
    "trace_u256(30004, q_perm_eval)",
    "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(YP_14), q_perm_eval, r), r))",
    "for { let q_perm_i := 1 } lt(q_perm_i, 3) { q_perm_i := add(q_perm_i, 1) } {",
    "let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))",
    "let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))",
    "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)",
    "trace_u256(add(30004, q_perm_i), q_perm_eval)",
    "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(sub(YP_14, shl(5, q_perm_i))), q_perm_eval, r), r))",
    "}",
    "mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))",
    "for { let q_perm_set := 0 } lt(q_perm_set, 3) { q_perm_set := add(q_perm_set, 1) } {",
    "let q_perm_start := mul(q_perm_set, q_perm_chunk_len)",
    "let q_perm_end := add(q_perm_start, q_perm_chunk_len)",
    "if gt(q_perm_end, q_perm_num_cols) { q_perm_end := q_perm_num_cols }",
    "let q_perm_left := mload(add(q_perm_z_next, shl(5, q_perm_set)))",
    "let q_perm_right := mload(add(q_perm_z_cur, shl(5, q_perm_set)))",
    "let q_perm_delta_pow := mload(q_perm_delta_base_ptr)",
    "for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {",
    "let q_perm_off := shl(5, q_perm_j)",
    "let q_perm_v := mload(add(q_perm_vals, q_perm_off))",
    "let q_perm_s := mload(add(q_perm_sigmas, q_perm_off))",
    "q_perm_left := mulmod(q_perm_left, addmod(addmod(q_perm_v, mulmod(mload(BETA_MPTR), q_perm_s, r), r), mload(GAMMA_MPTR), r), r)",
    "q_perm_right := mulmod(q_perm_right, addmod(addmod(q_perm_v, q_perm_delta_pow, r), mload(GAMMA_MPTR), r), r)",
    "q_perm_delta_pow := mulmod(q_perm_delta_pow, delta, r)",
    "}",
    "q_perm_eval := mulmod(addmod(1, sub(r, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r)), r), addmod(q_perm_left, sub(r, q_perm_right), r), r)",
    "trace_u256(add(30007, q_perm_set), q_perm_eval)",
    "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(sub(YP_11, shl(5, q_perm_set))), q_perm_eval, r), r))",
    "mstore(q_perm_delta_base_ptr, mulmod(mload(q_perm_delta_base_ptr), q_perm_delta_chunk, r))",
    "}",
    "}" ]

/-- The whole lookup block, Horner, trace off (GATE 9). -/
def kLookupBlock : List String :=
  [ "{",
    "let q_lookup_f := 0xa000",
    "let q_lookup_prefix := 0xa080",
    "let q_lookup_suffix := 0xa100",
    "let q_lookup_l0 := mload(L_0_MPTR)",
    "let q_lookup_llast := mload(L_LAST_MPTR)",
    "let q_lookup_lblind := mload(L_BLIND_MPTR)",
    "let q_lookup_lsum := addmod(q_lookup_l0, q_lookup_llast, r)",
    "let q_lookup_active := addmod(1, sub(r, addmod(q_lookup_llast, q_lookup_lblind, r)), r)",
    "let q_lookup_beta := mload(BETA_MPTR)",
    "let q_lookup_theta := mload(THETA_MPTR)",
    "{",
    "{",
    "let q_lookup_eval := mulmod(q_lookup_lsum, mload(0x7200), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "{",
    "let a_0 := mload(0x4000)",
    "let var0 := addmod(mulmod(0, q_lookup_theta, r), a_0, r)",
    "mstore(add(q_lookup_f, 0x0), addmod(var0, q_lookup_beta, r))",
    "let a_1 := mload(0x4020)",
    "let var1 := addmod(mulmod(0, q_lookup_theta, r), a_1, r)",
    "mstore(add(q_lookup_f, 0x20), addmod(var1, q_lookup_beta, r))",
    "let a_2 := mload(0x4040)",
    "let var2 := addmod(mulmod(0, q_lookup_theta, r), a_2, r)",
    "mstore(add(q_lookup_f, 0x40), addmod(var2, q_lookup_beta, r))",
    "let a_3 := mload(0x4060)",
    "let var3 := addmod(mulmod(0, q_lookup_theta, r), a_3, r)",
    "mstore(add(q_lookup_f, 0x60), addmod(var3, q_lookup_beta, r))",
    "let q_lookup_product := 1",
    "for { let q_lookup_prod_i := 0 } lt(q_lookup_prod_i, 4) { q_lookup_prod_i := add(q_lookup_prod_i, 1) } {",
    "q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)",
    "}",
    "mstore(q_lookup_prefix, 1)",
    "for { let q_lookup_pref_i := 1 } lt(q_lookup_pref_i, 4) { q_lookup_pref_i := add(q_lookup_pref_i, 1) } {",
    "let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)",
    "mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))",
    "}",
    "mstore(add(q_lookup_suffix, 0x60), 1)",
    "for { let q_lookup_suf_i := sub(4, 1) } gt(q_lookup_suf_i, 0) { q_lookup_suf_i := sub(q_lookup_suf_i, 1) } {",
    "let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)",
    "mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))",
    "}",
    "let q_lookup_sum := 0",
    "for { let q_lookup_sum_i := 0 } lt(q_lookup_sum_i, 4) { q_lookup_sum_i := add(q_lookup_sum_i, 1) } {",
    "q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)",
    "}",
    "let q_lookup_eval := addmod(mulmod(mload(0x7100), q_lookup_product, r), sub(r, q_lookup_sum), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "{",
    "let a_4 := mload(0x4080)",
    "let var0 := addmod(mulmod(0, q_lookup_theta, r), a_4, r)",
    "let q_lookup_eval := addmod(mulmod(mload(0x7120), addmod(var0, q_lookup_beta, r), r), sub(r, 1), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "{",
    "let q_lookup_sum_h := mload(0x7100)",
    "q_lookup_sum_h := addmod(q_lookup_sum_h, mload(0x7120), r)",
    "let f_1 := mload(0x4800)",
    "let var0 := addmod(mulmod(0, q_lookup_theta, r), f_1, r)",
    "let q_lookup_s_sum_h := mulmod(f_1, q_lookup_sum_h, r)",
    "let q_lookup_diff := addmod(mload(0x7300), sub(r, addmod(mload(0x7200), q_lookup_s_sum_h, r)), r)",
    "let q_lookup_t_beta := addmod(var0, q_lookup_beta, r)",
    "let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0x7000), r)",
    "let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "}",
    "{",
    "{",
    "let q_lookup_eval := mulmod(q_lookup_lsum, mload(0x7240), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "{",
    "let a_0 := mload(0x4000)",
    "let var0 := addmod(mulmod(0, q_lookup_theta, r), a_0, r)",
    "let var1 := mulmod(var0, q_lookup_theta, r)",
    "for { let q_lookup_shared_i := 0 } lt(q_lookup_shared_i, 3) { q_lookup_shared_i := add(q_lookup_shared_i, 1) } {",
    "let q_lookup_shared_off := shl(5, q_lookup_shared_i)",
    "let q_lookup_shared_tail := mload(add(0x4020, q_lookup_shared_off))",
    "let q_lookup_shared_compressed := addmod(var1, q_lookup_shared_tail, r)",
    "mstore(add(q_lookup_f, q_lookup_shared_off), addmod(q_lookup_shared_compressed, q_lookup_beta, r))",
    "}",
    "let q_lookup_product := 1",
    "for { let q_lookup_prod_i := 0 } lt(q_lookup_prod_i, 3) { q_lookup_prod_i := add(q_lookup_prod_i, 1) } {",
    "q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)",
    "}",
    "mstore(q_lookup_prefix, 1)",
    "for { let q_lookup_pref_i := 1 } lt(q_lookup_pref_i, 3) { q_lookup_pref_i := add(q_lookup_pref_i, 1) } {",
    "let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)",
    "mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))",
    "}",
    "mstore(add(q_lookup_suffix, 0x40), 1)",
    "for { let q_lookup_suf_i := sub(3, 1) } gt(q_lookup_suf_i, 0) { q_lookup_suf_i := sub(q_lookup_suf_i, 1) } {",
    "let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)",
    "mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))",
    "}",
    "let q_lookup_sum := 0",
    "for { let q_lookup_sum_i := 0 } lt(q_lookup_sum_i, 3) { q_lookup_sum_i := add(q_lookup_sum_i, 1) } {",
    "q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)",
    "}",
    "let q_lookup_eval := addmod(mulmod(mload(0x7140), q_lookup_product, r), sub(r, q_lookup_sum), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "{",
    "let q_lookup_sum_h := mload(0x7140)",
    "let f_1 := mload(0x4800)",
    "let var0 := addmod(mulmod(0, q_lookup_theta, r), f_1, r)",
    "let q_lookup_s_sum_h := mulmod(f_1, q_lookup_sum_h, r)",
    "let q_lookup_diff := addmod(mload(0x7340), sub(r, addmod(mload(0x7240), q_lookup_s_sum_h, r)), r)",
    "let q_lookup_t_beta := addmod(var0, q_lookup_beta, r)",
    "let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0x7040), r)",
    "let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_lookup_eval, r))",
    "}",
    "}",
    "}" ]

/-- The whole trash block, Horner, trace off (GATE 13). -/
def kTrashBlock : List String :=
  [ "{",
    "let q_trash_tau := mload(TRASH_CHALLENGE_MPTR)",
    "{",
    "let a_3 := mload(0x4060)",
    "let a_4 := mload(0x4080)",
    "let var0 := mulmod(a_3, a_4, r)",
    "let var1 := addmod(mulmod(0, q_trash_tau, r), var0, r)",
    "let f_1 := mload(0x4800)",
    "let q_trash_one_minus_selector := addmod(1, sub(r, f_1), r)",
    "let q_trash_scaled := mulmod(q_trash_one_minus_selector, mload(0x8000), r)",
    "let q_trash_eval := addmod(var1, sub(r, q_trash_scaled), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_trash_eval, r))",
    "}",
    "{",
    "let var0 := 0",
    "let a_5 := mload(0x40a0)",
    "let q_trash_one_minus_selector := addmod(1, sub(r, a_5), r)",
    "let q_trash_scaled := mulmod(q_trash_one_minus_selector, mload(0x8020), r)",
    "let q_trash_eval := addmod(var0, sub(r, q_trash_scaled), r)",
    "mstore(0xb000, mulmod(mload(0xb000), y, r))",
    "mstore(0xb000, addmod(mload(0xb000), q_trash_eval, r))",
    "}",
    "}" ]

/-- The whole trash block, Weighted m = 19, trace on (GATE 14). -/
def kTrashWBlock : List String :=
  [ "{",
    "let q_trash_tau := mload(TRASH_CHALLENGE_MPTR)",
    "{",
    "let a_3 := mload(0x4060)",
    "let a_4 := mload(0x4080)",
    "let var0 := mulmod(a_3, a_4, r)",
    "let var1 := addmod(mulmod(0, q_trash_tau, r), var0, r)",
    "let f_1 := mload(0x4800)",
    "let q_trash_one_minus_selector := addmod(1, sub(r, f_1), r)",
    "let q_trash_scaled := mulmod(q_trash_one_minus_selector, mload(0x8000), r)",
    "let q_trash_eval := addmod(var1, sub(r, q_trash_scaled), r)",
    "trace_u256(30017, q_trash_eval)",
    "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(YP_1), q_trash_eval, r), r))",
    "}",
    "{",
    "let var0 := 0",
    "let a_5 := mload(0x40a0)",
    "let q_trash_one_minus_selector := addmod(1, sub(r, a_5), r)",
    "let q_trash_scaled := mulmod(q_trash_one_minus_selector, mload(0x8020), r)",
    "let q_trash_eval := addmod(var0, sub(r, q_trash_scaled), r)",
    "trace_u256(30018, q_trash_eval)",
    "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(YP_0), q_trash_eval, r), r))",
    "}",
    "}" ]

/-! ## GATE 1-2: reachability and the abort messages (D-P19) -/

/-- GATE 1 (D-P19 reachability; FIRST #eval in the section so a wrong path is diagnosed and
    not silently matched). -/
def blocksArtifactReachable_ok : IO Bool := do
  let src ← readQArtifact
  pure (qReadOk src)

/-- GATE 2 (D-P19). Every message this file renders into an abort is read back out of the
    reference. The sixteen with Rust text are the expects, the panics and the assert_eq!s;
    the direct indices (Q:1728, Q:1776, Q:1885, Q:1974) have NO message in the Rust - a Vec
    index aborts with a bounds text, not a string literal - so their sites carry a
    descriptive message of the port's and are named as such in the header. -/
def blocksAbortMessagesArtifact_ok : IO Bool := do
  let src ← readQArtifact
  let qvm ← readQVMArtifact
  let msgs := [ "gate Yul expressions and typed expressions must stay aligned",
    "selector column present",
    "lookup identity index covered by protocol lookup chunks",
    "gate identity count must match protocol plan",
    "permutation identity count must match protocol plan",
    "lookup identity count must match protocol plan",
    "trash identity count must match protocol plan", "permutation sigma eval present" ]
  let shapes := [ "gate_items.len(),", "gates.len(),", "permutation.len(),", "lookup.len(),",
    "trash.len(),", "assert_eq!(" ]
  let qvmMsgs := [ "quotient expressions can only load memory-backed words",
    "negative quotient memory pointer", "negative quotient memory token offset",
    "unsupported quotient memory token",
    "virtual selectors must be removed before quotient lowering",
    "fixed eval present", "advice eval present", "committed instance eval present" ]
  pure (src.length > 60000 && qvm.length > 100000
    && msgs.all (fun m => src.contains m) && shapes.all (fun t => src.contains t)
    && qvmMsgs.all (fun m => qvm.contains m))

/-! ## GATE 3-8: the permutation block -/

/-- GATE 3 (EXACT LINES, hazard 3's standard). The whole structured_permutation_loop_block
    for the fixture: 4 permutation columns, 3 z sets, chunk_len 2, scratch 0xa000, stream
    base 3, Horner with trace off. Derived line by line from Q:1497-1678 and tied back to
    the reference by pinnedLinesTraceToReference_ok. The parts a smoke test misses: the
    delta_base pointer is sized by num_sets.saturating_sub(1) and so sits at 0xa200 and not
    0xa220; the sigma table compacts with mul(..._i, 0x40) while the value table reuses the
    destination offset; the z_last table does NOT compact because only two of its three
    entries exist (the third set has no z_last) and two is below the count < 3 floor; and
    the two family loops use FoldLoop.header while the inner q_perm_j loop is a literal. -/
def permBlockExactLines_ok : Bool :=
  match runFamilyBlock bEv (structuredPermutationLoopBlock bScratch bHorner 3) with
  | .ok (some block, sites, _) => block == kPermBlock && sites.isEmpty && block.length == 79
  | _ => false

/-- GATE 4 (EXACT LINES, THE HAZARD-3 PIN). The same block under StructuredFold::Weighted
    with m = 19 and trace = true: every fold becomes a trace_u256 plus a
    Q_MAIN_ACC += Y_POW[w] * e statement, and FOUR sites are recorded - the two fixed ones
    and one per loop, NOT one per iteration, because a loop site is expanded later by
    folds.rs. Every recorded function name is the EMPTY STRING: that is Q:1372 and Q:1381,
    and it is the whole answer to hazard 3. Weights: 18-3 = 15, 18-4 = 14, the continuity
    loop's k0 = 18-(3+1) = 14 and the product loop's k0 = 18-(3+1+3) = 11. Trace ids are
    QUOTIENT_IDENTITY_BASE + j, i.e. 30003, 30004, add(30004, q_perm_i), add(30007,
    q_perm_set). -/
def permBlockWeightedSites_ok : Bool :=
  match runFamilyBlock bEv (structuredPermutationLoopBlock bScratch bWeighted 3) with
  | .ok (some block, sites, _) =>
      block == kPermWBlock
        && sites.length == 4
        && sites.map siteKey ==
          [ "fn[] permutation first-set boundary w=15 bucket=Q_MAIN_ACC",
            "fn[] permutation last-set boundary w=14 bucket=Q_MAIN_ACC",
            "fn[] loop q_perm_i 1..3: permutation continuity of set 0 wdn=14/q_perm_i bucket=Q_MAIN_ACC",
            "fn[] loop q_perm_set 0..3: permutation product of set 0 wdn=11/q_perm_set bucket=Q_MAIN_ACC" ]
        && sites.all (fun s => s.function == "")
  | _ => false

/-- GATE 5. num_permutation_zs == 0 returns None BEFORE anything is pushed (Q:1479-1481), so
    the block is empty and the evaluator is untouched - counter, cache and pow5 flag all
    unchanged. A port that emitted the header and then returned would still "produce
    nothing" under some readings; this pins that it produced literally nothing. -/
def permBlockEmptyWhenNoZs_ok : Bool :=
  let e := Evaluator.new bField bCs { bMeta with numPermutationZs := 0 } bData
  match runFamilyBlock e (structuredPermutationLoopBlock bScratch bHorner 0) with
  | .ok (none, sites, ev) => sites.isEmpty && ev.varCounter == 0 && ev.varCache == []
  | _ => false

/-- GATE 6 (the picked-up helper, Q:1117-1204). All five single-line rejections, the
    count < 3 floor, and both stride arms - each pinned as exact text. The pair case is the
    boundary: two adjacent entries do NOT compact (Q:1170), three do. -/
def mstoreRunArms_ok : Bool :=
  let e (n : Nat) : String := "mload(0x" ++ hexDigits n ++ ")"
  let run (es : List (Nat × String)) : List String := pushMstoreMloadLiteralRuns [] "d" es "L"
  run [(0x00, "let x")] == ["mstore(add(d, 0x0), let x)"]
    && run [(0x00, e 0x100)] == ["mstore(add(d, 0x0), mload(0x100))"]
    && run [(0x00, e 0x100), (0x40, e 0x120)]
        == ["mstore(add(d, 0x0), mload(0x100))", "mstore(add(d, 0x40), mload(0x120))"]
    && run [(0x00, e 0x100), (0x20, "1")]
        == ["mstore(add(d, 0x0), mload(0x100))", "mstore(add(d, 0x20), 1)"]
    && run [(0x20, e 0x100), (0x40, e 0x80)]
        == ["mstore(add(d, 0x20), mload(0x100))", "mstore(add(d, 0x40), mload(0x80))"]
    && run [(0x00, e 0x100), (0x20, e 0x100)]
        == ["mstore(add(d, 0x0), mload(0x100))", "mstore(add(d, 0x20), mload(0x100))"]
    && run [(0x00, e 0x100), (0x20, e 0x120)]
        == ["mstore(add(d, 0x0), mload(0x100))", "mstore(add(d, 0x20), mload(0x120))"]
    && (run [(0x00, e 0x100), (0x20, e 0x120), (0x40, e 0x140)]).length == 7
    && ((run [(0x00, e 0x100), (0x20, e 0x120), (0x40, e 0x140)]).getD 3 "")
        == "let L_src_off := L_dst_off"
    && ((run [(0x00, e 0x100), (0x20, e 0x140), (0x40, e 0x180)]).getD 3 "")
        == "let L_src_off := mul(L_i, 0x40)"
    && (run [(0x00, e 0x100), (0x20, e 0x120), (0x40, e 0x140), (0x60, "x")]).length == 8

/-- GATE 7 (FINDING, and a perturbation that must NOT redden the port). The loop block's
    product loop runs 0..num_permutation_zs (Q:1633-1637) and clamps the column range per
    set (Q:1642), so it emits num_sets fold sites. The Evaluator's straight-line path
    iterates z_evals.zip(columns.chunks(chunk_len)) (YE:356-358), i.e.
    min(num_sets, ceil(num_cols / chunk_len)) product identities. For this fixture those
    are 3 and 2: the two paths DISAGREE, and nothing in the reference compares them - the
    only count check is the assert_eq! against the protocol plan, which sees the Evaluator's
    number. Recorded rather than reconciled: the port transcribes both. -/
def permProductCountDivergesFromEvaluator_ok : Bool :=
  let permIdentities := runOpt (permutationComputations.map fun ps => ps.length) bEv
  let loopSites := sitesOf (runFamilyBlock bEv (structuredPermutationLoopBlock bScratch bWeighted 3))
  let loopProductIters := loopSites.foldl (fun acc s => match s.label with
    | SiteLabel.loop lp _ => if lp.var == "q_perm_set" then acc + (lp.end_ - lp.start) else acc
    | _ => acc) 0
  permIdentities == some 6 && loopProductIters == 3
    && bMeta.protocol.quotient.permutation == 6

/-- GATE 8. The two family loops come from FoldLoop.header; the inner q_perm_j loop is a
    hand-written literal (Q:1647). A "tidy" port that routed all three through the header
    would change the q_perm_j line, because the header always counts UP by one from a
    literal start and the inner loop starts from a VARIABLE. -/
def permLoopsUseFoldHeaderNotHandWritten_ok : Bool :=
  let block := blockOf (runFamilyBlock bEv (structuredPermutationLoopBlock bScratch bHorner 3))
  let header := FoldLoop.header { var := "q_perm_set", start := 0, end_ := 3 }
  block.any (fun l => l == header)
    && block.any (fun l => l == "for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {")
    && !block.any (fun l => l == FoldLoop.header { var := "q_perm_j", start := 0, end_ := 3 })

/-! ## GATE 9-12: the lookup block -/

/-- GATE 9 (EXACT LINES). The whole structured_lookup_loop_block: two lookups, the first
    with chunks of 4 and 1 parallel inputs (so the generic staging arm AND the k == 1 arm)
    and the second with one chunk of 3 sharing a prefix (so the shared-prefix arm), stream
    base 10, Horner trace off. The parts a smoke test misses: max_parallel is 4 and not 3,
    so q_lookup_prefix is 0xa080 and q_lookup_suffix 0xa100; the k == 1 arm is the only
    place 'sub(r, 1)' appears; the suffix seed is at (k-1)*0x20 and not at 0; the three
    staging loops are hand-written strings and NOT FoldLoop.header; and the accumulator's
    sum_h is a let followed by reassignments, with the single-h_eval lookup emitting the let
    and no reassignment at all. -/
def lookupBlockExactLines_ok : Bool :=
  match runFamilyBlock bEv (structuredLookupLoopBlock bScratch bHorner 10) with
  | .ok (some block, sites, _) => block == kLookupBlock && sites.isEmpty && block.length == 125
  | _ => false

/-- GATE 10. The scratch layout and the arms, stated as facts and not as a diff:
    max_parallel * 3 words (Q:1444), the shared-prefix arm firing for lookup 1 and not for
    lookup 0, the k == 1 arm's uniqueness, and num_lookups == 0 returning None. -/
def lookupBlockArms_ok : Bool :=
  let maxPar := runOpt (structuredLookupMaxParallel bMeta) bEv
  let block := blockOf (runFamilyBlock bEv (structuredLookupLoopBlock bScratch bHorner 10))
  let empty := runFamilyBlock
    (Evaluator.new bField bCs { bMeta with numLookups := 0 } bData)
    (structuredLookupLoopBlock bScratch bHorner 0)
  maxPar == some 4
    && block.getD 1 "" == "let q_lookup_f := 0xa000"
    && block.getD 2 "" == "let q_lookup_prefix := 0xa080"
    && block.getD 3 "" == "let q_lookup_suffix := 0xa100"
    && (block.filter (fun l => l.contains "q_lookup_shared_i")).length == 2
    && (block.filter (fun l => l.contains "q_lookup_prod_i")).length == 4
    && (block.filter (fun l => l.contains "sub(r, 1)")).length == 1
    && (match empty with | .ok (none, sites, _) => sites.isEmpty | _ => false)
    && runOpt (structuredLookupMaxParallel { bMeta with numLookups := 0 }) bEv == some 0

/-- GATE 11. The fold positions the lookup block threads: boundary, one per chunk,
    accumulator, per lookup, and the counter keeps running ACROSS lookups (Q:1704 'j = base'
    then j += 1 at every fold). Under Weighted the positions are observable as weights:
    lookup 0 has 4 identities at j = 10..13 and lookup 1 has 3 at 14..16, so the weights are
    8, 7, 6, 5 then 4, 3, 2. A port that reset j per lookup would repeat 8, 7, 6, 5. -/
def lookupBlockStreamPositions_ok : Bool :=
  let sites := sitesOf (runFamilyBlock bEv (structuredLookupLoopBlock bScratch bWeighted 10))
  let weights := sites.map (fun s => match s.weight with
    | FoldWeight.fixed k => k | FoldWeight.loopDown k _ => k)
  let labels := sites.map (fun s => FoldLabel.display (match s.label with
    | SiteLabel.fixed l => l | SiteLabel.loop _ f => f 0))
  sites.length == 7 && weights == [8, 7, 6, 5, 4, 3, 2]
    && labels == [ "lookup 0 boundary", "lookup 0 helper of chunk 0",
      "lookup 0 helper of chunk 1", "lookup 0 accumulator", "lookup 1 boundary",
      "lookup 1 helper of chunk 0", "lookup 1 accumulator" ]

/-- GATE 12 (R4). 'data.lookup_evals[lookup_idx]' (Q:1728) and 'data.trashcan_evals[idx]'
    (Q:1974) are direct indices: a meta that claims more families than Data has aborts
    instead of emitting a short block. -/
def lookupAndTrashIndexPanics_ok : Bool :=
  faultSite (runFamilyBlock (Evaluator.new bField bCs bMeta { bData with lookupEvals := [] })
    (structuredLookupLoopBlock bScratch bHorner 0))
      == qPath ++ ":1728 (lookup evals index)"
    && faultSite (runFamilyBlock (Evaluator.new bField bCs bMeta { bData with trashcanEvals := [] })
      (structuredTrashLoopBlock bHorner 0))
      == qPath ++ ":1974 (trashcan evals index)"
    -- FINDING: num_lookups is only an early-return guard (Q:1697); the loop walks
    -- cs.lookups(), so inflating the meta cannot reach the index. A port that looped
    -- 0..num_lookups instead would abort here and not there.
    && faultSite (runFamilyBlock (Evaluator.new bField bCs { bMeta with numLookups := 9 } bData)
      (structuredLookupLoopBlock bScratch bHorner 0)) == ""

/-! ## GATE 13-14: the trash block -/

/-- GATE 13 (EXACT LINES). The whole structured_trash_loop_block: two trashcans, the second
    with NO constraint expressions, which is the arm that makes compressExpressions emit
    'let var0 := 0' and the only reason the second sub-block is shorter. Stream base 17. -/
def trashBlockExactLines_ok : Bool :=
  match runFamilyBlock bEv (structuredTrashLoopBlock bHorner 17) with
  | .ok (some block, sites, _) => block == kTrashBlock && sites.isEmpty && block.length == 24
  | _ => false

/-- GATE 14. The Weighted variant: two sites at j = 17 and 18, weights 1 and 0, both with an
    EMPTY function name, and trace ids 30017 / 30018. num_trashcans == 0 returns None. -/
def trashBlockWeightedAndEmpty_ok : Bool :=
  (match runFamilyBlock bEv (structuredTrashLoopBlock bWeighted 17) with
   | .ok (some block, sites, _) =>
       block == kTrashWBlock && sites.map siteKey
         == [ "fn[] trash argument 0 w=1 bucket=Q_MAIN_ACC",
              "fn[] trash argument 1 w=0 bucket=Q_MAIN_ACC" ]
   | _ => false)
    && (let e := Evaluator.new bField bCs { bMeta with numTrashcans := 0 } bData
        match runFamilyBlock e (structuredTrashLoopBlock bHorner 0) with
        | .ok (none, sites, _) => sites.isEmpty
        | _ => false)

/-! ## GATE 15-18: the compact assembly point -/

/-- GATE 15 (hazard 4: the item P-10 declined). The assembly is checked against the three
    standalone blocks rather than re-pinned: post_vm_computations is exactly [trash block],
    native_permutation_computation is exactly the permutation block, native_lookup_computation
    is exactly the lookup block. That is the coupling the Rust's doc at Q:1997-1999 promises
    ("inline prefixes, native callbacks, structured tails ... stay coupled"), and reusing the
    pins above means a drift in either direction reddens something. The bases differ (4, 10,
    14 from the protocol plan) but Horner ignores them, so the text must be IDENTICAL - which
    is itself the point of GATE 17. -/
def compactBlocksAssembly_ok : Bool :=
  match compactQuotientComputationBlocks bField bCs bMeta bData kPlan bScratch bSlots false with
  | .ok (blocks, sites) =>
      blocks.postVmComputations == [kTrashBlock]
        && blocks.nativePermutationComputation == kPermBlock
        && blocks.nativeLookupComputation == kLookupBlock
        && blocks.inlineComputations.length == 2
        && blocks.nativeIdentityComputations.length == 1
        && blocks.inlineComputations.getD 0 [] == kInlineMain
        && blocks.inlineComputations.getD 1 [] == kInlineSelector
        && blocks.nativeIdentityComputations.getD 0 [] == kInlineMain
        && sites.isEmpty
  | .error _ => false

/-- GATE 16 (hazard 3's second half). eval_numer_computations is Vec::new() at Q:2032 and
    the site recorder is empty at every fold, because all three family calls pass
    StructuredFold::Horner (Q:2039, Q:2057, Q:2074). Flipping the two native flags off must
    empty exactly the two fields they gate and leave the rest byte-identical; and an empty
    plan with no trash must be the Rust's Default. -/
def compactBlocksFlagsAndEmptyFamilies_ok : Bool :=
  match compactQuotientComputationBlocks bField bCs bMeta bData kPlan bScratch bSlots false with
  | .ok (blocks, sites) =>
      blocks.evalNumerComputations == [] && sites.isEmpty
        && (match compactQuotientComputationBlocks bField bCs bMeta bData
                { kPlan with hasNativePermutation := false, hasNativeLookup := false }
                bScratch bSlots false with
            | .ok (b2, _) =>
                b2.nativePermutationComputation == [] && b2.nativeLookupComputation == []
                  && b2.postVmComputations == blocks.postVmComputations
                  && b2.inlineComputations == blocks.inlineComputations
                  && b2.nativeIdentityComputations == blocks.nativeIdentityComputations
            | .error _ => false)
        && (match compactQuotientComputationBlocks bField bCs { bMeta with numTrashcans := 0 }
                bData { kPlan with inlineIdentities := [], nativeIdentities := [], hasNativePermutation := false, hasNativeLookup := false }
                bScratch bSlots false with
            | .ok (b3, _) => b3 == quotientComputationBlocksDefault
            | .error _ => false)
  | .error _ => false

/-- GATE 17. The three stream bases are DEAD in the compact path: Horner ignores the FoldPos
    (Q:1361-1363 routes to push_structured_main_fold, which never looks at the position), so
    changing every protocol count leaves the emitted text untouched - while the same change
    moves quotient_identity_parts' global indices (identityPartsCountAsserts_ok). That
    asymmetry is why the bases are threaded at all: Q:2011-2012 says they exist for the
    direct lowering's weights, which is M10. -/
def compactBasesInvisibleUnderHorner_ok : Bool :=
  let moved := { bProto with
    quotient := { bProto.quotient with gates := 9, permutation := 9, lookup := 9, trash := 9 } }
  match (compactQuotientComputationBlocks bField bCs { bMeta with protocol := moved } bData kPlan
            bScratch bSlots false,
         compactQuotientComputationBlocks bField bCs bMeta bData kPlan bScratch bSlots false) with
  | (.ok (a, _), .ok (b, _)) => a == b
  | _ => false

/-- GATE 18 (the two fault taxonomies). direct_quotient_block's selector-gap abort is a
    QVMFault; compact surfaces it as a Halo2 panic whose site is the QVMFault's own message,
    which for .panic is the site string unchanged (VmReference.lean:334). So the Q:1031 cite
    survives the crossing. -/
def liftQVMPreservesSite_ok : Bool :=
  let fold : SelectorFoldPlan :=
    { gapsByIdentity := [none, none], tailExponents := [], maxPower := 0 }
  let plan : QuotientProgramPlan := { kPlan with selectorFold := fold }
  match compactQuotientComputationBlocks bField bCs bMeta bData plan bScratch bSlots false with
  | .error (Fault.panic s) => s.contains ":1031 (selector gap for compact direct quotient block)"
  | _ => false

/-! ## GATE 19-24: the bridge and quotient_identity_parts -/

/-- GATE 19 (THE BRIDGE, both legs). For every identity the stream produces, re-parsing its
    emitted Yul through quotient_yul_expr reproduces the stored expr - the bridge is a fixed
    point of its own input, which is the property Q:976-977 claims ("Parse an
    evaluator-emitted Yul identity into the quotient AST once at plan-construction time").
    The three PARSED families round-trip exactly. The gate family does not, and cannot: its
    stored expr is the plonk lowering and the reparse is the Yul lowering, and the
    Evaluator's sum-fusion (YE:897-986) emits addmod(const, mul) where the Expression is
    Add(Mul, Const). GATE 19b pins that one divergence instead of hiding it. -/
def bridgeRoundTrip_ok : Bool :=
  match quotientIdentityParts bField bCs bMeta bData with
  | .ok ps =>
      let all := ps.allIdentities
      all.length == 19
        && (ps.permutation ++ ps.lookup ++ ps.trash).all (fun i =>
             match quotientYulExpr i.lines i.var with
             | .ok e => e == i.expr
             | .error _ => false)
        && (ps.gates.filter (fun i => match quotientYulExpr i.lines i.var with
              | .ok e => e != i.expr
              | .error _ => true)).length == 1
  | .error _ => false

/-- GATE 19b (FINDING, pinned rather than hidden). The gate family's two routes disagree
    for exactly one identity: g1's first polynomial is Sum(Scaled(a_2, 3), Constant 5), which
    the plonk lowering renders as add(mul(a_2,3), 5) while the Evaluator's sum-fusion emits
    'let var3 := addmod(5, mulmod(a_2, 3, r), r)', which reparses as add(5, mul(a_2,3)). Same
    field value, different operand ORDER, and therefore different QuotientExpr and different
    VM bytecode shape (the builder's commutative-key canonicalisation at QVM:2990 is what
    stops this from becoming a cache miss downstream - not ported here). A gate that only
    checked "the bridge reproduces the stored expr" would be false for the gate family and a
    careless port would "fix" the bridge instead of recording the divergence. -/
def gateRouteOperandOrderDivergence_ok : Bool :=
  match quotientIdentityParts bField bCs bMeta bData with
  | .ok ps => match (ps.gates.drop 1).head? with
    | some i =>
        exprKey i.expr == "((m(lit16448)*c3)+c5)"
          && (match quotientYulExpr i.lines i.var with
              | .ok e => exprKey e == "(c5+(m(lit16448)*c3))"
              | .error _ => false)
          && i.lines.any (fun l => l == "let var3 := addmod(var0, var2, r)")
          && i.lines.any (fun l => l == "let var0 := 0x5")
          && i.lines.any (fun l => l == "let var2 := mulmod(a_2, var1, r)")
    | none => false
  | .error _ => false

/-- GATE 20 (negative control, R-41). The bridge is a SHALLOW parser: a line it does not
    understand aborts rather than being skipped, and a variable it never saw aborts. Both are
    the QVM:1240 / QVM:1267 class of panic, and a port that returned a default expr instead
    would silently lower a wrong program. -/
def bridgeRejectsUnsupportedYul_ok : Bool :=
  isFault (quotientYulExpr ["let x := frobnicate(1, 2)"] "x")
    && isFault (quotientYulExpr ["not an assignment at all"] "y")
    && isFault (quotientYulExpr ["let x := mload(0x100)"] "never_bound")
    && (match quotientYulExpr ["let x := mload(0x100)"] "x" with
        | .ok e => e == QuotientExpr.mem (QuotientMem.literal 0x100)
        | .error _ => false)

/-- GATE 21 (the QVM chain's arms and aborts, R4). Every arm of DataQuotientExpressionEnv and
    every abort of word_to_quotient_expr / ptr_to_quotient_mem, each pinned to its own line:
    the simple-selector fixed column synthesises 1 and does NOT look up; a virtual selector
    aborts; a missing eval aborts; a challenge index past the end aborts; a CALLOUT-DATA word
    aborts at :2957 and not at :2967; a negative integer pointer aborts; a negative token
    offset aborts BEFORE the token name is consulted; and an unknown token name carries the
    name in its message. -/
def plonkEnvArms_ok : Bool :=
  let env := DataQuotientExpressionEnv.env { meta_ := bMeta, data := bData }
  (match env.fixed 0 0 with | .ok e => e == QuotientExpr.const (BitVec.ofNat 256 1) | _ => false)
    && (match env.fixed 1 0 with
        | .ok e => e == QuotientExpr.mem (QuotientMem.literal 0x4800) | _ => false)
    && isFault (env.fixed 7 0)
    && (match env.advice 2 0 with
        | .ok e => e == QuotientExpr.mem (QuotientMem.literal (pA 2)) | _ => false)
    && (match env.instance_ 0 0 with
        | .ok e => e == QuotientExpr.mem (QuotientMem.literal (pCi 0)) | _ => false)
    && (match env.instance_ 1 0 with
        | .ok e => e == QuotientExpr.mem (QuotientMem.literal pIe) | _ => false)
    && (match env.challenge 0 with
        | .ok e => e == QuotientExpr.mem (QuotientMem.literal (pCh 0)) | _ => false)
    && faultSite (env.challenge 9) == qvmPath ++ ":2950 (challenges index)"
    && faultSite (env.selector { index := 0, isSimple := false })
        == qvmPath ++ ":2904 (virtual selectors must be removed before quotient lowering)"
    && faultSite (wordToQuotientExpr (Word.fromPtr (ptrCalldata (valueFromNat 0x100))))
        == qvmPath ++ ":2957 (quotient expressions can only load memory-backed words)"
    && faultSite (ptrToQuotientMem (ptrMemory (Value.integer (-1))))
        == qvmPath ++ ":2973 (negative quotient memory pointer)"
    && faultSite (ptrToQuotientMem (ptrMemory (Value.identifier "NOPE_MPTR" 0)))
        == qvmPath ++ ":2979 (unsupported quotient memory token: NOPE_MPTR)"
    && faultSite (ptrToQuotientMem (ptrMemory (Value.identifier "L_0_MPTR" (-0x20))))
        == qvmPath ++ ":2977 (negative quotient memory token offset)"
    && (match ptrToQuotientMem (ptrMemory (Value.identifier "L_0_MPTR" 0)) with
        | .ok m => match ptrToQuotientMem (ptrMemory (Value.identifier "L_0_MPTR" 0x20)) with
            | .ok m2 => m != m2 && (match m, m2 with
                | QuotientMem.token t, QuotientMem.tokenOffset t2 o => t == t2 && o == 0x20
                | _, _ => false)
            | _ => false
        | _ => false)

/-- GATE 22 (EXACT STREAM). The 15 identities of the fixture, keyed by global_index /
    source / var / target / line-count / expression shape. This is the item P-10 named last,
    and the gate is the evidence that BOTH representations of every identity exist at once:
    the gate family's exprs come from the plonk Expression through
    quotient_expr_from_plonk_expr, the other three families' from parsed Yul. Note j=0 is
    tgt=sel0 (the simple selector on gate g0) and the rest are main; the lookup names are
    lookup_0 and lookup_1 from lookup_identity_source; and the trash names come from the
    three arms of trash_manifest_name - "gev" (the empty-polynomial gate) then "trc". -/
def identityPartsStream_ok : Bool :=
  match quotientIdentityParts bField bCs bMeta bData with
  | .ok ps =>
      let keys := ps.allIdentities.map identKey
      let dense := List.zip (List.range 19) (ps.allIdentities.map fun i => i.meta_.globalIndex)
      keys.length == 19
        && keys.getD 0 "" == kIdent0
        && keys.getD 1 "" == kIdent1
        && keys.getD 3 "" == kIdent3
        && keys.getD 4 "" == kIdent4
        && keys.getD 10 "" == kIdent10
        && keys.getD 13 "" == kIdent13
        && keys.getD 14 "" == kIdent14
        && ps.sortedSimple == [0]
        && dense.all (fun p => p.fst == p.snd)
        && ps.gates.length == 4 && ps.permutation.length == 6
        && ps.lookup.length == 7 && ps.trash.length == 2
  | .error _ => false

/-- GATE 23 (R-41 negative controls). Each of the four count asserts, reddened one at a
    time, and each producing ITS OWN message; plus the selector-target expect (Q:848) and the
    alignment assert (Q:827) being reachable. A port that checked only one of the four, or
    that reused one message, fails here. -/
def identityPartsCountAsserts_ok : Bool :=
  let bad (which : Nat) : String :=
    let proto := match which with
      | 0 => { bProto with quotient := { bProto.quotient with gates := 5 } }
      | 1 => { bProto with quotient := { bProto.quotient with permutation := 7 } }
      | 2 => { bProto with quotient := { bProto.quotient with lookup := 8 } }
      | _ => { bProto with quotient := { bProto.quotient with trash := 3 } }
    faultSite (quotientIdentityParts bField bCs { bMeta with protocol := proto } bData)
  bad 0 == qPath ++ ":944 (gate identity count must match protocol plan)"
    && bad 1 == qPath ++ ":949 (permutation identity count must match protocol plan)"
    && bad 2 == qPath ++ ":954 (lookup identity count must match protocol plan)"
    && bad 3 == qPath ++ ":959 (trash identity count must match protocol plan)"
    && faultSite (quotientIdentityParts bField { bCs with trashcans := #[] } bMeta bData)
        == qPath ++ ":959 (trash identity count must match protocol plan)"
    && faultSite (quotientIdentityParts bField bCs
          { bMeta with simpleSelectorCols := [] } bData)
        == qPath ++ ":848 (selector column present)"
    && faultSite (quotientIdentityParts bField { bCs with lookups := #[] } bMeta bData)
        == qPath ++ ":954 (lookup identity count must match protocol plan)"

/-- GATE 23b (FINDING: an assert that cannot fire). Q:827-831 compares gate_items.len() with
    gate_exprs.len(), but BOTH are the flat_map of cs.gates() over Gate::polynomials - the
    evaluator's gate_computations_tagged (YE:211-238) and the map at Q:819-826 walk the same
    array in the same order - so for any ConstraintSystem the two lengths are equal by
    construction and the assert is a tautology. It is ported (R1: transcribe, do not
    improve), and this gate records that it is NOT reachable rather than pretending to
    exercise it: three perturbations that change the gate list all keep the two lengths
    equal. The four count asserts at Q:941-960 are the opposite case - they compare against
    the protocol plan, an independent input, and GATE 23 reddens each of them. -/
def identityPartsAlignmentAssertIsTautological_ok : Bool :=
  (bCs.gates.toList.flatMap (fun g => (Gate.polynomials g).toList)).length == 4
    && runOpt (gateComputationsTagged.map fun gs => gs.length) bEv == some 4
    && ((bCs.gates.toList.drop 2).flatMap fun g => (Gate.polynomials g).toList).length == 1
    && ((bCs.gates.toList.take 2).flatMap fun g => (Gate.polynomials g).toList).length == 3

/-- GATE 24. trash_manifest_name's three arms (DIAG:233-246) and the fact that the FILTER
    comes before the nth: with one empty-polynomial gate, index 0 names that gate and not
    trashcans[0]. -/
def trashManifestNameArms_ok : Bool :=
  trashManifestName bCs 0 == "gev"
    && trashManifestName bCs 1 == "trc"
    && trashManifestName bCs 7 == "trash_7"
    && trashManifestName { bCs with gates := #[] } 0 == "trb"
    && trashManifestName { bCs with gates := #[], trashcans := #[] } 2 == "trash_2"

/-- GATE 25 (D-P19, hazard 2). The enumerate sites this package ports are re-read from the
    reference at #eval time: ten of them, in the two ranges this file covers. If a future
    commit adds or removes one, this reddens and the zipIdx swaps have to be re-checked. -/
def zipIdxSites_ok : IO Bool := do
  let src ← readQArtifact
  let ls := src.splitOn "\n"
  let mine := ls.zipIdx.filterMap fun (l, n) =>
    if (n + 1 >= 804 && n + 1 <= 993) || (n + 1 >= 1340 && n + 1 <= 2099) then some l else none
  let hits := mine.filter (fun l => l.contains ".enumerate()")
  pure (hits.length == 10
    && ls.any (fun l => l.contains ".zip(gate_exprs)")
    && ls.any (fun l => l.contains "for (chunk, (input_chunk, h_eval)) in"))

/-- GATE 26 (anti-circularity). Of the 228 pinned lines, exactly 102 appear VERBATIM in
    quotient.rs; every other pinned line came from one of the format skeletons below, which
    are the Rust's own format! strings with their placeholders left in. So the pins are tied
    to the reference and not only to this port. -/
def pinnedLinesTraceToReference_ok : IO Bool := do
  let src ← readQArtifact
  let all := kPermBlock ++ kLookupBlock ++ kTrashBlock
  let verbatim := (all.filter fun l => src.contains l).length
  let skeletons :=
    [ "let delta := {delta}", "let q_perm_vals := {vals_mptr:#x}",
      "let q_perm_num_cols := {num_cols}", "let q_perm_delta_chunk := {delta_chunk}",
      "let q_perm_zn := mload(add(q_perm_z_cur, {final_z_offset:#x}))",
      "mstore(add({dst}, {dst_base:#x}), {expr})",
      "for {{ let {loop_prefix}_i := 0 }} lt({loop_prefix}_i, {count}) {{ {loop_prefix}_i := add({loop_prefix}_i, 1) }} {{",
      "let {loop_prefix}_src_off := mul({loop_prefix}_i, {src_stride:#x})",
      "mstore(add(add({dst}, {dst_base:#x}), {loop_prefix}_dst_off), mload(add({src_base:#x}, {loop_prefix}_src_off)))",
      "let q_lookup_eval := mulmod(q_lookup_lsum, {}, r)",
      "let q_lookup_eval := addmod(mulmod({}, addmod({compressed_var}, q_lookup_beta, r), r), sub(r, 1), r)",
      "mstore(add(q_lookup_f, {:#x}), addmod({compressed_var}, q_lookup_beta, r))",
      "mstore(add(q_lookup_suffix, {:#x}), 1)",
      "let q_lookup_eval := addmod(mulmod({}, q_lookup_product, r), sub(r, q_lookup_sum), r)",
      "let {sum_h} := {}",
      "{sum_h} := addmod({sum_h}, {}, r)",
      "let q_trash_scaled := mulmod(q_trash_one_minus_selector, {}, r)" ]
  pure (verbatim == 102 && skeletons.all (fun s => src.contains s) && all.length == 228)

/-- GATE 27 (R9, the reference's own rule). The DELTA literal is COMPUTED from the field
    dictionary and no literal for it appears in this file - the same property P-09h gates at
    Evaluator.lean:1735 for the Evaluator, restated here because the permutation block is
    the OTHER place the constant reaches the emitted text (Q:1494). -/
def deltaFrLiteralIsNotHardcoded_ok : IO Bool := do
  let src ← readQArtifact
  pure (src.contains "let delta = fr_delta_literal();"
    && src.contains "Fq::DELTA.pow_vartime([chunk_len as u64])")

/-- GATE 28 (R-48). The fixture is not degenerate and is not P-09h's: 4 permutation columns
    at two different strides, 3 z sets whose last has no z_last, 2 lookups with different
    chunk shapes, 2 trashcans one of which is empty, and one gate with no polynomials. Word
    has no BEq (plans README queued item F5), so the cross-fixture comparisons go through
    wordString rather than inventing a comparator again. -/
def blocksFixturesNonDegenerate_ok : Bool :=
  bMeta.permutationColumns.length == 4
    && ((bData.permutationEvals.map fun (_, w) => wordString w).length == 4)
    && bData.permutationZEvals.length == 3
    && (bData.permutationZEvals.filter fun (_, _, l) => l.isNone).length == 1
    && bCs.lookups.size == 2 && bCs.trashcans.size == 2
    && (bCs.gates.toList.filter fun g => (Gate.polynomials g).isEmpty).length == 1
    && bMeta.numPermutationZs != qMeta.numPermutationZs
    && bMeta.permutationChunkLen != qMeta.permutationChunkLen
    && bMeta.numLookups != qMeta.numLookups
    && bMeta.numTrashcans != qMeta.numTrashcans
    && (bData.permutationZEvals.map fun (a, _, _) => wordString a)
        != (qData.permutationZEvals.map fun (a, _, _) => wordString a)
    && (bData.lookupEvals.map fun (m, _, _, _) => wordString m)
        != (qData.lookupEvals.map fun (m, _, _, _) => wordString m)
/-- GATE 29 (AN INHERITED DEFECT, FOUND BY P-10c AND REPAIRED). Evaluator.lean:750
    originally rendered the shared-prefix loop header with ONE BRACE TOO MANY: the Rust's
    format string at YE:181 ends '... add(q_lookup_shared_i, 1) }} {{', which renders
    ') } {', while the Lean ended with an extra brace, rendering ') }} {'. The emitted Yul
    was therefore not the reference's and would not parse as a Yul for-loop header - and
    P-09h's own gate (Evaluator.lean:1566) pinned the wrong text, so nothing in the tree
    caught it.

    P-10c could not edit Evaluator.lean (not its file), so it made THIS gate pin the
    defective text as a tripwire: repairing the source would redden here and force the pin
    to be updated in the same change. That is what happened - the orchestrator fixed
    Evaluator.lean:750 and its pin, this gate went false as designed, and the expectation
    has now been moved to the correct text. It stays as a REGRESSION guard: if the brace
    is ever re-broken, this gate reddens again. -/
def knownEvaluatorSharedPrefixBraceDefect_ok : Bool :=
  let header := (blockOf (runFamilyBlock bEv (structuredLookupLoopBlock bScratch bHorner 10))
    ).filter (fun l => l.contains "q_lookup_shared_i := 0")
  header.length == 1
    && header.getD 0 "" == "for { let q_lookup_shared_i := 0 } lt(q_lookup_shared_i, 3) { q_lookup_shared_i := add(q_lookup_shared_i, 1) } {"
    && Midfall.Generator.QuotientEvaluatorKats.lookupSharedPrefix_ok

/-- GATE 30. Under Horner no site is ever recorded, by any of the three blocks, for any
    base, even with trace on. Together with GATE 16 this is the statement that the recorder
    path is only reachable from the Weighted arm - and therefore only from quotient_direct.rs,
    which is M10. -/
def hornerNeverRecordsSites_ok : Bool :=
  (match runBlocks (structuredPermutationLoopBlock bScratch bHornerTrace 0) with
   | .ok (some b) => !b.isEmpty
   | _ => false)
    && (match runBlocks (structuredLookupLoopBlock bScratch bHornerTrace 0) with
        | .ok (some b) => !b.isEmpty
        | _ => false)
    && (match runBlocks (structuredTrashLoopBlock bHornerTrace 0) with
        | .ok (some b) => !b.isEmpty
        | _ => false)

#eval Midfall.Generator.QuotientBlocksKats.blocksArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.blocksAbortMessagesArtifact_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.permBlockExactLines_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.permBlockWeightedSites_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.permBlockEmptyWhenNoZs_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.mstoreRunArms_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.permProductCountDivergesFromEvaluator_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.permLoopsUseFoldHeaderNotHandWritten_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.lookupBlockExactLines_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.lookupBlockArms_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.lookupBlockStreamPositions_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.lookupAndTrashIndexPanics_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.trashBlockExactLines_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.trashBlockWeightedAndEmpty_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.compactBlocksAssembly_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.compactBlocksFlagsAndEmptyFamilies_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.compactBasesInvisibleUnderHorner_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.liftQVMPreservesSite_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.bridgeRoundTrip_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.gateRouteOperandOrderDivergence_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.bridgeRejectsUnsupportedYul_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.plonkEnvArms_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.identityPartsStream_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.identityPartsCountAsserts_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.identityPartsAlignmentAssertIsTautological_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.trashManifestNameArms_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.zipIdxSites_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.pinnedLinesTraceToReference_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.deltaFrLiteralIsNotHardcoded_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.blocksFixturesNonDegenerate_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.knownEvaluatorSharedPrefixBraceDefect_ok -- expect true
#eval Midfall.Generator.QuotientBlocksKats.hornerNeverRecordsSites_ok -- expect true

end Midfall.Generator.QuotientBlocksKats
