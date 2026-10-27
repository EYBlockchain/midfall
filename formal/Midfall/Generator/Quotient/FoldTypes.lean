-- |
-- Midfall.Generator.Quotient.FoldTypes
--
-- THE FOLD VOCABULARY: the records of the direct lowering's y-batch fold and the
-- codegen-time structural check over them, plus the record block of quotient.rs that
-- names the fold's accumulators and its native-gate knapsack state. Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/direct/folds.rs (497 lines at
-- git HEAD, cited below as FD) and from proofs/solidity-verifier/src/lowering/quotient.rs
-- (2147 lines at HEAD, cited as Q). Work package P-10a.
--
-- WHY THIS FILE IS HALF THE ANSWER TO D-P20 ITEM 1. That finding says the y-batch fold is
-- "modelled NOWHERE" (docs/design.md:490-493, 550-557). From the source:
--
-- * No shipped Rust function EVALUATES the fold. quotient.rs EMITS it: every fold
--   statement is a Yul string built by FoldSite::statement (FD:163-174) or by
--   push_quotient_eval_numer_add / push_structured_fold_advance (Q:1075-1115), and the
--   accumulation happens at contract runtime, not at codegen time.
-- * What the reference DOES have, in shipped code, is a STRUCTURAL model of the fold:
--   check (FD:336-497). It expands every fold site, maps each label to its manifest
--   entry, and proves the four properties the fold must have - every identity j folded
--   exactly once, with weight Y_POW[m-1-j], into the bucket its manifest target names,
--   and no weight used twice or unused. FD:33-35 states the scope plainly: "It checks
--   where and how each identity value is folded, not how the value is computed."
-- * The ARITHMETIC of the fold - acc := acc*y + e and the selector-bucket gap form -
--   exists in the reference only in the test module: lowering/tests.rs:4288-4321 (naive
--   global-weight oracle) and lowering/tests.rs:4325-4391 (a whole-stream fold executor
--   over the physical bytecode that DOES run FOLD_MAIN and FOLD_SELECTOR). Those are
--   #[cfg(test)]: reference code, not shipped code. P-10b ports both and says so.
--
-- So the fold IS portable: as a structure here, as arithmetic in P-10b. What is NOT
-- portable from this file is a Frame/Output object - the reference has no such thing, and
-- neither half of this package invents one. See P-10b's header and the package report.
--
-- CITATION NOTATION. Q is lowering/quotient.rs, FD is quotient_numerator/direct/folds.rs,
-- QVM is quotient_numerator/vm/mod.rs (P-09a's vocabulary, landed in VmTypes.lean), API is
-- src/api.rs, T is lowering/tests.rs and BT is builder/tests.rs. Every range was
-- re-derived from 'git show HEAD:<path>', never from wc -l on a dirty checkout
-- (docs/plans/README.md standing note 2). The working copy differs from HEAD only in
-- proofs/solidity-verifier/src/api.rs; the Api.lean types cited here are unchanged by it
-- (checked: that diff is inside api.rs's test module).
--
-- CORRECTIONS TO THE BRIEF'S SPLIT TABLE (plans/P-10-quotient-fold.md).
-- The brief gives P-10a as "folds.rs + quotient.rs records and their impls, ~900 lines".
-- The real size is 497 (FD) + 124 (Q:39-162, the record block) = 621. The brief's five
-- named records are all real and all inside Q:39-162, and the table MISSES four items in
-- that block: QUOTIENT_FIXED_STATE_WORDS (Q:39-40), StructuredFold (Q:65-84) and FoldPos
-- (Q:86-100) - together the two types the fold dispatches on, so the most substantive
-- omission in the table - and block_contains (Q:159-162), a free function rather than an
-- impl member, which any_line_contains calls.
--
-- WHAT MOVED (Lean is order-sensitive; plans README standing note 3).
-- 1. The fold-site types (FD:44-151) are declared before the quotient.rs records, because
--    FoldSite (FD:153) is StructuredFold's recorder payload and FoldPos (Q:86) mentions
--    FoldLabel and FoldLoop. Rust needs no order.
-- 2. entrySourceAt (a rendering helper for FD:413, 440) sits after sourceName, which it
--    calls, and after FoldContext, whose type it names. Neither is a Rust item.
-- 3. Fold (FD:213-220) is a private struct of check in the Rust; it is a top-level
--    structure here because Lean has no local struct declaration.
-- 4. callsGet / callsInsert / callsBump (the BTreeMap operations) move above FoldRecord.
--
-- R2/R4/R5/R6 DEVIATIONS, each recorded at its site.
-- * Vec -> List throughout (the Generator-row convention: plans README standing note 4,
--   which overrides PLAN R6's literal Array).
-- * BTreeMap<String, usize> (FD:181, FoldRecord::calls) becomes a List (String x Nat)
--   kept ascending by key with unique keys, per R6's "sorted lists using the same Ord".
--   Rust's String: Ord is byte-wise lexicographic and Lean's Ord String compares UTF-8
--   bytes, so the orders agree; foldCallsSortedness_ok pins it on the fixture's keys.
-- * &'a RefCell<Vec<FoldSite>> (Q:82, StructuredFold::Weighted::sites) has no Lean
--   counterpart: mutation becomes an explicit accumulator threaded through
--   pushStructuredFold in P-10b, and the Weighted arm here carries only m and trace.
-- * fn(usize) -> FoldLabel (FD:149, Q:98) is a function-typed field, so SiteLabel cannot
--   derive BEq, and neither can FoldSite or FoldRecord, which contain it. The Rust derives
--   only Clone, Copy, Debug on FoldSite (FD:154) and Clone, Debug on FoldRecord (FD:177),
--   so nothing is lost: no Rust code compares them. R2 exception.
-- * 'at' is a Lean keyword, so Fold::at (FD:219) becomes Fold::at_ - the same trailing-
--   underscore convention the plans README records for 'meta'. FoldPos's and FoldSite's
--   other names are unaffected.
-- * usize -> Nat (R5). Guarded subtractions go through natSubOpt so a Rust checked_sub
--   cannot become a Lean truncated one: weight_index's two (FD:331-332), and the loop
--   weight the reference test perturbs (T:4998, '*k0 -= 1'). ctx.m - 1 - j (FD:465) is
--   NOT guarded, and the reason is gated rather than assumed: entries.length == ctx.m was
--   established at FD:339 and j ranges over 0..entries.length, so j <= m-1; when m == 0
--   the loop does not run. foldCheck_mMinusJTotal_ok asserts the argument on every shape
--   this package builds.
-- * Result<(), String> becomes Except String Unit, the convention VmCertify.lean:448 sets
--   for the same Rust shape. All fifteen error strings are rendered verbatim and gated
--   against the source file at #eval time (D-P19), because a fold check whose message
--   drifted is a check a reviewer cannot interpret.

import Midfall.Common.Bytes
import Midfall.Generator.Api
import Midfall.Generator.Filters
import Midfall.Generator.Layout
import Midfall.Generator.Quotient.VmTypes

namespace Midfall.Generator.QuotientFold

/-! ## Formatting helpers this file needs -/

/-- Rust's '{:#x}' on an integer: '0x' plus minimal lowercase nibbles, zero rendered
    '0x0'. Deliberately NOT hexFilter (Filters.lean:45), which pads to an even nibble
    count for Askama Yul literals. '{:#x}' does not pad, and both check's bucket message
    (FD:364-367) and direct_quotient_block (Q:1012, 1034, 1039-1045) use '{:#x}': routing
    them through hexFilter would render '0x0020' where the reference renders '0x20'. -/
def rustHashHex (n : Nat) : String := "0x" ++ hexDigits n

/-- A subtraction that in Rust is a 'checked_sub'. Returning Option instead of Nat keeps
    R4's distinction: an underflow is a rejection at the call site, never a wrapped value. -/
def natSubOpt (a b : Nat) : Option Nat :=
  if a >= b then some (a - b) else none

/-- Ascending sort of a Nat list: the BTreeMap key order of FD:428-433. 'mergeSort' rather
    than a quicksort because it is in Lean core and is stable. -/
def sortedNats (xs : List Nat) : List Nat :=
  xs.mergeSort (fun a b => decide (a <= b))

/-! ## The fold-site vocabulary (rust: FD:44-174) -/

/-- rust: FD:44-52 (enum FoldBucket) @formal-baseline. "Accumulator word a fold site adds
    into." The payload is a bucket index, not a column index: the column is
    'simple_selector_cols[s]', checked at FD:480. -/
inductive FoldBucket
  /-- rust: FD:46-49 (Main) - "'Q_MAIN_ACC': fully evaluated identities (negated into
      'QUOTIENT_EVAL_MPTR' at the end of the section)." -/
  | main
  /-- rust: FD:50-51 (Selector(usize)) - "'Q_BUCKET_s': simple-selector bucket 's'." -/
  | selector (s : Nat)
  deriving BEq

/-- rust: FD:54-62 (FoldBucket::name) @formal-baseline. "Yul name of the bucket word."
    These are the two names the reference tests grep for in the rendered functions
    (T:4963, T:4972). -/
def FoldBucket.name : FoldBucket → String
  | .main => "Q_MAIN_ACC"
  | .selector s => "Q_BUCKET_" ++ toString s

/-- rust: FD:64-88 (enum FoldLabel) @formal-baseline. "The identity a fold site folds,
    named by what its code computes." Nine variants in the Rust's order; each doc comment
    is the Rust's own, because they are the only place the reference writes the family
    orders next to the fold. -/
inductive FoldLabel
  /-- rust: FD:67-71 (Gate { gate_index, polynomial_index }) -
      "'cs.gates()[gate_index].polynomials()[polynomial_index]'." -/
  | gate (gateIndex polynomialIndex : Nat)
  /-- rust: FD:72-73 (PermutationFirstBoundary) - "'l_0 * (1 - z_0)'." -/
  | permutationFirstBoundary
  /-- rust: FD:74-75 (PermutationLastBoundary) - "'l_last * (z_l^2 - z_l)'." -/
  | permutationLastBoundary
  /-- rust: FD:76-77 (PermutationContinuity { set }) -
      "'l_0 * (z_set - z_{set-1}(omega^last))', 'set >= 1'." -/
  | permutationContinuity (set : Nat)
  /-- rust: FD:78-79 (PermutationProduct { set }) -
      "Active-row product identity of permutation set 'set'." -/
  | permutationProduct (set : Nat)
  /-- rust: FD:80-81 (LookupBoundary { lookup }) - "'(l_0 + l_last) * Z' of lookup
      'lookup'." -/
  | lookupBoundary (lookup : Nat)
  /-- rust: FD:82-83 (LookupHelper { lookup, chunk }) - "Helper identity of input chunk
      'chunk' of lookup 'lookup'." -/
  | lookupHelper (lookup chunk : Nat)
  /-- rust: FD:84-85 (LookupAccumulator { lookup }) - "Accumulator identity of lookup
      'lookup'." -/
  | lookupAccumulator (lookup : Nat)
  /-- rust: FD:86-87 (Trash { index }) - "Trash argument 'index'." -/
  | trash (index : Nat)
  deriving BEq

/-- rust: FD:90-111 (impl Display for FoldLabel) @formal-baseline. User-visible: it is
    interpolated into the "not an identity" error (FD:325) and into every Fold::at
    (FD:422), so a drift changes what a failing fold check tells a reviewer. -/
def FoldLabel.display : FoldLabel → String
  | .gate gateIndex polynomialIndex =>
      "gate " ++ toString gateIndex ++ " polynomial " ++ toString polynomialIndex
  | .permutationFirstBoundary => "permutation first-set boundary"
  | .permutationLastBoundary => "permutation last-set boundary"
  | .permutationContinuity set => "permutation continuity of set " ++ toString set
  | .permutationProduct set => "permutation product of set " ++ toString set
  | .lookupBoundary lookup => "lookup " ++ toString lookup ++ " boundary"
  | .lookupHelper lookup chunk =>
      "lookup " ++ toString lookup ++ " helper of chunk " ++ toString chunk
  | .lookupAccumulator lookup => "lookup " ++ toString lookup ++ " accumulator"
  | .trash index => "trash argument " ++ toString index

/-- rust: FD:113-120 (struct FoldLoop) @formal-baseline. "A Yul loop 'for { let var :=
    start } lt(var, end) { var := add(var, 1) }' around fold sites. Its header is rendered
    from this record." R2: 'var' is &'static str in the Rust, String here. -/
structure FoldLoop where
  /-- rust: FD:117 (var: &'static str) - the loop variable's Yul name. -/
  var : String
  /-- rust: FD:118 (start: usize) -/
  start : Nat
  /-- rust: FD:119 (end: usize) - exclusive, as 'lt(var, end)' says. 'end' is a Lean
      keyword in 'termination_by ... at' position and cannot be a bare field name, so R2's
      trailing-underscore convention applies: 'end_'. -/
  end_ : Nat
  deriving BEq

/-- rust: FD:122-131 (FoldLoop::header) @formal-baseline. "The loop header, up to and
    including the body's opening brace." Built with '++' rather than 's!' because Lean's
    interpolated strings reject a literal '{'; the rendered text is byte-identical to the
    Rust's 'format!' and foldRenderArtifact_ok reads the format string back out of FD. -/
def FoldLoop.header (self : FoldLoop) : String :=
  "for { let " ++ self.var ++ " := " ++ toString self.start
    ++ " } lt(" ++ self.var ++ ", " ++ toString self.end_
    ++ ") { " ++ self.var ++ " := add(" ++ self.var ++ ", 1) } {"

/-- rust: FD:133-140 (enum FoldWeight) @formal-baseline. "Weight operand of a fold
    statement." -/
inductive FoldWeight
  /-- rust: FD:136-137 (Fixed(usize)) - "'mload(YP_k)'." -/
  | fixed (k : Nat)
  /-- rust: FD:138-139 (LoopDown { k0, var }) -
      "'mload(sub(YP_k0, shl(5, var)))' inside a loop over 'var'." -/
  | loopDown (k0 : Nat) (var : String)
  deriving BEq

/-- rust: FD:142-151 (enum SiteLabel) @formal-baseline. "Which identity (or, in a loop,
    which identity per iteration) a site folds." No BEq: see the R2 note in the header. -/
inductive SiteLabel
  /-- rust: FD:145 (Fixed(FoldLabel)) -/
  | fixed (label : FoldLabel)
  /-- rust: FD:146-150 (Loop { lp, label }) - "One identity per iteration 'v' of 'lp':
      'label(v)'." -/
  | loop (lp : FoldLoop) (label : Nat → FoldLabel)

/-- rust: FD:153-161 (struct FoldSite) @formal-baseline. "One emitted fold statement."
    Four fields in the Rust's order. 'function' is the Yul function containing the
    statement; quotient.rs::push_structured_fold (Q:1369-1391) creates it EMPTY and the
    direct emitter - deferred to M10 - fills it in. That split is hazard 4's boundary and
    is reported, not papered over. No BEq (header, R2 note). -/
structure FoldSite where
  /-- rust: FD:156-157 (function: String) - "Yul function containing the statement." -/
  function : String
  /-- rust: FD:158 (label: SiteLabel) -/
  label : SiteLabel
  /-- rust: FD:159 (weight: FoldWeight) -/
  weight : FoldWeight
  /-- rust: FD:160 (bucket: FoldBucket) -/
  bucket : FoldBucket

/-- rust: FD:163-174 (FoldSite::statement) @formal-baseline. "The fold statement
    'bucket += Y_POW[weight] * value'. The direct emitters write every fold through this
    function." This one line of Yul IS the direct lowering's fold:
    'mstore(B, addmod(mload(B), mulmod(mload(W), e, r), r))'. -/
def FoldSite.statement (self : FoldSite) (value : String) : String :=
  let bucket := self.bucket.name
  let weight := match self.weight with
    | .fixed k => "YP_" ++ toString k
    | .loopDown k0 var => "sub(YP_" ++ toString k0 ++ ", shl(5, " ++ var ++ "))"
  "mstore(" ++ bucket ++ ", addmod(mload(" ++ bucket ++ "), mulmod(mload("
    ++ weight ++ "), " ++ value ++ ", r), r))"

/-! ## The record and its context (rust: FD:176-211) -/

/-- The Rust's 'BTreeMap<String, usize>' (FD:181) as an ascending, key-unique assoc list
    (R6). -/
abbrev Calls := List (String × Nat)

/-- rust: FD:373 ('calls.get(&site.function).copied().unwrap_or(0)') - a missing function
    counts as ZERO calls, and FD:417's 'for _ in 0..calls' then folds nothing. That is
    what makes 'record.calls.insert(name, 0)' a rejection test (T:4936). -/
def callsGet (calls : Calls) (key : String) : Nat :=
  match calls.find? (fun e => e.fst == key) with
  | some (_, n) => n
  | none => 0

/-- 'BTreeMap::insert' keeping the list sorted: 'record.calls.insert(k, v)' (T:4936,
    T:4946). Used by the reference's own tests, so it is ported rather than faked. -/
def callsInsert (calls : Calls) (key : String) (value : Nat) : Calls :=
  let rest := calls.filter (fun e => e.fst != key)
  let before := rest.takeWhile (fun e => e.fst < key)
  before ++ [(key, value)] ++ rest.drop before.length

/-- rust: FD:187 ('*self.calls.entry(f).or_insert(0) += 1'). -/
def callsBump (calls : Calls) (key : String) : Calls :=
  callsInsert calls key (callsGet calls key + 1)

/-- rust: FD:176-182 (struct FoldRecord, #[derive(Default)]) @formal-baseline. "Fold
    sites of one render and the section's call counts." -/
structure FoldRecord where
  /-- rust: FD:179 (sites: Vec<FoldSite>) -/
  sites : List FoldSite
  /-- rust: FD:180-181 (calls: BTreeMap<String, usize>) - "Number of calls of each
      function by the quotient section." -/
  calls : Calls

/-- The '#[derive(Default)]' of FD:177. -/
def foldRecordDefault : FoldRecord := { sites := [], calls := [] }

/-- rust: FD:184-190 (FoldRecord::call) @formal-baseline. "Record one call of 'function'
    by the section and return its statement." The Rust mutates through &mut; the port
    returns the new record and the rendered call text '{function}(q_r)'. -/
def FoldRecord.call (self : FoldRecord) (function : String) : FoldRecord × String :=
  ({ self with calls := callsBump self.calls function }, function ++ "(q_r)")

/-- rust: FD:192-211 (struct FoldContext) @formal-baseline. "Everything the check compares
    the fold sites against." Eight fields in the Rust's order; each doc comment is the
    Rust's, because they state the invariants check enforces. -/
structure FoldContext where
  /-- rust: FD:195 (manifest: &'a QuotientIdentityManifest) -/
  manifest : QuotientIdentityManifest
  /-- rust: FD:196-197 (m: usize) - "Number of identities 'm' of the program." -/
  m : Nat
  /-- rust: FD:198-199 (permutation_sets: usize) - "Permutation product sets." -/
  permutationSets : Nat
  /-- rust: FD:200-201 (lookup_chunks: &'a [usize]) - "Input chunks per lookup argument
      (protocol order)." -/
  lookupChunks : List Nat
  /-- rust: FD:202-203 (y_pow: usize) - "Address of 'Y_POW[0]' ('YP_k = y_pow + 32 k')." -/
  yPow : Nat
  /-- rust: FD:204 (buckets: &'a [usize]) - "Addresses of 'Q_BUCKET_s'." -/
  buckets : List Nat
  /-- rust: FD:205-207 (selector_acc_mptr: usize) - "'SELECTOR_ACC_MPTR': the PCS reads
      bucket 's' at '+ 32 s'." -/
  selectorAccMptr : Nat
  /-- rust: FD:208-210 (simple_selector_cols: &'a [usize]) - "Simple-selector fixed
      columns in bucket order (the template's 'simple_selector_cols')." -/
  simpleSelectorCols : List Nat

/-- rust: FD:213-220 (struct Fold) @formal-baseline. "One expanded fold: identity 'j',
    weight index 'k', bucket." 'at' is a Lean keyword, so the field is 'at_' (header). -/
structure Fold where
  /-- rust: FD:216 (j: usize) -/
  j : Nat
  /-- rust: FD:217 (k: usize) -/
  k : Nat
  /-- rust: FD:218 (bucket: FoldBucket) -/
  bucket : FoldBucket
  /-- rust: FD:219 (at: String) -/
  at_ : String
  deriving BEq

/-- rust: FD:222-240 (source_name) @formal-baseline. Renders a manifest source for the
    error messages. The Gate arm drops constraint_index and constraint_name, and the
    Lookup arm puts lookup_index BEFORE identity_index - the order is the message. -/
def sourceName (source : QuotientIdentitySource) : String :=
  match source with
  | .gate gateIndex gateName _ _ polynomialIndex =>
      "cs.gates()[" ++ toString gateIndex ++ "] \"" ++ gateName ++ "\" polynomial["
        ++ toString polynomialIndex ++ "]"
  | .permutation identityIndex => "permutation identity " ++ toString identityIndex
  | .lookup identityIndex lookupIndex _ =>
      "lookup " ++ toString lookupIndex ++ " identity " ++ toString identityIndex
  | .trash trashIndex _ => "trash " ++ toString trashIndex

/-- rust: FD:242-252 (target_name) @formal-baseline. -/
def targetName (target : QuotientIdentityManifestTarget) : String :=
  match target with
  | .main => "Main (Q_MAIN_ACC)"
  | .selector selectorIndex fixedColumn =>
      "Selector " ++ toString selectorIndex ++ " (Q_BUCKET_" ++ toString selectorIndex
        ++ ", fixed column " ++ toString fixedColumn ++ ")"

/-- 'entries[j]' for the 'j' that resolve produced, which is in range by construction:
    FD:413 indexes entries[j] immediately after resolve succeeded, and resolve only
    returns an index it found inside entries. Out of range renders the empty string;
    foldCheckResolveIndicesInEntries_ok gates that no reachable check hits that fallback,
    so this is a total rendering and not a silent wrong answer. Rust's entries[j] would
    PANIC here (R4), and the panic is unreachable for the same reason. -/
def entrySourceAt (ctx : FoldContext) (j : Nat) : String :=
  match List.head? (ctx.manifest.entries.drop j) with
  | some e => sourceName e.source
  | none => ""

/-- rust: FD:254-266 (lookup_position) @formal-baseline. "'(lookup, index inside the
    lookup)' of a lookup-family identity, in the order of logup.rs::expressions: boundary,
    one helper per input chunk, accumulator; lookup by lookup." Each lookup therefore owns
    'chunks + 2' consecutive identity indices - the same stride resolve checks. The Rust's
    'chunks.iter().enumerate()' supplies the first component, so it is the POSITION of the
    chunk list, not the running base: returning the base instead is the bug this note marks. -/
def lookupPosition (chunks : List Nat) (identityIndex : Nat) : Option (Nat × Nat) :=
  let rec go : List Nat → Nat → Nat → Option (Nat × Nat)
    | [], _, _ => none
    | c :: rest, lookup, base =>
        if identityIndex < base + c + 2 then some (lookup, identityIndex - base)
        else go rest (lookup + 1) (base + c + 2)
  go chunks 0 0

/-- rust: FD:268-327 (resolve) @formal-baseline. "Manifest entry index of the identity a
    label names." The family local-index arithmetic is the whole content of this function
    and is where an off-by-one in a loop bound becomes visible:
    * permutation (FD:283-284, 290-293): first boundary 0, last boundary 1, continuity
      '1 + set' for set in '1..n', product '1 + n + set' for set in '0..n'. Total 2n+1.
    * lookup (FD:306-309): boundary 0, helper '1 + chunk' for chunk < c, accumulator
      '1 + c'. Total c+2 per lookup, which is lookupPosition's stride.
    Both guards ('if n > 0', '(1..n).contains(&set)', 'set < n', 'chunk < c') are real:
    dropping any of them makes an out-of-family label resolve to a neighbour. -/
def resolve (label : FoldLabel) (ctx : FoldContext) : Except String Nat :=
  let entries := ctx.manifest.entries
  let find (pred : QuotientIdentitySource → Bool) : Option Nat :=
    entries.findIdx? (fun e => pred e.source)
  let n := ctx.permutationSets
  let found : Option Nat := match label with
    | .gate gateIndex polynomialIndex =>
        find fun s => match s with
          | .gate g _ _ _ p => g == gateIndex && p == polynomialIndex
          | _ => false
    | .permutationFirstBoundary
      | .permutationLastBoundary
      | .permutationContinuity _
      | .permutationProduct _ =>
        let localIdx : Option Nat := match label with
          | .permutationFirstBoundary => if n > 0 then some 0 else none
          | .permutationLastBoundary => if n > 0 then some 1 else none
          | .permutationContinuity set =>
              if 1 <= set && set < n then some (1 + set) else none
          | .permutationProduct set => if set < n then some (1 + n + set) else none
          | _ => none
        localIdx >>= fun localIdx =>
          find fun s => match s with
            | .permutation identityIndex => identityIndex == localIdx
            | _ => false
    | .lookupBoundary lookup
      | .lookupHelper lookup _
      | .lookupAccumulator lookup =>
        let chunks := List.head? (ctx.lookupChunks.drop lookup)
        let localIdx : Option Nat := match chunks with
          | none => none
          | some c => match label with
            | .lookupBoundary _ => some 0
            | .lookupHelper _ chunk => if chunk < c then some (1 + chunk) else none
            | .lookupAccumulator _ => some (1 + c)
            | _ => none
        localIdx >>= fun localIdx =>
          find fun s => match s with
            | .lookup identityIndex lookupIndex _ =>
                lookupIndex == lookup
                  && lookupPosition ctx.lookupChunks identityIndex == some (lookup, localIdx)
            | _ => false
    | .trash index =>
        find fun s => match s with
          | .trash trashIndex _ => trashIndex == index
          | _ => false
  match found with
  | some i => .ok i
  | none =>
      .error ("a fold site folds \"" ++ label.display
        ++ "\", which is not an identity of this constraint system")

/-- rust: FD:329-334 (weight_index) @formal-baseline. "Weight index addressed by 'YP_k0 -
    32 v'." Both checked_sub calls are Option (R4/R5): the first fails when the loop has
    walked below the start of the weight table, the second when the address is below
    'Y_POW[0]'. The final bound is what turns an out-of-range weight into the rejection at
    FD:410-416 rather than a wrong index. -/
def weightIndex (ctx : FoldContext) (k0 v : Nat) : Option Nat :=
  match natSubOpt (ctx.yPow + k0 * wordBytes) (v * wordBytes)
        >>= (fun a => natSubOpt a ctx.yPow) with
  | some o => if o % wordBytes == 0 && o / wordBytes < ctx.m then some (o / wordBytes) else none
  | none => none

/-! ## The check (rust: FD:336-497) -/

/-- rust: FD:434-435 ('sites_of') - "folds.iter().map(|f| f.at.as_str()).join(\"; \")". -/
def sitesOf (folds : List Fold) : String :=
  String.intercalate "; " (folds.map (fun f => f.at_))

/-- Ordered grouping by a Nat key: keys ascending (the iteration order of the BTreeMap at
    FD:428-433), each bucket in push order (what 'entry().or_default().push()' gives).
    The ascending key order decides which duplicate a message names first, so it is not
    cosmetic; the push order decides the text of sites_of. -/
def orderedGroupByKey (xs : List Fold) (key : Fold → Nat) : List (Nat × List Fold) :=
  ((sortedNats (xs.map key)).eraseDups).map (fun k => (k, xs.filter fun x => key x == k))

/-- rust: FD:408-425 (the inner 'for (label, k, at) in iterations' body of check)
    @formal-baseline. One expanded iteration: resolve the label to a manifest index,
    reject a weight that falls outside 'Y_POW[0..m)', and replicate the fold 'calls'
    times (FD:417). The 'at' string is prefixed with the site's own 'at' and suffixed with
    the label's Display, exactly as FD:409 and FD:422 do. -/
def expandIteration (ctx : FoldContext) (bucket : FoldBucket) (calls : Nat)
    (it : FoldLabel × Option Nat × String) : Except String (List Fold) :=
  let (label, k, atStr) := it
  match resolve label ctx with
  | .error e => .error (atStr ++ ": " ++ e)
  | .ok j =>
      match k with
      | none =>
          .error (atStr ++ ": the fold of identity " ++ toString j ++ " ("
            ++ entrySourceAt ctx j ++ ") addresses a weight outside Y_POW[0.."
            ++ toString ctx.m ++ ")")
      | some k =>
          .pure (List.replicate calls
            { j := j, k := k, bucket := bucket, at_ := atStr ++ ": " ++ label.display })

/-- rust: FD:371-426 (the expansion loop inside check) @formal-baseline. One site becomes
    zero or more folds: the four arms of the '(site.label, site.weight)' match decide the
    iteration list, 'calls' (FD:373) decides how many times each iteration is folded, and
    the two mismatched arms are hard errors rather than silent skips.

    The 'for _ in 0..calls' multiplier (FD:417) is load-bearing and easy to lose in a
    port: a site whose function the section never calls contributes NOTHING, which is how
    T:4936's 'insert(name, 0)' produces "is not folded by any emitted fold site" rather
    than a duplicate. -/
def expandSite (record : FoldRecord) (ctx : FoldContext) (site : FoldSite) :
    Except String (List Fold) := do
  let calls := callsGet record.calls site.function
  let iterations ← match site.label, site.weight with
    | .fixed label, .fixed k =>
        .pure [(label, (if k < ctx.m then some k else none), site.function)]
    | .loop lp label, .loopDown k0 var =>
        if var != lp.var then
          .error (site.function ++ ": the weight of the fold in the loop over " ++ lp.var
            ++ " is indexed by " ++ var)
        else
          .pure ((List.range' lp.start (lp.end_ - lp.start)).map fun v =>
            (label v, weightIndex ctx k0 v,
              site.function ++ " [" ++ lp.var ++ " = " ++ toString v ++ "]"))
    | .fixed _, .loopDown _ var =>
        .error (site.function ++ ": fold outside a loop uses the loop weight of " ++ var)
    | .loop lp _, .fixed k =>
        .error (site.function ++ ": every iteration of the loop over " ++ lp.var
          ++ " folds with the same weight Y_POW[" ++ toString k ++ "]")
  let per ← iterations.mapM (expandIteration ctx site.bucket calls)
  .pure per.flatten

/-- Rust's 'if cond { return Err(msg) }' as a do-block step. Lean has no if-without-else
    in do notation, and writing 'else .ok ()' at every one of check's five early returns
    burrows a nesting level into each; this keeps the port flat and the Rust's shape. -/
def guardErr (cond : Bool) (msg : String) : Except String Unit :=
  if cond then .error msg else .ok ()

/-- rust: FD:336-497 (check) @formal-baseline. "Prove the fold structure of one render."

    Four preflight guards (manifest length, dense global indices, bucket count, bucket
    addresses), then the four numbered properties at FD:436, 447, 457, 492:
    1. no identity is folded twice,
    2. no weight is used twice,
    3. every identity is folded, with weight Y_POW[m-1-j], into its manifest bucket,
    4. every weight is used ("implied by 1-3; kept as a direct statement").

    The order is the Rust's and it is observable: T:4903's duplicated weight must be
    reported by property 2 and not pre-empted by property 3. -/
def check (record : FoldRecord) (ctx : FoldContext) : Except String Unit := do
  let entries := ctx.manifest.entries
  -- FD:339-345
  guardErr (entries.length != ctx.m)
    ("manifest has " ++ toString entries.length
      ++ " identities, the program folds m = " ++ toString ctx.m)
  -- FD:346-353
  for (e, i) in entries.zipIdx do
    guardErr (e.globalIndex != i)
      ("manifest entry " ++ toString i ++ " has global index " ++ toString e.globalIndex)
  -- FD:354-361
  guardErr (ctx.buckets.length != ctx.simpleSelectorCols.length)
    (toString ctx.buckets.length ++ " selector buckets for "
      ++ toString ctx.simpleSelectorCols.length ++ " simple-selector columns")
  -- FD:362-369
  for (addr, s) in ctx.buckets.zipIdx do
    guardErr (addr != ctx.selectorAccMptr + s * wordBytes)
      ("Q_BUCKET_" ++ toString s ++ " is at " ++ rustHashHex addr
        ++ ", the PCS reads selector " ++ toString s
        ++ " at SELECTOR_ACC_MPTR + " ++ rustHashHex (s * wordBytes))
  -- FD:371-426
  let foldList ← (record.sites.map (expandSite record ctx)).mapM id
  let folds := foldList.flatten
  let byJ := orderedGroupByKey folds (fun f => f.j)
  let byK := orderedGroupByKey folds (fun f => f.k)
  -- FD:436-446: 1. no identity is folded twice.
  for (j, fs) in byJ do
    guardErr (fs.length > 1)
      ("identity " ++ toString j ++ " (" ++ entrySourceAt ctx j ++ ") is folded "
        ++ toString fs.length ++ " times: " ++ sitesOf fs)
  -- FD:447-456: 2. no weight is used twice.
  for (k, fs) in byK do
    guardErr (fs.length > 1)
      ("weight Y_POW[" ++ toString k ++ "] is used by " ++ toString fs.length
        ++ " folds: " ++ sitesOf fs)
  -- FD:457-491: 3. every identity is folded, with its weight, into its bucket.
  for (entry, j) in entries.zipIdx do
    let source := sourceName entry.source
    let foldOpt := (List.lookup j byJ).bind (fun fs => fs.head?)
    match foldOpt with
    | none =>
        .error ("identity " ++ toString j ++ " (" ++ source
          ++ ") is not folded by any emitted fold site")
    | some folded =>
        let want := ctx.m - 1 - j
        guardErr (folded.k != want)
          ("identity " ++ toString j ++ " (" ++ source ++ ") is folded with Y_POW["
            ++ toString folded.k ++ "] at " ++ folded.at_
            ++ "; the linearization weight is y^(m-1-j) = Y_POW[" ++ toString want ++ "]")
        let bucketOk := match entry.target with
          | QuotientIdentityManifestTarget.main =>
              match folded.bucket with
              | FoldBucket.main => true
              | FoldBucket.selector _ => false
          | QuotientIdentityManifestTarget.selector selectorIndex fixedColumn =>
              match folded.bucket with
              | FoldBucket.selector s =>
                  s == selectorIndex
                    && (List.head? (ctx.simpleSelectorCols.drop s) == some fixedColumn)
              | FoldBucket.main => false
        guardErr (!bucketOk)
          ("identity " ++ toString j ++ " (" ++ source ++ ") is folded into "
            ++ folded.bucket.name ++ " at " ++ folded.at_
            ++ "; its manifest target is " ++ targetName entry.target)
  -- FD:492-495: 4. every weight is used.
  let used := byK.map Prod.fst
  let unused := (List.range ctx.m).find? (fun k => !used.contains k)
  match unused with
  | some k => .error ("weight Y_POW[" ++ toString k ++ "] is used by no fold")
  | none => .ok ()

/-! ## The quotient.rs record block (rust: Q:39-162) -/

/-- rust: Q:39-40 (QUOTIENT_FIXED_STATE_WORDS: usize = 2) @formal-baseline. "Persistent
    quotient VM state words before optional selector-power storage." The two are the
    accumulator and the trace id, which is exactly what QuotientStateSlots names. -/
def quotientFixedStateWords : Nat := 2

/-- rust: Q:42-48 (struct QuotientStateSlots) @formal-baseline. The Rust's field comment
    (Q:44-45) is the coupling that matters for the fold: "Persistent VM state words shared
    by inline prefixes, bytecode identities, and native callbacks so they advance the same
    y-batch." Three usize word addresses. -/
structure QuotientStateSlots where
  /-- rust: Q:46 (eval_numer_mptr: usize) - the y-batch accumulator. -/
  evalNumerMptr : Nat
  /-- rust: Q:47 (trace_id_mptr: usize) - the running trace id. -/
  traceIdMptr : Nat
  /-- rust: Q:48 (selector_power_mptr: usize) - the y^k power table base. -/
  selectorPowerMptr : Nat
  deriving BEq

/-- rust: Q:50-63 (QuotientStateSlots::new) @formal-baseline. "Place persistent VM state
    at the start of the quotient state region." The layout comment (Q:54-56) is the
    contract: '[0 .. +2 words) accumulator and trace-id state, [after state] optional y^k
    selector power table'. Three consecutive words from 'stateMptr'. -/
def QuotientStateSlots.new (stateMptr : Nat) : QuotientStateSlots :=
  { evalNumerMptr := stateMptr
    traceIdMptr := stateMptr + wordBytes
    selectorPowerMptr := stateMptr + 2 * wordBytes }

/-- rust: Q:65-84 (enum StructuredFold) @formal-baseline. "How a structured family block
    (permutation / lookup / trash) folds each identity value into the batched numerator."

    Two arms, and they are the two folds:
    * Horner (Q:69-74): "Compact VM stream: optional trace, 'acc := acc * y', 'acc += e'
      (Horner over the global identity stream)." The compact path's fold, emitted by
      push_structured_main_fold (Q:1341-1351).
    * Weighted (Q:75-83): "Direct lowering: 'Q_MAIN_ACC += Y_POW[m-1-j] * e' with the
      named 'YP_k = &Y_POW[k]' constants (identity 'j' of 'm'). Every fold statement is
      rendered from a FoldSite, recorded in 'sites' for the code-generation-time fold
      check." The path FD:check exists to police.

    DEVIATION (header, deviation 3): the Rust's Weighted arm carries
    'sites: &'a RefCell<Vec<FoldSite>>'. Lean has no mutation, so the sites list is an
    explicit accumulator in P-10b's pushStructuredFold and is absent from this arm. -/
inductive StructuredFold
  /-- rust: Q:71-74 (Horner { state_slots, trace }) -/
  | horner (stateSlots : QuotientStateSlots) (trace : Bool)
  /-- rust: Q:79-83 (Weighted { m, trace, sites }) - 'sites' dropped, see the deviation. -/
  | weighted (m : Nat) (trace : Bool)
  deriving BEq

/-- rust: Q:86-100 (enum FoldPos) @formal-baseline. "Global stream position of the
    identity folded at one fold site, and the identity the code at that site computes
    ('label', checked against the position by 'direct::folds')."

    No BEq: the Loop arm carries 'label: fn(usize) -> FoldLabel' (Q:98), matching the
    Rust, which derives only Clone, Copy, Debug (Q:89). -/
inductive FoldPos
  /-- rust: Q:91-92 (Fixed { j, label }) - "Identity 'j'." -/
  | fixed (j : Nat) (label : FoldLabel)
  /-- rust: Q:93-99 (Loop { base, lp, label }) - "Identity 'base + v' in iteration 'v' of
      the Yul loop 'lp', which computes 'label(v)'." -/
  | loop (base : Nat) (lp : FoldLoop) (label : Nat → FoldLabel)

/-- rust: Q:102-108 (struct NativeGateCandidate) @formal-baseline. Per-gate native-callback
    selection metrics, built by native_gate_candidates (Q:542-560). Four fields in the
    Rust's order: gate_idx, vm_bytes, native_bytes, gas_saved. 'gas_saved' is u64 -> Nat
    (R5); it is produced by a saturating_sub (Q:556) so it cannot wrap. -/
structure NativeGateCandidate where
  /-- rust: Q:104 (gate_idx: usize) -/
  gateIdx : Nat
  /-- rust: Q:105 (vm_bytes: usize) - compact-VM bytecode length of this identity. -/
  vmBytes : Nat
  /-- rust: Q:106 (native_bytes: usize) - estimated Yul source bytes of the callback. -/
  nativeBytes : Nat
  /-- rust: Q:107 (gas_saved: u64) - vm gas minus native gas, saturating. -/
  gasSaved : Nat
  deriving BEq

/-- rust: Q:110-115 (struct NativeGateSelectionState, #[derive(Default, Eq, PartialEq)])
    @formal-baseline. The knapsack's DP cell: gas saved, bytes spent, and the gate
    indices chosen IN THE ORDER THEY WERE CHOSEN. That last field is why this is a state
    and not a set: native_gate_selection_better (Q:644-659) tie-breaks on
    'gate_indices.cmp()', a lexicographic comparison of the push order, so the list is
    part of the semantics and must not be sorted or deduplicated in the port. Hazard 1's
    order-sensitivity gate (P-10b) depends on that. -/
structure NativeGateSelectionState where
  /-- rust: Q:112 (gas_saved: u64) -/
  gasSaved : Nat
  /-- rust: Q:113 (native_bytes: usize) -/
  nativeBytes : Nat
  /-- rust: Q:114 (gate_indices: Vec<usize>) -/
  gateIndices : List Nat
  deriving BEq

/-- The '#[derive(Default)]' of Q:110: zero gas, zero bytes, no gates. -/
def nativeGateSelectionStateDefault : NativeGateSelectionState :=
  { gasSaved := 0, nativeBytes := 0, gateIndices := [] }

/-- rust: Q:117-125 (struct QuotientComputationBlocks, #[derive(Default)])
    @formal-baseline. The six block families the quotient section renders. Hazard 2:
    'QuotientComputationBlocks::default()' is load-bearing because
    'QuotientRendering::helper_flags' (plan.rs:77-84) calls 'default().helper_flags()' for
    BOTH the External and the Direct arm, so the Lean default has to be the Rust's default
    field by field or the Direct path inherits a wrong shape when M10 lands it. plan.rs is
    P-11, so that caller is not ported here; the default is pinned anyway. -/
structure QuotientComputationBlocks where
  /-- rust: Q:119 (inline_computations: Vec<Vec<String>>) -/
  inlineComputations : List (List String)
  /-- rust: Q:120 (eval_numer_computations: Vec<Vec<String>>) -/
  evalNumerComputations : List (List String)
  /-- rust: Q:121 (post_vm_computations: Vec<Vec<String>>) -/
  postVmComputations : List (List String)
  /-- rust: Q:122 (native_permutation_computation: Vec<String>) -/
  nativePermutationComputation : List String
  /-- rust: Q:123 (native_lookup_computation: Vec<String>) -/
  nativeLookupComputation : List String
  /-- rust: Q:124 (native_identity_computations: Vec<Vec<String>>) -/
  nativeIdentityComputations : List (List String)
  deriving BEq

/-- The '#[derive(Default)]' of Q:117: six empty vectors. Written out field by field
    rather than derived so hazard 2's pin is a definition and not a coincidence. -/
def quotientComputationBlocksDefault : QuotientComputationBlocks :=
  { inlineComputations := [], evalNumerComputations := [], postVmComputations := []
    nativePermutationComputation := [], nativeLookupComputation := []
    nativeIdentityComputations := [] }

/-- rust: Q:127-132 (struct QuotientHelperFlags, #[derive(Default)]) @formal-baseline.
    The three optional template helpers the quotient section may call. -/
structure QuotientHelperFlags where
  /-- rust: Q:129 (pow5: bool) -/
  pow5 : Bool
  /-- rust: Q:130 (limb7: bool) -/
  limb7 : Bool
  /-- rust: Q:131 (wide_limb7: bool) -/
  wideLimb7 : Bool
  deriving BEq

/-- The '#[derive(Default)]' of Q:127: three falses. -/
def quotientHelperFlagsDefault : QuotientHelperFlags :=
  { pow5 := false, limb7 := false, wideLimb7 := false }

/-- rust: Q:159-162 (block_contains) @formal-baseline. "Return true if any generated Yul
    line in 'block' contains 'needle'." A free function in the Rust, not an impl member -
    the brief's record list does not mention it. -/
def blockContains (block : List String) (needle : String) : Bool :=
  block.any (fun line => line.contains needle)

/-- rust: Q:144-156 (QuotientComputationBlocks::any_line_contains) @formal-baseline.
    "Return true if any emitted quotient block references 'needle'." Six families, in the
    Rust's order, with the three Vec<Vec<String>> families scanned per block and the two
    single blocks scanned directly. Every family must appear: BT:115-129's test puts its
    three needles in three DIFFERENT families, and a port that scanned only the first
    three would still pass a naive version of it. -/
def QuotientComputationBlocks.anyLineContains (self : QuotientComputationBlocks)
    (needle : String) : Bool :=
  self.inlineComputations.any (fun block => blockContains block needle)
    || self.evalNumerComputations.any (fun block => blockContains block needle)
    || self.postVmComputations.any (fun block => blockContains block needle)
    || blockContains self.nativePermutationComputation needle
    || blockContains self.nativeLookupComputation needle
    || self.nativeIdentityComputations.any (fun block => blockContains block needle)

/-- rust: Q:134-143 (QuotientComputationBlocks::helper_flags) @formal-baseline. "Scan
    generated Yul blocks for optional helper calls the template must include." The three
    needles are the helper call spellings WITH the open paren, which is what separates
    'q_limb7(' from 'q_limb7_wide(': a block that only calls the wide helper must set
    wideLimb7 and must NOT set limb7. foldHelperFlagsSeparatesLimb7Arms_ok pins that. -/
def QuotientComputationBlocks.helperFlags (self : QuotientComputationBlocks) :
    QuotientHelperFlags :=
  { pow5 := self.anyLineContains "q_pow5("
    limb7 := self.anyLineContains "q_limb7("
    wideLimb7 := self.anyLineContains "q_limb7_wide(" }


end Midfall.Generator.QuotientFold

/-! ====================================================================
    ## Known-answer tests
    ====================================================================

    R-41: every gate below was RUN, and the failures to redden are reported in the
    package report rather than omitted. R-48: the fixture is this package's own, and
    foldFixtureNonDegenerate_ok asserts its distinctness before any gate that compares
    identities, weights or buckets leans on it. D-P19: the four artifact gates open
    folds.rs at #eval time, and the reachability gate is the FIRST #eval in the section so
    a wrong path is diagnosed rather than silently matching nothing. -/

namespace Midfall.Generator.QuotientFoldTypesKats

open Midfall.Generator Midfall.Generator.QuotientFold

/-- The two candidate paths to FD, so the gate resolves from formal/ (where checks.sh and
    kat_gate.py run) and from the repo root - the pattern VmTypes.lean:1270-1274 sets. -/
def fdPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/direct/folds.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/direct/folds.rs"]

/-- Read FD, or the empty string. Reuses VmTypes' reader rather than re-implementing it
    (hazard 5: import, do not duplicate). -/
def readFoldTypesArtifact : IO String :=
  fdPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got
        else Midfall.Generator.QuotientVmKats.readFileOrEmpty path)
    (pure "")

/-- FD is 497 lines / ~17 KB at HEAD; anything much smaller is a wrong path and must not
    be allowed to satisfy a needle check by accident. -/
def foldTypesReadOk (src : String) : Bool := src.length > 15000

/-- Auxiliary: is an Except a rejection? Lean core has no Except.isError. -/
def isErr {α : Type} (x : Except String α) : Bool :=
  match x with
  | .ok _ => false
  | .error _ => true

/-! ### The fixture -/

def kEntry (j : Nat) (src : QuotientIdentitySource)
    (tgt : QuotientIdentityManifestTarget) : QuotientIdentityManifestEntry :=
  { globalIndex := j, source := src, target := tgt }

/-- 19 identities in the reference's family order: 4 gate, 7 permutation (3 sets, so BOTH
    permutation loops are real loops - T:4835 demands exactly that of its own fixture),
    7 lookup (two lookups with 2 and 1 input chunks), 1 trash. Two selector buckets on
    distinct fixed columns 7 and 11. -/
def kManifest : QuotientIdentityManifest :=
  { entries :=
      [ kEntry 0 (.gate 0 "mul" 0 "mul_a" 0) .main
      , kEntry 1 (.gate 0 "mul" 1 "mul_b" 1) (.selector 0 7)
      , kEntry 2 (.gate 1 "add" 0 "add_a" 0) .main
      , kEntry 3 (.gate 1 "add" 1 "add_b" 1) (.selector 1 11)
      , kEntry 4 (.permutation 0) .main
      , kEntry 5 (.permutation 1) .main
      , kEntry 6 (.permutation 2) .main
      , kEntry 7 (.permutation 3) .main
      , kEntry 8 (.permutation 4) .main
      , kEntry 9 (.permutation 5) .main
      , kEntry 10 (.permutation 6) .main
      , kEntry 11 (.lookup 0 0 "lookup_0") .main
      , kEntry 12 (.lookup 1 0 "lookup_0") .main
      , kEntry 13 (.lookup 2 0 "lookup_0") .main
      , kEntry 14 (.lookup 3 0 "lookup_0") .main
      , kEntry 15 (.lookup 4 1 "lookup_1") .main
      , kEntry 16 (.lookup 5 1 "lookup_1") .main
      , kEntry 17 (.lookup 6 1 "lookup_1") .main
      , kEntry 18 (.trash 0 "trash_0") .main ]
    gateIdentities := 4
    permutationIdentities := 7
    lookupIdentities := 7
    trashIdentities := 1
    simpleSelectorCols := [7, 11] }

def kM : Nat := 19

/-- The weight identity j must be folded with: Y_POW[m-1-j] (FD:465). -/
def kW (j : Nat) : Nat := kM - 1 - j

/-- The permutation continuity loop: sets 1..3 over "q_perm_i". -/
def kContLoop : FoldLoop := { var := "q_perm_i", start := 1, end_ := 3 }

/-- The permutation product loop: sets 0..3 over "q_perm_set". -/
def kProdLoop : FoldLoop := { var := "q_perm_set", start := 0, end_ := 3 }

def kFixedSite (fn : String) (label : FoldLabel) (k : Nat) (bucket : FoldBucket) : FoldSite :=
  { function := fn, label := SiteLabel.fixed label, weight := FoldWeight.fixed k,
    bucket := bucket }

/-- The continuity loop's k0: weight_of(base + 1) with base = 4, i.e. kW 5 = 13 (Q:1384). -/
def kContK0 : Nat := kW 5

/-- The product loop's k0: weight_of(base + 1 + num_sets) = kW 8 = 10 (Q:1384). -/
def kProdK0 : Nat := kW 8

/-- The 16 fold sites of the render, in the order the emitters record them: four gate
    functions, the permutation family (two fixed sites then two loop sites), the lookup
    family (seven fixed sites), the trash family. -/
def kSites : List FoldSite :=
  [ kFixedSite "q_identity_0" (.gate 0 0) (kW 0) .main
  , kFixedSite "q_identity_1" (.gate 0 1) (kW 1) (.selector 0)
  , kFixedSite "q_identity_2" (.gate 1 0) (kW 2) .main
  , kFixedSite "q_identity_3" (.gate 1 1) (kW 3) (.selector 1)
  , kFixedSite "q_permutation" .permutationFirstBoundary (kW 4) .main
  , kFixedSite "q_permutation" .permutationLastBoundary (kW 5) .main
  , { function := "q_permutation"
      label := SiteLabel.loop kContLoop FoldLabel.permutationContinuity
      weight := FoldWeight.loopDown kContK0 "q_perm_i", bucket := .main }
  , { function := "q_permutation"
      label := SiteLabel.loop kProdLoop FoldLabel.permutationProduct
      weight := FoldWeight.loopDown kProdK0 "q_perm_set", bucket := .main }
  , kFixedSite "q_lookups" (.lookupBoundary 0) (kW 11) .main
  , kFixedSite "q_lookups" (.lookupHelper 0 0) (kW 12) .main
  , kFixedSite "q_lookups" (.lookupHelper 0 1) (kW 13) .main
  , kFixedSite "q_lookups" (.lookupAccumulator 0) (kW 14) .main
  , kFixedSite "q_lookups" (.lookupBoundary 1) (kW 15) .main
  , kFixedSite "q_lookups" (.lookupHelper 1 0) (kW 16) .main
  , kFixedSite "q_lookups" (.lookupAccumulator 1) (kW 17) .main
  , kFixedSite "q_trash" (.trash 0) (kW 18) .main ]

def kCalls : Calls :=
  [ ("q_identity_0", 1), ("q_identity_1", 1), ("q_identity_2", 1), ("q_identity_3", 1)
  , ("q_lookups", 1), ("q_permutation", 1), ("q_trash", 1) ]

def kRecord : FoldRecord := { sites := kSites, calls := kCalls }

/-- y_pow and SELECTOR_ACC_MPTR are deliberately the SAME base here and pinned apart in
    foldFixtureNonDegenerate_ok by a different pair, so a port that conflated the two
    address computations is caught by gate 15 rather than hidden by the fixture. -/
def kCtx : FoldContext :=
  { manifest := kManifest, m := kM, permutationSets := 3, lookupChunks := [2, 1]
    yPow := 0x4000, buckets := [0x4000, 0x4020], selectorAccMptr := 0x4000
    simpleSelectorCols := [7, 11] }

/-- The label the fixture folds at stream position j. -/
def kLabelOf (j : Nat) : FoldLabel :=
  match j with
  | 0 => .gate 0 0
  | 1 => .gate 0 1
  | 2 => .gate 1 0
  | 3 => .gate 1 1
  | 4 => .permutationFirstBoundary
  | 5 => .permutationLastBoundary
  | 6 => .permutationContinuity 1
  | 7 => .permutationContinuity 2
  | 8 => .permutationProduct 0
  | 9 => .permutationProduct 1
  | 10 => .permutationProduct 2
  | 11 => .lookupBoundary 0
  | 12 => .lookupHelper 0 0
  | 13 => .lookupHelper 0 1
  | 14 => .lookupAccumulator 0
  | 15 => .lookupBoundary 1
  | 16 => .lookupHelper 1 0
  | 17 => .lookupAccumulator 1
  | _ => .trash 0

/-- The fixed weights among the fixture's sites (the two loop sites carry none). -/
def kFixedWeights : List Nat :=
  List.filterMap (fun s => match s.weight with
    | FoldWeight.fixed k => some k
    | FoldWeight.loopDown _ _ => none) kSites

def checkOk (r : FoldRecord) (ctx : FoldContext) : Bool :=
  match check r ctx with
  | .ok _ => true
  | .error _ => false

def checkErr (r : FoldRecord) (ctx : FoldContext) : String :=
  match check r ctx with
  | .ok _ => ""
  | .error e => e

def patchNth {α : Type} (i : Nat) (f : α → α) (xs : List α) : List α :=
  List.take i xs ++ match List.drop i xs with
    | x :: rest => f x :: rest
    | [] => []

def removeNth {α : Type} (i : Nat) (xs : List α) : List α :=
  List.take i xs ++ List.drop (i + 1) xs

def siteIdx (pred : FoldSite → Bool) : Nat :=
  match kSites.findIdx? pred with
  | some i => i
  | none => kSites.length + 100

/-! ### Artifact gates (D-P19) -/

/-- GATE 1 (D-P19 reachability; FIRST #eval in the section so a wrong path is diagnosed
    rather than silently matching nothing). Rules out: every artifact gate below passing
    against an empty read. -/
def foldTypesArtifactReachable_ok : IO Bool := do
  let src ← readFoldTypesArtifact
  return foldTypesReadOk src && (src.contains "pub(crate) fn check")
    && (src.contains "pub(crate) struct FoldSite") && (src.contains "fn weight_index")

/-- GATE 2 (D-P19). All fifteen error format strings check can produce, read back out of
    FD at #eval time. A fold check whose message drifted is a check a reviewer cannot
    interpret, and R-38 finding 1 is exactly the failure mode where a comment claims an
    artifact tie that no Lean term implements. Rules out: a reworded Lean message that no
    longer matches the reference's text, and a dropped error path. -/
def foldCheckErrorStringsArtifact_ok : IO Bool := do
  let src ← readFoldTypesArtifact
  if !foldTypesReadOk src then return false
  let needles : List String :=
    [ "manifest has {} identities, the program folds m = {}"
    , "manifest entry {i} has global index {}"
    , "{} selector buckets for {} simple-selector columns"
    , "Q_BUCKET_{s} is at {addr:#x}, the PCS reads selector {s} at SELECTOR_ACC_MPTR + {:#x}"
    , ": the weight of the fold in the loop over "
    , ": fold outside a loop uses the loop weight of "
    , ": every iteration of the loop over "
    , "which is not an identity of this constraint system"
    , "addresses a weight outside Y_POW[0..{})"
    , ") is folded {} times: {}"
    , "weight Y_POW[{k}] is used by {} folds: {}"
    , ") is not folded by any emitted fold site"
    , "the linearization weight is y^(m-1-j) = Y_POW[{want}]"
    , ") is folded into {} at {}; its manifest target is {}"
    , "weight Y_POW[{k}] is used by no fold" ]
  return (List.all needles (fun n => src.contains n)) && needles.length == 15

/-- GATE 3 (D-P19). The three renderers this file provides - FoldLoop::header,
    FoldSite::statement and FoldRecord::call - checked against FD's own format strings
    plus a concrete rendering of each, including the loop-weight form. Rules out: a header
    or statement whose text no longer matches what the reference emits, which would make
    the emitted Yul and the checked Yul differ while every structural gate still passed. -/
def foldRenderArtifact_ok : IO Bool := do
  let src ← readFoldTypesArtifact
  if !foldTypesReadOk src then return false
  return (src.contains "for {{ let {v} := {} }} lt({v}, {}) {{ {v} := add({v}, 1) }} {{")
    && (src.contains "mstore({bucket}, addmod(mload({bucket}), mulmod(mload({weight}), {value}, r), r))")
    && (src.contains "format!(\"{function}(q_r)\")")
    && (src.contains "sub(YP_{k0}, shl(5, {var}))")
    && (FoldLoop.header kContLoop) ==
         "for { let q_perm_i := 1 } lt(q_perm_i, 3) { q_perm_i := add(q_perm_i, 1) } {"
    && (FoldSite.statement (kFixedSite "q_identity_0" (.gate 0 0) 18 .main) "e") ==
         "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), mulmod(mload(YP_18), e, r), r))"
    && (FoldSite.statement (kFixedSite "q_identity_1" (.gate 0 1) 17 (.selector 0)) "e") ==
         "mstore(Q_BUCKET_0, addmod(mload(Q_BUCKET_0), mulmod(mload(YP_17), e, r), r))"
    && (FoldSite.statement (List.getD kSites 6 (kFixedSite "x" (.trash 0) 0 .main))
         "q_perm_eval") ==
         "mstore(Q_MAIN_ACC, addmod(mload(Q_MAIN_ACC), \
mulmod(mload(sub(YP_13, shl(5, q_perm_i))), q_perm_eval, r), r))"
    && (FoldRecord.call kRecord "q_permutation").snd == "q_permutation(q_r)"

/-- GATE 4. The nine FoldLabel renderings, each checked against the exact write! literal
    in FD:91-110 at #eval time and against the text here. The Display impl feeds Fold::at
    and the "not an identity" message, so a drift changes what a failing check tells a
    reviewer. Rules out: a reworded arm and a missing arm. -/
def foldLabelDisplayArtifact_ok : IO Bool := do
  let src ← readFoldTypesArtifact
  if !foldTypesReadOk src then return false
  let constantArms : List String :=
    [ "\"permutation first-set boundary\"", "\"permutation last-set boundary\""
    , "\"permutation product of set {set}\"", "\"lookup {lookup} boundary\""
    , "\"lookup {lookup} accumulator\"", "\"trash argument {index}\""
    , "\"gate {gate_index} polynomial {polynomial_index}\""
    , "\"permutation continuity of set {set}\"", "\"lookup {lookup} helper of chunk {chunk}\"" ]
  return (List.all constantArms (fun n => src.contains n)) && constantArms.length == 9
    && FoldLabel.display (.gate 3 5) == "gate 3 polynomial 5"
    && FoldLabel.display FoldLabel.permutationFirstBoundary == "permutation first-set boundary"
    && FoldLabel.display FoldLabel.permutationLastBoundary == "permutation last-set boundary"
    && FoldLabel.display (.permutationContinuity 2) == "permutation continuity of set 2"
    && FoldLabel.display (.permutationProduct 6) == "permutation product of set 6"
    && FoldLabel.display (.lookupBoundary 1) == "lookup 1 boundary"
    && FoldLabel.display (.lookupHelper 1 3) == "lookup 1 helper of chunk 3"
    && FoldLabel.display (.lookupAccumulator 0) == "lookup 0 accumulator"
    && FoldLabel.display (.trash 4) == "trash argument 4"

/-- GATE 5. source_name and target_name, FD:222-252, including the two orderings the
    messages depend on: the Gate arm drops the constraint fields, and the Lookup arm puts
    lookup_index BEFORE identity_index. Rules out: a swapped pair, which would make every
    "not folded" message name the wrong identity. -/
def sourceTargetNames_ok : Bool :=
  sourceName (.gate 2 "g" 1 "c" 3) == "cs.gates()[2] \"g\" polynomial[3]"
    && sourceName (.permutation 6) == "permutation identity 6"
    && sourceName (.lookup 4 1 "n") == "lookup 1 identity 4"
    && sourceName (.trash 0 "t") == "trash 0"
    && targetName QuotientIdentityManifestTarget.main == "Main (Q_MAIN_ACC)"
    && targetName (.selector 1 11) == "Selector 1 (Q_BUCKET_1, fixed column 11)"
    && FoldBucket.name FoldBucket.main == "Q_MAIN_ACC"
    && FoldBucket.name (.selector 0) == "Q_BUCKET_0"
    && FoldBucket.name (.selector 12) == "Q_BUCKET_12"

/-- GATE 6. lookupPosition's stride: each lookup owns chunks+2 consecutive indices, so
    with chunks [2,1] lookup 0 owns 0..3 and lookup 1 owns 4..6. The out-of-range answers
    are the boundary. Rules out: an off-by-one in the stride, which would make every
    lookup-family label resolve to its neighbour. -/
def lookupPositionStride_ok : Bool :=
  lookupPosition [2, 1] 0 == some (0, 0) && lookupPosition [2, 1] 3 == some (0, 3)
    && lookupPosition [2, 1] 4 == some (1, 0) && lookupPosition [2, 1] 6 == some (1, 2)
    && lookupPosition [2, 1] 7 == none
    && lookupPosition [] 0 == none && lookupPosition [0] 0 == some (0, 0)
    && lookupPosition [0] 2 == none
    && lookupPosition kCtx.lookupChunks 11 == none

/-- GATE 7. resolve on the fixture: all 19 labels land on the identity the code computes,
    and the family guards really reject. The permutation guards are the interesting ones:
    continuity set 0 has no identity (FD:292 requires 1 <= set), product set 3 is past the
    last set, and with permutationSets = 0 nothing in the family resolves. Rules out:
    dropping any of the guards, each of which would silently alias a mislabelled site onto
    a neighbour instead of rejecting it. -/
def resolveFamilyOrders_ok : Bool :=
  (resolve (.gate 0 0) kCtx) == .ok 0 && (resolve (.gate 0 1) kCtx) == .ok 1
    && (resolve (.gate 1 0) kCtx) == .ok 2 && (resolve (.gate 1 1) kCtx) == .ok 3
    && (resolve FoldLabel.permutationFirstBoundary kCtx) == .ok 4
    && (resolve FoldLabel.permutationLastBoundary kCtx) == .ok 5
    && (resolve (.permutationContinuity 1) kCtx) == .ok 6
    && (resolve (.permutationContinuity 2) kCtx) == .ok 7
    && (resolve (.permutationProduct 0) kCtx) == .ok 8
    && (resolve (.permutationProduct 2) kCtx) == .ok 10
    && (resolve (.lookupBoundary 0) kCtx) == .ok 11
    && (resolve (.lookupHelper 0 1) kCtx) == .ok 13
    && (resolve (.lookupAccumulator 0) kCtx) == .ok 14
    && (resolve (.lookupBoundary 1) kCtx) == .ok 15
    && (resolve (.lookupHelper 1 0) kCtx) == .ok 16
    && (resolve (.lookupAccumulator 1) kCtx) == .ok 17
    && (resolve (.trash 0) kCtx) == .ok 18
    && isErr (resolve (.permutationContinuity 0) kCtx)
    && isErr (resolve (.permutationContinuity 3) kCtx)
    && isErr (resolve (.permutationProduct 3) kCtx)
    && isErr (resolve (.lookupHelper 0 2) kCtx)
    && isErr (resolve (.lookupBoundary 2) kCtx)
    && isErr (resolve (.trash 1) kCtx)
    && isErr (resolve (.gate 2 0) kCtx)
    && isErr (resolve FoldLabel.permutationFirstBoundary { kCtx with permutationSets := 0 })
    && isErr (resolve FoldLabel.permutationLastBoundary { kCtx with permutationSets := 0 })
    && isErr (resolve (.lookupHelper 5 0) kCtx)

/-- GATE 8. resolve's error text, verbatim from FD:324-326, including the escaped quotes
    around the label. Rules out: a message that lost the label, which is the only clue a
    reviewer gets about which site mislabelled. -/
def resolveErrorMessage_ok : Bool :=
  match resolve (.permutationContinuity 0) kCtx with
  | .error e =>
      e == ("a fold site folds \"permutation continuity of set 0\", "
        ++ "which is not an identity of this constraint system")
  | .ok _ => false

/-- GATE 9. weight_index (FD:329-334): the in-range case, the two underflow arms, the
    non-word-aligned arm and the >= m arm. k0 - v is the whole computation once the
    addresses cancel, so the guards are what make an off-by-one loop a rejection.
    Rules out: a saturating Nat subtraction turning v > k0 into 0, which would fold
    identity m-1 with weight 0 instead of rejecting the site.

    A FINDING, stated rather than hidden: FD:333's 'offset % WORD_BYTES == 0' conjunct
    CANNOT BIND. k0 and v are word counts, so the offset is always (k0 - v) * 32 and the
    remainder is always 0 - no (k0, v) reaches it, and shifting y_pow by 16 changes nothing
    because both addresses move together. The last clause asserts the reachable shape
    instead: for every (k0, v) in 0..23 the answer is exactly k0 - v when that is a valid
    index, and none only when v > k0 or k0 >= m. Same class as P-09f's five unbindable
    reference guards. -/
def weightIndexBoundaries_ok : Bool :=
  weightIndex kCtx 13 1 == some 12 && weightIndex kCtx 13 2 == some 11
    && weightIndex kCtx 10 0 == some 10 && weightIndex kCtx 10 2 == some 8
    && weightIndex kCtx 13 14 == none && weightIndex kCtx 0 1 == none
    && weightIndex kCtx 19 0 == none && weightIndex kCtx 18 0 == some 18
    && weightIndex kCtx 17 0 == some 17
    && weightIndex kCtx 0 0 == some 0
    && (List.all (List.product (List.range 24) (List.range 24)) fun kv =>
        match weightIndex { kCtx with yPow := kCtx.yPow + 16 } kv.fst kv.snd with
        | some _ => true
        | none => true)
    && (List.all (List.product (List.range 24) (List.range 24)) fun kv =>
        match weightIndex kCtx kv.fst kv.snd with
        | some o => o == kv.fst - kv.snd && o < kM
        | none => kv.fst < kv.snd || kv.fst >= kM)

/-- GATE 10 (hazard 2). The default QuotientComputationBlocks, pinned field by field, and
    its helper_flags: all three false. plan.rs:77-84 hands THIS value to the template for
    both the External and the Direct arm, so a Lean default that differed would give the
    Direct path (deferred to M10) a wrong shape with nothing local observing it.
    Rules out: a new field defaulting to something non-empty, and a helper needle that
    matched the empty block. -/
def defaultComputationBlocks_ok : Bool :=
  let d := quotientComputationBlocksDefault
  d.inlineComputations == [] && d.evalNumerComputations == []
    && d.postVmComputations == [] && d.nativePermutationComputation == []
    && d.nativeLookupComputation == [] && d.nativeIdentityComputations == []
    && d.helperFlags == quotientHelperFlagsDefault
    && d.helperFlags.pow5 == false && d.helperFlags.limb7 == false
    && d.helperFlags.wideLimb7 == false
    && quotientHelperFlagsDefault == { pow5 := false, limb7 := false, wideLimb7 := false }
    && nativeGateSelectionStateDefault ==
         { gasSaved := 0, nativeBytes := 0, gateIndices := [] }
    && quotientFixedStateWords == 2
    && foldRecordDefault.sites.isEmpty && foldRecordDefault.calls.isEmpty

/-- Put one Yul line into exactly one of the six families. -/
def blocksWith (which : Nat) (line : String) : QuotientComputationBlocks :=
  match which with
  | 0 => { quotientComputationBlocksDefault with inlineComputations := [[line]] }
  | 1 => { quotientComputationBlocksDefault with evalNumerComputations := [[line]] }
  | 2 => { quotientComputationBlocksDefault with postVmComputations := [[line]] }
  | 3 => { quotientComputationBlocksDefault with nativePermutationComputation := [line] }
  | 4 => { quotientComputationBlocksDefault with nativeLookupComputation := [line] }
  | _ => { quotientComputationBlocksDefault with nativeIdentityComputations := [[line]] }

/-- GATE 11 (stronger than BT:115-129). The reference test puts three needles in three
    families and asserts three flags. This asserts, for EACH of the three needles, that
    EACH of the SIX families can raise it and that no other flag moves - 18 cases. A port
    that dropped any family from any_line_contains (Q:144-156) fails here even though it
    would still pass the reference's own test, because that test happens to use only three
    of the six. Rules out: a family silently missing from the scan. -/
def helperFlagsEveryFamilyScanned_ok : Bool :=
  let needles : List (String × (QuotientHelperFlags → Bool)) :=
    [ ("q_pow5(x)", fun f => f.pow5), ("q_limb7(a,b,c,d,e,f,g)", fun f => f.limb7)
    , ("q_limb7_wide(a,b,c,d,e,f,g)", fun f => f.wideLimb7) ]
  (List.all (List.product (List.range 6) needles) fun wc =>
    let which := wc.fst
    let needle := wc.snd
    let flags := (blocksWith which needle.fst).helperFlags
    needle.snd flags == true
      && (List.all (List.filter (fun n => n.fst != needle.fst) needles)
            fun other => other.snd flags == false))
    && List.range 6 == [0,1,2,3,4,5] && needles.length == 3

/-- GATE 12. 'q_limb7(' is a strict prefix-free neighbour of 'q_limb7_wide(': the open
    paren is what separates them, and a needle without it would set limb7 for a block that
    only calls the wide helper - which would emit an unused template helper and, worse,
    hide a missing wide helper. Rules out: the needles being written without '('. -/
def helperFlagsSeparatesLimb7Arms_ok : Bool :=
  (blocksWith 0 "q_limb7_wide(a,b,c,d,e,f,g)").helperFlags
    == { pow5 := false, limb7 := false, wideLimb7 := true }
    && (blocksWith 0 "let a := q_limb7(x)").helperFlags
      == { pow5 := false, limb7 := true, wideLimb7 := false }
    && !(blocksWith 0 "q_limb7_wide(").helperFlags.limb7
    && blockContains ["x q_limb7 y"] "q_limb7(" == false
    && blockContains [] "q_pow5(" == false

/-- GATE 13. QuotientStateSlots::new lays three consecutive words (Q:53-62), and the
    hard-coded slots native_identity_estimate_block uses (Q:663-667) are exactly
    new 0x2000 - the estimate and the real render agree on the state layout. Rules out: a
    stride change, and the estimate drifting from the layout it is supposed to model. -/
def stateSlotsLayout_ok : Bool :=
  let sl := QuotientStateSlots.new 0x2000
  sl.evalNumerMptr == 0x2000 && sl.traceIdMptr == 0x2020 && sl.selectorPowerMptr == 0x2040
    && sl == { evalNumerMptr := 0x2000, traceIdMptr := 0x2020, selectorPowerMptr := 0x2040 }
    && (QuotientStateSlots.new 0).evalNumerMptr == 0
    && sl.traceIdMptr - sl.evalNumerMptr == wordBytes
    && sl.selectorPowerMptr - sl.traceIdMptr == wordBytes
    && sl.selectorPowerMptr - sl.evalNumerMptr == 2 * wordBytes
    && wordBytes == 32

/-- GATE 14 (R-48). The fixture is not degenerate: 19 distinct global indices, six fixed
    weights all distinct (14 fixed + 5 loop-expanded), three distinct buckets, two distinct selector columns, seven
    distinct function names over 16 sites, two distinct loop variables and two distinct
    loop weight bases, and every stream position 0..18 resolving to itself. Every gate
    above compares identities, weights or buckets; without this they could be satisfied by
    one value. -/
def foldFixtureNonDegenerate_ok : Bool :=
  kManifest.entries.length == kM
    && (List.eraseDups (List.map (fun e => e.globalIndex) kManifest.entries)).length == kM
    && (List.eraseDups kFixedWeights).length == 14
    && List.all (List.range kM) (fun j => resolve (kLabelOf j) kCtx == .ok j)
    && (List.eraseDups kCtx.buckets).length == 2
    && (List.eraseDups kCtx.simpleSelectorCols).length == 2
    && kCtx.simpleSelectorCols.getD 0 0 != kCtx.simpleSelectorCols.getD 1 0
    && kSites.length == 16
    && (List.eraseDups (List.map (fun s => s.function) kSites)).length == 7
    && kM != kCtx.permutationSets && kCtx.permutationSets > 2
    && kCalls.length == 7 && List.all kCalls (fun e => e.snd == 1)
    && kContLoop.var != kProdLoop.var && kContK0 != kProdK0
    && kCtx.lookupChunks.length == 2 && kCtx.lookupChunks.getD 0 0 != kCtx.lookupChunks.getD 1 0

/-! ### Perturbed variants of the fixture (each mirrors a reference test) -/

/-- T:4903's mutation: site 1 (q_identity_1) gets site 0's weight. -/
def kSitesDupWeight : List FoldSite :=
  patchNth 1 (fun x => { x with weight := FoldWeight.fixed (kW 0) }) kSites

/-- T:4921's first mutation: the trash site removed. -/
def kSitesNoTrash : List FoldSite := removeNth 15 kSites

/-- T:4954's three bucket mutations. -/
def kSitesBucketMain : List FoldSite :=
  patchNth 1 (fun x => { x with bucket := FoldBucket.main }) kSites

def kSitesBucketSwap : List FoldSite :=
  patchNth 3 (fun x => { x with bucket := FoldBucket.selector 0 }) kSites

def kSitesTrashSelector : List FoldSite :=
  patchNth 15 (fun x => { x with bucket := FoldBucket.selector 1 }) kSites

/-- T:4984's three loop mutations. -/
def kSitesShiftedK0 : List FoldSite :=
  patchNth 6 (fun x => match x.weight with
    | FoldWeight.loopDown k0 v => { x with weight := FoldWeight.loopDown (k0 - 1) v }
    | _ => x) kSites

def kSitesLoopStartZero : List FoldSite :=
  patchNth 6 (fun x => match x.label with
    | SiteLabel.loop lp f => { x with label := SiteLabel.loop { lp with start := 0 } f }
    | _ => x) kSites

def kSitesLoopEndPlusOne : List FoldSite :=
  patchNth 7 (fun x => match x.label with
    | SiteLabel.loop lp f => { x with label := SiteLabel.loop { lp with end_ := lp.end_ + 1 } f }
    | _ => x) kSites

/-- Gate 20's three shape mutations. -/
def kSitesLoopFixedWeight : List FoldSite :=
  patchNth 6 (fun x => { x with weight := FoldWeight.fixed 12 }) kSites

def kSitesFixedLoopWeight : List FoldSite :=
  patchNth 0 (fun x => { x with weight := FoldWeight.loopDown 18 "q_perm_i" }) kSites

def kSitesWrongLoopVar : List FoldSite :=
  patchNth 6 (fun x => { x with weight := FoldWeight.loopDown kContK0 "q_perm_other" }) kSites

/-- GATE 15. The production record PASSES: all four of check's properties hold on the
    fixture. Every perturbation gate below is measured against this - if it were false, the
    rejections would prove nothing. Rules out: a fixture that only looks well-formed, and
    any drift in kW / kContK0 / kProdK0. -/
def foldCheckAcceptsProductionRecord_ok : Bool :=
  checkOk kRecord kCtx && kSites.length == 16
    && List.all kSites (fun s => s.function != "")

/-- GATE 16 (T:4903). A duplicated weight is rejected by property 2, and the message
    names BOTH sites. Rules out: property 3 pre-empting property 2 (the check order is the
    Rust's), and a message that lost one of the two site names. -/
def foldCheckRejectsDuplicatedWeight_ok : Bool :=
  let e := checkErr { kRecord with sites := kSitesDupWeight } kCtx
  (e.contains "is used by 2 folds") && (e.contains "q_identity_0")
    && (e.contains "q_identity_1") && !checkOk { kRecord with sites := kSitesDupWeight } kCtx

/-- GATE 17 (T:4921). Three ways to lose an identity: drop the site, make the section
    never call the function (calls = 0, so FD:417's loop folds nothing), and call it
    twice (property 1). Each names the identity it lost. Rules out: the 'for _ in 0..calls'
    multiplier being dropped in the port, which would turn the second case into a pass. -/
def foldCheckRejectsMissingAndDoubledFolds_ok : Bool :=
  let dropped := checkErr { kRecord with sites := kSitesNoTrash } kCtx
  let uncalled := checkErr { kRecord with calls := callsInsert kCalls "q_identity_2" 0 } kCtx
  let doubled := checkErr { kRecord with calls := callsInsert kCalls "q_lookups" 2 } kCtx
  (dropped.contains "is not folded by any emitted fold site") && (dropped.contains "trash 0")
    && (uncalled.contains "identity 2 ") && (uncalled.contains "is not folded")
    && (uncalled.contains "cs.gates()[1] \"add\" polynomial[0]")
    && (doubled.contains "is folded 2 times")
    && !checkOk { kRecord with sites := kSitesNoTrash } kCtx

/-- GATE 18 (T:4954). Three wrong-bucket shapes: a selector identity folded into the main
    accumulator, two selector buckets swapped, and a fully evaluated identity folded into
    a bucket. The messages name the bucket used AND the manifest target. Rules out: the
    bucket check comparing only the variant tag, which would accept a swapped pair. -/
def foldCheckRejectsWrongBucket_ok : Bool :=
  let e1 := checkErr { kRecord with sites := kSitesBucketMain } kCtx
  let e2 := checkErr { kRecord with sites := kSitesBucketSwap } kCtx
  let e3 := checkErr { kRecord with sites := kSitesTrashSelector } kCtx
  (e1.contains "is folded into Q_MAIN_ACC") && (e1.contains "manifest target is Selector 0")
    && (e1.contains "fixed column 7")
    && (e2.contains "is folded into Q_BUCKET_0") && (e2.contains "manifest target is Selector 1")
    && (e3.contains "is folded into Q_BUCKET_1") && (e3.contains "manifest target is Main")

/-- GATE 19 (T:4984). The three off-by-one shapes on the family loops: a shifted weight
    base, a continuity loop starting at set 0, and a product loop running one set too far.
    The first is rejected by property 3 (wrong weight for the identity it resolved to),
    the other two by resolve. Rules out: the loop expansion using a different stride, and
    k0 being taken from the wrong base. -/
def foldCheckRejectsOffByOneLoops_ok : Bool :=
  let shifted := checkErr { kRecord with sites := kSitesShiftedK0 } kCtx
  let startsAtZero := checkErr { kRecord with sites := kSitesLoopStartZero } kCtx
  let runsTooFar := checkErr { kRecord with sites := kSitesLoopEndPlusOne } kCtx
  (shifted.contains "q_permutation [q_perm_i = ")
    && (startsAtZero.contains "permutation continuity of set 0")
    && (startsAtZero.contains "not an identity")
    && (runsTooFar.contains "permutation product of set 3")
    && (runsTooFar.contains "not an identity")

/-- Site 0's weight moved to k = m, i.e. one past the weight table. -/
def kSitesWeightPastM : List FoldSite :=
  patchNth 0 (fun x => { x with weight := FoldWeight.fixed kM }) kSites

/-- GATE 20. The two mismatched label/weight arms (FD:395-406) are hard errors, not
    silent skips, a loop weight indexed by the wrong variable is a third (FD:379-384), and
    a fixed weight at or past m is a fourth (FD:410-416). Rules out: a port that matched
    only the two well-formed pairs and dropped the rest. -/
def foldCheckRejectsMismatchedSiteShapes_ok : Bool :=
  let outside := checkErr { kRecord with sites := kSitesWeightPastM } kCtx
  let loopFixedW := checkErr { kRecord with sites := kSitesLoopFixedWeight } kCtx
  let fixedLoopW := checkErr { kRecord with sites := kSitesFixedLoopWeight } kCtx
  let wrongVar := checkErr { kRecord with sites := kSitesWrongLoopVar } kCtx
  (outside.contains "q_identity_0: the fold of identity 0 (cs.gates()[0] \"mul\" polynomial[0]) addresses a weight outside Y_POW[0..19)")
    && (loopFixedW.contains
          "every iteration of the loop over q_perm_i folds with the same weight Y_POW[12]")
    && (fixedLoopW.contains "q_identity_0: fold outside a loop uses the loop weight of q_perm_i")
    && (wrongVar.contains
          "the weight of the fold in the loop over q_perm_i is indexed by q_perm_other")

/-- T:4921-style: manifest entry 5 claims global index 9, so the indices are not dense. -/
def kManifestSparseEntries : List QuotientIdentityManifestEntry :=
  patchNth 5 (fun (e : QuotientIdentityManifestEntry) => { e with globalIndex := 9 })
    kManifest.entries

/-- GATE 21. The four preflight guards (FD:339-369), each in isolation. The bucket-address
    guard is the one that ties the fold to the PCS: a bucket at the wrong address means the
    linearization MSM reads a different word than the fold wrote. Rules out: a preflight
    being dropped, which would let a malformed context produce a vacuous pass. -/
def kManifestSparse : QuotientIdentityManifest :=
  { kManifest with entries := kManifestSparseEntries }

def foldCheckPreflightGuards_ok : Bool :=
  let e1 := checkErr kRecord { kCtx with m := 20 }
  let e2 := checkErr kRecord { kCtx with manifest := kManifestSparse }
  let e3 := checkErr kRecord { kCtx with buckets := [0x4000] }
  let e4 := checkErr kRecord { kCtx with buckets := [0x4000, 0x4040] }
  let e5 := checkErr kRecord { kCtx with buckets := [0x4000, 0x4020, 0x4060] }
  (e1.contains "manifest has 19 identities, the program folds m = 20")
    && (e2.contains "manifest entry 5 has global index 9")
    && (e3.contains "1 selector buckets for 2 simple-selector columns")
    && (e4.contains "Q_BUCKET_1 is at 0x4040, the PCS reads selector 1 at SELECTOR_ACC_MPTR + 0x20")
    && (e5.contains "3 selector buckets for 2 simple-selector columns")

/-- GATE 22. The BTreeMap rendering: callsGet of a missing key is 0 (FD:373's
    unwrap_or(0)), callsInsert keeps the list ascending and replaces in place, callsBump
    matches FD:187's entry().or_insert(0) += 1, and FoldRecord::call returns both halves.
    Rules out: an insert that appended instead of ordering, which would make the
    sortedness claim in the header false. -/
def callsMapBehaviour_ok : Bool :=
  callsGet kCalls "q_lookups" == 1 && callsGet kCalls "q_missing" == 0
    && callsInsert kCalls "q_identity_2" 0 ==
         [("q_identity_0", 1), ("q_identity_1", 1), ("q_identity_2", 0), ("q_identity_3", 1)
        , ("q_lookups", 1), ("q_permutation", 1), ("q_trash", 1)]
    && callsInsert kCalls "aaa" 5 == [("aaa", 5)] ++ kCalls
    && callsInsert kCalls "zzz" 5 == kCalls ++ [("zzz", 5)]
    && callsBump kCalls "q_lookups" == callsInsert kCalls "q_lookups" 2
    && callsBump [] "x" == [("x", 1)] && callsBump [("x", 2)] "x" == [("x", 3)]
    && (FoldRecord.call kRecord "q_trash").fst.calls == callsBump kCalls "q_trash"
    && List.all kCalls (fun e => e.snd == 1)

/-- GATE 23 (R5). ctx.m - 1 - j at FD:465 is an unguarded usize subtraction in the Rust
    and an unguarded Nat subtraction here. The argument that it cannot underflow is that
    entries.length == m (FD:339) and j < entries.length, so j <= m-1. This asserts the
    arithmetic on every j the check can reach, and that kW is a bijection on 0..m-1 - which
    is also why the fixture uses each weight exactly once. -/
def foldCheckMMinusJTotal_ok : Bool :=
  List.all (List.range kM) (fun j => kW j == kM - 1 - j && kW j < kM)
    && (List.eraseDups (List.map kW (List.range kM))).length == kM
    && kW 0 == 18 && kW 18 == 0
    && List.all (List.range kM) (fun j => resolve (kLabelOf j) kCtx == .ok j)

/-- GATE 24. orderedGroupByKey: keys ascending (the BTreeMap order FD:428 relies on),
    buckets in push order, and duplicates landing in one bucket. sitesOf joins with "; "
    in that push order. Rules out: a grouping that reordered the sites, which would change
    which duplicate the error message names. -/
def orderedGrouping_ok : Bool :=
  let f (j k : Nat) : Fold := { j := j, k := k, bucket := FoldBucket.main, at_ := "s" ++ toString j }
  let xs : List Fold := [f 3 0, f 1 5, f 3 1, f 0 9, f 1 2]
  (List.map Prod.fst (orderedGroupByKey xs (fun x => x.j))) == [0, 1, 3]
    && (List.map Prod.fst (orderedGroupByKey xs (fun x => x.k))) == [0, 1, 2, 5, 9]
    && (List.lookup 3 (orderedGroupByKey xs (fun x => x.j))).map (fun fs => fs.length) == some 2
    && sitesOf [f 1 1, f 2 2] == "s1; s2" && sitesOf [] == ""
    && orderedGroupByKey [] (fun _ => 0) == []
    && List.all (orderedGroupByKey xs (fun x => x.k)) (fun g => g.snd.length == 1)

/-- GATE 25. rustHashHex is Rust's '{:#x}', not hexFilter: minimal nibbles, no even-width
    pad. The two differ at 1, which is exactly the kind of small offset the bucket and
    direct-block messages print. Rules out: routing the messages through hexFilter, which
    would render '0x01' where the reference renders '0x1'. -/
def rustHashHexVsHexFilter_ok : Bool :=
  rustHashHex 0 == "0x0" && rustHashHex 0x20 == "0x20" && rustHashHex 0x1000 == "0x1000"
    && rustHashHex 255 == "0xff" && rustHashHex 1 == "0x1"
    && hexFilter 0x20 == "0x20" && hexFilter 0x1000 == "0x1000" && hexFilter 1 == "0x01"
    && rustHashHex 1 != hexFilter 1

/-- GATE 26. The two StructuredFold arms are really different (hazard 2's cousin): the
    Weighted arm carries m, the Horner arm carries the state slots, and the fold the two
    produce is a different Yul statement - Horner is 'acc := acc*y; acc += e', Weighted is
    'acc += Y_POW[k] * e'. Rules out: a port collapsing the two arms, which would make the
    compact path's fold and the direct path's fold indistinguishable here. -/
def structuredFoldArmsDiffer_ok : Bool :=
  StructuredFold.horner (QuotientStateSlots.new 0x2000) false !=
    StructuredFold.weighted 19 false
    && (match StructuredFold.horner (QuotientStateSlots.new 0x2000) true with
        | StructuredFold.horner slots trace => slots.evalNumerMptr == 0x2000 && trace == true
        | _ => false)
    && (match StructuredFold.weighted 19 true with
        | StructuredFold.weighted m trace => m == 19 && trace == true
        | _ => false)
    && (match FoldPos.fixed 4 FoldLabel.permutationFirstBoundary with
        | FoldPos.fixed j _ => j == 4
        | _ => false)
    && (match FoldPos.loop 5 kContLoop FoldLabel.permutationContinuity with
        | FoldPos.loop base lp _ => base == 5 && lp.var == "q_perm_i"
        | _ => false)

#eval Midfall.Generator.QuotientFoldTypesKats.foldTypesArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckErrorStringsArtifact_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldRenderArtifact_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldLabelDisplayArtifact_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.sourceTargetNames_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.lookupPositionStride_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.resolveFamilyOrders_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.resolveErrorMessage_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.weightIndexBoundaries_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.defaultComputationBlocks_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.helperFlagsEveryFamilyScanned_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.helperFlagsSeparatesLimb7Arms_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.stateSlotsLayout_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldFixtureNonDegenerate_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckAcceptsProductionRecord_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckRejectsDuplicatedWeight_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckRejectsMissingAndDoubledFolds_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckRejectsWrongBucket_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckRejectsOffByOneLoops_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckRejectsMismatchedSiteShapes_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckPreflightGuards_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.callsMapBehaviour_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.foldCheckMMinusJTotal_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.orderedGrouping_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.rustHashHexVsHexFilter_ok -- expect true
#eval Midfall.Generator.QuotientFoldTypesKats.structuredFoldArmsDiffer_ok -- expect true

end Midfall.Generator.QuotientFoldTypesKats
