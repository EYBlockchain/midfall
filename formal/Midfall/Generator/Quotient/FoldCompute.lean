-- |
-- Midfall.Generator.Quotient.FoldCompute
--
-- THE FOLD COMPUTED: the selector-fold schedule, the native-gate knapsack, the emitters
-- that write the fold statements, and the arithmetic the reference uses to say what the
-- fold MEANS. Ported from proofs/solidity-verifier/src/lowering/quotient.rs (2147 lines
-- at git HEAD, cited as Q) with the test-module oracles from
-- proofs/solidity-verifier/src/lowering/tests.rs (5156 lines at HEAD, cited as T).
-- Work package P-10b. P-10a (FoldTypes.lean) holds the records and folds.rs::check.
--
-- THE REQUIRED FINDING, IN ONE PARAGRAPH. The fold is portable, in three distinct senses,
-- and this file is the evidence for two of them:
--
-- * STRUCTURALLY (P-10a): folds.rs::check proves which identity is folded with which
--   weight into which bucket. Shipped reference code.
-- * AS EMITTED TEXT (this file): direct_quotient_block (Q:997-1051),
--   push_quotient_trace / push_quotient_eval_numer_add / push_structured_fold_advance
--   (Q:1053-1115) and push_structured_fold (Q:1354-1399) are pure functions from the
--   identity's Yul lines plus the state slots to a List String. They are the fold, as
--   strings. Nothing in them needs a contract run.
-- * AS ARITHMETIC (this file): the reference's own statement of what the fold computes is
--   expected_linearization_artifacts_for_test (T:4288-4321) - main_numerator =
--   sum_j value_j * y^(m-1-j), quotient_expected_eval = -main_numerator - and the proof
--   that the compact path's SPARSE gap form computes the same thing is
--   selector_sparse_fold_exhaustive_matches_naive_global_y_powers (T:1289-1340), an
--   exhaustive agreement over every Main/Selector(0)/Selector(1) target pattern up to
--   length 8. That test is the fold's correctness statement, and it is portable:
--   sparseFoldMatchesNaiveGlobalPowers_ok below is it.
--
-- What is NOT portable from either file, and is therefore named rather than implied:
-- there is still no Frame and no Output object. T:4275-4280's TestLinearizationArtifacts
-- is the closest thing the reference has to an Output - four fields, and the negation
-- written to QUOTIENT_EVAL_MPTR is one of them - but it is a test struct, and it is not
-- what PLAN 9.5's outputOf names. See the package report.
--
-- SCOPE BOUNDARY (hazard 4). Four items of quotient.rs are NOT ported here because they
-- need objects this tree does not have, and hazard 4 says report rather than import
-- around:
--   * quotient_identity_parts (Q:804-969) needs Evaluator (quotient_numerator), the halo2
--     ConstraintSystem (vk.cs().gates(), .lookups(), .trashcans()) and
--     quotient_expr_from_expression. None is ported; the halo2 side is Exec/, not
--     Generator/.
--   * structured_permutation_loop_block (Q:1471-1680), structured_lookup_loop_block
--     (Q:1688-1934) and structured_trash_loop_block (Q:1941-1993) need the same Evaluator
--     (reset_locals, compress_expressions_with_challenge_var, evaluate_expression,
--     lookup_shared_prefix_f_plus_beta) plus Data's permutation_z_evals / lookup_evals /
--     trashcan_evals read through it. These are the three emitters that CONSUME
--     StructuredFold, so the fold's family arms cannot be executed here - only the gate
--     arm (direct_quotient_block) and the site-recording arm (push_structured_fold) can.
--   * compact_quotient_computation_blocks (Q:2000-2099) is the assembly point and calls
--     all three, so it is NOT ported. Its two arms that do not need the Evaluator -
--     inline_computations and native_identity_computations, both maps of
--     direct_quotient_block over a list of identities - are reachable through the ported
--     directQuotientBlock, but the record-filling function itself is not transcribed, and
--     no Lean def here claims otherwise. eval_numer_computations is Vec::new() at Q:2032
--     and post_vm_computations is the trash block, so of the six families two are blocked
--     on the Evaluator, one is a literal empty, and three are direct_quotient_block maps.
--   * compact_quotient_program_for (Q:166-180), quotient_template_program (Q:189-238),
--     quotient_program_plan (Q:426-526), build_quotient_program_items (Q:2101-2146),
--     structured_permutation_scratch_words (Q:1401-1417), structured_lookup_max_parallel /
--     structured_lookup_scratch_words / native_callback_scratch_words (Q:1419-1464),
--     push_mstore_mload_literal_runs (Q:1117-1204), quotient_identity_expr /
--     quotient_yul_expr / quotient_expr_from_plonk_expr (Q:971-993),
--     quotient_vm_guards (Q:242-256), quotient_opcode_usage (Q:258-294),
--     quotient_mem_usage (Q:296-310), quotient_stack_words_for_build (Q:312-322),
--     quotient_external_frame (Q:759-775) and quotient_external_frame_from_bounds
--     (Q:777-794) need VerifierBuildInputs, the VK, the halo2 ConstraintSystem, the memory
--     layout or the protocol plan - P-11, the Vk row and the Evaluator, not this package.
--     That is 21 of the file's 55 items; the R11 table in the package report lists every
--     one with its reason.
--
-- UNOWNED ITEMS PICKED UP (report, hazard 4's second half). direct_quotient_block calls
-- specialize_limb7_chains (Q:1211-1240), which needs five Yul-text helpers from vm/mod.rs
-- - yul_let_assignment (QVM:4199-4202), yul_const_value (QVM:4204-4212),
--   yul_mulmod_assignment (QVM:4214-4223), yul_addmod_assignment (QVM:4225-4234) and
--   parse_usize_literal (QVM:4144-4151). They live in vm/mod.rs, which P-09a..f own, but
--   no P-09 package ported them: P-09c stopped at QVM:4120 and P-09f at QVM:4081. They
--   are ported here with their QVM cites so the fold emitter can be complete, and the
--   orchestrator should decide whether they belong to a later P-09 touch. VmBuilder's
--   existing yul_assignment, call_args, is_literal, parse_u256 and trim/drop helpers are
--   IMPORTED, not duplicated (hazard 5).
--
-- WHAT MOVED (Lean is order-sensitive; plans README standing note 3).
-- 1. The Yul-text helpers (QVM:4144-4234) come first: specialize_limb7_chains needs them.
-- 2. The limb7 cluster (Q:1211-1339) comes before direct_quotient_block, which calls it.
--    Rust leaves it 200 lines later in the same impl block.
-- 3. native_gate_selection_better (Q:644-659) comes before the two functions that use it.
-- 4. The estimators (Q:680-757) come before native_gate_candidates (Q:542-560), which
--    calls them; Rust's order reads top-down but schedules nothing.
-- 5. selector_power_words and selector_tail_updates (Q:330-352) come before
--    quotient_state_words and selector_fold_plan.
--
-- R2/R4/R5/R6 DEVIATIONS, each recorded at its site.
-- * Vec -> List (Generator row). HashSet<usize> (Q:529, native_gate_indices) becomes a
--   List Nat: the only observation of it is 'contains' (Q:451, Q:457), so R6's
--   iteration-order argument is satisfied and knapsackIndicesMembershipOnly_ok states it.
-- * HashMap appears at Q:376, Q:386 (selector_fold_plan) and Q:1213, Q:1245 (the limb7
--   constant table). All four are get-or-insert only - never iterated - so R6 permits them
--   as assoc lists; the argument is at each site.
-- * R4: the two .expect calls in selector_fold_plan (Q:393 "global indices must be dense",
--   Q:398 "selector identity must be present") are real release-profile panics and are
--   ported as panicAt sites in P-09b's QVMFault. The 'let ... else { return None }' and
--   '?'' forms in the limb7 cluster are rejections, not panics.
-- * R5: usize -> Nat. 'div_ceil' (Q:600, 608) is ported as divCeil; 'saturating_sub'
--   (Q:556) as Nat.sub, which saturates by definition; the u64 gas totals (Q:691-701)
--   cannot overflow a Nat and are not emulated.
-- * R4 release profile (BASELINE.md:143): no overflow panic, debug_assert! compiled out,
--   but indexing and division by zero DO panic. Two places matter. (a) 'positions[prev_pos]'
--   (Q:382) is a bounds-checked index that cannot fail because prev_pos < pos < positions
--   .len(); ported with an explicit getD so a wrong index is a visible none rather than a
--   silent 0. (b) 'raw / 2' (Q:704) divides by a literal, never zero.
-- * The DP table (Q:601) is a Vec<Vec<Option<State>>>; here it is a List (List (Option
--   State)) indexed [count][used] with listSet2d, and the two reverse loops are ported as
--   descending index lists (R3: 'rev' behaves as in Rust).

import Midfall.Common.Bytes
import Midfall.Generator.Api
import Midfall.Generator.Layout
import Midfall.Generator.Models
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmValidator
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.FoldTypes

namespace Midfall.Generator.QuotientFoldCompute

open Midfall.Generator Midfall.Generator.QuotientFold Midfall.Generator.QuotientBuilder
  Midfall.Generator.QuotientValidator

/-- The Rust file, so the panic sites stay readable. -/
def qPath : String := "proofs/solidity-verifier/src/lowering/quotient.rs"

/-- The vm/mod.rs file, for the five helpers this package picks up from it. -/
def qvmPath : String := "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"

def siteDenseIndices : String := qPath ++ ":393 (quotient identity global indices must be dense)"

def siteGapPresent : String := qPath ++ ":398 (selector identity must be present in selector gaps)"

def siteSelectorGap : String := qPath ++ ":1031 (selector gap for compact direct quotient block)"

/-- rust: QVM:4144-4151 (parse_usize_literal) @formal-baseline. "Parse a literal if it
    fits in usize." On Nat everything fits, so the try_into can only fail for a negative,
    which a literal is not. UNOWNED ITEM - see the header. -/
def parseUsizeLiteral (value : String) : M (Option Nat) :=
  if ! isLiteral value then .ok none
  else do
    let w ← parseU256 value
    .ok (some w.toNat)

/-- rust: QVM:4122-4128 (u256_string) @formal-baseline. "Render a U256 as the shortest
    stable hexadecimal Yul literal." The 'bit_len() < 64' arm and the general arm render
    the SAME text for any value that fits 64 bits, so the branch is documentation dressed
    as a case split - a guard that cannot bind, in the sense P-09f established for the
    recognizer conjuncts. Ported with the branch and gated as such. UNOWNED ITEM. -/
def u256String (value : Word256) : String :=
  if value.toNat < (2^64) then "0x" ++ hexDigits value.toNat else "0x" ++ hexDigits value.toNat

/-- rust: QVM:4198-4202 (yul_let_assignment) @formal-baseline. "Parse a generated
    'let dst := expr' assignment." UNOWNED ITEM. -/
def yulLetAssignment (line : String) : Option (String × String) :=
  match yulAssignment line with
  | some a => if a.hasLet then some (a.dst, a.expr) else none
  | none => none

/-- rust: QVM:4204-4212 (yul_const_value) @formal-baseline. "Resolve a literal or
    previously bound constant variable to canonical text." The const table is a
    HashMap<String, String> read only by key, so an assoc list is R6-legal. DEVIATION: the
    Rust's parse_u256 PANICS on a malformed literal (QVM:4108-4120); the port reads it as
    "not a constant", because this function is pure in the port and every caller treats
    none as a rejection anyway. Recorded as an R4 rendering, gated by
    yulConstValueMalformed_ok. UNOWNED ITEM. -/
def yulConstValue (value : String) (constVars : List (String × String)) : Option String :=
  let value := trimStr value
  if isLiteral value then (u256String <$> (parseU256 value).toOption)
  else (constVars.find? (fun e => e.fst == value)).map Prod.snd

/-- rust: QVM:4214-4223 (yul_mulmod_assignment) @formal-baseline. "Parse
    'let dst := mulmod(lhs, rhs, r)'." The third argument must be exactly 'r'. -/
def yulMulmodAssignment (line : String) : Option (String × String × String) :=
  match yulLetAssignment line with
  | some (dst, expr) =>
      match callArgs expr "mulmod" with
      | .ok (some args) =>
          if args.length == 3 && trimStr (args.getD 2 "") == "r" then
            some (dst, trimStr (args.getD 0 ""), trimStr (args.getD 1 ""))
          else none
      | _ => none
  | none => none

/-- rust: QVM:4225-4234 (yul_addmod_assignment) @formal-baseline. "Parse
    'let dst := addmod(lhs, rhs, r)'." -/
def yulAddmodAssignment (line : String) : Option (String × String × String) :=
  match yulLetAssignment line with
  | some (dst, expr) =>
      match callArgs expr "addmod" with
      | .ok (some args) =>
          if args.length == 3 && trimStr (args.getD 2 "") == "r" then
            some (dst, trimStr (args.getD 0 ""), trimStr (args.getD 1 ""))
          else none
      | _ => none
  | none => none

/-- rust: QVM:4236-4244 (yul_mload_literal_expr) @formal-baseline. "Parse
    'mload(literal_ptr)'." -/
def yulMloadLiteralExpr (expr : String) : Option Nat :=
  match callArgs (trimStr expr) "mload" with
  | .ok (some args) =>
      if args.length == 1 then (parseUsizeLiteral (trimStr (args.getD 0 ""))).toOption.getD none
      else none
  | _ => none

/-- Non-overlapping occurrences of 'needle' in 'hay', i.e. Rust's
    'str::matches(needle).count()'. -/
def countNeedle (hay needle : String) : Nat :=
  let ns := needle.toList
  let rec go : List Char → Nat
    | [] => 0
    | c :: rest => (if ns.isPrefixOf (c :: rest) then 1 else 0) + go rest
  go hay.toList

/-! ## The limb7 specialiser (rust: Q:1206-1339) -/

/-- rust: Q:1330-1339 (record_yul_const_assignment) @formal-baseline. "Record
    'let name := const' bindings for later limb-chain matching." -/
def recordYulConstAssignment (line : String) (constVars : List (String × String)) :
    List (String × String) :=
  match yulLetAssignment line with
  | some (dst, rhs) =>
      match yulConstValue rhs constVars with
      | some value => (constVars.filter (fun e => e.fst != dst)) ++ [(dst, value)]
      | none => constVars
  | none => constVars

/-- rust: Q:1321-1328 (yul_coeff_matches) @formal-baseline. "Return whether a literal or
    constant variable equals 'expected_coeff'." -/
def yulCoeffMatches (value expectedCoeff : String)
    (constVars : List (String × String)) : Bool :=
  yulConstValue value constVars == some expectedCoeff

/-- rust: Q:1305-1319 (parse_limb7_mul_assignment) @formal-baseline. "Parse one
    'mulmod(coeff, limb, r)' line in a limb7 chain." Either operand may be the coefficient
    and the OTHER one is returned as the limb argument - the operand order is not
    normalised, which is what makes the two arms observable. -/
def parseLimb7MulAssignment (line expectedCoeff : String)
    (constVars : List (String × String)) : Option (String × String) :=
  match yulMulmodAssignment line with
  | some (dst, lhs, rhs) =>
      if yulCoeffMatches lhs expectedCoeff constVars then some (dst, rhs)
      else if yulCoeffMatches rhs expectedCoeff constVars then some (dst, lhs)
      else none
  | none => none

/-- rust: Q:1242-1303 (try_limb7_chain) @formal-baseline. "Try to recognize one
    helper-compatible seven-limb add/mul chain." Six coefficients, two lines per step, up to
    four intervening 'let' lines skipped per step (Q:1258's 'skipped > 4'), and the
    accumulator threading through 'previous_acc' is what makes it a CHAIN rather than six
    independent mulmods. The inner 'loop { break }' (Q:1257-1276) becomes stepLoop, which
    recurses on the remaining lines; mainLoop recurses on the remaining coefficients, so
    both are structurally terminating (R10) without fuel. -/
def tryLimb7Chain (lines : List String) (constVars : List (String × String))
    (coeffs : List String) (helperName : String) :
    Option (Nat × List String × List (String × String)) :=
  let rec stepLoop : List String → Nat → Nat → String → List String →
      List (String × String) →
      Option (String × String × Nat × List String × List (String × String))
    | [], _, _, _, keep, consts => none
    | line :: rest, idx, start, coeff, keep, consts =>
        if idx - start > 4 then none
        else match parseLimb7MulAssignment line coeff consts with
          | some (dst, arg) => some (dst, arg, idx, keep, consts)
          | none =>
              match yulLetAssignment line with
              | some _ =>
                  stepLoop rest (idx + 1) start coeff (keep ++ [line])
                    (recordYulConstAssignment line consts)
              | none => none
  let rec mainLoop : List String → Nat → List String → List String
      → List (String × String) → Option String → Bool
      → Option (Nat × List String × List (String × String))
    | [], idx, keep, args, consts, prevAcc, _ =>
        match prevAcc with
        | some pa =>
            some (idx, keep ++ ["let " ++ pa ++ " := " ++ helperName ++ "("
              ++ String.intercalate ", " args ++ ")"], consts)
        | none => none
    | coeff :: rest, idx, keep, args, consts, prevAcc, isFirst =>
        match stepLoop (List.drop idx lines) idx idx coeff keep consts with
        | some (mulDst, mulArg, mulIdx, keep1, consts1) =>
            match yulAddmodAssignment (lines.getD (mulIdx + 1) "") with
            | some (addDst, lhs, rhs) =>
                if lhs != mulDst && rhs != mulDst then none
                else
                  let addend := if lhs == mulDst then rhs else lhs
                  if !isFirst && prevAcc != some addend then none
                  else
                    let args' := if isFirst then args ++ [addend, mulArg] else args ++ [mulArg]
                    mainLoop rest (mulIdx + 2) keep1 args' consts1 (some addDst) false
            | none => none
        | none => none
  mainLoop coeffs 0 [] [] constVars none true

/-- rust: Q:1206-1240 (specialize_limb7_chains) @formal-baseline. "Replace recognized
    seven-limb linear chains with helper calls." The doc at Q:1208-1210 is the scope note:
    "This operates on legacy/direct Yul text, not on the compact VM AST." The two
    coefficient tables are tried in order - narrow then wide - and the first match wins
    (Q:1218-1226's or_else). Fuel is lines.length + 1: each arm consumes at least one line,
    so the Rust's while loop terminates in at most that many steps (R10). -/
def specializeLimb7Chains (lines : List String) : List String :=
  let rec go : Nat → Nat → List (String × String) → List String → List String
    | 0, _, _, out => out
    | fuel + 1, idx, consts, out =>
        if idx >= lines.length then out
        else
          let rest := List.drop idx lines
          match tryLimb7Chain rest consts limb7YulCoeffs "q_limb7" with
          | some (consumed, replacement, consts') =>
              go fuel (idx + consumed) consts' (out ++ replacement)
          | none =>
              match tryLimb7Chain rest consts wideLimb7YulCoeffs "q_limb7_wide" with
              | some (consumed, replacement, consts') =>
                  go fuel (idx + consumed) consts' (out ++ replacement)
              | none =>
                  go fuel (idx + 1)
                    (recordYulConstAssignment (lines.getD idx "") consts)
                    (out ++ [lines.getD idx ""])
  go (lines.length + 1) 0 [] []

/-! ## The fold emitters (rust: Q:1053-1115, 1341-1399, 995-1051) -/

/-- rust: Q:1053-1073 (push_quotient_trace) @formal-baseline. "Append trace emission for a
    quotient identity value." Two lines: trace_u256 of the current id, then the id plus
    one. With trace = false, nothing at all - the flag is not a formatting choice. -/
def pushQuotientTrace (block : List String) (slots : QuotientStateSlots)
    (value : String) (trace : Bool) : List String :=
  if !trace then block
  else
    block ++ ["trace_u256(mload(" ++ rustHashHex slots.traceIdMptr ++ "), " ++ value ++ ")",
      "mstore(" ++ rustHashHex slots.traceIdMptr ++ ", add(mload("
        ++ rustHashHex slots.traceIdMptr ++ "), 1))"]

/-- rust: Q:1075-1086 (push_quotient_eval_numer_add) @formal-baseline. "Add an identity
    value into the current numerator accumulator." THE FOLD, one line:
    'mstore(EVAL, addmod(mload(EVAL), value, r))'. -/
def pushQuotientEvalNumerAdd (block : List String) (slots : QuotientStateSlots)
    (value : String) : List String :=
  block ++ ["mstore(" ++ rustHashHex slots.evalNumerMptr ++ ", addmod(mload("
    ++ rustHashHex slots.evalNumerMptr ++ "), " ++ value ++ ", r))"]

/-- rust: Q:1088-1115 (push_structured_fold_advance) @formal-baseline. "Advance the global
    y-fold state by 'count' identity positions." The doc's second paragraph is the compact
    VM's contract: "Compact VM mode advances only the main accumulator here: selector
    buckets use codegen-time gap updates at selector identity positions." count == 1 is
    straight-line; anything else emits a loop over 'loopVar'. THE OTHER HALF OF THE FOLD:
    'mstore(EVAL, mulmod(mload(EVAL), y, r))'. The loop header reuses P-10a's
    FoldLoop.header, so the compact path and the direct path cannot drift in how a loop is
    spelled. -/
def pushStructuredFoldAdvance (block : List String) (count : Nat) (loopVar : String)
    (slots : QuotientStateSlots) : List String :=
  let one : List String :=
    ["mstore(" ++ rustHashHex slots.evalNumerMptr ++ ", mulmod(mload("
      ++ rustHashHex slots.evalNumerMptr ++ "), y, r))"]
  if count == 1 then block ++ one
  else
    block ++ [FoldLoop.header { var := loopVar, start := 0, end_ := count }]
      ++ one ++ ["}"]

/-- rust: Q:1341-1351 (push_structured_main_fold) @formal-baseline. "Trace, advance, and
    accumulate one main quotient identity value." The three-step Horner fold, in order:
    trace, acc := acc * y, acc += e. -/
def pushStructuredMainFold (block : List String) (value : String)
    (slots : QuotientStateSlots) (trace : Bool) : List String :=
  let b := pushQuotientTrace block slots value trace
  let b := pushStructuredFoldAdvance b 1 "q_main_fold_i" slots
  pushQuotientEvalNumerAdd b slots value

/-- rust: Q:1353-1399 (push_structured_fold) @formal-baseline. "Fold one family identity
    value according to 'fold'." THE DISPATCH between the two folds, and the only place a
    FoldSite is built outside the direct emitter. The Weighted arm's weight_of (Q:1368) is
    '(m - 1).checked_sub(j).unwrap_or(usize::MAX)' - an out-of-range position records an
    out-of-range weight, which check then rejects; the doc at Q:1366-1367 says so, and
    pushStructuredFoldOutOfRangeWeight_ok exercises it. usize::MAX is 2^64-1.
    Returns the extended block AND the extended site list: the Rust's RefCell recorder
    becomes the accumulator (P-10a header, deviation 3). -/
def pushStructuredFold (block : List String) (sites : List FoldSite) (fold : StructuredFold)
    (value : String) (pos : FoldPos) : List String × List FoldSite :=
  match fold with
  | .horner slots trace =>
      (pushStructuredMainFold block value slots trace, sites)
  | .weighted m trace =>
      let traceBase := Trace.quotientIdentityBase
      let weightOf (j : Nat) : Nat :=
        match natSubOpt (m - 1) j with | some k => k | none => 2^64 - 1
      match pos with
      | .fixed j label =>
          let site : FoldSite :=
            { function := "", label := SiteLabel.fixed label,
              weight := FoldWeight.fixed (weightOf j), bucket := FoldBucket.main }
          let b := if trace then
            block ++ ["trace_u256(" ++ toString (traceBase + j) ++ ", " ++ value ++ ")"]
          else block
          (b ++ [site.statement value], sites ++ [site])
      | .loop base lp label =>
          let site : FoldSite :=
            { function := "", label := SiteLabel.loop lp label,
              weight := FoldWeight.loopDown (weightOf base) lp.var,
              bucket := FoldBucket.main }
          let b := if trace then
            block ++ ["trace_u256(add(" ++ toString (traceBase + base) ++ ", " ++ lp.var
              ++ "), " ++ value ++ ")"]
          else block
          (b ++ [site.statement value], sites ++ [site])

/-- rust: Q:995-1051 (direct_quotient_block) @formal-baseline. "Emit one direct/native
    quotient identity block and its y-fold side effects." THE FOLD AS EMITTED TEXT for the
    gate arm: the identity's own lines, a store of the value into the scratch slot, the
    trace, the y-advance, and then either the main addmod or the selector-bucket update
    with its gap power. The selector arm's '.expect' (Q:1031) is a release panic (R4). -/
def directQuotientBlock (lines : List String) (var : String) (target : QuotientTarget)
    (selectorGap : Option Nat) (evalScratchSlot : Nat) (slots : QuotientStateSlots)
    (trace : Bool) : M (List String) := do
  let specialized := specializeLimb7Chains lines
  let b0 := ["{"] ++ specialized
    ++ ["mstore(" ++ rustHashHex evalScratchSlot ++ ", " ++ var ++ ")", "}"]
  let b1 := pushQuotientTrace b0 slots ("mload(" ++ rustHashHex evalScratchSlot ++ ")") trace
  let b2 := pushStructuredFoldAdvance b1 1 "q_direct_fold_i" slots
  match target with
  | QuotientTarget.main =>
      .ok (pushQuotientEvalNumerAdd b2 slots ("mload(" ++ rustHashHex evalScratchSlot ++ ")"))
  | QuotientTarget.selector idx =>
      let gap ← match selectorGap with
        | some g => .ok g
        | none => panicAt siteSelectorGap
      let offset := idx * 0x20
      let b3 := b2 ++ ["{",
        "let q_selector_ptr := add(SELECTOR_ACC_MPTR, " ++ rustHashHex offset ++ ")",
        "let q_selector_acc := mload(q_selector_ptr)"]
      let b4 := if gap != 0 then
        b3 ++ ["q_selector_acc := mulmod(q_selector_acc, mload(add("
          ++ rustHashHex slots.selectorPowerMptr ++ ", "
          ++ rustHashHex (gap * wordBytes) ++ ")), r)"]
      else b3
      .ok (b4 ++ ["mstore(q_selector_ptr, addmod(q_selector_acc, mload("
        ++ rustHashHex evalScratchSlot ++ "), r))", "}"])

/-! ## The selector fold schedule (rust: Q:324-423) -/

/-- rust: Q:330-337 (selector_power_words) @formal-baseline. "Number of y^k words needed by
    selector gap/tail folding." max_power == 0 means no table at all; otherwise max_power+1
    slots. -/
def selectorPowerWords (selectorFold : SelectorFoldPlan) : Nat :=
  if selectorFold.maxPower == 0 then 0 else selectorFold.maxPower + 1

/-- rust: Q:324-328 (quotient_state_words) @formal-baseline. "Number of persistent VM temp
    words needed for state plus selector powers." -/
def quotientStateWords (selectorFold : SelectorFoldPlan) : Nat :=
  quotientFixedStateWords + selectorPowerWords selectorFold

/-- rust: Q:339-352 (selector_tail_updates) @formal-baseline. "Render-time selector tail
    updates, omitting zero tails." The two byte offsets are the bucket address and the
    power address, both scaled by WORD_BYTES. -/
def selectorTailUpdates (selectorFold : SelectorFoldPlan) : List QuotientSelectorTail :=
  List.filterMap
    (fun (pair : Nat × Nat) =>
      if pair.snd != 0 then
        some { selectorOffset := pair.fst * wordBytes, powerOffset := pair.snd * wordBytes
               : QuotientSelectorTail }
      else none)
    ((selectorFold.tailExponents.zipIdx).map (fun p => (p.snd, p.fst)))

/-- rust: Q:354-423 (selector_fold_plan) @formal-baseline. "Build the codegen-time selector
    gap schedule over the full identity stream."

    R6: the two HashMaps (Q:376 target_by_global_index, Q:386 selector_gap_by_global_index)
    are read only by key - never iterated - so assoc lists are faithful. The 'expect' at
    Q:393 fires when the stream's global indices are not exactly 0..n-1, and the one at
    Q:398 when a selector identity is missing from the gap table; both are release panics
    and both are ported as panicAt.

    The gap is 'pos.checked_sub(1).map_or(0, |prev| global_index - positions[prev])'
    (Q:381-382): the first identity in a bucket has gap 0, and later ones the distance from
    the previous identity of the SAME bucket. 'positions[prev]' is an index that cannot
    fail (prev < positions.len()); the getD fallback below is the same value, so it cannot
    mask a bug - selectorFoldPlanGapForm_ok pins the form directly. -/
def selectorFoldPlan (identities : List QuotientIdentity) (selectorCount : Nat) :
    M SelectorFoldPlan := do
  let selectorPositions : List (List Nat) :=
    (List.range selectorCount).map fun selectorIdx =>
      List.filterMap
        (fun (identity : QuotientIdentity) =>
          match identity.target with
          | QuotientTarget.selector idx =>
              if idx == selectorIdx then some identity.meta_.globalIndex else none
          | QuotientTarget.main => none)
        identities
  let targetByGlobal : List (Nat × QuotientTarget) :=
    identities.map fun identity => (identity.meta_.globalIndex, identity.target)
  let gapByGlobal : List (Nat × Nat) :=
    List.flatten (selectorPositions.map fun positions =>
      (positions.zipIdx).map fun (globalIndex, pos) =>
        (globalIndex, match natSubOpt pos 1 with
          | none => 0
          | some prevPos => globalIndex - positions.getD prevPos globalIndex))
  let gapsByIdentity ← (List.range identities.length).mapM fun globalIndex =>
    match List.lookup globalIndex targetByGlobal with
    | none => panicAt siteDenseIndices
    | some target =>
        match target with
        | QuotientTarget.selector _ =>
            match List.lookup globalIndex gapByGlobal with
            | none => panicAt siteGapPresent
            | some gap => .ok (some gap)
        | QuotientTarget.main => .ok none
  let tailExponents := selectorPositions.map fun positions =>
    match positions.getLast? with
    | none => 0
    | some lastIndex => identities.length - 1 - lastIndex
  let candidates := (List.filterMap id gapsByIdentity) ++ tailExponents
  let maxPower := match candidates.maximum with | some x => x | none => 0
  .ok { gapsByIdentity := gapsByIdentity, tailExponents := tailExponents,
        maxPower := maxPower }

/-! ## The native-gate knapsack (rust: Q:528-715) -/

/-- The EVM-word rounding unit of Q:599. -/
def byteUnit : Nat := 32

/-- Rust's usize::div_ceil (Q:600, Q:608). A zero divisor cannot occur here: byte_budget
    is checked non-zero at Q:593 and the unit is a literal 32. -/
def divCeil (a b : Nat) : Nat := if b == 0 then 0 else (a + b - 1) / b

/-- Lexicographic comparison of two Nat lists, i.e. Rust's Vec<usize>::cmp (Q:657). Declared
    before nativeGateSelectionBetter, which uses it. -/
def compareListNat : List Nat → List Nat → Ordering
  | [], [] => Ordering.eq
  | [], _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | x :: xs, y :: ys => if x == y then compareListNat xs ys else compare x y

/-- rust: Q:562-585 (default_native_gate_byte_budget) @formal-baseline. "Preserve the
    previous top-N byte envelope as the default native budget." Ranked by vm_bytes
    DESCENDING then gate_idx ASCENDING (Q:577-579's comparator), take max_count, sum the
    native_bytes. Rust's sort_by is stable; the comparator's second key makes the order
    total for distinct indices, so stability is not load-bearing here - but the tie-break
    IS, and knapsackBudgetTieBreak_ok pins it. -/
def defaultNativeGateByteBudget (candidates : List NativeGateCandidate) (maxCount : Nat) : Nat :=
  let ranked := candidates.map (fun c => (c.vmBytes, c.gateIdx, c.nativeBytes))
  let ranked := ranked.mergeSort (fun a b =>
    if a.1 != b.1 then a.1 > b.1 else a.2.1 <= b.2.1)
  (List.take maxCount ranked).foldl (fun acc r => acc + r.2.2) 0

/-- rust: Q:644-659 (native_gate_selection_better) @formal-baseline. "Deterministic
    tie-breaker for native gate knapsack states." Four keys, in order: MORE gas saved;
    FEWER native bytes; FEWER gates; then lexicographically SMALLER gate_indices. Note the
    asymmetry the port must keep: gas is candidate-over-incumbent, the other three are
    incumbent-over-candidate, and the last compares the PUSH ORDER. -/
def nativeGateSelectionBetter (candidate : NativeGateSelectionState)
    (incumbent : Option NativeGateSelectionState) : Bool :=
  match incumbent with
  | none => true
  | some inc =>
      if candidate.gasSaved != inc.gasSaved then candidate.gasSaved > inc.gasSaved
      else if inc.nativeBytes != candidate.nativeBytes then inc.nativeBytes > candidate.nativeBytes
      else if inc.gateIndices.length != candidate.gateIndices.length
        then inc.gateIndices.length > candidate.gateIndices.length
      else compareListNat inc.gateIndices candidate.gateIndices == Ordering.gt

/-- One cell of the DP table (Q:601): (max_count + 1) rows of (budget_units + 1) columns. -/
def dpRow (budgetUnits : Nat) : List (Option NativeGateSelectionState) :=
  List.replicate (budgetUnits + 1) none

def dpTable (maxCount budgetUnits : Nat) : List (List (Option NativeGateSelectionState)) :=
  List.replicate (maxCount + 1) (dpRow budgetUnits)

def dpGet (dp : List (List (Option NativeGateSelectionState))) (count used : Nat) :
    Option NativeGateSelectionState :=
  List.getD (List.getD dp count []) used none

def dpSet (dp : List (List (Option NativeGateSelectionState))) (count used : Nat)
    (v : Option NativeGateSelectionState) : List (List (Option NativeGateSelectionState)) :=
  let setCell (row : List (Option NativeGateSelectionState)) : List (Option NativeGateSelectionState) :=
    List.take used row ++ [v] ++ List.drop (used + 1) row
  List.take count dp ++ [setCell (dp.getD count [])] ++ List.drop (count + 1) dp

/-- rust: Q:587-642 (select_native_gate_candidates) @formal-baseline. "Solve a small 0/1
    knapsack: maximize estimated gas saved under bytes." HAZARD 1'S OBJECT.

    The shape that makes this order-dependent, and why the port must not normalise it:
    * each cell of dp[count][used] holds ONE state, not a Pareto set, so which candidate
      last wrote a cell decides what a later candidate extends;
    * the candidate loop runs in the caller's order (Q:604) and filters on gas_saved > 0
      and native_bytes > 0 (Q:606);
    * the inner loops run DESCENDING (Q:613-614) so a candidate is used at most once;
    * the tie-break compares gate_indices lexicographically, and gate_indices is in PUSH
      order (Q:621), i.e. candidate-list order;
    * the final scan (Q:634-640) walks count ascending and used ascending and keeps the
      first strict improvement, so the scan order matters too.
    All five are mirrored here, and knapsackOrderSensitivity_ok shows a permutation of the
    candidate list that changes the answer. -/
def selectNativeGateCandidates (candidates : List NativeGateCandidate) (maxCount : Nat)
    (byteBudget : Nat) : NativeGateSelectionState :=
  if maxCount == 0 || byteBudget == 0 then nativeGateSelectionStateDefault
  else
    let budgetUnits := divCeil byteBudget byteUnit
    let dp0 := dpSet (dpTable maxCount budgetUnits) 0 0 (some nativeGateSelectionStateDefault)
    let usable := candidates.filter fun c => c.gasSaved > 0 && c.nativeBytes > 0
    let step (dp : List (List (Option NativeGateSelectionState)))
        (candidate : NativeGateCandidate) : List (List (Option NativeGateSelectionState)) :=
      let costUnits := max 1 (divCeil candidate.nativeBytes byteUnit)
      if costUnits > budgetUnits then dp
      else
        List.foldl (fun (acc : List (List (Option NativeGateSelectionState))) (count : Nat) =>
          List.foldl (fun (dp2 : List (List (Option NativeGateSelectionState))) (used : Nat) =>
            match dpGet dp2 count used with
            | none => dp2
            | some state =>
                let next : NativeGateSelectionState :=
                  { gasSaved := state.gasSaved + candidate.gasSaved
                    , nativeBytes := state.nativeBytes + candidate.nativeBytes
                    , gateIndices := state.gateIndices ++ [candidate.gateIdx] }
                let nextCount := count + 1
                let nextUsed := used + costUnits
                if nativeGateSelectionBetter next (dpGet dp2 nextCount nextUsed) then
                  dpSet dp2 nextCount nextUsed (some next)
                else dp2)
            acc ((List.range (budgetUnits - costUnits + 1)).reverse)
          ) dp ((List.range maxCount).reverse)
    let dpFinal := List.foldl step dp0 usable
    let flat := List.flatten dpFinal
    List.foldl (fun (best : NativeGateSelectionState) (st : Option NativeGateSelectionState) =>
      match st with
      | none => best
      | some s => if nativeGateSelectionBetter s (some best) then s else best)
      nativeGateSelectionStateDefault flat

/-- rust: Q:680-684 (yul_block_source_bytes) @formal-baseline. "Source-byte proxy for the
    native callback's contribution to runtime size." One byte per line plus the newline. -/
def yulBlockSourceBytes (block : List String) : Nat :=
  block.foldl (fun acc line => acc + line.length + 1) 0

/-- rust: Q:686-705 (estimate_native_yul_gas) @formal-baseline. "Relative gas proxy for a
    generated native Yul callback." Per line: 4 base, plus 8 per mload, 10 per mstore, 38
    per addmod, 42 per mulmod, 18 per add, 18 per sub, 16 per mul; the total halved. The
    comment at Q:702-703 says plainly that this is a RELATIVE selector score, not an EVM
    gas model - so no theorem may read an absolute number out of it. -/
def estimateNativeYulGas (block : List String) : Nat :=
  let raw := block.foldl (fun (acc : Nat) (line : String) =>
    4 + 8 * countNeedle line "mload(" + 10 * countNeedle line "mstore("
      + 38 * countNeedle line "addmod(" + 42 * countNeedle line "mulmod("
      + 18 * countNeedle line "add(" + 18 * countNeedle line "sub("
      + 16 * countNeedle line "mul(" + acc) 0
  raw / 2

/-- rust: Q:717-757 (estimate_quotient_vm_gas) @formal-baseline. "Relative gas proxy for
    the compact quotient VM interpreter." One number per opcode, three of them dependent on
    an operand (the two run-length ops read their u16 count, MODARITH7 reads its total
    length), and a fallback of 'len * 12' for anything the table does not name. Walked with
    P-09e's quotientBytecodeOps, so the offsets are the offsets the validator uses. -/
def estimateQuotientVmGas (bytes : List Nat) : VResult Nat := do
  let ops ← quotientBytecodeOps bytes
  .ok (ops.foldl (fun (acc : Nat) (o : QuotientBytecodeOp) =>
    let idx := o.1
    let op := o.2.1
    let len := o.2.2
    acc + if op == qOpPushConst then 54
      else if op == qOpPushMemLiteral then 56
      else if op == qOpPushMemToken then 60
      else if op == qOpPushMemTokenOffset then 66
      else if op == qOpPushMemU16 then 48
      else if op == qOpAdd then 38
      else if op == qOpMul then 42
      else if op == qOpNeg then 24
      else if op == qOpPushConstU8 then 42
      else if op == qOpFoldMain then 70
      else if op == qOpFoldSelector then 92
      else if op == qOpAddConstU8 || op == qOpAddConst then 46
      else if op == qOpMulConstU8 || op == qOpMulConst then 50
      else if op == qOpAddMemU16 then 48
      else if op == qOpMulMemU16 then 52
      else if op == qOpAddMulMemMemConstU8 then 78
      else if op == qOpAddMulConstU8MemU16 then 66
      else if op == qOpAddMulMemMem then 70
      else if op == qOpRunAddMulMemMemConstU8 then
        32 + 58 * (QuotientValidator.readU16 bytes (idx + 1)).toOption.getD 0
      else if op == qOpRunAddMulConstU8MemU16 then
        32 + 48 * (QuotientValidator.readU16 bytes (idx + 1)).toOption.getD 0
      else if op == qOpNativePermutation || op == qOpNativeLookup then 0
      else if op == qOpNativeIdentity then 0
      else if op == qOpLin7 then 190
      else if op == qOpBilin7Row then 260
      else if op == qOpBilin7Pairwise then 980
      else if op == qOpModarith7 then
        90 + 9 * (QuotientValidator.quotientOpLen bytes idx).toOption.getD 0
      else if op == qOpPow5 then 58
      else len * 12) 0)

/-- rust: Q:707-715 (quotient_identity_program_metrics) @formal-baseline. "Estimate
    compact-VM byte and gas cost of one identity." Note the selector gap here is
    'then_some(0)' (Q:711), NOT the real gap: the estimate only needs the fold opcode to be
    the right SHAPE, and it is what makes the byte count comparable across targets. The
    builder runs with P-09f's real recognizers, so the byte count is the one the render
    would produce. -/
def quotientIdentityProgramMetrics (identity : QuotientIdentity) : M (Nat × Nat) := do
  let selectorGap := match identity.target with
    | QuotientTarget.selector _ => some 0
    | QuotientTarget.main => none
  let s ← identityExpr Midfall.Generator.QuotientRecognizers.shapeRecognizers
    builderDefault identity.expr identity.target selectorGap
  let bytes := s.bytes
  match estimateQuotientVmGas bytes with
  | .ok gas => .ok (bytes.length, gas)
  | .error _ => panicAt (qPath ++ ":713 (vm gas estimate walk)")

/-- rust: Q:661-678 (native_identity_estimate_block) @formal-baseline. "Estimate the
    generated native callback block for one identity." The state slots are HARD-CODED to
    0x2000/0x2020/0x2040 (Q:663-667) - which is exactly QuotientStateSlots.new 0x2000, and
    P-10a's stateSlotsLayout_ok pins that - and the scratch slot is 0x1000. The selector
    gap is 'then_some(1)' (Q:668): a one-position gap, not the real one. trace = false. -/
def nativeIdentityEstimateBlock (identity : QuotientIdentity) : M (List String) :=
  directQuotientBlock identity.lines identity.var identity.target
    (match identity.target with
      | QuotientTarget.selector _ => some 1
      | QuotientTarget.main => none)
    0x1000 (QuotientStateSlots.new 0x2000) false

/-- rust: Q:542-560 (native_gate_candidates) @formal-baseline. "Build per-gate
    native-callback selection metrics." gas_saved is vm_gas.saturating_sub(native_gas)
    (Q:556) - on Nat, subtraction already saturates, so the two agree by definition and
    knapsackSaturatingSub_ok states that rather than assuming it. -/
def nativeGateCandidates (gates : List QuotientIdentity) : M (List NativeGateCandidate) :=
  List.mapM (fun (pair : QuotientIdentity × Nat) => do
    let (vmBytes, vmGas) ← quotientIdentityProgramMetrics pair.fst
    let nativeBlock ← nativeIdentityEstimateBlock pair.fst
    .ok { gateIdx := pair.snd, vmBytes := vmBytes,
          nativeBytes := yulBlockSourceBytes nativeBlock,
          gasSaved := vmGas - estimateNativeYulGas nativeBlock })
    (gates.zipIdx)

/-- rust: config.rs:19 (DEFAULT_QUOTIENT_NATIVE_GATES: usize = 4) @formal-baseline, with
    its comment: "up to N remaining gate identities are emitted as VM opcodes that call
    generated Yul blocks ... Selection is a gas/byte knapsack under an estimated native
    callback byte budget." -/
def defaultQuotientNativeGates : Nat := 4

/-- rust: config.rs:12 (DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES: usize = 4). -/
def defaultHybridQuotientInlineIdentities : Nat := 4

/-- rust: Q:528-540 (native_gate_indices) @formal-baseline. "Pick native gate callbacks by
    estimated gas saved under a byte budget." max_count is gates.len().min(4); zero
    short-circuits to the empty set. The HashSet return is a List here: only membership is
    observed (Q:451, Q:457), which knapsackIndicesMembershipOnly_ok states. -/
def nativeGateIndices (gates : List QuotientIdentity) : M (List Nat) := do
  let maxCount := min gates.length defaultQuotientNativeGates
  if maxCount == 0 then .ok []
  else
    let candidates ← nativeGateCandidates gates
    let byteBudget := defaultNativeGateByteBudget candidates maxCount
    let selection := selectNativeGateCandidates candidates maxCount byteBudget
    .ok selection.gateIndices


/-! ## The fold's arithmetic (rust: T:4267-4321, T:1314-1335, T:4325-4391) -/

/-- rust: T:4283-4285 (fq_pow) @formal-baseline. "Small exponentiation helper for expected
    linearization powers." Repeated multiplication, not square-and-multiply: the Rust is
    '(0..exp).fold(ONE, |acc,_| acc * base)'. R7 says Exec code uses explicit
    square-and-multiply; this is a Generator-side test helper and it is ported as written,
    because the fold's meaning depends on it being exactly base^exp and nothing else. -/
def qvmFrPow (base : QVMFr) (exp : Nat) : QVMFr :=
  (List.range exp).foldl (fun acc _ => qvmFrMul acc base) 1

/-- rust: T:4267-4272 (struct TestIdentityTraceEntry) @formal-baseline. -/
structure TestIdentityTraceEntry where
  /-- rust: T:4268 (global_index: usize) -/
  globalIndex : Nat
  /-- rust: T:4269 (target: QuotientTarget) -/
  target : QuotientTarget
  /-- rust: T:4270 (value: Fq) -/
  value : QVMFr
  /-- rust: T:4271 (y_power: usize) -/
  yPower : Nat
  deriving BEq

/-- rust: T:4274-4280 (struct TestLinearizationArtifacts) @formal-baseline. THE CLOSEST
    THING THE REFERENCE HAS TO AN OUTPUT OBJECT: the folded main numerator, the selector
    buckets, and - explicitly - the negation that the Yul writes to QUOTIENT_EVAL_MPTR.
    It is a #[cfg(test)] struct, so it is reference code but not shipped code, and PLAN
    9.5's 'outputOf' does not name it. That distinction is the required finding's point. -/
structure TestLinearizationArtifacts where
  /-- rust: T:4276 (identity_trace: Vec<TestIdentityTraceEntry>) -/
  identityTrace : List TestIdentityTraceEntry
  /-- rust: T:4277 (main_numerator: Fq) -/
  mainNumerator : QVMFr
  /-- rust: T:4278 (selector_buckets: Vec<Fq>) -/
  selectorBuckets : List QVMFr
  /-- rust: T:4279 (quotient_expected_eval: Fq) -/
  quotientExpectedEval : QVMFr
  deriving BEq

/-- The test memory of T:4290's 'HashMap<u32, Fq>'. R4: the Rust's 'mem[&ptr]' PANICS on a
    missing key; the port returns 0 and every fixture is gated to hit only present keys
    (foldComputeFixturesNonDegenerate_ok), so the fallback is unreachable rather than
    silently wrong. -/
def TestMem := List (Nat × QVMFr)

def testMemGet (mem : TestMem) (ptr : Nat) : QVMFr :=
  match List.lookup ptr mem with
  | some v => v
  | none => 0

/-- rust: T:4394-4410 (eval_quotient_expr_for_test) @formal-baseline. "Evaluate the typed
    quotient expression tree for tests." The Token / TokenOffset arms PANIC in the Rust
    ("test expressions use literal memory only"); here they are 0 with the same
    unreachable-in-fixture argument, and foldComputeFixturesNonDegenerate_ok checks every
    fixture expression is literal-only. -/
def evalQuotientExprForTest (expr : QuotientExpr) (mem : TestMem) : QVMFr :=
  match expr with
  | .const value => (fqFromU256 value).toOption.getD 0
  | .mem (QuotientMem.literal ptr) => testMemGet mem ptr
  | .mem (QuotientMem.token _) => 0
  | .mem (QuotientMem.tokenOffset _ _) => 0
  | .add lhs rhs => qvmFrAdd (evalQuotientExprForTest lhs mem) (evalQuotientExprForTest rhs mem)
  | .mul lhs rhs => qvmFrMul (evalQuotientExprForTest lhs mem) (evalQuotientExprForTest rhs mem)
  | .neg inner => qvmFrNeg (evalQuotientExprForTest inner mem)

/-- rust: T:4288-4321 (expected_linearization_artifacts_for_test) @formal-baseline.
    "Evaluate expected quotient linearization artifacts directly from identities."

    THIS IS THE FOLD, AS ARITHMETIC: for each identity j, weight y^(m-1-j); Main adds into
    main_numerator, Selector(s) adds into bucket s; and quotient_expected_eval is the
    NEGATION of the main numerator, which is what the Yul stores into QUOTIENT_EVAL_MPTR.
    D-P20 item 1 says that negation is "Yul-side and modelled nowhere" - it is modelled
    here, in the reference's own test oracle, and nothing in this port invents it. -/
def expectedLinearizationArtifacts (identities : List QuotientIdentity) (mem : TestMem)
    (y : QVMFr) (selectorCount : Nat) : TestLinearizationArtifacts :=
  let total := identities.length
  let step (acc : TestLinearizationArtifacts) (identity : QuotientIdentity) :
      TestLinearizationArtifacts :=
    let value := evalQuotientExprForTest identity.expr mem
    let yPower := total - 1 - identity.meta_.globalIndex
    let scaled := qvmFrMul value (qvmFrPow y yPower)
    match identity.target with
    | QuotientTarget.main =>
        { acc with mainNumerator := qvmFrAdd acc.mainNumerator scaled }
    | QuotientTarget.selector s =>
        { acc with selectorBuckets :=
            List.mapIdx (fun (i : Nat) (b : QVMFr) =>
              if i == s then qvmFrAdd b scaled else b) acc.selectorBuckets }
  let base := List.foldl step
    { identityTrace := [], mainNumerator := 0, selectorBuckets :=
        List.replicate selectorCount 0, quotientExpectedEval := 0 } identities
  { identityTrace := (identities.map fun identity =>
      { globalIndex := identity.meta_.globalIndex, target := identity.target
        value := evalQuotientExprForTest identity.expr mem
        yPower := total - 1 - identity.meta_.globalIndex })
    mainNumerator := base.mainNumerator
    selectorBuckets := base.selectorBuckets
    quotientExpectedEval := qvmFrNeg base.mainNumerator }

/-- rust: T:1314-1335 (the sparse fold inside
    selector_sparse_fold_exhaustive_matches_naive_global_y_powers) @formal-baseline.
    "The compact path's fold": Main does acc := acc*y + value; a Selector identity first
    advances the MAIN accumulator by one y, then does bucket[s] := bucket[s]*y^gap + value;
    and at the end every bucket is advanced by its tail exponent. This is exactly what
    push_structured_main_fold (Q:1341-1351) and the selector arm of direct_quotient_block
    (Q:1029-1048) EMIT, read back as arithmetic - and T:1337-1339 asserts it equals the
    naive global-power form. sparseFoldMatchesNaiveGlobalPowers_ok is that assertion. -/
def sparseFoldArtifacts (identities : List QuotientIdentity) (mem : TestMem)
    (y : QVMFr) (fold : SelectorFoldPlan) (selectorCount : Nat) :
    TestLinearizationArtifacts :=
  let step (acc : QVMFr × List QVMFr) (identity : QuotientIdentity) : QVMFr × List QVMFr :=
    let value := evalQuotientExprForTest identity.expr mem
    match identity.target with
    | QuotientTarget.main => (qvmFrAdd (qvmFrMul (Prod.fst acc) y) value, Prod.snd acc)
    | QuotientTarget.selector s =>
        let buckets := List.mapIdx (fun (i : Nat) (b : QVMFr) =>
          if i == s then
            qvmFrAdd (qvmFrMul b (qvmFrPow y ((fold.gapFor identity).getD 0))) value
          else b) (Prod.snd acc)
        (qvmFrMul (Prod.fst acc) y, buckets)
  let raw := List.foldl step (0, List.replicate selectorCount 0) identities
  let tailStep (acc : List QVMFr) (pair : QVMFr × Nat) : List QVMFr :=
    List.mapIdx (fun (i : Nat) (b : QVMFr) =>
      if i == pair.snd then qvmFrMul b (qvmFrPow y pair.fst) else b) acc
  let finalBuckets := List.foldl tailStep (Prod.snd raw) (fold.tailExponents.zipIdx)
  { identityTrace := []
    mainNumerator := Prod.fst raw
    selectorBuckets := finalBuckets
    quotientExpectedEval := qvmFrNeg (Prod.fst raw) }

/-- rust: T:4325-4391 (eval_quotient_program_artifacts_for_test) @formal-baseline.
    "Interpret folded quotient bytecode into the same artifacts the verifier uses." THE
    WHOLE-STREAM FOLD EXECUTOR: it walks the physical bytecode, splits it at each fold
    opcode, evaluates the expression segment, and folds - FOLD_MAIN doing acc := acc*y + v,
    FOLD_SELECTOR reading its u24 (bucket, gap) and doing main *= y then
    bucket[b] := bucket[b]*y^gap + v. This is the object D-P20 item 1 says does not exist,
    and it does exist - in the test module.

    DEVIATION (R1): the Rust calls eval_quotient_vm_for_test (T:4413-4560), a test-local
    THIRD interpreter with twenty opcode arms. This port takes the segment value as a
    parameter instead, because P-09b already ships the reference interpreter at the same
    ABI over a different memory model, and the fold logic under test is independent of
    which one evaluates a segment. foldTestSegmentEval below supplies it for the opcodes
    the fixtures emit, and it is stated as a partial evaluator rather than hidden. -/
def evalQuotientProgramArtifacts (bytes : List Nat) (y : QVMFr)
    (selectorTailExponents : List Nat) (segmentValue : Nat → Nat → QVMFr) :
    Except String TestLinearizationArtifacts :=
  let rec go : Nat → Nat → QVMFr → List QVMFr → List TestIdentityTraceEntry →
      Except String (QVMFr × List QVMFr × List TestIdentityTraceEntry)
    | idx, identityStart, mainAcc, buckets, trace =>
        if idx >= bytes.length then
          if identityStart != bytes.length then
            .error "program ended mid-identity"
          else
            let total := trace.length
            let trace' := trace.map (fun e => { e with yPower := total - 1 - e.globalIndex })
            let buckets' := List.foldl (fun (acc : List QVMFr) (pair : QVMFr × Nat) =>
              List.mapIdx (fun (i : Nat) (b : QVMFr) =>
                if i == pair.snd then qvmFrMul b (qvmFrPow y pair.fst) else b) acc)
              buckets (selectorTailExponents.zipIdx)
            .ok (mainAcc, buckets', trace')
        else
          let op := bytes.getD idx 0
          if op == qOpFoldMain then
            let value := segmentValue identityStart idx
            go (idx + 1) (idx + 1) (qvmFrAdd (qvmFrMul mainAcc y) value) buckets
              (trace ++ [{ globalIndex := trace.length, target := QuotientTarget.main,
                           value := value, yPower := 0 }])
          else if op == qOpFoldSelector then
            let value := segmentValue identityStart idx
            let selectorIdx := bytes.getD (idx + 1) 0
            let gap := (bytes.getD (idx + 2) 0) * 256 + (bytes.getD (idx + 3) 0)
            let buckets' := List.mapIdx (fun (i : Nat) (b : QVMFr) =>
              if i == selectorIdx then
                qvmFrAdd (qvmFrMul b (qvmFrPow y gap)) value
              else b) buckets
            go (idx + 4) (idx + 4) (qvmFrMul mainAcc y) buckets'
              (trace ++ [{ globalIndex := trace.length,
                           target := QuotientTarget.selector selectorIdx,
                           value := value, yPower := 0 }])
          else
            match quotientOpcodeByteLen op with
            | some (len + 1) => go (idx + len + 1) identityStart mainAcc buckets trace
            | _ => .error ("opcode " ++ toString op ++ " at byte " ++ toString idx
              ++ " has no positive fixed byte length")
  termination_by idx => bytes.length - idx
  do
    let (mainAcc, buckets, trace) ← go 0 0 0 (List.replicate selectorTailExponents.length 0) []
    .ok { identityTrace := trace, mainNumerator := mainAcc, selectorBuckets := buckets,
          quotientExpectedEval := qvmFrNeg mainAcc }

/-- The segment evaluator the fixtures use: a partial interpreter over the five opcodes a
    hand-built identity expression emits (PUSH_MEM_U16, PUSH_CONST_U8, ADD, MUL, NEG),
    reading literal pointers from a TestMem. NOT a port of T:4413-4560 - see the deviation
    note above. An unimplemented opcode yields 0 rather than panicking, and
    foldTestSegmentEvalCoverage_ok gates that no fixture segment contains one. -/
def foldTestSegmentEval (bytes : List Nat) (consts : List Word256) (mem : TestMem) : QVMFr :=
  let rec go : List Nat → List QVMFr → QVMFr
    | [], stack => match stack with | [v] => v | _ => 0
    | op :: rest, stack =>
        match op with
        | 0x05 => match rest with
            | a :: b :: rest' => go rest' ((testMemGet mem (a * 256 + b)) :: stack)
            | _ => 0
        | 0x09 => match rest with
            | a :: rest' => go rest' (((consts.getD a 0).toNat % qvmFrModulus) :: stack)
            | _ => 0
        | 0x06 => match stack with
            | rhs :: lhs :: st => go rest (qvmFrAdd lhs rhs :: st)
            | _ => 0
        | 0x07 => match stack with
            | rhs :: lhs :: st => go rest (qvmFrMul lhs rhs :: st)
            | _ => 0
        | 0x08 => match stack with
            | v :: st => go rest (qvmFrNeg v :: st)
            | _ => 0
        | _ => match rest with
            | _ :: r => go r stack
            | [] => 0
  go bytes []


end Midfall.Generator.QuotientFoldCompute
/-! ====================================================================
    ## Known-answer tests
    ====================================================================

    R-41: every gate below was RUN; the failures to redden and the reference guards that
    cannot bind are reported in the package report. R-48: the fixtures are this package's
    own and foldComputeFixturesNonDegenerate_ok asserts their distinctness first.
    D-P19: the artifact gate reads quotient.rs at #eval time and is the FIRST #eval. -/

namespace Midfall.Generator.QuotientFoldComputeKats

open Midfall.Generator Midfall.Generator.QuotientFold
  Midfall.Generator.QuotientFoldCompute Midfall.Generator.QuotientBuilder

def qPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient.rs",
   "proofs/solidity-verifier/src/lowering/quotient.rs"]

def readQuotientArtifact : IO String :=
  qPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got
        else Midfall.Generator.QuotientVmKats.readFileOrEmpty path)
    (pure "")

def quotientReadOk (src : String) : Bool := src.length > 60000

/-! ### Fixtures -/

def cMem (ptr : Nat) : QuotientExpr := QuotientExpr.mem (QuotientMem.literal ptr)
def cConst (n : Nat) : QuotientExpr := QuotientExpr.const (BitVec.ofNat 256 n)
def cAdd (a b : QuotientExpr) : QuotientExpr := QuotientExpr.add a b
def cMul (a b : QuotientExpr) : QuotientExpr := QuotientExpr.mul a b

/-- One identity record with the given stream position, target and expression. The lines
    and var are what the gate emitters consume; the source is a Gate so the manifest-style
    helpers have something to name. -/
def cIdentity (j : Nat) (target : QuotientTarget) (expr : QuotientExpr) : QuotientIdentity :=
  { meta_ := { globalIndex := j
               , source := QuotientIdentitySource.gate j "g" 0 "c" 0 }
    lines := ["let e := mload(0x100)"]
    var := "e"
    target := target
    expr := expr }

/-- T:837-861's five-identity stream, verbatim: Main, Selector(0), Selector(1), Main,
    Selector(0), with the same expressions and the same memory. -/
def tIdentities : List QuotientIdentity :=
  [ cIdentity 0 QuotientTarget.main (cAdd (cMem 0x100) (cMem 0x120))
  , cIdentity 1 (QuotientTarget.selector 0) (cMul (cMem 0x140) (cMem 0x160))
  , cIdentity 2 (QuotientTarget.selector 1) (QuotientExpr.neg (cMem 0x180))
  , cIdentity 3 QuotientTarget.main (cMul (cAdd (cMem 0x100) (cMem 0x120)) (cMem 0x1a0))
  , cIdentity 4 (QuotientTarget.selector 0) (cAdd (cMem 0x1c0) (cConst 29)) ]

def tMem : TestMem :=
  [(0x100, 3), (0x120, 5), (0x140, 7), (0x160, 11), (0x180, 13), (0x1a0, 17), (0x1c0, 19)]

/-- BT:57-77's three candidates, verbatim. -/
def btCandidates : List NativeGateCandidate :=
  [ { gateIdx := 0, vmBytes := 100, nativeBytes := 320, gasSaved := 100 }
  , { gateIdx := 1, vmBytes := 80, nativeBytes := 160, gasSaved := 60 }
  , { gateIdx := 2, vmBytes := 70, nativeBytes := 160, gasSaved := 55 } ]

/-- BT:86-106's three candidates for the byte-budget test. -/
def btBudgetCandidates : List NativeGateCandidate :=
  [ { gateIdx := 0, vmBytes := 100, nativeBytes := 300, gasSaved := 1 }
  , { gateIdx := 1, vmBytes := 80, nativeBytes := 200, gasSaved := 1 }
  , { gateIdx := 2, vmBytes := 70, nativeBytes := 100, gasSaved := 1 } ]

/-- Three equal-value candidates: the hazard-1 order-sensitivity fixture. Every gate saves
    the same gas and costs the same bytes, so the ONLY thing that distinguishes them is the
    order they were processed in - which is exactly what the tie-break's fourth key reads. -/
def eqCandidates : List NativeGateCandidate :=
  [ { gateIdx := 0, vmBytes := 100, nativeBytes := 32, gasSaved := 10 }
  , { gateIdx := 1, vmBytes := 100, nativeBytes := 32, gasSaved := 10 }
  , { gateIdx := 2, vmBytes := 100, nativeBytes := 32, gasSaved := 10 } ]

def perm102 : List NativeGateCandidate :=
  [eqCandidates.getD 1 { gateIdx := 9, vmBytes := 0, nativeBytes := 0, gasSaved := 0},
   eqCandidates.getD 0 { gateIdx := 9, vmBytes := 0, nativeBytes := 0, gasSaved := 0},
   eqCandidates.getD 2 { gateIdx := 9, vmBytes := 0, nativeBytes := 0, gasSaved := 0}]

/-- T:1410-1424's limb7 chain, verbatim. -/
def limb7Lines : List String :=
  [ "let c0 := 0x100000000000000", "let m0 := mulmod(c0, x1, r)", "let a0 := addmod(x0, m0, r)"
  , "let m1 := mulmod(0x10000000000000000000000000000, x2, r)"
  , "let a1 := addmod(a0, m1, r)", "let m2 := mulmod(0x400000000, x3, r)"
  , "let a2 := addmod(a1, m2, r)", "let m3 := mulmod(0x40000000000000000000000, x4, r)"
  , "let a3 := addmod(a2, m3, r)", "let m4 := mulmod(0x1000, x5, r)"
  , "let a4 := addmod(a3, m4, r)", "let m5 := mulmod(0x100000000000000000, x6, r)"
  , "let a5 := addmod(a4, m5, r)" ]

/-- Unwrap an Except with a default (Lean core has no Except.getD). -/
def okD {ε α : Type} (x : Except ε α) (d : α) : α := match x with | .ok v => v | .error _ => d

/-- The selector fold of T:863, used by the program builders below. -/
def tFold : SelectorFoldPlan := okD (selectorFoldPlan tIdentities 2) selectorFoldPlanDefault

def foldFor (identity : QuotientIdentity) : Option Nat :=
  tFold.gapsByIdentity.getD identity.meta_.globalIndex none

/-- The program the fold executor walks: the five T:837 identities lowered in order. -/
def kProgramStep : QuotientProgramBuilder → List QuotientIdentity →
    Midfall.Generator.QuotientBuilder.M QuotientProgramBuilder
  | st, [] => .ok st
  | st, identity :: rest =>
      identityExpr Midfall.Generator.QuotientRecognizers.shapeRecognizers st identity.expr
        identity.target (foldFor identity) >>= fun st' => kProgramStep st' rest

def kProgramBuilder : QuotientProgramBuilder :=
  okD (kProgramStep builderDefault tIdentities) builderDefault

def kProgramBytes : List Nat := kProgramBuilder.bytes

def kProgramConsts : List Word256 := kProgramBuilder.consts

/-! ### Artifact gate (D-P19) -/

/-- GATE 1 (D-P19 reachability, FIRST #eval). Rules out: every cite below being checked
    against an empty read. -/
def foldComputeArtifactReachable_ok : IO Bool := do
  let src ← readQuotientArtifact
  return quotientReadOk src && (src.contains "fn select_native_gate_candidates")
    && (src.contains "fn direct_quotient_block") && (src.contains "fn push_structured_fold")
    && (src.contains "fn estimate_quotient_vm_gas")

/-- GATE 2 (hazard 1, THE REQUIRED GATE). The knapsack is order-dependent in a way that
    changes the ANSWER, not just its spelling: three candidates with identical gas and
    identical bytes, budget 64 and max_count 2, selected in the order [0,1,2] give the gate
    set {0,1}; in the order [1,0,2] they give {0,2}. The sets differ. A port that sorted the
    candidate list, or that kept a Pareto frontier instead of one state per DP cell, would
    return the same set for every order and silently normalise a choice the reference makes.
    Rules out: exactly that normalisation. -/
def knapsackOrderSensitivity_ok : Bool :=
  let forward := selectNativeGateCandidates eqCandidates 2 64
  let swapped := selectNativeGateCandidates perm102 2 64
  forward.gateIndices == [0, 1] && swapped.gateIndices == [0, 2]
    && (List.eraseDups forward.gateIndices).mergeSort (fun a b => decide (a <= b)) !=
          (List.eraseDups swapped.gateIndices).mergeSort (fun a b => decide (a <= b))
    && forward.gasSaved == swapped.gasSaved
    && forward.nativeBytes == swapped.nativeBytes

/-- GATE 3. The reference's own two knapsack tests, reproduced number for number:
    BT:57-83's selection (gate_indices [1,2], gas 115, bytes 320) and BT:86-112's default
    budget (500). Rules out: a port that gets the DP shape roughly right but not exactly. -/
def knapsackReferenceCases_ok : Bool :=
  let sel := selectNativeGateCandidates btCandidates 2 320
  sel.gateIndices == [1, 2] && sel.gasSaved == 115 && sel.nativeBytes == 320
    && defaultNativeGateByteBudget btBudgetCandidates 2 == 500
    && defaultNativeGateByteBudget btCandidates 2 == 480

/-- GATE 4. Each tie-break key of native_gate_selection_better (Q:652-658) binds, and the
    third one binds only in the shape it can. Key 1: more gas wins even at more bytes.
    Key 2: at equal gas, FEWER bytes wins. Key 3: at equal gas AND equal bytes, FEWER gates
    wins - reachable only because per-candidate gas values differ, e.g. one gate saving 30
    against two saving 15 each. Key 4: at equal gas, bytes and count, the lexicographically
    SMALLER index list wins, and the list is in push order (gate 2 shows what that costs).
    Rules out: a port that dropped the incumbent-over-candidate direction on keys 2-4. -/
def knapsackTieBreakKeys_ok : Bool :=
  (selectNativeGateCandidates
    [{ gateIdx := 0, vmBytes := 0, nativeBytes := 64, gasSaved := 50 }
    , { gateIdx := 1, vmBytes := 0, nativeBytes := 32, gasSaved := 60 }] 1 64).gateIndices == [1]
    && (selectNativeGateCandidates
      [{ gateIdx := 0, vmBytes := 0, nativeBytes := 64, gasSaved := 50 }
      , { gateIdx := 1, vmBytes := 0, nativeBytes := 32, gasSaved := 50 }] 1 64).gateIndices == [1]
    && (selectNativeGateCandidates
      [{ gateIdx := 0, vmBytes := 0, nativeBytes := 32, gasSaved := 30 }
      , { gateIdx := 1, vmBytes := 0, nativeBytes := 16, gasSaved := 15 }
      , { gateIdx := 2, vmBytes := 0, nativeBytes := 16, gasSaved := 15 }] 2 32).gateIndices == [0]
    && (selectNativeGateCandidates
      [{ gateIdx := 5, vmBytes := 0, nativeBytes := 32, gasSaved := 10 }
      , { gateIdx := 3, vmBytes := 0, nativeBytes := 32, gasSaved := 10 }] 1 32).gateIndices == [3]

/-- GATE 5. The degenerate arms: max_count 0 and byte_budget 0 short-circuit (Q:593-595);
    gas_saved 0 and native_bytes 0 candidates are filtered out (Q:606); a candidate whose
    rounded cost exceeds the budget is skipped (Q:609-611). Rules out: a port that let a
    zero-gas candidate occupy a DP cell, which would displace a real one on the length key. -/
def knapsackDegenerateInputs_ok : Bool :=
  selectNativeGateCandidates eqCandidates 0 64 == nativeGateSelectionStateDefault
    && selectNativeGateCandidates eqCandidates 2 0 == nativeGateSelectionStateDefault
    && (selectNativeGateCandidates
        [{ gateIdx := 0, vmBytes := 0, nativeBytes := 32, gasSaved := 0 }
        , { gateIdx := 1, vmBytes := 0, nativeBytes := 32, gasSaved := 5 }] 1 64).gateIndices == [1]
    && (selectNativeGateCandidates
        [{ gateIdx := 0, vmBytes := 0, nativeBytes := 0, gasSaved := 99 }
        , { gateIdx := 1, vmBytes := 0, nativeBytes := 32, gasSaved := 5 }] 1 64).gateIndices == [1]
    && (selectNativeGateCandidates
        [{ gateIdx := 0, vmBytes := 0, nativeBytes := 128, gasSaved := 99 }
        , { gateIdx := 1, vmBytes := 0, nativeBytes := 32, gasSaved := 5 }] 1 32).gateIndices == [1]
    && divCeil 0 32 == 0 && divCeil 1 32 == 1 && divCeil 32 32 == 1 && divCeil 33 32 == 2
    && byteUnit == 32

/-- GATE 6. default_native_gate_byte_budget's ranking (Q:567-584): vm_bytes DESCENDING,
    gate_idx ASCENDING on a tie, take max_count, sum native_bytes. The tie case is the one
    that matters: two candidates with equal vm_bytes must be ordered by index, so swapping
    their positions in the list cannot change the budget. Rules out: the tie-break being
    dropped (then the sum depends on sort stability) and the direction being flipped. -/
def knapsackBudgetTieBreak_ok : Bool :=
  let tied : List NativeGateCandidate :=
    [ { gateIdx := 0, vmBytes := 50, nativeBytes := 100, gasSaved := 1 }
    , { gateIdx := 1, vmBytes := 50, nativeBytes := 200, gasSaved := 1 } ]
  defaultNativeGateByteBudget tied 1 == 100
    && defaultNativeGateByteBudget tied.reverse 1 == 100
    && defaultNativeGateByteBudget tied 2 == 300
    && defaultNativeGateByteBudget [] 4 == 0
    && defaultNativeGateByteBudget btCandidates 0 == 0
    && defaultNativeGateByteBudget btCandidates 99 == 640

/-- GATE 7. T:863-868 reproduced exactly: gaps_by_identity [None, Some 0, Some 0, None,
    Some 3] and tail_exponents [0, 2]. The Some(3) is the second Selector(0) identity,
    three stream positions after the first; the tail 2 is the distance from the last
    Selector(1) identity to the end. Rules out: a gap computed against the previous
    identity of ANY bucket, and a tail measured from the wrong end. -/
def selectorFoldPlanReferenceTest_ok : Bool :=
  tFold.gapsByIdentity == [none, some 0, some 0, none, some 3]
    && tFold.tailExponents == [0, 2]
    && tFold.maxPower == 3
    && (foldFor (tIdentities.getD 4 (cIdentity 4 QuotientTarget.main (cConst 0)))) == some 3
    && (tFold.gapFor (tIdentities.getD 0 (cIdentity 0 QuotientTarget.main (cConst 0)))) == none
    && selectorPowerWords tFold == 4
    && quotientStateWords tFold == 6
    && selectorPowerWords selectorFoldPlanDefault == 0
    && quotientStateWords selectorFoldPlanDefault == quotientFixedStateWords

/-- GATE 8. selector_tail_updates (Q:339-352) drops zero tails and scales both offsets by
    WORD_BYTES. On T:868's tails [0, 2] only the second survives, at selector offset 0x20
    and power offset 0x40. Rules out: emitting a zero tail (the template would multiply a
    bucket by y^0 for nothing) and the two offsets being swapped. -/
def selectorTailUpdates_ok : Bool :=
  (selectorTailUpdates tFold).map (fun t => (t.selectorOffset, t.powerOffset)) == [(0x20, 0x40)]
    && (selectorTailUpdates { tFold with tailExponents := [1, 0] }).map (fun t => (t.selectorOffset, t.powerOffset)) == [(0, 0x20)]
    && (selectorTailUpdates { tFold with tailExponents := [] }).map (fun t => (t.selectorOffset, t.powerOffset)) == []
    && (selectorTailUpdates { tFold with tailExponents := [3, 4] }).length == 2

/-- GATE 9 (THE FOLD'S CORRECTNESS STATEMENT, T:1289-1340). For every target pattern over
    Main / Selector(0) / Selector(1) up to length 4 - 3^1 + ... + 3^4 = 120 streams - the
    SPARSE fold the compact path emits (acc := acc*y + v for Main; main *= y then
    bucket[s] := bucket[s]*y^gap + v for a selector; a final y^tail per bucket) equals the
    NAIVE global-power fold sum_j v_j * y^(m-1-j), and the negation matches too. This is
    the reference's own exhaustive agreement test, ported; the Rust goes to length 8 and
    this goes to 4: at length 5 the #eval interpreter already needs a minute, so the bound is a runtime limit and is stated rather than hidden. Length 4 is enough to exercise multi-gap buckets AND a non-zero tail together.
    Rules out: the gap schedule being wrong in any way that survives a single fixture. -/
def sparseFoldMatchesNaiveGlobalPowers_ok : Bool :=
  let y : QVMFr := 31
  let rec cases : Nat → Nat → Bool
    | 0, _ => true
    | len + 1, _ =>
        (List.range (3 ^ (len + 1))).all fun code =>
          let digits := (List.range (len + 1)).map fun idx =>
            (code / (3 ^ idx)) % 3
          let identities := (digits.zipIdx).map fun (digit, idx) =>
            cIdentity idx (match digit with
              | 0 => QuotientTarget.main
              | 1 => QuotientTarget.selector 0
              | _ => QuotientTarget.selector 1)
              (cConst ((idx + 2) * 17))
          let fold := okD (selectorFoldPlan identities 2) selectorFoldPlanDefault
          let naive := expectedLinearizationArtifacts identities [] y 2
          let sparse := sparseFoldArtifacts identities [] y fold 2
          sparse.mainNumerator == naive.mainNumerator
            && sparse.selectorBuckets == naive.selectorBuckets
            && sparse.quotientExpectedEval == naive.quotientExpectedEval
        && cases len 0
  cases 4 0

/-- GATE 10. The whole-stream fold executor (T:4325-4391) run over a REAL multi-identity
    program built by P-09c's builder, against the naive oracle of T:4288. This is the
    object D-P20 item 1 says is modelled nowhere: it walks the physical bytecode, splits at
    each FOLD_MAIN / FOLD_SELECTOR, evaluates the segment, and folds. Rules out: the fold
    opcode's operands being read at the wrong offset (the u24 packs bucket then gap), and
    the tail exponents being applied before rather than after the walk. -/
def wholeStreamFoldExecutor_ok : Bool :=
  let bytes := kProgramBytes
  let consts := kProgramConsts
  bytes != [] &&
    (match evalQuotientProgramArtifacts bytes 31 tFold.tailExponents
        (fun start stop =>
          foldTestSegmentEval (List.take (stop - start) (List.drop start bytes)) consts tMem) with
     | .error _ => false
     | .ok out =>
         out.identityTrace.length == 5
           && out.quotientExpectedEval == qvmFrNeg out.mainNumerator
           && (out.identityTrace.zipIdx).all fun (e, i) =>
                e.globalIndex == i && e.yPower == 5 - 1 - i)

/-- GATE 11. direct_quotient_block (Q:997-1051), the gate arm of the fold, on both targets.
    The Main arm must contain, in order, the y-advance and the addmod into EVAL; the
    Selector arm must contain the bucket pointer, the gap power ONLY when the gap is
    non-zero, and the addmod into the bucket. Rules out: the gap line being emitted for a
    zero gap (which would multiply the bucket by y^0 and, worse, address a power slot the
    table may not have), and the trace flag being ignored. -/
def directQuotientBlockShapes_ok : Bool :=
  let slots := QuotientStateSlots.new 0x2000
  let main := okD (directQuotientBlock ["let e := add(1, 2)"] "e" QuotientTarget.main none
    0x1000 slots false) []
  let sel0 := okD (directQuotientBlock ["let e := add(1, 2)"] "e" (QuotientTarget.selector 0)
    (some 0) 0x1000 slots false) []
  let sel1 := okD (directQuotientBlock ["let e := add(1, 2)"] "e" (QuotientTarget.selector 1)
    (some 3) 0x1000 slots false) []
  let traced := okD (directQuotientBlock ["let e := add(1, 2)"] "e" QuotientTarget.main none
    0x1000 slots true) []
  main.contains "mstore(0x2000, mulmod(mload(0x2000), y, r))"
    && main.contains "mstore(0x2000, addmod(mload(0x2000), mload(0x1000), r))"
    && main.head? == some "{" && (List.getLast? main).isSome
    && !sel0.any (fun l => (l.contains "q_selector_acc := mulmod"))
    && sel0.any (fun l => (l.contains "add(SELECTOR_ACC_MPTR, 0x0)"))
    && sel1.any (fun l => (l.contains "add(SELECTOR_ACC_MPTR, 0x20)"))
    && sel1.any (fun l => (l.contains "mload(add(0x2040, 0x60))"))
    && sel1.any (fun l => (l.contains "mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x1000), r))"))
    && traced.any (fun l => (l.contains "trace_u256(mload(0x2020), mload(0x1000))"))
    && !main.any (fun l => (l.contains "trace_u256"))
    && traced.length == main.length + 2

/-- GATE 12 (R4). The selector arm's '.expect' (Q:1031) is a release panic: a selector
    target with no gap aborts the build rather than emitting a bucket update with no power.
    Rules out: a port that defaulted the gap to 0, which would silently fold into the bucket
    without advancing it. -/
def directQuotientBlockSelectorGapPanic_ok : Bool :=
  match directQuotientBlock ["let e := 1"] "e" (QuotientTarget.selector 0) none 0x1000
      (QuotientStateSlots.new 0x2000) false with
  | .error f => (QVMFault.message f).contains ":1031 (selector gap for compact direct quotient block)"
  | .ok _ => false

/-- The chain with the accumulator thread broken at step 3. -/
def brokenLines : List String :=
  List.take 8 limb7Lines ++ ["let a3 := addmod(aX, m3, r)"] ++ List.drop 9 limb7Lines

/-- GATE 13. T:1409-1438 reproduced exactly: the thirteen-line seven-limb chain collapses
    to the constant binding plus one q_limb7 call with the seven arguments in order. Plus
    the negatives: a six-line prefix is not a chain, and a chain whose accumulator does not
    thread is not a chain. Rules out: the recogniser firing on a partial chain, and the
    argument order being normalised. -/
def limb7ChainReferenceTest_ok : Bool :=
  specializeLimb7Chains limb7Lines
    == ["let c0 := 0x100000000000000", "let a5 := q_limb7(x0, x1, x2, x3, x4, x5, x6)"]
    && specializeLimb7Chains (List.take 11 limb7Lines) == List.take 11 limb7Lines
    && specializeLimb7Chains brokenLines == brokenLines
    && specializeLimb7Chains [] == []
    && (tryLimb7Chain limb7Lines [] Midfall.Generator.limb7YulCoeffs "q_limb7").isSome

/-- A stand-in used only as a getD fallback. -/
def kPlaceholder : FoldSite :=
  { function := "", label := SiteLabel.fixed (FoldLabel.gate 0 0),
    weight := FoldWeight.fixed 0, bucket := FoldBucket.main }

/-- GATE 14. push_structured_fold's Weighted arm (Q:1364-1397): the emitted statement is
    EXACTLY FoldSite::statement of the recorded site - the recorder and the emitter cannot
    disagree by construction - and the site carries the right weight and bucket. The Horner
    arm records nothing and emits the three-line main fold. Rules out: the site recorded
    being a different site from the statement emitted, which is the one way the fold check
    could pass while the Yul was wrong. -/
def pushStructuredFoldArms_ok : Bool :=
  let slots := QuotientStateSlots.new 0x2000
  let (b1, s1) := pushStructuredFold [] [] (StructuredFold.weighted 5 false) "e"
    (FoldPos.fixed 2 (FoldLabel.gate 0 0))
  b1.length == 1 && s1.length == 1
    && b1 == [(s1.getD 0 (kPlaceholder)).statement "e"]
    && (s1.getD 0 kPlaceholder).weight == FoldWeight.fixed 2
    && (s1.getD 0 kPlaceholder).function == ""
    && (match (s1.getD 0 kPlaceholder).label with
        | SiteLabel.fixed l => l == FoldLabel.gate 0 0
        | _ => false)
    && (match pushStructuredFold [] [] (StructuredFold.horner slots false) "e"
          (FoldPos.fixed 2 (FoldLabel.gate 0 0)) with
        | (b, s) => s.isEmpty && b.length == 2
            && b.contains "mstore(0x2000, mulmod(mload(0x2000), y, r))"
            && b.contains "mstore(0x2000, addmod(mload(0x2000), e, r))")

/-- GATE 15. The Weighted arm's out-of-range weight (Q:1368's
    'unwrap_or(usize::MAX)'): a position at or past m records Y_POW[2^64-1], which check
    then rejects. The doc at Q:1366-1367 says this is deliberate. Rules out: the port
    saturating to 0 instead, which would fold identity j with weight Y_POW[0] - a WRONG
    weight that check's property 3 would report as a mismatch rather than as out-of-range. -/
def pushStructuredFoldOutOfRangeWeight_ok : Bool :=
  let (_, sites) := pushStructuredFold [] [] (StructuredFold.weighted 5 false) "e"
    (FoldPos.fixed 5 (FoldLabel.gate 9 9))
  let (tb, _) := pushStructuredFold [] [] (StructuredFold.weighted 5 true) "e"
    (FoldPos.fixed 2 (FoldLabel.gate 0 0))
  let (lb, ls) := pushStructuredFold [] [] (StructuredFold.weighted 5 true) "e"
    (FoldPos.loop 2 { var := "q_perm_i", start := 1, end_ := 3 }
      FoldLabel.permutationContinuity)
  sites.length == 1
    && (List.getD sites 0 kPlaceholder).weight == FoldWeight.fixed (2^64 - 1)
    && List.head? tb == some "trace_u256(30002, e)"
    && List.head? lb == some "trace_u256(add(30002, q_perm_i), e)"
    && (List.getD ls 0 kPlaceholder).weight == FoldWeight.loopDown 2 "q_perm_i"

/-- GATE 16. The three byte/gas proxies. yul_block_source_bytes is len+1 per line;
    estimate_native_yul_gas is the per-line weighted count halved; estimate_quotient_vm_gas
    walks the program with P-09e's decoder, so the two run-length opcodes read their count
    and MODARITH7 reads its length. Rules out: the halving being dropped, and the fallback
    'len * 12' arm being applied to a named opcode. -/
def gasEstimatorProxies_ok : Bool :=
  yulBlockSourceBytes ["ab", "cde"] == 2 + 1 + 3 + 1
    && yulBlockSourceBytes [] == 0
    && estimateNativeYulGas ["mstore(0, mload(0))"] == (4 + 8 + 10) / 2
    && estimateNativeYulGas ["x := addmod(a, b, r)"] == (4 + 38) / 2
    && estimateNativeYulGas ["q := add(mul(a, b), sub(c, d))"] == (4 + 18 + 16 + 18) / 2
    && estimateNativeYulGas [] == 0
    && countNeedle "mload(mload(0))" "mload(" == 2
    && (okD (estimateQuotientVmGas [qOpAdd, qOpMul]) 0) == 38 + 42
    && (okD (estimateQuotientVmGas [qOpFoldMain]) 0) == 70
    && (okD (estimateQuotientVmGas [qOpNativeIdentity, 0, 0]) 9) == 0
    && (okD (estimateQuotientVmGas [qOpPushConstU8, 3]) 0) == 42

/-- GATE 17. native_gate_indices (Q:528-540) returns a HashSet in the Rust, so only
    MEMBERSHIP is observable - the plan uses it at Q:451 and Q:457 as a 'contains' test and
    rebuilds the ordered list from the gate stream instead. This asserts the port's list is
    duplicate-free and that the empty-gates case is the empty set. Rules out: a port that
    made the list order load-bearing where the reference made it a set. -/
def nativeGateIndicesMembershipOnly_ok : Bool :=
  okD (nativeGateIndices []) [] == []
    && (List.eraseDups (okD (nativeGateIndices gateFixture) [])).length == (okD (nativeGateIndices gateFixture) []).length
    && defaultQuotientNativeGates == 4
    && defaultHybridQuotientInlineIdentities == 4
  where
    gateFixture : List QuotientIdentity :=
      [ cIdentity 0 QuotientTarget.main (cAdd (cMem 0x100) (cMem 0x120))
      , cIdentity 1 (QuotientTarget.selector 0) (cMul (cMem 0x140) (cMem 0x160)) ]

/-- GATE 18. The two panic sites of selector_fold_plan (Q:393 dense indices, Q:398 gap
    present) are reachable, not decoration: a stream whose global indices skip a position
    aborts. Rules out: a port that read a missing entry as Main, which would drop a
    selector identity from the gap schedule and fold it into the wrong bucket. -/
def selectorFoldPlanPanics_ok : Bool :=
  match selectorFoldPlan [cIdentity 7 QuotientTarget.main (cConst 1)] 1 with
  | .error f => (QVMFault.message f).contains ":393 (quotient identity global indices must be dense)"
  | .ok _ => false

/-- GATE 19. u256_string's 'bit_len() < 64' branch (QVM:4123) cannot change the output:
    for any value below 2^64 the two arms render the same text, and above it the first arm
    is not taken. A guard that cannot bind, in the sense P-09f established - recorded rather
    than counted as enforcement. Rules out: the claim that the branch is load-bearing. -/
def u256StringBranchCannotBind_ok : Bool :=
  (List.all [0, 1, 255, 65535, 2^32 - 1, 2^63] fun n =>
    u256String (BitVec.ofNat 256 n) == "0x" ++ hexDigits n)
    && u256String (BitVec.ofNat 256 (2^64)) == "0x" ++ hexDigits (2^64)
    && u256String 0 == "0x0"

/-- GATE 20 (R-48). The fixtures are not degenerate: the five stream identities have
    distinct targets and distinct expressions, the memory pointers are pairwise distinct,
    the knapsack candidates differ in the field each gate relies on, the limb7 chain's six
    coefficients are distinct, and the program the fold executor walks really contains both
    fold opcodes. Rules out: gates above being satisfied by one value. -/
def foldComputeFixturesNonDegenerate_ok : Bool :=
  tIdentities.length == 5
    && (List.eraseDups (tIdentities.map (fun i => match i.target with
         | QuotientTarget.main => 0 | QuotientTarget.selector 0 => 1 | _ => 2))).length == 3
    && (List.eraseDups (tIdentities.map (fun i => i.expr))).length == 5
    && (List.eraseDups (List.map Prod.fst tMem)).length == tMem.length
    && (List.all tMem fun (_, v) => v != 0)
    && (List.eraseDups (btCandidates.map (fun c => c.gasSaved))).length == 3
    && (List.eraseDups (btCandidates.map (fun c => c.nativeBytes))).length == 2
    && (List.eraseDups (List.map (fun c => c.gasSaved) eqCandidates)).length == 1
    && (List.eraseDups Midfall.Generator.limb7YulCoeffs).length == 6
    && kProgramBytes.contains qOpFoldMain
    && kProgramBytes.contains qOpFoldSelector
    && kProgramBytes.length > 10
    && (tIdentities.all fun i =>
          (List.all (exprLiterals i.expr) fun p => (List.map Prod.fst tMem).contains p))
  where
    exprLiterals : QuotientExpr → List Nat
      | .const _ => []
      | .mem (QuotientMem.literal ptr) => [ptr]
      | .mem (QuotientMem.token _) => []
      | .mem (QuotientMem.tokenOffset _ _) => []
      | .add l r => exprLiterals l ++ exprLiterals r
      | .mul l r => exprLiterals l ++ exprLiterals r
      | .neg i => exprLiterals i

#eval Midfall.Generator.QuotientFoldComputeKats.foldComputeArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.knapsackOrderSensitivity_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.knapsackReferenceCases_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.knapsackTieBreakKeys_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.knapsackDegenerateInputs_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.knapsackBudgetTieBreak_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.selectorFoldPlanReferenceTest_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.selectorTailUpdates_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.sparseFoldMatchesNaiveGlobalPowers_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.wholeStreamFoldExecutor_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.directQuotientBlockShapes_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.directQuotientBlockSelectorGapPanic_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.limb7ChainReferenceTest_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.pushStructuredFoldArms_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.pushStructuredFoldOutOfRangeWeight_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.gasEstimatorProxies_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.nativeGateIndicesMembershipOnly_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.selectorFoldPlanPanics_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.u256StringBranchCannotBind_ok -- expect true
#eval Midfall.Generator.QuotientFoldComputeKats.foldComputeFixturesNonDegenerate_ok -- expect true

end Midfall.Generator.QuotientFoldComputeKats

