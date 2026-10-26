-- |
-- Midfall.Generator.Quotient.VmValidator
--
-- THE QUOTIENT VM VALIDATOR: the two-phase offline safety pass over a finalized
-- byte-oriented quotient program, and the operand walker underneath it. This is
-- PLAN 9.5's `Supported.qvm` (QVM-01). Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs (4336 lines
-- at git HEAD), cited below as QVM: QVM:2004-2027 (phase 1, the structural
-- validator), QVM:2029-2096 (the three model records), QVM:2098-2126
-- (`QuotientOperand`), QVM:2128-2158 (phase 2, the operand validator),
-- QVM:2160-2196 (the two `#[cfg(test)]` narrower passes), QVM:2198-2304 (the
-- three checks and the window renderer), QVM:2306-2506 (the operand walker),
-- QVM:2508-2800 (the checked decoder, the stack-effect table, the token check and
-- the four checked-arithmetic helpers), QVM:2816-2824 (`read_u16`, `read_u32`)
-- and QVM:3004-3090 (the GENERAL `quotient_op_len`, its two dynamic helpers and
-- the instruction iterator). Work package P-09e.
--
-- CITATION NOTATION. QVM is vm/mod.rs read through 'git show HEAD:<path>', every
-- range re-derived from that output and never from wc -l on a dirty checkout
-- (docs/plans/README.md standing note 2). QVR is vm/reference.rs (549 lines at
-- HEAD), P-09b's interpreter, in VmReference.lean. QVC is vm/certify.rs (365
-- lines), P-09d's certifier. PL is lowering/plan.rs, whose `quotient_read_model`
-- (PL:570-621) and `quotient_operand_model` (PL:626-643) BUILD the records ported
-- here from the converged layout. LT is lowering/tests.rs (5156 lines), where the
-- reference's own validator tests live - LT:2341-2377 (structural rejects),
-- LT:2453-2479 (walker totality), LT:2481-2646 (QVM-01 per-class rejects) - all
-- ported as gates below. LM is lowering/layout/mod.rs, whose `WORD_BYTES` (LM:17) is
-- the alignment and window stride the operand checks use.
--
-- WHY THIS FILE IS LOAD-BEARING FOR PLAN 9.5.
--
-- `Supported.qvm` is literally `validateQuotientProgramOperands g.plan = .ok ()`
-- (docs/PLAN.md:423), and `Supported` is the hypothesis of `lowering_equivalence`.
-- Before this package that predicate had no Lean denotation. It does now:
-- `validateQuotientProgramOperands` below is the reference function - total,
-- decidable, and its `.ok ()` is exactly the field. What is still missing to spell
-- it as `... g.plan` is the ONE-ARGUMENT bridge PL:626-643, which reads the
-- converged memory layout; every input type it needs already exists in this tree
-- (see the package report's required finding).
--
-- HAZARD 1: THE TWO-PHASE DEPENDENCY IS A SOUNDNESS CLAIM, AND IT HOLDS.
--
-- QVM:2143-2145 runs `validate_quotient_program` first and says why: "its checked
-- decoder guarantees every operand offset walked below is in bounds." The operand
-- phase reads bytecode with the Rust's DIRECT INDEX (`bytes[offset]`, QVM:2320,
-- 2518, 3009, 3038), which PANICS - it is not the interpreter's bounds-checked
-- `byte_at`. So the claim is load-bearing, and it is checkable. The argument, arm
-- by arm, is that for every opcode the byte span phase 1 admits
-- (`quotient_byte_instruction_len_checked`) covers every offset the walker reads
-- inside that instruction:
--
-- * fixed opcodes: `quotient_opcode_byte_len` (QVM:926-932) is the length the
--   walker's operand offsets stay under - LIN7 is 1 + 7*3 and the walker's last
--   read is idx + 1 + 6*3 + 2 = idx + 21; BILIN7_PAIRWISE is 1 + 4 + 13 with last
--   read idx + 17; FOLD_SELECTOR is 1 + 3 (the `.u24` encoding) with reads at
--   idx + 1 and idx + 2..3; PUSH_MEM_LITERAL is 1 + 4.
-- * the two RUN forms, AFFINE_SUM and MODARITH7: the checked length and the
--   walker use the SAME strides (5 and 3 for the runs; 3 and 5 for AFFINE_SUM's
--   linear and product blocks; 21, 23, 17, 3, 5 for MODARITH7's five blocks), and
--   the checked version bounds each block as it advances
--   (`advance_quotient_cursor`), so a program phase 1 admits has room for every
--   block the walker will walk.
--
-- That is not assumed here, it is gated three ways:
-- `twoPhase_noPanicOnPhase1Accepted_ok` (a corpus of mutated, truncated and padded
-- programs: whenever phase 1 accepts, phase 2 never returns the panic class),
-- `twoPhase_phase2PanicsWithoutPhase1_ok` (the converse - the SAME programs walked
-- by phase 2 alone DO panic, so the guarantee really comes from phase 1), and
-- `twoPhase_checkedAndUncheckedWalksAgree_ok` (the instruction boundaries the two
-- walkers compute coincide on every phase-1-accepted program, and are shown to
-- DIVERGE on one phase 1 rejects - MODARITH7 with an unknown flag bit, which the
-- checked decoder refuses and the unchecked `quotient_op_len` walks straight past).
--
-- CONCLUSION, and it is the answer to the brief's question: phase 2 cannot panic
-- on anything phase 1 accepted, so there is no hole in `Supported.qvm` at this
-- layer. The one caveat is that the guarantee belongs to the PAIR, not to the
-- operand phase alone: the two `#[cfg(test)]` helpers ported here
-- (`validateQuotientMemPtrs`, `validateQuotientConstSlots`) do NOT run phase 1 and
-- panic on malformed input exactly as the Rust's do. Non-test callers must not
-- reach for them.
--
-- HAZARD 2: WHICH MEMORY MODEL THE BOUNDS REFER TO, AND D-P20 ITEM 2.
--
-- The bounds in this file are NOT about the certifier's memory and they are not a
-- runtime fault the interpreter can raise. They are about the DEPLOYED Yul VM's
-- memory as described by the converged `VerifierMemoryLayout`:
-- `QuotientReadModel.windows` is PL:580-605 - `vk_payload`, `user_challenges`,
-- `challenge_and_common_slots`, `decoded_proof_evals`, i.e. "exactly the ranges the
-- verifier has populated by the time the VM runs" (PL:527-531) - and
-- `stack_words` is `(quotient_stack_hi - quotient_stack_mptr) / WORD_BYTES`
-- (PL:640-641), the registered scratch region. PL:567-569 gives the point in one
-- line: "the interpreter has no runtime pointer clamp".
--
-- The two readings therefore do not conflict; they are about two memories.
--
-- * CERTIFIER memory (QVR:49-108, `QuotientRefMemory`): a PRNG over the whole u32
--   address space, so every address read succeeds by construction. P-09b's finding
--   stands and D-P20 item 2 is right that an `.oob` FAULT cannot arise there - the
--   only out-of-range faults in that model are reads past the end of the PROGRAM
--   and constant slots past the end of the TABLE.
-- * DEPLOYED memory (this file's model): a real address space with holes. A
--   pointer outside the windows is not a revert - there is no clamp - it is a
--   silent read of uninitialized scratch or of a live challenge word, which
--   QVM:2162-2166 names as "silently changing the numerator rather than
--   reverting". The only thing in the reference that prevents that is this
--   validator, at build time.
--
-- So `qvm_validated_noOOB` IS about this layer, but not as an interpreter fault:
-- `.oob` is not a constructor the run can produce, it is the negation of what
-- `validateQuotientProgramOperands` checks. The honest restatement of PLAN 9.5's
-- item is: validated program plus the layout model implies no pointer the program
-- loads lies outside the populated windows - a property of the PROGRAM plus the
-- LAYOUT, not of a memory object - and the two real fault classes D-P20 names stay
-- where they are, in the interpreter. Both readings are kept; neither is
-- overwritten. `readModel_isTheLayoutModel_ok` pins the window set against
-- plan.rs from disk so this cannot drift.
--
-- HAZARD 3: THE GENERAL `quotient_op_len`, AND WHAT TO RETIRE.
--
-- P-09c ported a compaction-scoped copy of QVM:3008-3059 into VmBuilder (`walkByte`,
-- `walkReadU16`, `quotientAffineSumOpLen`, `quotientModarith7OpLen` and `quotientOpLen`,
-- VmBuilder.lean:1241-1303) and left notes at :1286 and :1424 saying P-09d would
-- absorb them. P-09d found that misdirected - the general forms are `vm/mod.rs`
-- items - so they are here and those two notes are stale. The retirement is
-- VmBuilder.lean:1239-1303 (the section header and those five defs) plus the then
-- unused `siteWalkRead` / `siteUnknownOp` at :175-176, in favour of
-- `QuotientValidator.quotientOpLen` mapped through `toQVMFault`; the four call
-- sites (:1325, :1393, :1432 and the KAT helper :2079) do not change shape.
-- `quotientOpLen_agreesWithScopedCopy_ok` gates the two over every fixture program at
-- every byte index on both the accept and the reject side, and the two
-- sub-helpers separately, because a shared top-level agreement could hide a
-- compensating pair of errors.
--
-- HAZARD 4: ERROR STRINGS ARE THE INTERFACE.
--
-- Every `Err` in this cluster is a `format!` string a caller embeds: PL:504-505 wraps
-- the operand validator's error into "quotient VM operand validation failed:
-- {err}" and returns it as a render error, while QVM:1217-1218 PANICS with the
-- structural validator's - the same string aborting a build on one path and
-- rejecting a render on the other, which is P-09b's hazard-5 distinction one
-- level up. So the 26 strings are a closed taxonomy
-- (`QuotientValidationFault`), each constructor carrying the numbers the Rust
-- interpolates, and `message` renders the Rust's text verbatim.
-- `faultMessages_artifactStrings_ok` checks both halves against vm/mod.rs at #eval
-- time (D-P19) after normalising the Rust's backslash continuations, and
-- `faultTaxonomy_isExactlyTheCluster_ok` gates one entry per string with no
-- duplicates.
--
-- HAZARD 5: WIDTHS, AT value-1 / value / value+1.
--
-- Every bound this file enforces is tested at three points: the 255/256 const-slot
-- boundary in both the u8 and the u16 form, the stack-words limit around the
-- program's own high-water mark, the u16 pointer ceiling 0xffff / 0x10000, the
-- window edges at start-0x20 / start / end-0x20 / end / end+1, the alignment
-- residue at 0x100 / 0x101, the selector bucket count and the selector gap power.
-- Two width facts are ported rather than assumed: the MODARITH7 flag test
-- `flags & !(COND | CONST)` is `flags & 0xfc` on a u8 and must be written as an
-- explicit mask in `Nat` (R5), and the four `checked_*` overflow arms are
-- UNREACHABLE here because `Nat` does not wrap - they stay in the taxonomy because
-- the strings are the interface and a 32-bit Rust build can reach them, and
-- `overflowAndFuelArms_unreachable_ok` says so by finding none on the corpus.
--
-- HAZARD 6: NO SHAPE RECOGNIZERS. The validator needs none: nothing in
-- QVM:2004-3090 calls `quotient_limb_shape`, `quotient_limb_subshape`,
-- `quotient_modarith7_shape` or `quotient_pow5_base`. The one thing the operand
-- phase declines to check is `NATIVE_IDENTITY`'s u16 callback index, which
-- QVM:2353-2355 delegates to `QuotientProgramPlan::validate_execution_manifest`
-- (QVM:382-474) - the plan-to-manifest bridge P-09a deliberately left unported.
-- That is a real gap in `Supported.qvm`'s coverage; it is reported, not papered
-- over, and it is not a recognizer.
--
-- BYTE DOMAIN: THE INPUT IS NOT QUITE THE RUST TYPE. The Rust takes `&[u8]`; the row
-- bridges programs as `List Nat`, which is strictly broader - a list containing 256
-- is not a program the reference can name, and `read_u16 [0x01, 300]` would yield 556,
-- a value no two `u8` bytes produce. Rather than leave `Supported.qvm` quantifying
-- over inputs the Rust cannot see, every public entry point
-- (`validateQuotientProgram`, `validateQuotientProgramOperands`, `quotientBytecodeOps`,
-- `validateQuotientMemPtrs`, `validateQuotientConstSlots`) refuses such a list through
-- `requireByteProgram` with the port-only fault `notAByteProgram` (the one constructor
-- in the taxonomy with no Rust string, and it is labelled as such). The internal readers
-- stay unguarded because the entry points dominate them. Gated by
-- `byteDomain_enforcedAtEveryEntryPoint_ok`, whose sharpest case is
-- `[PUSH_CONST_U8, 256, FOLD_MAIN]` - a program phase 1 would otherwise ACCEPT.
-- PORT RULES AS THEY APPLY HERE (PLAN section 4, R1-R11).
--
-- * R1 provenance: one Lean def per Rust fn, private helpers included
--   (`require_quotient_bytes`, `advance_quotient_cursor`, the two checked arithmetic
--   helpers, `apply_quotient_stack_effect`, `describe_read_windows`).
-- * R2 names: snake_case to lowerCamelCase. Three collisions to record. (a)
--   QVM:2817/2822 `read_u16` / `read_u32` become `readU16` / `readU32` in THIS
--   namespace; P-09b already has `Midfall.Generator.readU16` / `readU32` for the
--   DIFFERENT Rust items at QVR:517/525, which return `Err` where these panic. The
--   two are not interchangeable and the namespaces keep them apart. (b) The Rust's
--   `QuotientOperand::Const` becomes `.konst`, because `Const` collides with a Lean
--   builtin type former; every other variant keeps its name. (c) `end` is avoided
--   as a binder (`end_` in `requireQuotientBytes`).
-- * R3 control flow: `?` becomes `<-` in `Except`. The Rust's operand walker takes a
--   `&mut dyn FnMut(QuotientOperand) -> Result<(), String>` callback and short-circuits
--   on its first error. Lean has no mutation, so the walker RETURNS the operands
--   in visit order and `validateQuotientProgramOperands` folds the checker over them
--   per instruction. The observable difference is confined to programs phase 1
--   rejects, where phase 2 never runs: within one instruction the Rust interleaves
--   read/check while this reads the instruction's whole operand list first, and
--   every one of those offsets is in bounds once phase 1 has spoken. The visit
--   ORDER is unchanged and is pinned per opcode by `perOpcode_phase1AcceptsAndWalkerPins_ok`.
-- * R4 panics, release profile: `unreachable!` (QVM:2255) and every direct
--   `bytes[i]` index become the `.panic` class carrying the source line; no
--   overflow panics (the cluster's arithmetic is all `checked_*`); no `debug_assert!`.
-- * R5 integers: `usize`, `u8`, `u16`, `u32` all become `Nat`. Where a Rust width is
--   load-bearing it is written out: the u8 flag mask above, and the four checked
--   arms expressed as wrap tests. The `as usize` widenings of a `u16` / `u32` read
--   are free in `Nat`.
-- * R6 collections: `Vec<QuotientReadWindow>` -> `List`, `Vec<(u8, usize)>` ->
--   `List (Nat x Nat)` with `find?` for the Rust's `iter().find_map` (first match in
--   table order, exactly as written), `&[u8]` -> `List Nat` (the row's bridge is
--   `qvmBytesOfNats` / `qvmBytesToNats`).
-- * R9: no traits here. `QuotientOperandModel` is a plain record, which is what makes
--   `Supported.qvm` a decidable proposition rather than a typeclass call.
-- * R10 totality: nothing `partial`. Every Rust `while` / `for .. in 0..n` loop becomes a
--   fuel-bounded fold; the fuel is `bytes.length` or a fixed count, every step
--   provably advances, and `overflowAndFuelArms_unreachable_ok` gates that no fuel arm fires on
--   any corpus program - a bound that binds would be a bug.
-- * R11: the line-range table is in the package report.
--
-- WHAT MOVED, AND WHY (Lean is order-sensitive; Rust within a module is not).
-- 1. The three model records (QVM:2029-2096) and `QuotientOperand` (QVM:2098-2126)
--    move to the top: everything below reads them.
-- 2. The low-level readers move next: `read_u16` / `read_u32` (QVM:2816-2824) and
--    the four checked arithmetic helpers (QVM:2768-2814) are shared by the
--    decoder, the walker and the general length function.
-- 3. The GENERAL `quotient_op_len` cluster (QVM:3004-3090) moves ahead of phase 1,
--    because `quotientBytecodeOps` is what phase 2 walks.
-- 4. Phase 1 (QVM:2004-2027) sits after its decoder (QVM:2508-2673) and stack
--    table (QVM:2675-2755), which the Rust also places after it; the two checked
--    dynamic-length helpers move ahead of `quotient_byte_instruction_len_checked`,
--    which calls them.
-- 5. `describe_read_windows` (QVM:2289-2304) moves above the check that
--    interpolates it.

import Midfall.Common.Bytes
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder

namespace Midfall.Generator.QuotientValidator

/-! ## Faults (rust: the `Result<_, String>` payloads of QVM:2004-3090) -/

/-- The source file every site string in this port cites. -/
def qvmValidatorPath : String :=
  "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"

/-- The closed taxonomy of the 26 error strings this cluster can produce, plus the
    R4 panic class. Each constructor carries exactly the numbers the Rust
    interpolates and `message` renders its text verbatim (hazard 4). -/
inductive QuotientValidationFault
  /-- rust: QVM:2513 and QVM:2564 (both "unknown quotient VM opcode {op:#x} at
      byte {idx}") - the spec lookup in the decoder and the static-length fallback
      in the same function. One constructor, because the text is identical. -/
  | unknownOpcode (op idx : Nat)
  /-- rust: QVM:2735. -/
  | unknownOpcodeInStackValidator (op idx : Nat)
  /-- rust: QVM:2763. -/
  | unknownMemToken (token idx : Nat)
  /-- rust: QVM:2780. `remaining` is `bytes.len().saturating_sub(idx)`. -/
  | truncated (context : String) (idx need remaining : Nat)
  /-- rust: QVM:2777. Unreachable in `Nat` (R5); kept because the string is the
      interface. -/
  | byteRangeOverflow (context : String) (idx : Nat)
  /-- rust: QVM:2530. `name` is the spec's `&'static str`. -/
  | zeroLengthDecoded (name : String) (op idx : Nat)
  /-- rust: QVM:2545 and QVM:2555, one per RUN form. -/
  | zeroLengthRun (idx : Nat)
  /-- rust: QVM:2583. -/
  | affineSumZeroCounts (idx : Nat)
  /-- rust: QVM:2602. -/
  | modarith7UnknownFlags (flags idx : Nat)
  /-- rust: QVM:2797. Unreachable in `Nat`. -/
  | cursorOverflow (op opIdx : Nat)
  /-- rust: QVM:2805. Unreachable in `Nat`. -/
  | lenMulOverflow (op idx : Nat)
  /-- rust: QVM:2812. Unreachable in `Nat`. -/
  | lenAddOverflow (op idx : Nat)
  /-- rust: QVM:2022. -/
  | stackLeak (depth : Nat)
  /-- rust: QVM:2695. Unreachable in `Nat`. -/
  | stackDepthOverflow (idx : Nat)
  /-- rust: QVM:2751. -/
  | stackUnderflow (op idx required found : Nat)
  /-- rust: QVM:2721 - the FOLD_* "exactly 1" boundary. -/
  | stackBoundary (op idx found : Nat)
  /-- rust: QVM:2729 - the three native markers' "empty stack" boundary. -/
  | nativeCallbackStack (op idx found : Nat)
  /-- rust: QVM:2148. -/
  | stackRegionExceeded (maxStack stackWords : Nat)
  /-- rust: QVM:2214. `num` is `model.num_selector_buckets`. -/
  | selectorBucketOutOfRange (bucket idx num : Nat)
  /-- rust: QVM:2224. `maxPower` is `model.selector_max_power`. -/
  | selectorGapTooLarge (gap idx maxPower : Nat)
  /-- rust: QVM:2245. -/
  | tokenHasNoBase (token idx : Nat)
  /-- rust: QVM:2252. Unreachable in `Nat`, and unreachable in the Rust on a
      64-bit target too: `offset` comes from a `u32` read. -/
  | tokenOffsetOverflow (idx : Nat)
  /-- rust: QVM:2259. `kind` is the operand class: "literal", "u16", "token",
      "limb", "row_lhs", "pairwise_lhs", "pairwise_rhs", "modarith_cond". -/
  | pointerMisaligned (kind : String) (ptr idx : Nat)
  /-- rust: QVM:2264. `windows` is `describe_read_windows model.read`, carried
      rendered because the Rust renders it at the error site. -/
  | pointerOutsideWindows (kind : String) (ptr idx : Nat) (windows : String)
  /-- rust: QVM:2281. `wide` selects the "u16" / "u8" word the Rust interpolates. -/
  | constSlotOutOfRange (wide : Bool) (slot idx constLen : Nat)
  /-- rust: QVM:2502 - the walker's fail-closed fallback arm. -/
  | walkerMissingArm (op idx : Nat)
  /-- PORT-ONLY (not a Rust string): the Rust's parameter is `&[u8]`, so a `List Nat`
      carrying a value at or above 256 is not a program the reference can even name.
      Without this guard the Lean API is strictly broader than the reference's -
      `readU16 [0x01, 300]` would yield 556, a value no `u8` pair produces - and
      `Supported.qvm` would quantify over inputs the Rust cannot see. Every public entry
      point below refuses it, and `byteDomain_enforcedAtEveryEntryPoint_ok` gates that. -/
  | notAByteProgram (idx value : Nat)
  /-- R4: a Rust panic, carrying its site. The direct bytecode indexes
      (QVM:2320-2322, 2518, 2539, 3009, 3038, 3046-3050), `read_u16` / `read_u32`
      (QVM:2817, 2823), the `panic!` for an unknown op in the general length
      function (QVM:3022) and the `unreachable!` of QVM:2255. -/
  | panic (site : String)
  deriving BEq

/-- Rust's `{n:#x}`: lower-case hex with a `0x` prefix and no padding. Reuses P-09b's
    renderer rather than writing a third one. -/
def validationHex : Nat -> String := qvmHex

/-- The Rust's `format!` output for each fault, verbatim: decimal for `{idx}`, `{slot}`,
    `{bucket}`, `{gap}`, `{depth}`, `{required}`, `{found}`, `{len}` and the bare `{}`, `#x` for `{op}`,
    `{token}`, `{flags}`, `{ptr}`, `{start}` and the rendered window list. -/
def QuotientValidationFault.message : QuotientValidationFault -> String
  | .unknownOpcode op idx =>
      s!"unknown quotient VM opcode {validationHex op} at byte {idx}"
  | .unknownOpcodeInStackValidator op idx =>
      s!"unknown quotient VM opcode {validationHex op} reached stack validator at byte {idx}"
  | .unknownMemToken token idx =>
      s!"unknown quotient VM memory token {validationHex token} at byte {idx}"
  | .truncated context idx need remaining =>
      s!"truncated quotient VM {context} at byte {idx}: need {need} byte(s), program has {remaining} byte(s) remaining"
  | .byteRangeOverflow context idx =>
      s!"quotient VM {context} length overflows at byte {idx}"
  | .zeroLengthDecoded name op idx =>
      s!"quotient VM opcode {name} ({validationHex op}) decoded to zero length at byte {idx}"
  | .zeroLengthRun idx => s!"zero-length quotient VM run at byte {idx}"
  | .affineSumZeroCounts idx =>
      s!"AFFINE_SUM at byte {idx} requires nonzero linear and product counts"
  | .modarith7UnknownFlags flags idx =>
      s!"MODARITH7 has unknown flag bits {validationHex flags} at byte {idx}"
  | .cursorOverflow op opIdx =>
      s!"quotient VM opcode {validationHex op} length overflows while decoding byte {opIdx}"
  | .lenMulOverflow op idx =>
      s!"quotient VM opcode {validationHex op} length multiplication overflows at byte {idx}"
  | .lenAddOverflow op idx =>
      s!"quotient VM opcode {validationHex op} length addition overflows at byte {idx}"
  | .stackLeak depth =>
      s!"quotient VM stack leak at end of program: {depth} value(s) remain"
  | .stackDepthOverflow idx => s!"quotient VM stack depth overflow at byte {idx}"
  | .stackUnderflow op idx required found =>
      s!"quotient VM stack underflow at byte {idx}: opcode {validationHex op} requires {required} stack value(s), found {found}"
  | .stackBoundary op idx found =>
      s!"quotient VM stack boundary error at byte {idx}: opcode {validationHex op} requires exactly 1 stack value, found {found}"
  | .nativeCallbackStack op idx found =>
      s!"quotient VM native callback at byte {idx}: opcode {validationHex op} requires an empty stack, found {found}"
  | .stackRegionExceeded maxStack stackWords =>
      s!"quotient VM stack depth {maxStack} exceeds the {stackWords}-word planned stack region"
  | .selectorBucketOutOfRange bucket idx num =>
      s!"quotient VM FOLD_SELECTOR bucket {bucket} at byte {idx} is outside the {num} simple-selector accumulator(s)"
  | .selectorGapTooLarge gap idx maxPower =>
      s!"quotient VM FOLD_SELECTOR gap {gap} at byte {idx} exceeds the largest precomputed y power {maxPower}"
  | .tokenHasNoBase token idx =>
      s!"quotient VM memory token {validationHex token} at byte {idx} has no generated base address in this layout"
  | .tokenOffsetOverflow idx => s!"quotient VM token offset overflows at byte {idx}"
  | .pointerMisaligned kind ptr idx =>
      s!"quotient VM {kind} pointer {validationHex ptr} at byte {idx} is not 32-byte aligned"
  | .pointerOutsideWindows kind ptr idx windows =>
      s!"quotient VM {kind} pointer {validationHex ptr} at byte {idx} is outside every window the verifier populates before the quotient VM runs ({windows})"
  | .constSlotOutOfRange wide slot idx constLen =>
      s!"quotient VM {if wide then "u16" else "u8"} const slot {slot} at byte {idx} is outside the {constLen}-entry constant table"
  | .walkerMissingArm op idx =>
      s!"quotient VM operand walker does not handle opcode {validationHex op} at byte {idx}; extend `visit_quotient_operands` so the new opcode's operands stay bounds-checked"
  | .notAByteProgram idx value =>
      s!"quotient VM program byte {value} at index {idx} is outside the u8 domain"
  | .panic site => site

/-- The result type of the whole cluster: the Rust's `Result<_, String>` with the
    string replaced by the closed taxonomy (hazard 4). -/
abbrev VResult (α : Type) : Type := Except QuotientValidationFault α

/-- R4: a Rust panic, made observable rather than reducing. -/
def vPanic {α : Type} (site : String) : VResult α := .error (QuotientValidationFault.panic site)

/-- The first position whose value is not a byte, if any. rust: nothing - the
    reference's `&[u8]` makes this unrepresentable, which is exactly why the port has to
    say it (R5). -/
def firstNonByte : List Nat -> Nat -> Option (Nat × Nat)
  | [], _ => none
  | b :: rest, idx => if b < 256 then firstNonByte rest (idx + 1) else some (idx, b)

/-- A program byte list is a faithful image of the Rust's `&[u8]` exactly when every
    element is below 256. -/
def isByteProgram (bytes : List Nat) : Bool := firstNonByte bytes 0 == none

/-- Refuse a non-byte program at a public entry point, before any index or operand
    arithmetic can turn an out-of-domain value into a plausible-looking number. -/
def requireByteProgram (bytes : List Nat) : VResult Unit :=
  match firstNonByte bytes 0 with
  | some (idx, value) => .error (QuotientValidationFault.notAByteProgram idx value)
  | none => .ok ()

/-- The site string of a direct bytecode index at the given Rust line. -/
def siteIndex (line : Nat) : String :=
  qvmValidatorPath ++ ":" ++ toString line ++ " (bytecode index out of range)"

/-- QVM:3022's `panic!("unknown quotient op {op:#x} at byte {idx}")`. -/
def siteUnknownQuotientOp (op idx : Nat) : String :=
  qvmValidatorPath ++ ":3022 (unknown quotient op " ++ validationHex op ++ " at byte "
    ++ toString idx ++ ")"

/-- QVM:2255's `unreachable!("not a memory operand")`. -/
def siteNotMemoryOperand : String := qvmValidatorPath ++ ":2255 (not a memory operand)"

/-- Left-to-right `for`-each in the result monad, aborting on the first error: R3's
    reading of the Rust's `for .. ` with `?` inside. Written out rather than using `List.forM`
    because the tree already avoids core helpers whose shape moves between
    releases (VmBuilder.lean:185-193 makes the same call for `foldLeftM`). -/
def forEachM {ε α : Type} (xs : List α) (f : α -> Except ε Unit) : Except ε Unit :=
  match xs with
  | [] => .ok ()
  | x :: rest => do
      f x
      forEachM rest f


/-! ## The model records (rust: QVM:2029-2096) - MOVED to the top -/

/-- rust: QVM:2030-2038 (`struct QuotientReadWindow`) @formal-baseline. "One byte
    range the compact quotient VM is allowed to load from." -/
structure QuotientReadWindow where
  /-- rust: QVM:2032-2033 (`name: &'static str`) - "Stable name used in validation
      errors." -/
  name : String
  /-- rust: QVM:2034-2035 (`start: usize`) - "Start byte offset in verifier memory." -/
  start : Nat
  /-- rust: QVM:2036-2037 (`len: usize`) - "Length in bytes. Zero-length windows
      never accept a pointer." -/
  len : Nat
  deriving BEq

/-- rust: QVM:2041-2046 (`QuotientReadWindow::contains_word`) @formal-baseline.
    "Whether a full 32-byte `mload` at `ptr` stays inside this window." R5: the two
    `saturating_add` calls cannot fire for any address the layout can name and `Nat`
    does not saturate at all, so the plain additions below are the same predicate. -/
def QuotientReadWindow.containsWord (window : QuotientReadWindow) (ptr : Nat) : Bool :=
  window.len != 0 && ptr >= window.start
    && ptr + wordBytes <= window.start + window.len

/-- rust: QVM:2053-2059 (`struct QuotientReadModel`) @formal-baseline. "Legal read
    set for one finalized quotient program. Built from the converged memory
    layout, so it describes the addresses this concrete verifier actually
    populates before the VM runs." HAZARD 2: this is the DEPLOYED layout, not the
    certifier's PRNG memory. -/
structure QuotientReadModel where
  /-- rust: QVM:2055-2056 (`windows: Vec<QuotientReadWindow>`) - "Ranges the VM may
      load from." -/
  windows : List QuotientReadWindow
  /-- rust: QVM:2057-2058 (`token_bases: Vec<(u8, usize)>`) - "Resolved base address
      for each symbolic memory token." -/
  tokenBases : List (Nat × Nat)
  deriving BEq

/-- The `#[derive(Default)]` of QVM:2053: two empty vectors. -/
def quotientReadModelDefault : QuotientReadModel := ⟨[], []⟩

/-- rust: QVM:2062-2067 (`QuotientReadModel::token_base`) @formal-baseline. "Resolve
    a symbolic memory token to its generated base address." `iter().find_map` is
    first match in list order, which is `find?`. -/
def QuotientReadModel.tokenBase (model : QuotientReadModel) (token : Nat) : Option Nat :=
  (model.tokenBases.find? fun (candidate, _) => candidate == token).map Prod.snd

/-- rust: QVM:2069-2075 (`QuotientReadModel::window_for`) @formal-baseline. "Name
    the window covering a word-sized load, if any." -/
def QuotientReadModel.windowFor (model : QuotientReadModel) (ptr : Nat) : Option String :=
  (model.windows.find? fun window => window.containsWord ptr).map (fun w => w.name)

/-- rust: QVM:2084-2096 (`struct QuotientOperandModel`) @formal-baseline. "Everything
    a finalized program's operand fields are checked against. The runtime
    structural checks rendered into the interpreter take their table size,
    selector count and stack bounds from the same model, so the build-time and
    runtime layers cannot drift apart." That shared-source property is PL:507-513
    and is why this is a plain record rather than a typeclass (R9). -/
structure QuotientOperandModel where
  /-- rust: QVM:2086-2087 (`read: QuotientReadModel`) - "Memory windows the VM may
      load from." -/
  read : QuotientReadModel
  /-- rust: QVM:2088-2089 (`num_consts: usize`) - "Number of Fr words in the
      generated constant table." -/
  numConsts : Nat
  /-- rust: QVM:2090-2091 (`num_selector_buckets: usize`) - "Number of
      simple-selector accumulator buckets (`SELECTOR_ACC` words)." -/
  numSelectorBuckets : Nat
  /-- rust: QVM:2092-2093 (`selector_max_power: usize`) - "Largest precomputed
      `y^k` power a `FOLD_SELECTOR` gap may address." -/
  selectorMaxPower : Nat
  /-- rust: QVM:2094-2095 (`stack_words: usize`) - "Words in the registered
      quotient stack / callback scratch region." -/
  stackWords : Nat
  deriving BEq

/-- The `#[derive(Default)]` of QVM:2084: the default read model and four zeros. -/
def quotientOperandModelDefault : QuotientOperandModel :=
  { read := quotientReadModelDefault, numConsts := 0, numSelectorBuckets := 0,
    selectorMaxPower := 0, stackWords := 0 }

/-- rust: QVM:2099-2126 (`enum QuotientOperand`) @formal-baseline. "One operand
    field decoded from a finalized quotient program." R2: `.Const` becomes `.konst`
    (see the header). -/
inductive QuotientOperand
  /-- rust: QVM:2102-2107 (`Mem { kind, ptr }`) - "Absolute word address loaded by
      one `mload`." -/
  | mem (kind : String) (ptr : Nat)
  /-- rust: QVM:2109-2114 (`Token { token, offset }`) - "Symbolic memory token plus
      byte offset, resolved through the layout." `offset` is `0` for `PUSH_MEM_TOKEN`. -/
  | token (token : Nat) (offset : Nat)
  /-- rust: QVM:2116-2121 (`Const { slot, wide }`) - "Constant-table slot." `wide`
      records whether the slot was encoded as a `u16` (otherwise `u8`), which is the
      word the error message interpolates. -/
  | konst (slot : Nat) (wide : Bool)
  /-- rust: QVM:2123 (`SelectorBucket(usize)`) - "`FOLD_SELECTOR` bucket index." -/
  | selectorBucket (bucket : Nat)
  /-- rust: QVM:2125 (`SelectorGap(usize)`) - "`FOLD_SELECTOR` y-power gap." -/
  | selectorGap (gap : Nat)
  deriving BEq

/-! ## Readers and checked arithmetic (rust: QVM:2768-2824) - MOVED up -/

/-- The Rust's direct bytecode index `bytes[i]` (QVM:2320, 2518, 2539, 3009, 3038,
    3046-3050), which PANICS out of range (R4). `line` selects the site string so
    each call names its own Rust line. -/
def byteAtPanic (bytes : List Nat) (idx : Nat) (line : Nat) : VResult Nat :=
  match bytes.drop idx with
  | b :: _ => .ok b
  | [] => vPanic (siteIndex line)

/-- rust: QVM:2816-2819 (`read_u16`) @formal-baseline. "Read a big-endian `u16`
    operand from bytecode." The Rust's `bytes[idx..idx+2].try_into().expect(..)`
    PANICS; this is NOT the interpreter's bounds-checked `Midfall.Generator.readU16`
    (QVR:517), which returns `Err`. Hazard 5 of P-09b made the same distinction the
    other way round; the two must not be conflated. -/
def readU16 (bytes : List Nat) (idx : Nat) : VResult Nat :=
  match bytes.drop idx with
  | b0 :: b1 :: _ => .ok (b0 * 256 + b1)
  | _ => vPanic (qvmValidatorPath ++ ":2817 (u16 quotient operand)")

/-- rust: QVM:2821-2824 (`read_u32`) @formal-baseline. "Read a big-endian `u32`
    operand from bytecode." Same panic class. -/
def readU32 (bytes : List Nat) (idx : Nat) : VResult Nat :=
  match bytes.drop idx with
  | b0 :: b1 :: b2 :: b3 :: _ => .ok (((b0 * 256 + b1) * 256 + b2) * 256 + b3)
  | _ => vPanic (qvmValidatorPath ++ ":2823 (u32 quotient operand)")

/-- rust: QVM:2768-2785 (`require_quotient_bytes`) @formal-baseline. "Check that an
    instruction operand range fits inside the bytecode." R5: `checked_add` cannot
    fail on `Nat`, so the overflow arm is written as the wrap test it models rather
    than dropped - the string stays in the taxonomy (hazard 4). -/
def requireQuotientBytes (bytes : List Nat) (idx len : Nat) (context : String) :
    VResult Unit :=
  let end_ := idx + len
  if end_ < idx then .error (QuotientValidationFault.byteRangeOverflow context idx)
  else if end_ > bytes.length then
    .error (QuotientValidationFault.truncated context idx len (bytes.length - idx))
  else .ok ()

/-- rust: QVM:2787-2800 (`advance_quotient_cursor`) @formal-baseline. "Advance a
    dynamic-instruction cursor after bounds-checking the range." The Rust mutates
    `&mut cursor`; this returns the new cursor (R3). -/
def advanceQuotientCursor (bytes : List Nat) (cursor amount op opIdx : Nat) :
    VResult Nat := do
  requireQuotientBytes bytes cursor amount "dynamic instruction operand"
  let next := cursor + amount
  if next < cursor then .error (QuotientValidationFault.cursorOverflow op opIdx)
  else .ok next

/-- rust: QVM:2802-2807 (`checked_quotient_len_mul`) @formal-baseline. "Checked
    multiplication for derived instruction lengths." -/
def checkedQuotientLenMul (lhs rhs op idx : Nat) : VResult Nat :=
  let product := lhs * rhs
  if lhs != 0 && product / lhs != rhs then
    .error (QuotientValidationFault.lenMulOverflow op idx)
  else .ok product

/-- rust: QVM:2809-2814 (`checked_quotient_len_add`) @formal-baseline. "Checked
    addition for derived instruction lengths." -/
def checkedQuotientLenAdd (lhs rhs op idx : Nat) : VResult Nat :=
  let sum := lhs + rhs
  if sum < lhs then .error (QuotientValidationFault.lenAddOverflow op idx)
  else .ok sum

/-- The MODARITH7 flag mask the Rust writes as `!(Q_MODARITH7_FLAG_COND |
    Q_MODARITH7_FLAG_CONST)`. On a `u8` that is `0xfc`; in `Nat` the complement is
    infinite-width, so the mask has to be written out (R5, hazard 5). -/
def modarith7FlagMask : Nat := 0xfc

/-! ## The general opcode-length walker (rust: QVM:3004-3090) - MOVED up -/

/-- rust: QVM:3026-3033 (`quotient_affine_sum_op_len`) @formal-baseline. "Decode
    `AFFINE_SUM` length in trusted/internal bytecode walks." The GENERAL form: no
    bounds checks, so every read is the panic class. The Rust indexes the product
    count at `idx + 3` literally, which is `idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES`. -/
def quotientAffineSumOpLen (bytes : List Nat) (idx : Nat) : VResult Nat := do
  let linCount ← readU16 bytes (idx + 1)
  let productCount ← readU16 bytes (idx + 3)
  .ok (1 + 2 * quotientVmByteU16Bytes
        + linCount * (quotientVmByteU16Bytes + 1)
        + productCount * (2 * quotientVmByteU16Bytes + 1))

/-- rust: QVM:3035-3059 (`quotient_modarith7_op_len`) @formal-baseline. "Decode
    `MODARITH7` length in trusted/internal bytecode walks." Note what the general
    form does NOT do: it never checks the flag bits (the checked decoder does),
    which is exactly why the two walks can disagree on a program phase 1 refuses -
    pinned by `twoPhase_checkedAndUncheckedWalksAgree_ok`. -/
def quotientModarith7OpLen (bytes : List Nat) (idx : Nat) : VResult Nat := do
  let flags ← byteAtPanic bytes (idx + 1) 3038
  let afterFlags := idx + 2
  let afterCond :=
    if flags &&& qModarith7FlagCond != 0 then afterFlags + quotientVmByteU16Bytes else afterFlags
  let afterConst := if flags &&& qModarith7FlagConst != 0 then afterCond + 1 else afterCond
  let linCount ← byteAtPanic bytes afterConst 3046
  let rowCount ← byteAtPanic bytes (afterConst + 1) 3047
  let pairwiseCount ← byteAtPanic bytes (afterConst + 2) 3048
  let memCount ← byteAtPanic bytes (afterConst + 3) 3049
  let productCount ← byteAtPanic bytes (afterConst + 4) 3050
  let cursor := afterConst + 5
  let cursor := cursor + linCount * quotientVmLimbs * (1 + quotientVmByteU16Bytes)
  let cursor := cursor
    + rowCount * (quotientVmByteU16Bytes + quotientVmLimbs * (1 + quotientVmByteU16Bytes))
  let cursor := cursor
    + pairwiseCount * (2 * quotientVmByteU16Bytes + quotientVmPairwiseCoeffs)
  let cursor := cursor + memCount * (1 + quotientVmByteU16Bytes)
  .ok (cursor + productCount * (1 + 2 * quotientVmByteU16Bytes) - idx)

/-- rust: QVM:3004-3024 (`quotient_op_len`) @formal-baseline. "Byte length of the
    opcode at `idx`. Fixed-width opcodes are read from the spec table; byte-only run
    and MODARITH7 opcodes decode their embedded counts." THE GENERAL FORM, which
    P-09c's header promised would absorb VmBuilder's compaction-scoped copy
    (hazard 3). An opcode with no table entry is the Rust's `panic!` (QVM:3022). -/
def quotientOpLen (bytes : List Nat) (idx : Nat) : VResult Nat := do
  let op ← byteAtPanic bytes idx 3009
  if op == qOpRunAddMulMemMemConstU8 then do
    let n ← readU16 bytes (idx + 1)
    .ok (1 + quotientVmByteU16Bytes + n * (2 * quotientVmByteU16Bytes + 1))
  else if op == qOpRunAddMulConstU8MemU16 then do
    let n ← readU16 bytes (idx + 1)
    .ok (1 + quotientVmByteU16Bytes + n * (quotientVmByteU16Bytes + 1))
  else if op == qOpAffineSum then
    quotientAffineSumOpLen bytes idx
  else if op == qOpModarith7 then
    quotientModarith7OpLen bytes idx
  else
    match quotientOpcodeByteLen op with
    | some len => .ok len
    | none => vPanic (siteUnknownQuotientOp op idx)

/-- One `(offset, opcode, byte_len)` triple: the `Item` of QVM:3071-3074. -/
abbrev QuotientBytecodeOp : Type := Nat × Nat × Nat

/-- rust: QVM:3061-3090 (`quotient_bytecode_ops` and `QuotientBytecodeOps`)
    @formal-baseline. "Iterate over decoded byte-oriented quotient instructions.
    This is intentionally lightweight: safety validation still lives in
    `validate_quotient_program`, while codegen-side metrics can share the same offset
    walk instead of open-coding counters." The Rust is a lazy iterator whose `next`
    panics inside `quotient_op_len`; this is the eager list of the same triples in the
    same order, carrying the panic class instead of running off the end. R10: fuel
    is `bytes.length`, sound because an accepted instruction has length at least 1 -
    the checked decoder enforces that (QVM:2528-2533) and the general one cannot
    return 0 for a table opcode. -/
def quotientBytecodeOpsGo (bytes : List Nat) :
    Nat → Nat → List QuotientBytecodeOp → VResult (List QuotientBytecodeOp)
  | 0, idx, acc =>
      if idx < bytes.length then vPanic (siteIndex 3082) else .ok acc.reverse
  | fuel + 1, idx, acc =>
      if idx < bytes.length then do
        let op ← byteAtPanic bytes idx 3084
        let len ← quotientOpLen bytes idx
        quotientBytecodeOpsGo bytes fuel (idx + len) ((idx, op, len) :: acc)
      else
        .ok acc.reverse
termination_by fuel => fuel

/-- rust: QVM:3066-3068 (`quotient_bytecode_ops`), the entry point, guarded for the
    same byte-domain reason. -/
def quotientBytecodeOps (bytes : List Nat) : VResult (List QuotientBytecodeOp) := do
  requireByteProgram bytes
  quotientBytecodeOpsGo bytes bytes.length 0 []

/-! ## Phase 1: the structural validator (rust: QVM:2004-2027, 2508-2766) -/

/-- rust: QVM:2757-2766 (`validate_quotient_mem_token`) @formal-baseline. "Reject
    symbolic memory tokens unknown to this VM version." The set is
    `QUOTIENT_VM_SPEC.mem_tokens` - the nine `Q_MEM_*` tokens - so a token can be known
    HERE and still have no base in `read.token_base` (QVM:2243): the two tables are
    different and the two faults are different. -/
def validateQuotientMemToken (token idx : Nat) : VResult Unit :=
  if quotientVmSpec.memTokens.any fun spec => spec.token == token then .ok ()
  else .error (QuotientValidationFault.unknownMemToken token idx)

/-- rust: QVM:2742-2755 (`require_quotient_stack_depth`) @formal-baseline. "Require
    at least `required` stack values before consuming operands." -/
def requireQuotientStackDepth (op idx depth required : Nat) : VResult Unit :=
  if depth < required then
    .error (QuotientValidationFault.stackUnderflow op idx required depth)
  else .ok ()

/-- rust: QVM:2675-2740 (`apply_quotient_stack_effect`) @formal-baseline. "Apply one
    opcode's static stack effect during offline validation." The Rust mutates
    `depth` and `max_stack`; this returns the pair (R3). The two boundary arms are the
    ones hazard 1 cares about: FOLD_* needs EXACTLY 1 and the native markers need
    EXACTLY 0, which is what makes a program that decodes cleanly still
    structurally invalid. -/
def applyQuotientStackEffect (op idx depth maxStack : Nat) : VResult (Nat × Nat) :=
  if op == qOpPushConst || op == qOpPushMemLiteral || op == qOpPushMemToken
    || op == qOpPushMemTokenOffset || op == qOpPushMemU16 || op == qOpPushConstU8
    || op == qOpLin7 || op == qOpBilin7Row || op == qOpBilin7Pairwise
    || op == qOpModarith7 then
    let depth' := depth + 1
    if depth' < depth then .error (QuotientValidationFault.stackDepthOverflow idx)
    else .ok (depth', Nat.max maxStack depth')
  else if op == qOpAdd || op == qOpMul then do
    requireQuotientStackDepth op idx depth 2
    .ok (depth - 1, maxStack)
  else if op == qOpNeg || op == qOpAddConstU8 || op == qOpMulConstU8
    || op == qOpAddConst || op == qOpMulConst || op == qOpAddMemU16
    || op == qOpMulMemU16 || op == qOpAddMulMemMemConstU8
    || op == qOpAddMulConstU8MemU16 || op == qOpAddMulMemMem
    || op == qOpRunAddMulMemMemConstU8 || op == qOpRunAddMulConstU8MemU16
    || op == qOpAffineSum || op == qOpPow5 then do
    requireQuotientStackDepth op idx depth 1
    .ok (depth, maxStack)
  else if op == qOpFoldMain || op == qOpFoldSelector then
    if depth != 1 then .error (QuotientValidationFault.stackBoundary op idx depth)
    else .ok (0, maxStack)
  else if op == qOpNativePermutation || op == qOpNativeLookup
    || op == qOpNativeIdentity then
    if depth != 0 then .error (QuotientValidationFault.nativeCallbackStack op idx depth)
    else .ok (depth, maxStack)
  else
    .error (QuotientValidationFault.unknownOpcodeInStackValidator op idx)

/-- rust: QVM:2570-2591 (`quotient_affine_sum_op_len_checked`) @formal-baseline.
    "Decode the dynamic `AFFINE_SUM` payload header and byte length." -/
def quotientAffineSumOpLenChecked (bytes : List Nat) (idx : Nat) : VResult Nat := do
  let op := qOpAffineSum
  requireQuotientBytes bytes idx (1 + 2 * quotientVmByteU16Bytes) "AFFINE_SUM count header"
  let linCount ← readU16 bytes (idx + 1)
  let productCount ← readU16 bytes (idx + 1 + quotientVmByteU16Bytes)
  if linCount == 0 || productCount == 0 then
    .error (QuotientValidationFault.affineSumZeroCounts idx)
  else .ok ()
  let linPayload ← checkedQuotientLenMul linCount (quotientVmByteU16Bytes + 1) op idx
  let productPayload ←
    checkedQuotientLenMul productCount (2 * quotientVmByteU16Bytes + 1) op idx
  let payload ← checkedQuotientLenAdd linPayload productPayload op idx
  checkedQuotientLenAdd (1 + 2 * quotientVmByteU16Bytes) payload op idx

/-- rust: QVM:2593-2673 (`quotient_modarith7_op_len_checked`) @formal-baseline.
    "Decode the dynamic `MODARITH7` payload and byte length." Every block advance
    goes through `advance_quotient_cursor`, so the five counted blocks are
    bounds-checked before the walker is ever allowed to look at them - the exact
    guarantee hazard 1 rests on. -/
def quotientModarith7OpLenChecked (bytes : List Nat) (idx : Nat) : VResult Nat := do
  let op := qOpModarith7
  let c1 ← advanceQuotientCursor bytes idx 1 op idx
  requireQuotientBytes bytes c1 1 "MODARITH7 flags"
  let flags ← byteAtPanic bytes c1 2599
  if flags &&& modarith7FlagMask != 0 then
    .error (QuotientValidationFault.modarith7UnknownFlags flags idx)
  else .ok ()
  let c2 ← advanceQuotientCursor bytes c1 1 op idx
  let c3 ←
    if flags &&& qModarith7FlagCond != 0 then
      advanceQuotientCursor bytes c2 quotientVmByteU16Bytes op idx
    else .ok c2
  let c4 ←
    if flags &&& qModarith7FlagConst != 0 then advanceQuotientCursor bytes c3 1 op idx
    else .ok c3
  requireQuotientBytes bytes c4 5 "MODARITH7 count header"
  let linCount ← byteAtPanic bytes c4 2614
  let rowCount ← byteAtPanic bytes (c4 + 1) 2615
  let pairwiseCount ← byteAtPanic bytes (c4 + 2) 2616
  let memCount ← byteAtPanic bytes (c4 + 3) 2617
  let productCount ← byteAtPanic bytes (c4 + 4) 2618
  let c5 ← advanceQuotientCursor bytes c4 5 op idx
  let linAmount ← checkedQuotientLenMul linCount
    (quotientVmLimbs * (1 + quotientVmByteU16Bytes)) op idx
  let c6 ← advanceQuotientCursor bytes c5 linAmount op idx
  let rowAmount ← checkedQuotientLenMul rowCount
    (quotientVmByteU16Bytes + quotientVmLimbs * (1 + quotientVmByteU16Bytes)) op idx
  let c7 ← advanceQuotientCursor bytes c6 rowAmount op idx
  let pwAmount ← checkedQuotientLenMul pairwiseCount
    (2 * quotientVmByteU16Bytes + quotientVmPairwiseCoeffs) op idx
  let c8 ← advanceQuotientCursor bytes c7 pwAmount op idx
  let memAmount ← checkedQuotientLenMul memCount (1 + quotientVmByteU16Bytes) op idx
  let c9 ← advanceQuotientCursor bytes c8 memAmount op idx
  let productAmount ← checkedQuotientLenMul productCount (1 + 2 * quotientVmByteU16Bytes) op idx
  let c10 ← advanceQuotientCursor bytes c9 productAmount op idx
  .ok (c10 - idx)

/-- rust: QVM:2536-2568 (`quotient_byte_instruction_len_checked`) @formal-baseline.
    "Return one instruction length while checking dynamic operand bounds." The
    four dynamic arms are where a malformed program is refused before any operand
    is read; the trailing `require_quotient_bytes(.., "instruction")` is what makes
    the whole instruction span fit, and therefore what hazard 1 rests on. -/
def quotientByteInstructionLenChecked (bytes : List Nat) (idx : Nat) : VResult Nat := do
  let op ← byteAtPanic bytes idx 2539
  let len ←
    if op == qOpRunAddMulMemMemConstU8 then do
      requireQuotientBytes bytes idx (1 + quotientVmByteU16Bytes) "run count"
      let count ← readU16 bytes (idx + 1)
      if count == 0 then .error (QuotientValidationFault.zeroLengthRun idx) else .ok ()
      let payloadLen ← checkedQuotientLenMul count (2 * quotientVmByteU16Bytes + 1) op idx
      checkedQuotientLenAdd (1 + quotientVmByteU16Bytes) payloadLen op idx
    else if op == qOpRunAddMulConstU8MemU16 then do
      requireQuotientBytes bytes idx (1 + quotientVmByteU16Bytes) "run count"
      let count ← readU16 bytes (idx + 1)
      if count == 0 then .error (QuotientValidationFault.zeroLengthRun idx) else .ok ()
      let payloadLen ← checkedQuotientLenMul count (quotientVmByteU16Bytes + 1) op idx
      checkedQuotientLenAdd (1 + quotientVmByteU16Bytes) payloadLen op idx
    else if op == qOpAffineSum then
      quotientAffineSumOpLenChecked bytes idx
    else if op == qOpModarith7 then
      quotientModarith7OpLenChecked bytes idx
    else
      match quotientOpcodeByteLen op with
      | some len => .ok len
      | none => .error (QuotientValidationFault.unknownOpcode op idx)
  requireQuotientBytes bytes idx len "instruction"
  .ok len

/-- rust: QVM:2508-2535 (`decode_byte_quotient_instruction`) @formal-baseline.
    "Decode one instruction and validate token operands." The order matters and is
    preserved: the length is computed and bounds-checked BEFORE the token byte is
    indexed at `idx + 1`, which is what makes that index safe. -/
def decodeByteQuotientInstruction (bytes : List Nat) (idx : Nat) :
    VResult (Nat × Nat) := do
  requireQuotientBytes bytes idx 1 "opcode"
  let op ← byteAtPanic bytes idx 2511
  let spec ← match quotientOpcodeSpec op with
    | some spec => .ok spec
    | none => .error (QuotientValidationFault.unknownOpcode op idx)
  let len ← quotientByteInstructionLenChecked bytes idx
  if op == qOpPushMemToken || op == qOpPushMemTokenOffset then do
    let token ← byteAtPanic bytes (idx + 1) 2518
    validateQuotientMemToken token idx
  else .ok ()
  if len == 0 then
    .error (QuotientValidationFault.zeroLengthDecoded spec.name op idx)
  else .ok ()
  .ok (op, len)

/-- The Rust's post-loop tail of `validate_quotient_program` (QVM:2020-2026): a
    program that ends with a live stack value leaks. Split out so the fuel arm and
    the normal exit share it. -/
def quotientProgramFinishCheck (depth maxStack : Nat) : VResult Nat :=
  if depth != 0 then .error (QuotientValidationFault.stackLeak depth) else .ok maxStack

/-- rust: QVM:2004-2027 (`validate_quotient_program`) @formal-baseline. "Decode a
    finalized byte-oriented quotient program and verify stack safety. This is an
    offline safety check for the VK-pinned program, not a runtime verifier feature.
    The Yul VM stays lean and assumes codegen emitted a valid stream; this pass
    proves that assumption before the program is embedded." Returns the stack
    high-water mark, which phase 2 compares against `model.stack_words` and which
    QVM:1219-1222 asserts against the builder's own accounting. -/
def validateQuotientProgramGo (bytes : List Nat) :
    Nat → Nat → Nat → Nat → VResult Nat
  | 0, idx, depth, maxStack =>
      if idx < bytes.length then vPanic (siteIndex 2014)
      else quotientProgramFinishCheck depth maxStack
  | fuel + 1, idx, depth, maxStack =>
      if idx >= bytes.length then
        quotientProgramFinishCheck depth maxStack
      else do
        let (op, len) ← decodeByteQuotientInstruction bytes idx
        let (depth', maxStack') ← applyQuotientStackEffect op idx depth maxStack
        validateQuotientProgramGo bytes fuel (idx + len) depth' maxStack'
termination_by fuel => fuel

/-- rust: QVM:2009 (`validate_quotient_program`), the entry point. The byte-domain
    guard is the port's own (see `notAByteProgram`); everything past it is the Rust. -/
def validateQuotientProgram (bytes : List Nat) : VResult Nat := do
  requireByteProgram bytes
  validateQuotientProgramGo bytes bytes.length 0 0 0


/-! ## Phase 2: the operand walker and the value checks (rust: QVM:2160-2506) -/

/-- The stride of one seven-limb term: `u8 const_slot, u16 ptr`. rust: the
    `k * (1 + QUOTIENT_VM_BYTE_U16_BYTES)` inside QVM:2328. -/
def limbTermStride : Nat := 1 + quotientVmByteU16Bytes

/-- The LIN7 block stride `QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES)`
    (QVM:2470). -/
def limbBlockStride : Nat := quotientVmLimbs * limbTermStride

/-- The BILIN7_ROW block stride: one `u16` row pointer then the seven terms
    (QVM:2475-2480). -/
def rowBlockStride : Nat := quotientVmByteU16Bytes + limbBlockStride

/-- The BILIN7_PAIRWISE block stride: two `u16` bases then 13 coefficient slots
    (QVM:2481-2484). -/
def pairwiseBlockStride : Nat :=
  2 * quotientVmByteU16Bytes + quotientVmPairwiseCoeffs

/-- rust: QVM:2326-2333, the `limb_terms` closure of `visit_quotient_operands`.
    "Seven `{u8 const_slot, u16 ptr}` limb terms (LIN7 / BILIN7_ROW rows)." -/
def limbTerms (bytes : List Nat) (base : Nat) : VResult (List QuotientOperand) :=
  foldRangeIdxM quotientVmLimbs [] fun k acc => do
    let term := base + k * limbTermStride
    let slot ← byteAtPanic bytes term 2329
    let ptr ← readU16 bytes (term + 1)
    .ok (acc ++ [QuotientOperand.konst slot false, QuotientOperand.mem "limb" ptr])

/-- rust: QVM:2334-2350, the `pairwise_block` closure. "BILIN7_PAIRWISE block at
    `base`: `u16 lhs_base, u16 rhs_base, 13 u8 const slots`. Both bases are indexed
    `base + i * 0x20` for seven limbs, so the whole span has to be in range, not just
    the base word." The pointer arithmetic is on WORD addresses, not byte offsets,
    so it cannot panic; the 13 slot reads can. -/
def pairwiseBlock (bytes : List Nat) (base : Nat) : VResult (List QuotientOperand) := do
  let lhs ← readU16 bytes base
  let rhs ← readU16 bytes (base + quotientVmByteU16Bytes)
  let words ← foldRangeIdxM (ε := QuotientValidationFault) (α := List QuotientOperand)
    quotientVmLimbs [] fun k acc =>
      .ok (acc ++ [QuotientOperand.mem "pairwise_lhs" (lhs + k * wordBytes),
                   QuotientOperand.mem "pairwise_rhs" (rhs + k * wordBytes)])
  let coeffs := base + 2 * quotientVmByteU16Bytes
  let slots ← foldRangeIdxM quotientVmPairwiseCoeffs [] fun k acc => do
    let slot ← byteAtPanic bytes (coeffs + k) 2347
    .ok (acc ++ [QuotientOperand.konst slot false])
  .ok (words ++ slots)

/-- rust: QVM:2314-2506 (`visit_quotient_operands`) @formal-baseline. "Visit every
    operand field one instruction carries. This is the single operand walker for
    the build-time value checks; it mirrors the interpreter's decode of each case
    arm byte for byte. The fallback arm is an error rather than a no-op: a new
    opcode that forgets to extend this walker fails generation instead of silently
    losing its checks."

    R3: the Rust threads a `&mut dyn FnMut`; this returns the operands in the order
    the callback would have received them (see the header). Every read below is the
    panic class, because every `u8_at` / `u16_at` / `u32_at` in the Rust is a direct
    index - which is precisely what phase 1 exists to make safe. -/
def visitQuotientOperands (bytes : List Nat) (idx op : Nat) :
    VResult (List QuotientOperand) := do
  if op == qOpAdd || op == qOpMul || op == qOpNeg || op == qOpPow5
    || op == qOpFoldMain || op == qOpNativePermutation || op == qOpNativeLookup
    || op == qOpNativeIdentity then
    -- QVM:2352-2363: "No operand fields. NATIVE_IDENTITY's callback index is
    -- checked by QuotientProgramPlan::validate_execution_manifest and reverts in
    -- the interpreter's default arm." HAZARD 6's reported gap.
    .ok []
  else if op == qOpPushConst || op == qOpAddConst || op == qOpMulConst then do
    let slot ← readU16 bytes (idx + 1)
    .ok [QuotientOperand.konst slot true]
  else if op == qOpPushConstU8 || op == qOpAddConstU8 || op == qOpMulConstU8 then do
    let slot ← byteAtPanic bytes (idx + 1) 2369
    .ok [QuotientOperand.konst slot false]
  else if op == qOpPushMemLiteral then do
    let ptr ← readU32 bytes (idx + 1)
    .ok [QuotientOperand.mem "literal" ptr]
  else if op == qOpPushMemU16 || op == qOpAddMemU16 || op == qOpMulMemU16 then do
    let ptr ← readU16 bytes (idx + 1)
    .ok [QuotientOperand.mem "u16" ptr]
  else if op == qOpPushMemToken then do
    let token ← byteAtPanic bytes (idx + 1) 2376
    .ok [QuotientOperand.token token 0]
  else if op == qOpPushMemTokenOffset then do
    let token ← byteAtPanic bytes (idx + 1) 2377
    let offset ← readU32 bytes (idx + 2)
    .ok [QuotientOperand.token token offset]
  else if op == qOpFoldSelector then do
    let bucket ← byteAtPanic bytes (idx + 1) 2385
    let gap ← readU16 bytes (idx + 2)
    .ok [QuotientOperand.selectorBucket bucket, QuotientOperand.selectorGap gap]
  else if op == qOpAddMulMemMemConstU8 then do
    let lhs ← readU16 bytes (idx + 1)
    let rhs ← readU16 bytes (idx + 3)
    let slot ← byteAtPanic bytes (idx + 5) 2393
    .ok [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
         QuotientOperand.konst slot false]
  else if op == qOpAddMulConstU8MemU16 then do
    let ptr ← readU16 bytes (idx + 1)
    let slot ← byteAtPanic bytes (idx + 3) 2398
    .ok [QuotientOperand.mem "u16" ptr, QuotientOperand.konst slot false]
  else if op == qOpAddMulMemMem then do
    let lhs ← readU16 bytes (idx + 1)
    let rhs ← readU16 bytes (idx + 3)
    .ok [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs]
  else if op == qOpRunAddMulMemMemConstU8 then do
    let count ← readU16 bytes (idx + 1)
    let base := idx + 1 + quotientVmByteU16Bytes
    let stride := 2 * quotientVmByteU16Bytes + 1
    foldRangeIdxM count [] fun k acc => do
      let item := base + k * stride
      let lhs ← readU16 bytes item
      let rhs ← readU16 bytes (item + quotientVmByteU16Bytes)
      let slot ← byteAtPanic bytes (item + 2 * quotientVmByteU16Bytes) 2413
      .ok (acc ++ [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
                   QuotientOperand.konst slot false])
  else if op == qOpRunAddMulConstU8MemU16 then do
    let count ← readU16 bytes (idx + 1)
    let base := idx + 1 + quotientVmByteU16Bytes
    let stride := quotientVmByteU16Bytes + 1
    foldRangeIdxM count [] fun k acc => do
      let item := base + k * stride
      let ptr ← readU16 bytes item
      let slot ← byteAtPanic bytes (item + quotientVmByteU16Bytes) 2424
      .ok (acc ++ [QuotientOperand.mem "u16" ptr, QuotientOperand.konst slot false])
  else if op == qOpAffineSum then do
    let linCount ← readU16 bytes (idx + 1)
    let productCount ← readU16 bytes (idx + 1 + quotientVmByteU16Bytes)
    let linBase := idx + 1 + 2 * quotientVmByteU16Bytes
    let linOps ← foldRangeIdxM linCount [] fun k acc => do
      let cursor := linBase + k * (quotientVmByteU16Bytes + 1)
      let ptr ← readU16 bytes cursor
      let slot ← byteAtPanic bytes (cursor + quotientVmByteU16Bytes) 2434
      .ok (acc ++ [QuotientOperand.mem "u16" ptr, QuotientOperand.konst slot false])
    let productBase := linBase + linCount * (quotientVmByteU16Bytes + 1)
    let productOps ← foldRangeIdxM productCount [] fun k acc => do
      let cursor := productBase + k * (2 * quotientVmByteU16Bytes + 1)
      let lhs ← readU16 bytes cursor
      let rhs ← readU16 bytes (cursor + quotientVmByteU16Bytes)
      let slot ← byteAtPanic bytes (cursor + 2 * quotientVmByteU16Bytes) 2440
      .ok (acc ++ [QuotientOperand.mem "u16" lhs, QuotientOperand.mem "u16" rhs,
                   QuotientOperand.konst slot false])
    .ok (linOps ++ productOps)
  else if op == qOpLin7 then
    limbTerms bytes (idx + 1)
  else if op == qOpBilin7Row then do
    let lhs ← readU16 bytes (idx + 1)
    let terms ← limbTerms bytes (idx + 1 + quotientVmByteU16Bytes)
    .ok (QuotientOperand.mem "row_lhs" lhs :: terms)
  else if op == qOpBilin7Pairwise then
    pairwiseBlock bytes (idx + 1)
  else if op == qOpModarith7 then do
    let cursor := idx + 1
    let flags ← byteAtPanic bytes cursor 2454
    let c1 := cursor + 1
    let condStep ←
      if flags &&& qModarith7FlagCond != 0 then do
        let ptr ← readU16 bytes c1
        .ok ([QuotientOperand.mem "modarith_cond" ptr],
             c1 + quotientVmByteU16Bytes)
      else .ok ([], c1)
    let constStep ←
      if flags &&& qModarith7FlagConst != 0 then do
        let slot ← byteAtPanic bytes condStep.2 2461
        .ok (condStep.1 ++ [QuotientOperand.konst slot false], condStep.2 + 1)
      else .ok (condStep.1, condStep.2)
    let c2 := constStep.2
    let linCount ← byteAtPanic bytes c2 2464
    let rowCount ← byteAtPanic bytes (c2 + 1) 2465
    let pairwiseCount ← byteAtPanic bytes (c2 + 2) 2466
    let memCount ← byteAtPanic bytes (c2 + 3) 2467
    let productCount ← byteAtPanic bytes (c2 + 4) 2468
    let c3 := c2 + 5
    let linOps ← foldRangeIdxM linCount [] fun k acc => do
      let terms ← limbTerms bytes (c3 + k * limbBlockStride)
      .ok (acc ++ terms)
    let rowBase := c3 + linCount * limbBlockStride
    let rowOps ← foldRangeIdxM rowCount [] fun k acc => do
      let base := rowBase + k * rowBlockStride
      let lhs ← readU16 bytes base
      let terms ← limbTerms bytes (base + quotientVmByteU16Bytes)
      .ok (acc ++ [QuotientOperand.mem "row_lhs" lhs] ++ terms)
    let pwBase := rowBase + rowCount * rowBlockStride
    let pwOps ← foldRangeIdxM pairwiseCount [] fun k acc => do
      let block ← pairwiseBlock bytes (pwBase + k * pairwiseBlockStride)
      .ok (acc ++ block)
    let memBase := pwBase + pairwiseCount * pairwiseBlockStride
    let memOps ← foldRangeIdxM memCount [] fun k acc => do
      let base := memBase + k * (1 + quotientVmByteU16Bytes)
      let slot ← byteAtPanic bytes base 2487
      let ptr ← readU16 bytes (base + 1)
      .ok (acc ++ [QuotientOperand.konst slot false, QuotientOperand.mem "u16" ptr])
    let productBase := memBase + memCount * (1 + quotientVmByteU16Bytes)
    let productOps ← foldRangeIdxM productCount [] fun k acc => do
      let base := productBase + k * (1 + 2 * quotientVmByteU16Bytes)
      let slot ← byteAtPanic bytes base 2493
      let lhs ← readU16 bytes (base + 1)
      let rhs ← readU16 bytes (base + 1 + quotientVmByteU16Bytes)
      .ok (acc ++ [QuotientOperand.konst slot false, QuotientOperand.mem "u16" lhs,
                   QuotientOperand.mem "u16" rhs])
    .ok (constStep.1 ++ linOps ++ rowOps ++ pwOps ++ memOps ++ productOps)
  else
    .error (QuotientValidationFault.walkerMissingArm op idx)

/-- rust: QVM:2289-2304 (`describe_read_windows`) @formal-baseline. "Render the
    legal read set for a validation error message." -/
def describeReadWindows (model : QuotientReadModel) : String :=
  String.intercalate ", " (model.windows.map fun window =>
    s!"{window.name}=[{validationHex window.start}..{validationHex (window.start + window.len)})")

/-- rust: QVM:2272-2287 (`check_quotient_const_slot`) @formal-baseline. "Check one
    constant-table slot against the emitted table length." The `wide` flag only
    changes the word in the message, never the bound - which is the point of the
    255/256 gate in hazard 5. -/
def checkQuotientConstSlot (slot : Nat) (wide : Bool) (constLen idx : Nat) : VResult Unit :=
  if slot >= constLen then
    .error (QuotientValidationFault.constSlotOutOfRange wide slot idx constLen)
  else .ok ()

/-- rust: QVM:2234-2270 (`check_quotient_mem_operand`) @formal-baseline. "Check one
    memory operand: word-aligned and inside a populated window." The token leg
    resolves through the layout first, so a token with no base is a different fault
    from a base outside every window. The `_` arm is the Rust's `unreachable!` (R4). -/
def checkQuotientMemOperand (model : QuotientReadModel) (idx : Nat)
    (operand : QuotientOperand) : VResult Unit := do
  let (kind, ptr) ← match operand with
    | .mem kind ptr => .ok (kind, ptr)
    | .token token offset => do
        let base ← match model.tokenBase token with
          | some base => .ok base
          | none => .error (QuotientValidationFault.tokenHasNoBase token idx)
        let ptr := base + offset
        if ptr < base then .error (QuotientValidationFault.tokenOffsetOverflow idx)
        else .ok ("token", ptr)
    | _ => vPanic siteNotMemoryOperand
  if ptr % wordBytes != 0 then
    .error (QuotientValidationFault.pointerMisaligned kind ptr idx)
  else .ok ()
  if model.windowFor ptr == none then
    .error (QuotientValidationFault.pointerOutsideWindows kind ptr idx
      (describeReadWindows model))
  else .ok ()

/-- rust: QVM:2198-2232 (`check_quotient_operand`) @formal-baseline. "Check one
    decoded operand against the plan." -/
def checkQuotientOperand (model : QuotientOperandModel) (idx : Nat)
    (operand : QuotientOperand) : VResult Unit :=
  match operand with
  | QuotientOperand.mem .. | QuotientOperand.token .. =>
      checkQuotientMemOperand model.read idx operand
  | QuotientOperand.konst slot wide =>
      checkQuotientConstSlot slot wide model.numConsts idx
  | QuotientOperand.selectorBucket bucket =>
      if bucket >= model.numSelectorBuckets then
        .error (QuotientValidationFault.selectorBucketOutOfRange bucket idx
          model.numSelectorBuckets)
      else .ok ()
  | QuotientOperand.selectorGap gap =>
      if gap > model.selectorMaxPower then
        .error (QuotientValidationFault.selectorGapTooLarge gap idx model.selectorMaxPower)
      else .ok ()

/-- rust: QVM:2128-2158 (`validate_quotient_program_operands`) @formal-baseline.
    THE PREDICATE PLAN 9.5 calls `Supported.qvm`: "Validate a finalized program's
    structure and every operand value. ... It fails closed: the first violation is
    an error and generation stops before any verifier or VK is rendered." -/
def validateQuotientProgramOperands (bytes : List Nat)
    (model : QuotientOperandModel) : VResult Unit := do
  requireByteProgram bytes
  let maxStack ← validateQuotientProgram bytes
  if maxStack > model.stackWords then
    .error (QuotientValidationFault.stackRegionExceeded maxStack model.stackWords)
  else .ok ()
  let ops ← quotientBytecodeOps bytes
  forEachM (ops.map fun (idx, op, _len) => (idx, op)) fun (idx, op) => do
    let operands ← visitQuotientOperands bytes idx op
    forEachM operands (checkQuotientOperand model idx)

/-- rust: QVM:2160-2182 (`validate_quotient_mem_ptrs`) @formal-baseline.
    "Bounds-check every memory pointer a finalized program loads from."
    `#[cfg(test)]` in the Rust, and it does NOT run phase 1 - so on a malformed
    program it panics rather than reporting. Hazard 1's caveat, stated at the def. -/
def validateQuotientMemPtrs (bytes : List Nat) (model : QuotientReadModel) :
    VResult Unit := do
  requireByteProgram bytes
  let ops ← quotientBytecodeOps bytes
  forEachM (ops.map fun (idx, op, _len) => (idx, op)) fun (idx, op) => do
    let operands ← visitQuotientOperands bytes idx op
    forEachM operands fun operand =>
      match operand with
      | QuotientOperand.mem .. | QuotientOperand.token .. =>
          checkQuotientMemOperand model idx operand
      | _ => .ok ()

/-- rust: QVM:2184-2196 (`validate_quotient_const_slots`) @formal-baseline.
    "Bounds-check every constant-table slot referenced by a finalized program."
    Also `#[cfg(test)]`, also unguarded. -/
def validateQuotientConstSlots (bytes : List Nat) (constLen : Nat) : VResult Unit := do
  requireByteProgram bytes
  let ops ← quotientBytecodeOps bytes
  forEachM (ops.map fun (idx, op, _len) => (idx, op)) fun (idx, op) => do
    let operands ← visitQuotientOperands bytes idx op
    forEachM operands fun operand =>
      match operand with
      | QuotientOperand.konst slot wide => checkQuotientConstSlot slot wide constLen idx
      | _ => .ok ()

/-- Embed a validation fault into P-09b's interpreter fault type. This is what lets
    VmBuilder's compaction-scoped copies be replaced by the general ones above
    without widening `QuotientBuilder.M` (hazard 3's retirement path). -/
def toQVMFault (fault : QuotientValidationFault) : QVMFault := QVMFault.panic fault.message

end Midfall.Generator.QuotientValidator

/-! ## Known-answer tests

    Every gate below is a `Bool` or an `IO Bool` with a matching
    `#eval ... -- expect true` line at the end of the file, so
    `scripts/kat_gate.py` turns each one into a CI obligation (docs/REVIEW.md R-38).
    Each doc names the concrete wrong implementation it rules out, and the package
    report carries the perturbation actually run inside each stated scope (R-41).
    D-P19 binds the artifact gates: they open vm/mod.rs and plan.rs from disk while
    they evaluate, and the reachability gate is the first `#eval` in the file so a
    wrong path is diagnosed rather than matched by accident. R-48: the fixture
    non-degeneracy gate runs before any gate that compares numbers. -/

namespace Midfall.Generator.QuotientVmValidatorKats

open Midfall.Generator.QuotientValidator
open Midfall.Generator.QuotientVmKats (readFileOrEmpty hasDuplicateNat)

/-- The validator cluster's artifact. Two candidates so the gate resolves from
    `formal/` (where `lake` and `scripts/checks.sh` run) and from the repo root. -/
def vmModPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"]

/-- The caller that builds the operand model from the converged layout (hazard 2). -/
def planPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/plan.rs",
   "proofs/solidity-verifier/src/lowering/plan.rs"]

def readFrom (candidates : List String) : IO String :=
  candidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

def readVmMod : IO String := readFrom vmModPathCandidates
def readPlanSource : IO String := readFrom planPathCandidates

/-- vm/mod.rs is 4336 lines / 166317 bytes at HEAD; anything much smaller is a wrong
    path and must not be allowed to satisfy a needle check by accident. -/
def vmModReadOk (src : String) : Bool := src.length > 150000
/-- plan.rs is 1000+ lines; the same rule. -/
def planReadOk (src : String) : Bool := src.length > 15000

/-- The Rust's backslash line continuations inside a string literal: the newline and
    the next line's leading whitespace both disappear. Normalising the artifact this
    way is what lets a multi-line `format!` string be searched for as one needle,
    which is the difference between checking the error text and checking a fragment
    of it (hazard 4). -/
def stripRustContinuations (src : String) : String :=
  match src.splitOn "\\\n" with
  | [] => ""
  | first :: rest =>
      first ++ String.join (rest.map fun piece =>
        String.ofList (piece.toList.dropWhile fun c => c == ' ' || c == '\t'))

/-- Big-endian operand encoders, so the fixtures read like the Rust's own byte
    literals. -/
def be16 (n : Nat) : List Nat := [n / 256 % 256, n % 256]
def be32 (n : Nat) : List Nat := [n / 2^24 % 256, n / 2^16 % 256, n / 2^8 % 256, n % 256]

/-- Patch one byte of a program, leaving the length alone: the corruption class the
    Rust's own QVM-01 test uses, because it cannot move an instruction boundary. -/
def patchByte (bytes : List Nat) (idx : Nat) (value : Nat) : List Nat :=
  (bytes.take idx) ++ [value % 256] ++ (bytes.drop (idx + 1))

def isOk {α : Type} (x : VResult α) : Bool :=
  match x with
  | .ok _ => true
  | .error _ => false

def isPanic {α : Type} (x : VResult α) : Bool :=
  match x with
  | .error (QuotientValidationFault.panic _) => true
  | _ => false

/-- The fault a result carries, if it carries one. -/
def faultOf {α : Type} (x : VResult α) : Option QuotientValidationFault :=
  match x with
  | .ok _ => none
  | .error f => some f

def errText {α : Type} (x : VResult α) : String :=
  match x with
  | .ok _ => "<ok>"
  | .error f => f.message

/-- The Rust's `panic!` / index-out-of-range class, as a predicate a gate can name. -/
def isPanicFault (f : Option QuotientValidationFault) : Bool :=
  match f with
  | some (QuotientValidationFault.panic _) => true
  | _ => false

/-- Builder results come back in P-09c's fault type; this is the one-way view the
    fixtures need, so a failed build shows up as `none` and every gate that depends
    on it goes red rather than silently comparing an empty program. -/
def builderOk {α : Type} (x : Except QVMFault α) : Option α :=
  match x with
  | .ok a => some a
  | .error _ => none

/-! ### Fixtures -/

/-- One identity record, in the shape VmTypes' `QuotientIdentity` wants. -/
def vIdentity (globalIndex : Nat) (target : QuotientTarget) (expr : QuotientExpr) :
    QuotientIdentity :=
  { meta_ := { globalIndex := globalIndex,
               source := QuotientIdentitySource.gate globalIndex "validator" 0 "v" 0 }
    lines := ["t := add(1, 2)"]
    var := "t"
    target := target
    expr := expr }

/-- Emit a stream of identities through P-09c's emitter. KAT helper, not a Rust item. -/
def buildStream : List (QuotientExpr × QuotientTarget × Option Nat) →
    QuotientBuilder.QuotientProgramBuilder →
    Except QVMFault QuotientBuilder.QuotientProgramBuilder
  | [], s => .ok s
  | (e, t, g) :: rest, s => QuotientBuilder.identityExpr
      QuotientBuilder.noShapeRecognizers s e t g >>= fun s => buildStream rest s

/-- The four identities of the Rust's own QVM-01 fixture (LT:2485-2509), with the
    selector gaps the fold plan would have supplied (LT:2510, 2516). -/
def vLit (ptr : Nat) : QuotientExpr := QuotientExpr.mem (.literal ptr)
def vConst (v : Nat) : QuotientExpr := QuotientExpr.const v
def vAdd (a b : QuotientExpr) : QuotientExpr := QuotientExpr.add a b
def vMul (a b : QuotientExpr) : QuotientExpr := QuotientExpr.mul a b

def vSteps : List (QuotientExpr × QuotientTarget × Option Nat) :=
  [(vAdd (vMul (vLit 0x100) (vConst 3)) (vMul (vLit 0x120) (vLit 0x140)),
    QuotientTarget.main, none),
   (vAdd (vLit 0x160) (vConst 5), QuotientTarget.selector 0, some 1),
   (QuotientExpr.neg (vLit 0x180), QuotientTarget.selector 1, some 2),
   (vMul (vLit 0x1a0) (vConst 7), QuotientTarget.selector 0, some 3)]

/-- The finalized artifact of the synthetic fixture. -/
def syntheticBuildOpt : Option QuotientProgramBuild :=
  builderOk (buildStream vSteps QuotientBuilder.builderDefault) >>= fun s =>
    builderOk (QuotientBuilder.finish s)

/-- The finalized bytecode as the `List Nat` the validator walks. -/
def syntheticBytes : List Nat :=
  (syntheticBuildOpt.map fun b => qvmBytesToNats b.bytes).getD []

/-- The single window of the Rust's fixture (LT:2522-2526). -/
def syntheticWindow : QuotientReadWindow :=
  { name := "synthetic_evals", start := 0x100, len := 0xc0 }

/-- The operand model of the Rust's fixture (LT:2520-2533): the emitted constant
    table, two selector buckets, the fold plan's largest power and the program's own
    high-water mark as the stack region. -/
def syntheticModel : QuotientOperandModel :=
  match syntheticBuildOpt with
  | some b =>
      { read := { windows := [syntheticWindow], tokenBases := [] },
        numConsts := b.consts.length, numSelectorBuckets := 2,
        selectorMaxPower := 3, stackWords := b.maxStack }
  | none => quotientOperandModelDefault

/-- A model wide enough that every fixture operand is in range: used to gate the
    ACCEPT side of the checks, which the narrow synthetic model cannot do because its
    windows only cover its own pointers. -/
def wideModel : QuotientOperandModel :=
  { read := { windows := [{ name := "wide", start := 0, len := 0x20000 }],
              tokenBases := quotientMemTokenTable.map fun spec => (spec.token, 0x1000) },
    numConsts := 256, numSelectorBuckets := 256, selectorMaxPower := 65535,
    stackWords := 64 }

/-- One opcode's fixture: a whole program phase 1 accepts, the offset of the
    instruction under test, and the operand list the walker must produce for it. -/
structure OpcodeFixture where
  name : String
  op : Nat
  bytes : List Nat
  testIdx : Nat
  operands : List QuotientOperand

/-- The seven-limb term block the emitter writes, and the operand list it must walk
    to: slots 0..6 over the seven aligned pointers. Written independently of the
    walker so the pin is a second transcription, not a call. -/
def limbSlots : List Nat := List.range 7
def limbPtrs : List Nat := (List.range 7).map fun k => 0x100 + k * 0x20
def limbBlockBytes : List Nat :=
  (limbSlots.zip limbPtrs).flatMap fun (slot, ptr) => [slot] ++ be16 ptr
def limbBlockOperands : List QuotientOperand :=
  (limbSlots.zip limbPtrs).flatMap fun (slot, ptr) =>
    [QuotientOperand.konst slot false, QuotientOperand.mem "limb" ptr]

/-- The 13 pairwise coefficient slots and their bytes. -/
def pwSlots : List Nat := List.range 13
def pwBlockBytes : List Nat := pwSlots
def pwOperands (lhs rhs : Nat) : List QuotientOperand :=
  ((List.range 7).flatMap fun k =>
      [QuotientOperand.mem "pairwise_lhs" (lhs + k * 0x20),
       QuotientOperand.mem "pairwise_rhs" (rhs + k * 0x20)])
    ++ pwSlots.map fun s => QuotientOperand.konst s false

/-- THE FIXTURE TABLE: one entry per opcode in `QUOTIENT_OPCODE_TABLE`, i.e. all 31.
    Each `bytes` is a complete program that phase 1 accepts - the pushes and folds are
    there to satisfy the stack discipline, not decoration - and `operands` is the
    walker's expected visit order for the instruction at `testIdx`. -/
def opcodeFixtures : List OpcodeFixture :=
  [ { name := "push_const", op := qOpPushConst,
        bytes := [0x01] ++ be16 3 ++ [0x0a], testIdx := 0,
        operands := [QuotientOperand.konst 3 true] },
    { name := "push_mem_literal", op := qOpPushMemLiteral,
        bytes := [0x02] ++ be32 0x100 ++ [0x0a], testIdx := 0,
        operands := [QuotientOperand.mem "literal" 0x100] },
    { name := "push_mem_token", op := qOpPushMemToken,
        bytes := [0x03, qMemBeta] ++ [0x0a], testIdx := 0,
        operands := [QuotientOperand.token qMemBeta 0] },
    { name := "push_mem_token_offset", op := qOpPushMemTokenOffset,
        bytes := [0x04, qMemX] ++ be32 0x20 ++ [0x0a], testIdx := 0,
        operands := [QuotientOperand.token qMemX 0x20] },
    { name := "push_mem_u16", op := qOpPushMemU16,
        bytes := [0x05] ++ be16 0x120 ++ [0x0a], testIdx := 0,
        operands := [QuotientOperand.mem "u16" 0x120] },
    { name := "add", op := qOpAdd,
        bytes := [0x09, 0, 0x09, 0, 0x06, 0x0a], testIdx := 4, operands := [] },
    { name := "mul", op := qOpMul,
        bytes := [0x09, 0, 0x09, 0, 0x07, 0x0a], testIdx := 4, operands := [] },
    { name := "neg", op := qOpNeg,
        bytes := [0x09, 0, 0x08, 0x0a], testIdx := 2, operands := [] },
    { name := "push_const_u8", op := qOpPushConstU8,
        bytes := [0x09, 2, 0x0a], testIdx := 0,
        operands := [QuotientOperand.konst 2 false] },
    { name := "fold_main", op := qOpFoldMain,
        bytes := [0x09, 0, 0x0a], testIdx := 2, operands := [] },
    { name := "fold_selector", op := qOpFoldSelector,
        bytes := [0x09, 0, 0x0b, 1] ++ be16 3, testIdx := 2,
        operands := [QuotientOperand.selectorBucket 1, QuotientOperand.selectorGap 3] },
    { name := "add_const_u8", op := qOpAddConstU8,
        bytes := [0x09, 0, 0x0c, 5, 0x0a], testIdx := 2,
        operands := [QuotientOperand.konst 5 false] },
    { name := "mul_const_u8", op := qOpMulConstU8,
        bytes := [0x09, 0, 0x0d, 6, 0x0a], testIdx := 2,
        operands := [QuotientOperand.konst 6 false] },
    { name := "add_const", op := qOpAddConst,
        bytes := [0x09, 0, 0x0e] ++ be16 7 ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.konst 7 true] },
    { name := "mul_const", op := qOpMulConst,
        bytes := [0x09, 0, 0x0f] ++ be16 1 ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.konst 1 true] },
    { name := "add_mem_u16", op := qOpAddMemU16,
        bytes := [0x09, 0, 0x10] ++ be16 0x140 ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x140] },
    { name := "mul_mem_u16", op := qOpMulMemU16,
        bytes := [0x09, 0, 0x11] ++ be16 0x160 ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x160] },
    { name := "add_mul_mem_mem_const_u8", op := qOpAddMulMemMemConstU8,
        bytes := [0x09, 0, 0x12] ++ be16 0x100 ++ be16 0x120 ++ [3] ++ [0x0a],
        testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x100, QuotientOperand.mem "u16" 0x120,
                     QuotientOperand.konst 3 false] },
    { name := "add_mul_const_u8_mem_u16", op := qOpAddMulConstU8MemU16,
        bytes := [0x09, 0, 0x13] ++ be16 0x100 ++ [4] ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x100, QuotientOperand.konst 4 false] },
    { name := "add_mul_mem_mem", op := qOpAddMulMemMem,
        bytes := [0x09, 0, 0x14] ++ be16 0x100 ++ be16 0x120 ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x100, QuotientOperand.mem "u16" 0x120] },
    { name := "run_add_mul_mem_mem_const_u8", op := qOpRunAddMulMemMemConstU8,
        bytes := [0x09, 0, 0x15] ++ be16 2 ++ be16 0x100 ++ be16 0x120 ++ [1]
          ++ be16 0x140 ++ be16 0x160 ++ [2] ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x100, QuotientOperand.mem "u16" 0x120,
                     QuotientOperand.konst 1 false, QuotientOperand.mem "u16" 0x140,
                     QuotientOperand.mem "u16" 0x160, QuotientOperand.konst 2 false] },
    { name := "run_add_mul_const_u8_mem_u16", op := qOpRunAddMulConstU8MemU16,
        bytes := [0x09, 0, 0x16] ++ be16 2 ++ be16 0x100 ++ [3] ++ be16 0x120 ++ [4]
          ++ [0x0a], testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x100, QuotientOperand.konst 3 false,
                     QuotientOperand.mem "u16" 0x120, QuotientOperand.konst 4 false] },
    { name := "native_permutation", op := qOpNativePermutation,
        bytes := [0x19], testIdx := 0, operands := [] },
    { name := "native_identity", op := qOpNativeIdentity,
        bytes := [0x1b] ++ be16 7, testIdx := 0, operands := [] },
    { name := "native_lookup", op := qOpNativeLookup,
        bytes := [0x1f], testIdx := 0, operands := [] },
    { name := "lin7", op := qOpLin7,
        bytes := [0x1c] ++ limbBlockBytes ++ [0x0a], testIdx := 0,
        operands := limbBlockOperands },
    { name := "bilin7_row", op := qOpBilin7Row,
        bytes := [0x1d] ++ be16 0x100 ++ limbBlockBytes ++ [0x0a], testIdx := 0,
        operands := QuotientOperand.mem "row_lhs" 0x100 :: limbBlockOperands },
    { name := "bilin7_pairwise", op := qOpBilin7Pairwise,
        bytes := [0x1e] ++ be16 0x100 ++ be16 0x200 ++ pwBlockBytes ++ [0x0a],
        testIdx := 0, operands := pwOperands 0x100 0x200 },
    { name := "modarith7", op := qOpModarith7,
        bytes := [0x21, 0x03] ++ be16 0x100 ++ [0] ++ [2, 2, 2, 2, 2]
          ++ limbBlockBytes ++ limbBlockBytes
          ++ be16 0x100 ++ limbBlockBytes ++ be16 0x120 ++ limbBlockBytes
          ++ be16 0x100 ++ be16 0x200 ++ pwBlockBytes
          ++ be16 0x140 ++ be16 0x240 ++ pwBlockBytes
          ++ [2] ++ be16 0x140 ++ [4] ++ be16 0x160
          ++ [3] ++ be16 0x160 ++ be16 0x180 ++ [5] ++ be16 0x1a0 ++ be16 0x1c0
          ++ [0x0a],
        testIdx := 0,
        operands := [QuotientOperand.mem "modarith_cond" 0x100,
                     QuotientOperand.konst 0 false]
          ++ limbBlockOperands ++ limbBlockOperands
          ++ (QuotientOperand.mem "row_lhs" 0x100 :: limbBlockOperands)
          ++ (QuotientOperand.mem "row_lhs" 0x120 :: limbBlockOperands)
          ++ pwOperands 0x100 0x200 ++ pwOperands 0x140 0x240
          ++ [QuotientOperand.konst 2 false, QuotientOperand.mem "u16" 0x140]
          ++ [QuotientOperand.konst 4 false, QuotientOperand.mem "u16" 0x160]
          ++ [QuotientOperand.konst 3 false, QuotientOperand.mem "u16" 0x160,
              QuotientOperand.mem "u16" 0x180]
          ++ [QuotientOperand.konst 5 false, QuotientOperand.mem "u16" 0x1a0,
              QuotientOperand.mem "u16" 0x1c0] },
    { name := "pow5", op := qOpPow5,
        bytes := [0x09, 0, 0x20, 0x0a], testIdx := 2, operands := [] },
    { name := "affine_sum", op := qOpAffineSum,
        bytes := [0x09, 0, 0x22] ++ be16 1 ++ be16 1 ++ be16 0x100 ++ [2]
          ++ be16 0x120 ++ be16 0x140 ++ [3] ++ [0x0a],
        testIdx := 2,
        operands := [QuotientOperand.mem "u16" 0x100, QuotientOperand.konst 2 false,
                     QuotientOperand.mem "u16" 0x120, QuotientOperand.mem "u16" 0x140,
                     QuotientOperand.konst 3 false] } ]

/-- The fixture programs, named, for the corpus sweeps. -/
def fixturePrograms : List (String × List Nat) :=
  (opcodeFixtures.map fun f => (f.name, f.bytes)) ++
    (match syntheticBuildOpt with
     | some b => [("synthetic", qvmBytesToNats b.bytes)]
     | none => [])

/-- The programs phase 1 must refuse, each with the fault the Rust names. The first
    four are LT:2341-2371 verbatim; the rest cover arms that test has no case for. -/
def structurallyInvalid : List (String × List Nat × QuotientValidationFault) :=
  [("underflow", [qOpAdd], QuotientValidationFault.stackUnderflow qOpAdd 0 2 0),
   ("leak", [qOpPushConstU8, 0, qOpPushConstU8, 0, qOpFoldMain],
    QuotientValidationFault.stackBoundary qOpFoldMain 4 2),
   ("bad_token", [qOpPushMemToken, 0xff, qOpFoldMain],
    QuotientValidationFault.unknownMemToken 0xff 0),
   ("truncated", [qOpPushConst, 0],
    QuotientValidationFault.truncated "instruction" 0 3 2),
   ("unknown_opcode", [0x99], QuotientValidationFault.unknownOpcode 0x99 0),
   ("zero_run", [qOpRunAddMulMemMemConstU8, 0x00, 0x00],
    QuotientValidationFault.zeroLengthRun 0),
   ("affine_sum_zero", [qOpAffineSum, 0x00, 0x00, 0x00, 0x00],
    QuotientValidationFault.affineSumZeroCounts 0),
   ("modarith7_flags", [qOpModarith7, 0x04, 0, 0, 0, 0, 0],
    QuotientValidationFault.modarith7UnknownFlags 0x04 0),
   ("native_nonempty", [qOpPushConstU8, 0, qOpNativePermutation],
    QuotientValidationFault.nativeCallbackStack qOpNativePermutation 2 1),
   ("stack_leak", [qOpPushConstU8, 0], QuotientValidationFault.stackLeak 1),
   ("truncated_operand", [qOpLin7, 0, 0, 0],
    QuotientValidationFault.truncated "instruction" 0 22 4)]

/-- The corpus hazard 1 is gated over: every fixture, every single-byte mutation of
    every fixture at four probe values, and every prefix of every fixture. -/
def mutationValues : List Nat := [0x00, 0x1a, 0x99, 0xff]

def corpus : List (String × List Nat) :=
  fixturePrograms
    ++ (fixturePrograms.flatMap fun (name, bytes) =>
          (List.range bytes.length).flatMap fun i =>
            mutationValues.map fun v =>
              (name ++ "/m" ++ toString i ++ ":" ++ toString v, patchByte bytes i v))
    ++ (fixturePrograms.flatMap fun (name, bytes) =>
          (List.range (bytes.length + 1)).map fun k =>
            (name ++ "/p" ++ toString k, bytes.take k))
    ++ structurallyInvalid.map fun (name, bytes, _) => ("bad/" ++ name, bytes)

/-- The corpus as bare programs. -/
def corpusBytes : List (List Nat) := corpus.map Prod.snd

/-- How many corpus programs phase 1 accepts. Non-vacuity for hazard 1: a corpus
    that phase 1 refused wholesale would make the no-panic claim true for free. -/
def corpusAccepted : List (List Nat) :=
  (corpus.filter fun (_, bytes) => isOk (validateQuotientProgram bytes)).map Prod.snd

/-- How many corpus programs phase 1 refuses. The other half of non-vacuity. -/
def corpusRejected : List (List Nat) :=
  (corpus.filter fun (_, bytes) => ! isOk (validateQuotientProgram bytes)).map Prod.snd


/-- The instruction triples phase 1's own walk produces, collected the same way
    `validate_quotient_program` walks. KAT helper, not a Rust item: it exists so
    the walk-agreement gate can compare the checked walk with the unchecked one phase
    2 uses. -/
def checkedOpsGo (bytes : List Nat) :
    Nat → Nat → List QuotientBytecodeOp → VResult (List QuotientBytecodeOp)
  | 0, _, acc => .ok acc.reverse
  | fuel + 1, idx, acc =>
      if idx >= bytes.length then
        .ok acc.reverse
      else do
        let (op, len) ← decodeByteQuotientInstruction bytes idx
        checkedOpsGo bytes fuel (idx + len) ((idx, op, len) :: acc)
termination_by fuel => fuel

/-- The checked walk, entered at byte 0 with one more step of fuel than the program
    has bytes, so it can only stop by reaching the end. -/
def checkedOps (bytes : List Nat) : VResult (List QuotientBytecodeOp) :=
  checkedOpsGo bytes (bytes.length + 1) 0 []

/-- The instruction boundaries phase 2 walks, or `[]` if the unchecked walk
    refused. -/
def uncheckedOps (bytes : List Nat) : List QuotientBytecodeOp :=
  match quotientBytecodeOps bytes with
  | .ok os => os
  | .error _ => []

/-- The operand positions the Rust's QVM-01 test corrupts, found the way it finds
    them (LT:2556-2561): the first instruction with one of these opcodes, plus one for
    the opcode byte. -/
def firstOpAt (ops : List QuotientBytecodeOp) (wanted : List Nat) : Option Nat :=
  (ops.find? fun (_, op, _) => wanted.contains op).map fun (idx, _, _) => idx

def syntheticOps : List QuotientBytecodeOp := uncheckedOps syntheticBytes
/-- The instruction offsets. The Rust's faults name the INSTRUCTION offset (QVM:2153
    passes @BT@idx@BT@ from the iterator), while the corrupted byte sits one or two further
    on, so the two are kept apart explicitly. -/
def syntheticPtrIdx : Nat := (firstOpAt syntheticOps [qOpPushMemU16]).getD 0
def syntheticConstIdx : Nat :=
  (firstOpAt syntheticOps [qOpMulConstU8, qOpAddConstU8, qOpPushConstU8]).getD 0
def syntheticFoldAt : Nat := (firstOpAt syntheticOps [qOpFoldSelector]).getD 0
def syntheticPtrAt : Nat := syntheticPtrIdx + 1
def syntheticConstAt : Nat := syntheticConstIdx + 1

/-- Patch a big-endian `u16` operand in place, leaving the length alone. -/
def patchBe16 (bytes : List Nat) (idx : Nat) (value : Nat) : List Nat :=
  (bytes.take idx) ++ be16 value ++ (bytes.drop (idx + 2))

/-- One QVM-01 corruption: what was broken, the program, the model, and the exact
    fault the validator must name. Mirrors the case list at LT:2563-2615. -/
structure Qvm01Case where
  name : String
  bytes : List Nat
  model : QuotientOperandModel
  fault : QuotientValidationFault

/-- The synthetic program's own high-water mark, which is also `model.stackWords`. -/
def syntheticMaxStack : Nat :=
  match validateQuotientProgram syntheticBytes with
  | .ok n => n
  | .error _ => 0

/-- The seven corruptions of LT:2548-2615. Each keeps the program structurally valid
    - that is the point of the test, and of hazard 1. -/
def qvm01Cases : List Qvm01Case :=
  let windows := describeReadWindows syntheticModel.read
  [ { name := "pointer below the windows",
        bytes := patchBe16 syntheticBytes syntheticPtrAt 0x0020,
        model := syntheticModel,
        fault := QuotientValidationFault.pointerOutsideWindows "u16" 0x20
          syntheticPtrIdx windows },
    { name := "pointer past the windows",
        bytes := patchBe16 syntheticBytes syntheticPtrAt 0x01c0,
        model := syntheticModel,
        fault := QuotientValidationFault.pointerOutsideWindows "u16" 0x1c0
          syntheticPtrIdx windows },
    { name := "misaligned pointer",
        bytes := patchBe16 syntheticBytes syntheticPtrAt 0x0101,
        model := syntheticModel,
        fault := QuotientValidationFault.pointerMisaligned "u16" 0x101 syntheticPtrIdx },
    { name := "u8 const slot past the table",
        bytes := patchByte syntheticBytes syntheticConstAt syntheticModel.numConsts,
        model := syntheticModel,
        fault := QuotientValidationFault.constSlotOutOfRange false
          syntheticModel.numConsts syntheticConstIdx syntheticModel.numConsts },
    { name := "selector bucket",
        bytes := patchByte syntheticBytes (syntheticFoldAt + 1) 2,
        model := syntheticModel,
        fault := QuotientValidationFault.selectorBucketOutOfRange 2 syntheticFoldAt 2 },
    { name := "selector gap",
        bytes := patchBe16 syntheticBytes (syntheticFoldAt + 2)
          (syntheticModel.selectorMaxPower + 1),
        model := syntheticModel,
        fault := QuotientValidationFault.selectorGapTooLarge
          (syntheticModel.selectorMaxPower + 1) syntheticFoldAt
          syntheticModel.selectorMaxPower },
    { name := "stack region",
        bytes := syntheticBytes,
        model := { syntheticModel with stackWords := syntheticMaxStack - 1 },
        fault := QuotientValidationFault.stackRegionExceeded syntheticMaxStack
          (syntheticMaxStack - 1) } ]

/-- List duplicate detection for types with `BEq` but no `Ord`. -/
def hasDuplicateOf {α : Type} [BEq α] (xs : List α) : Bool :=
  match xs with
  | [] => false
  | x :: rest => (rest.any fun y => y == x) || hasDuplicateOf rest

/-- A single double-quote character, so a Rust format string can be searched for the
    way the source writes it - with its delimiting quotes - without a Lean escape
    sequence at every use site. -/
def qchar : String := String.ofList ['\u0022']

/-! ### GATE 0 - artifact reachability (D-P19: must be the first `#eval`) -/

/-- Both artifacts the gates read must actually be openable, and big enough that a
    wrong path cannot satisfy a needle by accident. Rules out: every artifact gate in
    this file silently passing because `readFileOrEmpty` returned the empty string. -/
def artifactReachable_ok : IO Bool := do
  let vm ← readVmMod
  let plan ← readPlanSource
  pure (vmModReadOk vm && planReadOk plan
    && (stripRustContinuations vm).contains "fn validate_quotient_program_operands")

/-! ### GATES 1-3 - hazard 4: the error strings are the interface -/

/-- Payloads used to render each fault: 7 for `idx`, 0x99 for an unknown opcode,
    0x0f for a token, 3 / 2 / 1 for the stack numbers, 0x101 for a pointer, 9 for a
    slot, 4 for a table length, 0x04 for flag bits. Deliberately all different, so a
    dropped or swapped payload shows up (R-43 F2's payload-loss class). -/
def faultFormatFixtures : List (String × QuotientValidationFault × String) :=
  [("quotient VM stack leak at end of program: {depth} value(s) remain",
    QuotientValidationFault.stackLeak 3,
    "quotient VM stack leak at end of program: 3 value(s) remain"),
   ("quotient VM stack depth {max_stack} exceeds the {}-word planned stack region",
    QuotientValidationFault.stackRegionExceeded 3 2,
    "quotient VM stack depth 3 exceeds the 2-word planned stack region"),
   ("quotient VM FOLD_SELECTOR bucket {bucket} at byte {idx} is outside the {} simple-selector accumulator(s)",
    QuotientValidationFault.selectorBucketOutOfRange 9 7 2,
    "quotient VM FOLD_SELECTOR bucket 9 at byte 7 is outside the 2 simple-selector accumulator(s)"),
   ("quotient VM FOLD_SELECTOR gap {gap} at byte {idx} exceeds the largest precomputed y power {}",
    QuotientValidationFault.selectorGapTooLarge 9 7 4,
    "quotient VM FOLD_SELECTOR gap 9 at byte 7 exceeds the largest precomputed y power 4"),
   ("quotient VM memory token {token:#x} at byte {idx} has no generated base address in this layout",
    QuotientValidationFault.tokenHasNoBase 0x0f 7,
    "quotient VM memory token 0xf at byte 7 has no generated base address in this layout"),
   ("quotient VM token offset overflows at byte {idx}",
    QuotientValidationFault.tokenOffsetOverflow 7,
    "quotient VM token offset overflows at byte 7"),
   ("quotient VM {kind} pointer {ptr:#x} at byte {idx} is not 32-byte aligned",
    QuotientValidationFault.pointerMisaligned "u16" 0x101 7,
    "quotient VM u16 pointer 0x101 at byte 7 is not 32-byte aligned"),
   ("quotient VM {kind} pointer {ptr:#x} at byte {idx} is outside every window the verifier populates before the quotient VM runs ({})",
    QuotientValidationFault.pointerOutsideWindows "u16" 0x101 7 "w=[0x100..0x1c0)",
    "quotient VM u16 pointer 0x101 at byte 7 is outside every window the verifier populates before the quotient VM runs (w=[0x100..0x1c0))"),
   ("quotient VM {} const slot {slot} at byte {idx} is outside the {const_len}-entry constant table",
    QuotientValidationFault.constSlotOutOfRange true 9 7 4,
    "quotient VM u16 const slot 9 at byte 7 is outside the 4-entry constant table"),
   ("quotient VM operand walker does not handle opcode {op:#x} at byte {idx}; extend `visit_quotient_operands` so the new opcode's operands stay bounds-checked",
    QuotientValidationFault.walkerMissingArm 0x99 7,
    "quotient VM operand walker does not handle opcode 0x99 at byte 7; extend `visit_quotient_operands` so the new opcode's operands stay bounds-checked"),
   ("unknown quotient VM opcode {op:#x} at byte {idx}",
    QuotientValidationFault.unknownOpcode 0x99 7,
    "unknown quotient VM opcode 0x99 at byte 7"),
   ("quotient VM opcode {} ({op:#x}) decoded to zero length at byte {idx}",
    QuotientValidationFault.zeroLengthDecoded "affine_sum" 0x22 7,
    "quotient VM opcode affine_sum (0x22) decoded to zero length at byte 7"),
   ("zero-length quotient VM run at byte {idx}",
    QuotientValidationFault.zeroLengthRun 7,
    "zero-length quotient VM run at byte 7"),
   ("AFFINE_SUM at byte {idx} requires nonzero linear and product counts",
    QuotientValidationFault.affineSumZeroCounts 7,
    "AFFINE_SUM at byte 7 requires nonzero linear and product counts"),
   ("MODARITH7 has unknown flag bits {flags:#x} at byte {idx}",
    QuotientValidationFault.modarith7UnknownFlags 0x04 7,
    "MODARITH7 has unknown flag bits 0x4 at byte 7"),
   ("quotient VM stack depth overflow at byte {idx}",
    QuotientValidationFault.stackDepthOverflow 7,
    "quotient VM stack depth overflow at byte 7"),
   ("quotient VM stack boundary error at byte {idx}: opcode {op:#x} requires exactly 1 stack value, found {depth}",
    QuotientValidationFault.stackBoundary 0x0a 7 3,
    "quotient VM stack boundary error at byte 7: opcode 0xa requires exactly 1 stack value, found 3"),
   ("quotient VM native callback at byte {idx}: opcode {op:#x} requires an empty stack, found {depth}",
    QuotientValidationFault.nativeCallbackStack 0x19 7 3,
    "quotient VM native callback at byte 7: opcode 0x19 requires an empty stack, found 3"),
   ("unknown quotient VM opcode {op:#x} reached stack validator at byte {idx}",
    QuotientValidationFault.unknownOpcodeInStackValidator 0x99 7,
    "unknown quotient VM opcode 0x99 reached stack validator at byte 7"),
   ("quotient VM stack underflow at byte {idx}: opcode {op:#x} requires {required} stack value(s), found {depth}",
    QuotientValidationFault.stackUnderflow 0x06 7 2 1,
    "quotient VM stack underflow at byte 7: opcode 0x6 requires 2 stack value(s), found 1"),
   ("unknown quotient VM memory token {token:#x} at byte {idx}",
    QuotientValidationFault.unknownMemToken 0x0f 7,
    "unknown quotient VM memory token 0xf at byte 7"),
   ("quotient VM {context} length overflows at byte {idx}",
    QuotientValidationFault.byteRangeOverflow "instruction" 7,
    "quotient VM instruction length overflows at byte 7"),
   ("truncated quotient VM {context} at byte {idx}: need {len} byte(s), program has {} byte(s) remaining",
    QuotientValidationFault.truncated "instruction" 7 4 2,
    "truncated quotient VM instruction at byte 7: need 4 byte(s), program has 2 byte(s) remaining"),
   ("quotient VM opcode {op:#x} length overflows while decoding byte {op_idx}",
    QuotientValidationFault.cursorOverflow 0x21 7,
    "quotient VM opcode 0x21 length overflows while decoding byte 7"),
   ("quotient VM opcode {op:#x} length multiplication overflows at byte {idx}",
    QuotientValidationFault.lenMulOverflow 0x21 7,
    "quotient VM opcode 0x21 length multiplication overflows at byte 7"),
   ("quotient VM opcode {op:#x} length addition overflows at byte {idx}",
    QuotientValidationFault.lenAddOverflow 0x21 7,
    "quotient VM opcode 0x21 length addition overflows at byte 7")]

/-- HAZARD 4, both halves: the Rust still writes each string, and the port still
    renders it. Rules out: an error text changing on either side, and a fault
    constructor that drops a payload the Rust interpolates. -/
def faultMessages_artifactStrings_ok : IO Bool := do
  let src ← readVmMod
  if ! (vmModReadOk src) then pure false else
    let norm := stripRustContinuations src
    pure (faultFormatFixtures.all fun (fmt, fault, rendered) =>
            (norm.contains (qchar ++ "" ++ fmt ++ "" ++ qchar))
              && fault.message == rendered)

/-- The taxonomy is exactly the cluster: 26 strings, no duplicate needle, no
    duplicate fault, no duplicate rendering. Rules out: two constructors claiming one
    string, a constructor with no string, and a rendering collision that would let a
    caller dispatch on the wrong class. -/
def faultTaxonomy_isExactlyTheCluster_ok : IO Bool := do
  let src ← readVmMod
  if ! (vmModReadOk src) then pure false else
    let needles := faultFormatFixtures.map fun (fmt, _, _) => fmt
    let faults := faultFormatFixtures.map fun (_, f, _) => f
    let rendered := faultFormatFixtures.map fun (_, _, r) => r
    pure (needles.length == 26 && ! hasDuplicateOf needles
      && ! hasDuplicateOf faults && ! hasDuplicateOf rendered
      && (faultFormatFixtures.all fun (_, f, r) => f.message == r))

/-- The window renderer: the Rust's `{}=[{:#x}..{:#x})` joined by `", "`, checked
    against the artifact and pinned on a two-window model whose numbers differ in
    every position. Rules out: a swapped start / end, a missing `0x`, a decimal
    rendering, and the join separator. -/
def windowRenderer_matchesArtifact_ok : IO Bool := do
  let src ← readVmMod
  if ! (vmModReadOk src) then pure false else
    let norm := stripRustContinuations src
    let model : QuotientReadModel :=
      { windows := [ { name := "vk_payload", start := 0x100, len := 0xc0 },
                     { name := "user_challenges", start := 0x2000, len := 0x40 } ],
        tokenBases := [] }
    pure (norm.contains (qchar ++ "{}=[{:#x}..{:#x})" ++ qchar)
      && describeReadWindows model
        == "vk_payload=[0x100..0x1c0), user_challenges=[0x2000..0x2040)")


/-! ### GATES 4-6 - the walker is total over the opcode table -/

/-- HAZARD 1's positive half, per opcode: every fixture program is accepted by phase
    1, and the walker reproduces exactly the pinned operand list - same classes, same
    payloads, same visit order. Rules out: a walker arm that reads an operand at the
    wrong offset, swaps a slot for a pointer, or reorders the LIN7 pair (the Rust's
    `konst`-then-`mem` order is what the interpreter's decode assumes). -/
def perOpcode_phase1AcceptsAndWalkerPins_ok : Bool :=
  opcodeFixtures.all fun f =>
    isOk (validateQuotientProgram f.bytes)
      && match visitQuotientOperands f.bytes f.testIdx f.op with
         | .ok os => os == f.operands && os.length == f.operands.length
         | .error _ => false

/-- Every fixture validates against a model wide enough to contain it, i.e. the
    accept side of the checks is reachable and not only the reject side. Rules out: a
    check that rejects everything, which would make gate 11 pass for free. -/
def perOpcode_validatesUnderWideModel_ok : Bool :=
  opcodeFixtures.all fun f => isOk (validateQuotientProgramOperands f.bytes wideModel)

/-- rust: LT:2453-2479 (`quotient_operand_walker_covers_every_opcode`). "The operand
    walker must know every opcode's operand fields... it fails closed on an unhandled
    opcode rather than skipping it." Zero operands keep every embedded count at zero,
    so the dynamic forms terminate on a padded one-byte instruction. The reserved byte
    0x1a - deliberately unassigned (QVM:564-565) - must hit the fallback arm. -/
def walkerCoversEveryTableOpcode_ok : Bool :=
  (quotientVmSpec.opcodes.all fun spec =>
    let bytes := [spec.opcode] ++ List.replicate 64 0
    match visitQuotientOperands bytes 0 spec.opcode with
    | .ok _ => true
    | .error f => f != QuotientValidationFault.walkerMissingArm 0 0
      && ! (f.message.contains "operand walker does not handle"))
    && match visitQuotientOperands ([0x1a] ++ List.replicate 64 0) 0 0x1a with
       | .error f => f.message.contains "operand walker does not handle"
       | .ok _ => false

/-! ### GATES 7-10 - HAZARD 1: the two-phase dependency -/

/-- The structurally invalid programs, each with the fault phase 1 must name. The
    first four are LT:2341-2371 verbatim; the rest cover arms that test has no case
    for (unknown opcode, zero-length run, AFFINE_SUM zero counts, MODARITH7 bad flags,
    native callback on a non-empty stack, stack leak, truncated limb block). -/
def structuralRejects_matchTheRustTest_ok : Bool :=
  structurallyInvalid.all fun (name, bytes, expected) =>
    faultOf (validateQuotientProgram bytes) == some expected
      && faultOf (validateQuotientProgramOperands bytes syntheticModel) == some expected

/-- HAZARD 1, the second half the brief asked for: a program that is structurally
    INVALID is refused by PHASE 1, and phase 2 surfaces that same fault rather than
    panicking. Rules out: phase 2 running first, and a phase-1 gap that lets a bad
    offset reach the direct index. -/
def twoPhase_phase1RefusesBeforePhase2Panics_ok : Bool :=
  structurallyInvalid.all fun (_, bytes, expected) =>
    match faultOf (validateQuotientProgramOperands bytes syntheticModel) with
    | some (QuotientValidationFault.panic _) => false
    | some f => f == expected
    | none => false

/-- HAZARD 1, the converse that makes the guarantee non-luck: the SAME programs, fed
    to the operand phase WITHOUT phase 1, panic on the direct index. This is what the
    `#[cfg(test)]` helpers do when a caller reaches for them on unvalidated input,
    and it is the concrete evidence that the bound comes from the structural pass. -/
def twoPhase_phase2PanicsWithoutPhase1_ok : Bool :=
  [("truncated_push_const", [qOpPushConst, 0x00], qOpPushConst),
   ("truncated_lin7", [qOpLin7, 0x00, 0x00], qOpLin7),
   ("run_overruns_program", [qOpRunAddMulMemMemConstU8, 0x00, 0x05],
    qOpRunAddMulMemMemConstU8)].all fun (_, bytes, op) =>
      isPanic (visitQuotientOperands bytes 0 op)
        && ! isOk (validateQuotientProgram bytes)
    && isPanic (quotientBytecodeOps [0x99]) && ! isOk (validateQuotientProgram [0x99])

/-- THE HAZARD-1 GATE. Over the whole corpus - every fixture, every single-byte
    mutation at four probe values, every prefix, every known-bad program - whenever
    phase 1 accepts, phase 2 never returns the panic class. Non-vacuity is asserted in
    the same gate: the corpus must contain both accepted and rejected programs, and it
    must be big enough that a trivially-rejecting phase 2 could not hide in it. -/
def twoPhase_noPanicOnPhase1Accepted_ok : Bool :=
  corpusAccepted.all fun bytes => ! isPanic (validateQuotientProgramOperands bytes syntheticModel)
    && corpusAccepted.length > 100 && corpusRejected.length > 100
    && corpus.length > 1000

/-- The instruction boundaries the checked decoder computes are the ones the
    unchecked walk computes, on every program phase 1 accepts - which is exactly the
    content of the `guarantees every operand offset walked below is in bounds`
    comment. The second half shows the claim is not vacuous: on MODARITH7 with an
    unknown flag bit the two walks DISAGREE, because only the checked decoder looks
    at the flags. Rules out: a stride that matches today and drifts on one opcode. -/
def twoPhase_checkedAndUncheckedWalksAgree_ok : Bool :=
  corpusAccepted.all fun bytes =>
    match checkedOps bytes with
    | .ok checked => checked == uncheckedOps bytes
    | .error _ => false
    && match checkedOps [0x21, 0x04, 0, 0, 0, 0, 0] with
       | .error _ => uncheckedOps [0x21, 0x04, 0, 0, 0, 0, 0] == [(0, 0x21, 7)]
       | .ok _ => false

/-! ### GATES 11-12 - QVM-01 proper -/

/-- rust: LT:2548-2626 (`quotient_operand_validator_rejects_each_out_of_range_operand_class`).
    The emitted program satisfies its own model, and each of the seven corruptions
    (a) stays structurally valid - the coverage is new, not a restatement of phase 1 -
    and (b) is rejected by exactly the named fault. Rules out: a check that looks at
    only one operand class, a window test that forgot the word at the end, and a stack
    bound compared with the wrong side. -/
def qvm01_rejectsEachOperandClass_ok : Bool :=
  isOk (validateQuotientProgramOperands syntheticBytes syntheticModel)
    && qvm01Cases.all fun c =>
      isOk (validateQuotientProgram c.bytes)
        && faultOf (validateQuotientProgramOperands c.bytes c.model) == some c.fault

/-- The seven corruptions must name seven DIFFERENT faults, or gate 11 could be
    satisfied by one catch-all rejection (R-48's vacuity class). -/
def qvm01_faultsAreDistinct_ok : Bool :=
  ! hasDuplicateOf (qvm01Cases.map fun c => c.fault) && qvm01Cases.length == 7

/-- rust: LT:2628-2645. The `u16` slot form is checked the same way as the `u8` one -
    slot 256 against a 256-entry table - and the two narrower passes see exactly their
    own operand class: a pointer corruption is not a const-slot violation, and the
    pointer pass still refuses it. Rules out: the `wide` flag being ignored, and the
    two `#[cfg(test)]` filters swapping their operand classes. -/
def qvm01_narrowHelpersAndWideSlot_ok : Bool :=
  (match validateQuotientProgramOperands [qOpPushConst, 0x01, 0x00, qOpFoldMain]
      { quotientOperandModelDefault with numConsts := 0x100, stackWords := 1 } with
   | .error f => f.message == "quotient VM u16 const slot 256 at byte 0 is outside the 256-entry constant table"
   | .ok _ => false)
    && match qvm01Cases.find? fun c => c.name == "pointer below the windows" with
       | some c => isOk (validateQuotientConstSlots c.bytes syntheticModel.numConsts)
         && ! isOk (validateQuotientMemPtrs c.bytes syntheticModel.read)
       | none => false

/-! ### GATES 13-16 - hazard 3 and the builder's deferred leg -/

/-- One fixture's two op-len readings compared at one index. `none` means both
    refused; `some n` means both accepted with the same length. -/
def opLenPair (bytes : List Nat) (idx : Nat) : Option Nat :=
  match quotientOpLen bytes idx, QuotientBuilder.quotientOpLen bytes idx with
  | .ok a, .ok b => if a == b then some a else none
  | .error _, .error _ => some 0
  | _, _ => none

/-- HAZARD 3. The general `quotient_op_len` ported here and P-09c's compaction-scoped
    copy agree on every fixture program at every byte index, including indices past
    the end and the malformed mutations, on both the accept and the reject side. This
    is what makes the retirement of VmBuilder.lean:1239-1303 safe rather than
    plausible. Rules out: any stride, count or table-lookup difference between the two
    copies - the class of drift the two stale `P-09d will absorb` notes left open. -/
def quotientOpLen_agreesWithScopedCopy_ok : Bool :=
  (corpus.map Prod.snd).all fun bytes =>
    ((List.range (bytes.length + 2)).all fun idx => opLenPair bytes idx != none)
    && (bytes.length + 2) > 0

/-- The two dynamic sub-helpers compared separately: a top-level agreement could hide
    a compensating pair of errors, and these two are the ones with five counted blocks
    between them. Rules out: MODARITH7's block order or AFFINE_SUM's product stride
    differing between the copies while the totals happen to match on the fixtures. -/
def opLenSubHelpers_agreeWithScopedCopy_ok : Bool :=
  (corpus.map Prod.snd).all fun bytes =>
    ((List.range (bytes.length + 2)).all fun idx =>
      match quotientAffineSumOpLen bytes idx,
            QuotientBuilder.quotientAffineSumOpLen bytes idx with
      | .ok a, .ok b => a == b
      | .error _, .error _ => true
      | _, _ => false)
      && ((List.range (bytes.length + 2)).all fun idx =>
        match quotientModarith7OpLen bytes idx,
              QuotientBuilder.quotientModarith7OpLen bytes idx with
        | .ok a, .ok b => a == b
        | .error _, .error _ => true
        | _, _ => false)

/-- rust: LT:2325-2339 (`quotient_vm_lengths_are_derived_from_opcode_spec`). For every
    fixed-width opcode, a program of that many copies of the opcode byte has exactly
    that length. Rules out: the general walker drifting from the static table P-09a
    pinned, which is the only thing keeping the two sources of byte lengths honest. -/
def opLen_matchesStaticTable_ok : Bool :=
  (quotientVmSpec.opcodes.filter fun spec => spec.byteLen != 0).all fun spec =>
    match quotientOpLen (List.replicate spec.byteLen spec.opcode) 0 with
    | .ok n => n == spec.byteLen
    | .error _ => false
    && (quotientVmSpec.opcodes.filter fun spec => spec.byteLen == 0).length == 4

/-- VmBuilder's `finishValidatorLeg` obligation (VmBuilder.lean:1445-1451), discharged:
    the Rust's `finish` runs `validate_quotient_program` and asserts the depth it
    computes equals the builder's `max_stack` (QVM:1219-1222). For every emitter
    fixture the structural validator accepts the finalized bytes and its high-water
    mark is exactly the number the artifact carries. Rules out: an emitter whose stack
    accounting disagrees with the stack-effect table - which is a silent artifact
    change, since compaction runs before this check in the Rust. -/
def finish_maxStackAgreesWithValidator_ok : Bool :=
  QuotientVmBuilderKats.allExprs.all fun (_, e) =>
    match QuotientBuilder.identityExpr QuotientBuilder.noShapeRecognizers
        QuotientBuilder.builderDefault e QuotientTarget.main none
        >>= QuotientBuilder.finish with
    | .error _ => false
    | .ok b => match validateQuotientProgram (qvmBytesToNats b.bytes) with
               | .ok n => n == b.maxStack
               | .error _ => false


/-! ### GATES 17-22 - hazard 5: every bound at value-1, value and value+1 -/

/-- The 255 / 256 const-slot boundary, in both encodings. `constFitsU8Slot` in the
    emitter refuses a slot of 256; the validator must refuse it at exactly the same
    place, and the `wide` flag must change only the word in the message, never the
    bound. Rules out: `slot > constLen` instead of `>=` (one late), and a message
    that loses the u8 / u16 distinction the Rust reports. -/
def constSlot_boundaries_ok : Bool :=
  (List.zip [254, 255, 256] [true, true, false]).all fun (slot, ok) =>
    isOk (checkQuotientConstSlot slot false 256 7) == ok
      && isOk (checkQuotientConstSlot slot true 256 7) == ok
    && (checkQuotientConstSlot 3 false 4 7 |> isOk) && ! (checkQuotientConstSlot 4 false 4 7 |> isOk)
    && (checkQuotientConstSlot 255 false 256 7 |> isOk)
    && errText (checkQuotientConstSlot 256 true 256 7)
        == "quotient VM u16 const slot 256 at byte 7 is outside the 256-entry constant table"
    && errText (checkQuotientConstSlot 256 false 256 7)
        == "quotient VM u8 const slot 256 at byte 7 is outside the 256-entry constant table"

/-- The stack-words limit at the program's own high-water mark minus one, exactly, and
    plus one. The synthetic program peaks at 1; a two-push program peaks at 2. Rules
    out: the comparison being `>=` instead of `>`, which would reject a program that
    exactly fills its region. -/
def stackWords_boundary_ok : Bool :=
  let peak := syntheticMaxStack
  (peak == 1)
    && ! isOk (validateQuotientProgramOperands syntheticBytes
        { syntheticModel with stackWords := peak - 1 })
    && isOk (validateQuotientProgramOperands syntheticBytes
        { syntheticModel with stackWords := peak })
    && isOk (validateQuotientProgramOperands syntheticBytes
        { syntheticModel with stackWords := peak + 1 })
    && match validateQuotientProgram [qOpPushConstU8, 0, qOpPushConstU8, 0, qOpAdd, qOpFoldMain] with
       | .ok n => n == 2
         && ! isOk (validateQuotientProgramOperands [qOpPushConstU8, 0, qOpPushConstU8, 0, qOpAdd, qOpFoldMain]
              { wideModel with stackWords := 1 })
         && isOk (validateQuotientProgramOperands [qOpPushConstU8, 0, qOpPushConstU8, 0, qOpAdd, qOpFoldMain]
              { wideModel with stackWords := 2 })
       | .error _ => false

/-- The window predicate at every edge: start minus a word, start, end minus a word,
    end, end plus a word; a zero-length window, which must never accept; and a window
    one byte shorter than a word, which cannot hold a load. Rules out: an off-by-one
    in `contains_word` in either direction, and the `len != 0` guard being dropped.

    NOTE ON ONE EQUIVALENT MUTANT. Deleting the `len != 0` clause reddens
    nothing, and that is provable rather than a coverage gap: with `len = 0` the range
    test `ptr + 32 <= start` already fails for every `ptr >= start`, and a `ptr < start`
    fails it too, so the clause is defensive - exactly as the Rust documents it
    (`Zero-length windows never accept a pointer`). Recorded rather than hidden, per
    R-41. -/

def window_containsWord_boundaries_ok : Bool :=
  let w : QuotientReadWindow := { name := "synthetic_evals", start := 0x100, len := 0xc0 }
  let edges := (List.zip [0xe0, 0x100, 0x1a0, 0x1c0, 0x1e0] [false, true, true, false, false]).all
    fun (ptr, want) => w.containsWord ptr == want
  let empty := ({ name := "empty", start := 0x100, len := 0 } : QuotientReadWindow).containsWord 0x100
  let short := ({ name := "short", start := 0x100, len := 0x1f } : QuotientReadWindow).containsWord 0x100
  let exact := ({ name := "exact", start := 0x100, len := 0x20 } : QuotientReadWindow).containsWord 0x100
  let rm : QuotientReadModel := { quotientReadModelDefault with windows := [w] }
  let lookup := (List.zip [0x100, 0x1e0] [true, false]).all
    fun (ptr, want) => (rm.windowFor ptr != none) == want
  edges && empty == false && short == false && exact == true && lookup

/-- Alignment and the pointer ceilings. 0x100 is aligned, 0x101 and 0xff are not; the
    `u16` operand form reaches 0xffff and no further, and the `u32` literal form is
    the only one that can address 0x10000 - so a window ending exactly at 0x10000
    accepts the widest `u16` pointer and refuses the smallest `u32` one above it.
    Rules out: a stride of 16 or 64 instead of 32, and a window bound that silently
    truncates a `u32` pointer to 16 bits. -/
def alignmentAndPointerCeiling_ok : Bool :=
  let read := { windows := [{ name := "w", start := 0x100, len := 0xc0 }], tokenBases := [] }
  (List.zip [0x100, 0x101, 0xff, 0x110, 0x120] [true, false, false, false, true]).all
    fun (ptr, want) =>
    isOk (checkQuotientMemOperand read 7 (QuotientOperand.mem "u16" ptr)) == want
  && isOk (validateQuotientProgramOperands ([qOpPushMemU16] ++ be16 0xffe0 ++ [qOpFoldMain])
      { wideModel with read := { windows := [{ name := "u16max", start := 0, len := 0x10000 }],
                                 tokenBases := wideModel.read.tokenBases } })
  && ! isOk (validateQuotientProgramOperands ([qOpPushMemU16] ++ be16 0xffff ++ [qOpFoldMain]) wideModel)
  && isOk (validateQuotientProgramOperands ([qOpPushMemLiteral] ++ be32 0x10000 ++ [qOpFoldMain])
      { wideModel with read := { windows := [{ name := "wide", start := 0, len := 0x10020 }],
                                 tokenBases := wideModel.read.tokenBases } })
  && ! isOk (validateQuotientProgramOperands ([qOpPushMemLiteral] ++ be32 0x10000 ++ [qOpFoldMain])
      { wideModel with read := { windows := [{ name := "narrow", start := 0, len := 0x10000 }],
                                 tokenBases := wideModel.read.tokenBases } })

/-- The selector bucket count and the selector gap power, each at minus-one, exact and
    plus-one. Note the two bounds are different shapes - bucket is `>=` against the
    count, gap is `>` against the largest power - and swapping them is exactly the
    off-by-one this gate catches. -/
def selectorBucketGap_boundaries_ok : Bool :=
  let model := { quotientOperandModelDefault with numSelectorBuckets := 2,
                                                  selectorMaxPower := 3, stackWords := 1 }
  (List.zip [1, 2] [true, false]).all fun (bucket, want) =>
    isOk (checkQuotientOperand model 7 (QuotientOperand.selectorBucket bucket)) == want
    && (List.zip [2, 3, 4] [true, true, false]).all fun (gap, want2) =>
      isOk (checkQuotientOperand model 7 (QuotientOperand.selectorGap gap)) == want2
    && errText (checkQuotientOperand model 7 (QuotientOperand.selectorBucket 2))
        == "quotient VM FOLD_SELECTOR bucket 2 at byte 7 is outside the 2 simple-selector accumulator(s)"

/-- HAZARD 5 and R5: the MODARITH7 flag test. The Rust masks with the `u8` complement
    `!(COND | CONST)`, which is `0xfc`; in `Nat` the complement is infinite-width and
    would reject every legal program, so the mask is written out. Checked against the
    artifact text and against behaviour: 0x00, 0x01, 0x02, 0x03 decode, 0x04 and 0x80
    and 0xff do not. Rules out: the mask being `0xfe`, `0xf8`, or the complement. -/
def modarith7FlagMask_width_ok : IO Bool := do
  let src ← readVmMod
  if ! (vmModReadOk src) then pure false else
    let norm := stripRustContinuations src
    let prog (flags : Nat) : List Nat :=
      [qOpModarith7, flags]
        ++ (if flags &&& qModarith7FlagCond != 0 then [0x10, 0x00] else [])
        ++ (if flags &&& qModarith7FlagConst != 0 then [0] else [])
        ++ [0, 0, 0, 0, 0, qOpFoldMain]
    pure (norm.contains "flags & !(Q_MODARITH7_FLAG_COND | Q_MODARITH7_FLAG_CONST) != 0"
      && modarith7FlagMask == 0xfc
      && (List.zip [0, 1, 2, 3] [true, true, true, true]).all fun (f, want) =>
        isOk (validateQuotientProgram (prog f)) == want
      && (List.zip [0x04, 0x80, 0xff] [false, false, false]).all fun (f, want) =>
        isOk (validateQuotientProgram (prog f)) == want
      && faultOf (validateQuotientProgram (prog 0x04))
        == some (QuotientValidationFault.modarith7UnknownFlags 0x04 0))

/-! ### GATES 23-29 - the port-only arms, the memory model, and the byte domain -/

/-- R5 and R10 together: none of the five overflow faults and none of the two
    port-only fuel panics fire anywhere on the corpus. They are in the taxonomy because
    the strings are the interface (hazard 4) and a 32-bit Rust build can reach them,
    not because this port can. Rules out: a fuel bound that actually binds, which would
    mean the walk is not well-founded on the arithmetic the Rust relies on. -/
def overflowAndFuelArms_unreachable_ok : Bool :=
  let overflowFaults :=
    [QuotientValidationFault.byteRangeOverflow "instruction" 0,
     QuotientValidationFault.cursorOverflow qOpModarith7 0,
     QuotientValidationFault.lenMulOverflow qOpModarith7 0,
     QuotientValidationFault.lenAddOverflow qOpModarith7 0,
     QuotientValidationFault.stackDepthOverflow 0,
     QuotientValidationFault.tokenOffsetOverflow 0]
  let fuelPansics :=
    [QuotientValidationFault.panic (siteIndex 2014),
     QuotientValidationFault.panic (siteIndex 3082)]
  (corpus.map Prod.snd).all fun bytes =>
    (match validateQuotientProgram bytes with
     | .error f => !(overflowFaults.any fun o => o == f) && !(fuelPansics.any fun p => p == f)
     | .ok _ => true)
    && (match validateQuotientProgramOperands bytes syntheticModel with
        | .error f => !(overflowFaults.any fun o => o == f) && !(fuelPansics.any fun p => p == f)
        | .ok _ => true)
    && (match checkQuotientMemOperand { windows := [], tokenBases := [(qMemBeta, 2^64)] } 0
            (QuotientOperand.token qMemBeta (2^32 - 1)) with
        | .error f => f != QuotientValidationFault.tokenOffsetOverflow 0
        | .ok _ => true)

/-- HAZARD 2, from the artifact: the read model this file checks against is the
    converged verifier memory layout built at PL:570-621 - four named windows, nine
    token bases, and a stack region measured in words from the layout's own bounds.
    Read from disk at #eval time (D-P19), not pasted. Rules out: the Lean record
    drifting from the layout constructor the Rust actually calls, which would make
    `Supported.qvm` check bounds nobody imposes. -/
def readModel_isTheLayoutModel_ok : IO Bool := do
  let plan ← readPlanSource
  if ! (planReadOk plan) then pure false else
    let names := ["vk_payload", "user_challenges",
                  "challenge_and_common_slots", "decoded_proof_evals"]
    let tokens := ["vm::Q_MEM_L0", "vm::Q_MEM_L_LAST", "vm::Q_MEM_L_BLIND",
                   "vm::Q_MEM_BETA", "vm::Q_MEM_GAMMA", "vm::Q_MEM_X",
                   "vm::Q_MEM_THETA", "vm::Q_MEM_TRASH_CHALLENGE",
                   "vm::Q_MEM_INSTANCE_EVAL"]
    pure ((names.all fun n => plan.contains ("name: " ++ qchar ++ n ++ qchar))
      && plan.contains "windows: vec!["
      && (plan.splitOn "QuotientReadWindow {").length - 1 == 4
      && (tokens.all fun t => plan.contains t) && tokens.length == 9
      && plan.contains
        "stack_words: (memory.quotient_stack_hi - memory.quotient_stack_mptr)"
      && plan.contains "no runtime pointer clamp")

/-- The token table the structural phase accepts is exactly the nine `Q_MEM_*` tokens,
    and nothing else: 0x00 (no token), 0x0a (a fold opcode byte, the confusion this
    rules out) and 0xff (LT:2358's case) are refused. Rules out: the token set being
    derived from the operand model's `token_bases` instead of the spec table - the two
    differ, and gate 26 pins that. -/
def memToken_acceptsExactlyTheNine_ok : Bool :=
  (quotientMemTokenTable.all fun spec => isOk (validateQuotientMemToken spec.token 0))
    && (List.zip [0x00, 0x0a, 0x0b, 0xff] [false, false, false, false]).all fun (t, want) =>
      isOk (validateQuotientMemToken t 0) == want
    && quotientMemTokenTable.length == 9

/-- The two token faults are different and both reachable: a token the VM knows but
    the layout never resolved is `tokenHasNoBase`, one that resolved outside every
    window is `pointerOutsideWindows`, and one that resolved onto an unaligned base is
    `pointerMisaligned`. Rules out: the token leg collapsing into the literal-pointer
    leg, which would hide a missing layout entry as a window error. -/
def tokenFaults_areDistinct_ok : Bool :=
  faultOf (checkQuotientMemOperand { windows := [{ name := "w", start := 0x100, len := 0xc0 }],
                                     tokenBases := [] } 0
      (QuotientOperand.token qMemBeta 0))
    == some (QuotientValidationFault.tokenHasNoBase qMemBeta 0)
  && faultOf (checkQuotientMemOperand { windows := [{ name := "w", start := 0x100, len := 0xc0 }],
                                        tokenBases := [(qMemBeta, 0x2000)] } 0
      (QuotientOperand.token qMemBeta 0))
    == some (QuotientValidationFault.pointerOutsideWindows "token" 0x2000 0
      (describeReadWindows { windows := [{ name := "w", start := 0x100, len := 0xc0 }],
                             tokenBases := [(qMemBeta, 0x2000)] }))
  && faultOf (checkQuotientMemOperand { windows := [{ name := "w", start := 0x100, len := 0xc0 }],
                                        tokenBases := [(qMemBeta, 0x101)] } 0
      (QuotientOperand.token qMemBeta 0))
    == some (QuotientValidationFault.pointerMisaligned "token" 0x101 0)
  && isOk (checkQuotientMemOperand { windows := [{ name := "w", start := 0x100, len := 0xc0 }],
                                     tokenBases := [(qMemBeta, 0x100)] } 0
      (QuotientOperand.token qMemBeta 0x20))

/-- THE BYTE-DOMAIN GATE (review finding). The Rust takes `&[u8]`; `List Nat` is
    strictly broader, so every public entry point refuses a program with a byte at or
    above 256 before any index or operand arithmetic can turn it into a plausible
    number. The sharpest case is `[PUSH_CONST_U8, 256, FOLD_MAIN]`: phase 1 would
    otherwise ACCEPT it - 256 is a legal slot for a `u8` that cannot exist - and the
    operand check would then compare 256 against the table. Rules out: the guard being
    dropped from any one entry point, and `isByteProgram` accepting 256. -/
def byteDomain_enforcedAtEveryEntryPoint_ok : Bool :=
  isByteProgram [] && isByteProgram [0x00, 0xff] && ! (isByteProgram [0x100])
    && ! (isByteProgram [0x05, 0x01, 300])
    && faultOf (validateQuotientProgram [0x05, 0x01, 300])
      == some (QuotientValidationFault.notAByteProgram 2 300)
    && faultOf (validateQuotientProgram [qOpPushConstU8, 256, qOpFoldMain])
      == some (QuotientValidationFault.notAByteProgram 1 256)
    && faultOf (validateQuotientProgramOperands [qOpPushConstU8, 256, qOpFoldMain] wideModel)
      == some (QuotientValidationFault.notAByteProgram 1 256)
    && faultOf (quotientBytecodeOps [qOpPushConstU8, 256, qOpFoldMain])
      == some (QuotientValidationFault.notAByteProgram 1 256)
    && faultOf (validateQuotientMemPtrs [qOpPushConstU8, 256, qOpFoldMain] wideModel.read)
      == some (QuotientValidationFault.notAByteProgram 1 256)
    && faultOf (validateQuotientConstSlots [qOpPushConstU8, 256, qOpFoldMain] 256)
      == some (QuotientValidationFault.notAByteProgram 1 256)
    && isOk (validateQuotientProgram [qOpPushConstU8, 255, qOpFoldMain])
    && (corpus.map Prod.snd).all isByteProgram

/-- R-48. The fixtures this file's gates lean on are not degenerate: 31 distinct
    opcodes covering the whole table, distinct programs, a corpus with both accepted
    and rejected members, and a synthetic program whose three checked number families
    (slots, buckets, gaps) are pairwise different so a swapped bound cannot hide. -/
def fixturesNonDegenerate_ok : Bool :=
  opcodeFixtures.length == 31
    && ! hasDuplicateOf (opcodeFixtures.map fun f => f.op)
    && (opcodeFixtures.map fun f => f.op).all fun op =>
      (quotientVmSpec.opcodes.any fun spec => spec.opcode == op)
    && quotientVmSpec.opcodes.length == 31
    && ! hasDuplicateOf (opcodeFixtures.map fun f => f.bytes)
    && syntheticBytes.length > 20 && syntheticModel.numConsts > 0
    && syntheticModel.numSelectorBuckets != syntheticModel.selectorMaxPower
      || syntheticModel.numSelectorBuckets == 2
    && corpusAccepted.length > 0 && corpusRejected.length > 0
    && (fixturePrograms.map Prod.snd).all isByteProgram

/-- The proposition as a `Bool`, which is what a `Supported` record field needs. -/
def supportedQvmBool (bytes : List Nat) (model : QuotientOperandModel) : Bool :=
  match validateQuotientProgramOperands bytes model with
  | .ok _ => true
  | .error _ => false

/-- THE HEADLINE. `Supported.qvm` is now a decidable proposition with a denotation: the
    reference's own predicate, applied to a real emitter artifact and the model built
    from it, is `.ok ()` - and every one of the seven out-of-range operand classes makes
    it `false`. Rules out: the field being unsatisfiable (the accept half) and being
    satisfiable for free (the reject half). -/
def supportedQvm_acceptsTheBuiltProgram_ok : Bool :=
  supportedQvmBool syntheticBytes syntheticModel
    && qvm01Cases.all fun c => ! supportedQvmBool c.bytes c.model
    && ! supportedQvmBool syntheticBytes { syntheticModel with stackWords := 0 }

end Midfall.Generator.QuotientVmValidatorKats

#eval Midfall.Generator.QuotientVmValidatorKats.artifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.faultMessages_artifactStrings_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.faultTaxonomy_isExactlyTheCluster_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.windowRenderer_matchesArtifact_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.fixturesNonDegenerate_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.perOpcode_phase1AcceptsAndWalkerPins_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.perOpcode_validatesUnderWideModel_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.walkerCoversEveryTableOpcode_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.structuralRejects_matchTheRustTest_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.twoPhase_phase1RefusesBeforePhase2Panics_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.twoPhase_phase2PanicsWithoutPhase1_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.twoPhase_noPanicOnPhase1Accepted_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.twoPhase_checkedAndUncheckedWalksAgree_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.qvm01_rejectsEachOperandClass_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.qvm01_faultsAreDistinct_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.qvm01_narrowHelpersAndWideSlot_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.quotientOpLen_agreesWithScopedCopy_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.opLenSubHelpers_agreeWithScopedCopy_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.opLen_matchesStaticTable_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.finish_maxStackAgreesWithValidator_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.constSlot_boundaries_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.stackWords_boundary_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.window_containsWord_boundaries_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.alignmentAndPointerCeiling_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.selectorBucketGap_boundaries_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.modarith7FlagMask_width_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.overflowAndFuelArms_unreachable_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.readModel_isTheLayoutModel_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.memToken_acceptsExactlyTheNine_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.tokenFaults_areDistinct_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.byteDomain_enforcedAtEveryEntryPoint_ok -- expect true
#eval Midfall.Generator.QuotientVmValidatorKats.supportedQvm_acceptsTheBuiltProgram_ok -- expect true
