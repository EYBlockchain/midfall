-- |
-- Midfall.Generator.Quotient.VmBuilder
--
-- THE QUOTIENT VM BUILDER: the emitter that lowers quotient identities into finalized
-- bytecode plus a constant table. Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs (4336 lines,
-- 166317 bytes at git HEAD), cited below as QVM. Work package P-09c.
--
-- CITATION NOTATION. QVM is vm/mod.rs read through 'git show HEAD:', every range
-- re-derived from that output rather than from the brief's relative listing
-- (docs/plans/README.md standing note 2; the brief asked for this and the ranges were
-- indeed off - the corrected table is in the package report). QVR is vm/reference.rs,
-- ported by P-09b into VmReference.lean and imported here as the interpreter this
-- emitter has to agree with. VT is VmTypes.lean, P-09a's vocabulary, which this file
-- reuses and never re-declares: opcodes, tokens, QuotientExpr, QuotientMem,
-- QuotientLeaf, QuotientProductAdd, QuotientLimbShape, QuotientModarith7Shape,
-- QuotientTarget, QuotientProgramBuild, the opcode table and quotientOpcodeByteLen.
--
-- WHY THIS FILE IS THE CRITICAL PATH. docs/design.md D-P20 item 3: the certifier's seed
-- is Keccak over the FINALIZED bytecode (QVC:48-76), and nothing in the Lean tree could
-- regenerate that artifact until now. 'finish' below is that artifact boundary.
--
-- WHAT IS NOT HERE, AND WHY (plan P-09c hazard 7 - reported, not imported sideways).
--
-- * validate_quotient_program (QVM:2009-2027), decode_byte_quotient_instruction,
--   apply_quotient_stack_effect, visit_quotient_operands and the operand walker: P-09d.
--   The Rust's finish calls the validator. It cannot change a byte of the artifact - it
--   only panics on a bad program - so finish below produces the same
--   QuotientProgramBuild and omits that leg. The obligation is named, not hidden:
--   'finishValidatorLeg' states what P-09d adds back, and
--   'finishMaxStack_agreesWithInterpreter_ok' re-establishes the substance of the
--   Rust's assert_eq!(validated_max_stack, self.max_stack) (QVM:1219-1222) by measuring
--   the compacted program's real stack high-water mark with P-09b's own step function
--   instead of with P-09d's stack-effect table.
--   'quotient_program_usage' (QVM:1976-1994) IS ported here, and with it the opcode
--   length walker (QVM:3008-3059), because QuotientProgramBuild has no other way to be
--   inhabited and compact_quotient_runs cannot walk without it. Both are the minimum the
--   artifact needs, both live in this namespace only, and P-09d should absorb them.
-- * quotient_limb_shape (QVM:3157-3173), quotient_limb_subshape (QVM:3190-3227),
--   quotient_modarith7_shape (QVM:3231-3238) and quotient_pow5_base (QVM:3176-3187):
--   P-09e's shape recognizers, ~900 lines of sum collection behind them. The builder
--   reaches them through four function-typed fields of 'QuotientShapeRecognizers'
--   (R9: a trait-shaped dependency becomes a structure of functions).
--   'noShapeRecognizers' - every hook returning none - is the conservative
--   instantiation: emit_expr then takes the generic Fr path for every input, which is
--   exactly the fallback the QVM:966-971 doc comment promises. P-09e supplies the real
--   hooks; nothing in this file has to change when it does.
--
-- A DIVERGENCE IN P-09a THAT FORCED A LOCAL COPY.
-- VT.QuotientModarith7Shape.coefficientOperands (VmTypes.lean:579-586) puts
-- shape.constant in the list UNCONDITIONALLY. The Rust's modarith7_coeffs
-- (QVM:3533-3550) pushes it only 'if shape.constant != U256::ZERO', which is also the
-- condition under which emit_modarith7_shape reserves a slot for it (QVM:1535-1539).
-- Feeding the VT helper to peek_u8_const_slots would therefore predict one slot too many
-- for a zero-constant shape: a spurious rejection at the 255/256 boundary and a wrong
-- slot prediction one place earlier. So this file ports its own faithful
-- 'modarith7Coeffs' and does not use the VT helper. VmTypes.lean is another package's
-- file and was not edited (plans README: report, do not fix sideways). Finding F-1.
--
-- R6, THE TWO HASHMAPS. const_slots: HashMap<U256, u16> (QVM:1082) and vars:
-- HashMap<String, QuotientExpr> (QVM:1083) are both modelled as association lists. The
-- iteration order is unobservable in the Rust: const_slots is only read with get /
-- contains_key and written with insert (QVM:1841, 1847, 1854, 1855, 1868), vars only
-- with get, insert and clear (QVM:1128, 1242, 1276); neither is collected, sorted,
-- iterated or hashed into anything the artifact sees. The lists are kept in insertion
-- order, which is also what makes const_slot's first-match lookup match the map's.
--
-- R4, PANICS. Every assert!, assert_eq!, expect and unwrap_or_else(panic!) in the
-- ported range becomes 'throw (QVMFault.panic "vm/mod.rs:<line>")', reusing P-09b's
-- fault type rather than inventing a second taxonomy: the panic constructor already
-- carries a source position and QVMFault is the only quotient-VM fault type in the
-- tree. Sites: 1134 (stack leak), 1146 (missing selector gap), 1148 (selector index
-- width), 1152 (gap width), 1172 / 1187 / 1201 (native marker with a non-empty stack),
-- 1240 (unsupported assignment), 1253 / 1254 / 1260 / 1261 / 1267 / 1268 / 1271 (Yul
-- arity and modulus), 1279 (unknown variable), 1477 / 1491 / 1510 / 1537 / 1541 / 1557 /
-- 1566 / 1576 / 1582 / 1588 (const slots the preflight said would fit), 1706 / 1714
-- (emit_product_add), 1819 (stack underflow), 1824 (u16), 1830 (u24), 1845 (too many
-- constants), 2817 (operand read past the end while walking), 3022 (unknown opcode while
-- walking), 4092 / 4094 / 4096 / 4099 (mload pointer), 4114 / 4117 (bad literal), 4265
-- (unbalanced expression). The reference profile is release (BASELINE.md:143), so
-- arithmetic overflow is NOT a panic site and debug_assert! is compiled out; there is no
-- debug_assert! in the ported range.
--
-- R10, FUEL. Two recursions are structural in the Rust but not provably so here.
-- (a) emit_expr recurses into strict subterms in the generic path, but the limb
-- decomposition path re-enters it on a recognizer-supplied residue, and with the
-- recognizers behind a hook Lean cannot see that the residue is smaller. (b) parse_expr
-- recurses into strictly shorter substrings, which Lean cannot see either. Both are
-- given an explicit fuel argument decremented per recursive call, with a panic-class
-- error when it runs out - the same device VmReference.lean:869-892 uses for the
-- interpreter's while loop. emitterFuelNeverBinds_ok and parseFuelNeverBinds_ok assert
-- the bound is never reached by any fixture, so the fuel is a totality crutch and not a
-- behaviour. Inside a 'mutual' block Lean only accepts termination_by when the fuel is
-- bound by an equation pattern, which is why every member of the group below is written
-- '(r : ..) : Nat -> .. -> ..' with the fuel matched in the patterns.
--
-- WHAT MOVED (Lean is order-sensitive; plans README standing note 3).
-- 1. push_stack / pop_stack / u16 / u24 / u32 (QVM:1800-1837) are pulled to the top of
--    the impl block because every emitter uses them.
-- 2. is_affine_add_op (QVM:1962-1968) and the opcode-length walker (QVM:3008-3059) are
--    pulled above compact_quotient_runs (QVM:1884-1960), which is pulled above finish.
-- 3. quotient_leaf and collect_product_leaves (QVM:3093-3121) are pulled above
--    try_emit_add_product, their only caller in this file. They are leaf flattening, not
--    shape recognition, so they belong to this package rather than to P-09e.
-- 4. The Yul parser helpers (QVM:4085-4119, 4135-4142, 4153-4156, 4174-4196, 4246-4275)
--    are pulled above assignment / parse_expr (QVM:1233-1281), which is the only reason
--    they are in this package at all.
-- 5. The two &self preflight predicates (limb_shape_has_u8_const_slots,
--    modarith7_shape_has_u8_const_slots, QVM:1446-1463) are pulled above the emitters
--    that use them, which also puts modarith7_coeffs (QVM:3533-3550) in this file.
-- 6. The panic-site strings are collected as named constants at the top so no site text
--    is ever split across lines; the strings themselves are verbatim.
--
-- NO THEOREM HERE, AND NOTHING UNDER Instances/ IS IMPORTED (D-P17). Everything below
-- is computable and every gate is a Bool or an IO Bool with a matching
-- '#eval ... -- expect true' line at the end of the file, so scripts/kat_gate.py turns
-- each one into a CI obligation (docs/REVIEW.md R-38). D-P19 binds the artifact gates:
-- they open vm/mod.rs and lowering/config.rs from disk while they evaluate, and the
-- reachability gate runs first so a wrong path is diagnosed rather than matched by
-- accident. lake build caches, so it is checks.sh re-running every KAT file that makes
-- the pattern load-bearing in CI.

import Midfall.Common.Bytes
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Quotient.VmReference

namespace Midfall.Generator.QuotientBuilder

/-- The port's error monad: the builder's panics, rendered per R4 through P-09b's fault
    type. -/
abbrev M (α : Type) := Except QVMFault α

/-- R4 rendering of one Rust panic site. -/
def panicAt {α : Type} (site : String) : M α := .error (QVMFault.panic site)

/-- The Rust file, so the site constants below stay readable. -/
def qvmPath : String := "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"

/-- The panic sites of the ported range, one constant each (WHAT MOVED 6). -/
def siteStackLeak : String := qvmPath ++ ":1134 (quotient VM stack leak)"
def siteNoSelectorGap : String := qvmPath ++ ":1146 (selector fold gap for selector identity)"
def siteSelectorIdxWidth : String := qvmPath ++ ":1148 (selector fold selector index exceeds 8 bits)"
def siteSelectorGapWidth : String := qvmPath ++ ":1152 (selector fold gap exceeds 16 bits)"
def siteNativePermStack : String := qvmPath ++ ":1172 (native permutation expects empty VM stack)"
def siteNativeLookupStack : String := qvmPath ++ ":1187 (native lookup expects empty VM stack)"
def siteNativeIdentityStack : String := qvmPath ++ ":1201 (native identity expects empty VM stack)"
def siteUnsupportedAssignment : String := qvmPath ++ ":1240 (unsupported quotient assignment: "
def siteParseFuel : String := qvmPath ++ ":1250 (parse fuel exhausted - port-only bound, see the header)"
def siteAddmodArity : String := qvmPath ++ ":1253 (addmod arity)"
def siteAddmodModulus : String := qvmPath ++ ":1254 (addmod modulus)"
def siteMulmodArity : String := qvmPath ++ ":1260 (mulmod arity)"
def siteMulmodModulus : String := qvmPath ++ ":1261 (mulmod modulus)"
def siteSubArity : String := qvmPath ++ ":1267 (sub arity)"
def siteSubForm : String := qvmPath ++ ":1268 (only sub(r, x) is supported)"
def siteMloadArity : String := qvmPath ++ ":1271 (mload arity)"
def siteUnknownVar : String := qvmPath ++ ":1279 (unknown quotient variable: "
def siteEmitFuel : String := qvmPath ++ ":1288 (emitter fuel exhausted - port-only bound, see the header)"
def siteLin7Slot : String := qvmPath ++ ":1477 (lin7 const slot checked)"
def siteBilin7RowSlot : String := qvmPath ++ ":1491 (bilin7 row const slot checked)"
def siteBilin7PairwiseSlot : String := qvmPath ++ ":1510 (bilin7 pairwise const slot checked)"
def siteModarith7ConstSlot : String := qvmPath ++ ":1537 (modarith7 const slot checked)"
def siteModarith7Count : String := qvmPath ++ ":1541 (modarith7 count checked)"
def siteModarith7LinSlot : String := qvmPath ++ ":1557 (modarith7 lin const slot checked)"
def siteModarith7RowSlot : String := qvmPath ++ ":1566 (modarith7 row const slot checked)"
def siteModarith7PairwiseSlot : String := qvmPath ++ ":1576 (modarith7 pairwise const slot checked)"
def siteModarith7MemSlot : String := qvmPath ++ ":1582 (modarith7 mem const slot checked)"
def siteModarith7ProductSlot : String := qvmPath ++ ":1588 (modarith7 product const slot checked)"
def siteProductAddSlot : String := qvmPath ++ ":1706 (const slot checked)"
def siteProductAddSlot2 : String := qvmPath ++ ":1714 (const slot checked)"
def siteStackUnderflow : String := qvmPath ++ ":1819 (quotient VM stack underflow)"
def siteU16Overflow : String := qvmPath ++ ":1824 (quotient VM u16 overflow)"
def siteU24Overflow : String := qvmPath ++ ":1830 (quotient VM u24 overflow)"
def siteTooManyConsts : String := qvmPath ++ ":1845 (too many quotient constants)"
def siteCompactionFuel : String := qvmPath ++ ":1893 (compaction fuel exhausted - port-only bound)"
def siteWalkRead : String := qvmPath ++ ":2817 (u16 quotient operand)"
def siteUnknownOp : String := qvmPath ++ ":3022 (unknown quotient op "
def siteAddPointerArity : String := qvmPath ++ ":4092 (add pointer arity)"
def siteMloadBase : String := qvmPath ++ ":4094 (unsupported quotient mload base: "
def siteMloadOffset : String := qvmPath ++ ":4096 (unsupported quotient mload offset: "
def siteMloadPointer : String := qvmPath ++ ":4099 (unsupported quotient mload pointer: "
def siteBadLiteral : String := qvmPath ++ ":4114 (invalid U256: "
def siteUnbalanced : String := qvmPath ++ ":4265 (balanced quotient expression)"
def siteDepthFuel : String := qvmPath ++ ":1220 (segment depth fuel exhausted)"

/-- Left fold over a list in the panic monad, aborting on the first error: R3's reading
    of Rust's mutating for-loops. Written out rather than using List.foldM because the tree
    already avoids core helpers v4.35 does not have (Kzg/Utils.lean:71). -/
def foldLeftM {α β : Type} (f : α → β → M α) (init : α) (xs : List β) : M α :=
  match xs with
  | [] => .ok init
  | x :: rest => do
      let acc ← f init x
      foldLeftM f acc rest

/-- The same for the Option-shaped predicates (product_add_macro), where Rust's '?' inside
    a loop short-circuits to None. -/
def foldLeftOpt {α β : Type} (f : α → β → Option α) (init : α) (xs : List β) : Option α :=
  match xs with
  | [] => some init
  | x :: rest =>
      match f init x with
      | none => none
      | some acc => foldLeftOpt f acc rest

/-- rust: proofs/solidity-verifier/src/lowering/config.rs:27
    (DEFAULT_QUOTIENT_LIMB_VM_OPS: bool = true) @formal-baseline, read by QVM:1099.
    R8: this is the toggle with_limb_vm_ops sets. BOTH branches are ported - every
    limb-shaped emitter checks 'limbVmOps' first, exactly as QVM:1363, 1413 and 1431 do -
    and the DEPLOYED one is 'true': quotient.rs:2110 passes the crate default and the doc
    at quotient.rs:2117-2122 says "Rendering always uses the crate default. The false
    build exists so the generator can cross-check". limbVmOps_deployedBranch_ok re-reads
    config.rs at #eval time so the 'true' here cannot go stale. -/
def defaultQuotientLimbVmOps : Bool := true

/-! ## The recognizer hooks P-09e owns (hazard 7) -/

/-- The four recognizer calls the builder makes. Not a Rust type: it is the R9 rendering
    of the builder's dependency on QVM:3157-3238, which P-09e owns. Each field mirrors one
    Rust fn's signature, including the triple quotient_limb_subshape returns (shape,
    residue, matched terms). -/
structure QuotientShapeRecognizers where
  /-- rust: QVM:3176-3187 (quotient_pow5_base). -/
  pow5Base : QuotientExpr → Option QuotientExpr
  /-- rust: QVM:3157-3173 (quotient_limb_shape). -/
  limbShape : QuotientExpr → Option QuotientLimbShape
  /-- rust: QVM:3190-3227 (quotient_limb_subshape). -/
  limbSubshape : QuotientExpr → Option (QuotientLimbShape × QuotientExpr × List QuotientExpr)
  /-- rust: QVM:3231-3238 (quotient_modarith7_shape). -/
  modarith7Shape : QuotientExpr → Option QuotientModarith7Shape

/-- The conservative instantiation: nothing is recognized, so every expression takes the
    generic Fr path. This is the state the QVM:966-971 doc comment describes ("If a shape
    is not recognized exactly, the builder falls back to ordinary Fr VM opcodes") and it is
    what the gates in this file run under unless they say otherwise. -/
def noShapeRecognizers : QuotientShapeRecognizers :=
  { pow5Base := fun _ => none
    limbShape := fun _ => none
    limbSubshape := fun _ => none
    modarith7Shape := fun _ => none }

/-- The fuel the Rust does not need and Lean does (header, R10). Every generic-path call
    descends at least one node; the constant absorbs the per-term overhead of the affine
    fallback. Gated never to bind by emitterFuelNeverBinds_ok. -/
def emitFuel (expr : QuotientExpr) : Nat := 8 * (expr.nodeCount + 1)

/-! ## The builder state (rust: QVM:1071-1111) -/

/-- rust: QVM:1071-1087 (struct QuotientProgramBuilder) @formal-baseline. "Lowers quotient
    identities into VM bytecode and a constant table. The builder owns stack-depth
    accounting and all byte-level encoding. It emits an expression as an isolated stack
    computation followed by exactly one fold opcode, so identity boundaries are explicit
    and native callback markers can be interleaved safely."

    Hazard 2: 'bytes' is the append-only instruction buffer in PROGRAM order, index 0
    first, which is the same List Nat the P-09b interpreter indexes. Every mutation in
    this file appends; nothing rewrites or reorders a byte except compactQuotientRuns, and
    that is a separate function over a separate copy. -/
structure QuotientProgramBuilder where
  /-- rust: QVM:1078-1080 (bytes: Vec<u8>) - "Raw byte-oriented program before run
      compaction. All stack-depth accounting happens against this stream." -/
  bytes : List Nat
  /-- rust: QVM:1081 (consts: Vec<U256>) -/
  consts : List Word256
  /-- rust: QVM:1082 (const_slots: HashMap<U256, u16>) - assoc list, see the R6 note. -/
  constSlots : List (Word256 × Nat)
  /-- rust: QVM:1083 (vars: HashMap<String, QuotientExpr>) - assoc list, see R6. -/
  vars : List (String × QuotientExpr)
  /-- rust: QVM:1084 (stack_depth: usize) -/
  stackDepth : Nat
  /-- rust: QVM:1085 (max_stack: usize) -/
  maxStack : Nat
  /-- rust: QVM:1086 (limb_vm_ops: bool) -/
  limbVmOps : Bool
  deriving BEq

/-- rust: QVM:1089-1102 (impl Default for QuotientProgramBuilder) @formal-baseline.
    "Start an empty VM program with the crate's default limb-opcode policy." Named
    builderDefault rather than a Default instance because Lean's Default has no
    quotient-VM meaning to inherit and R1 forbids inventing one. -/
def builderDefault : QuotientProgramBuilder :=
  { bytes := []
    consts := []
    constSlots := []
    vars := []
    stackDepth := 0
    maxStack := 0
    limbVmOps := defaultQuotientLimbVmOps }

/-- rust: QVM:1104-1111 (QuotientProgramBuilder::with_limb_vm_ops) @formal-baseline.
    "Create a builder, optionally enabling limb-specialized opcode emission." -/
def withLimbVmOps (enabled : Bool) : QuotientProgramBuilder :=
  { builderDefault with limbVmOps := enabled }

/-! ## Byte and stack primitives (rust: QVM:1800-1881) - MOVED; WHAT MOVED 1 -/

/-- rust: QVM:1800-1803 (op0) @formal-baseline. "Emit a zero-operand opcode." Also the
    rendering of every bare self.bytes.push(op) in the file. -/
def op0 (s : QuotientProgramBuilder) (op : Nat) : QuotientProgramBuilder :=
  { s with bytes := s.bytes ++ [op] }

/-- rust: self.bytes.extend_from_slice(&..). -/
def appendBytes (s : QuotientProgramBuilder) (bs : List Nat) : QuotientProgramBuilder :=
  { s with bytes := s.bytes ++ bs }

/-- rust: self.bytes.push(b). -/
def pushByte (s : QuotientProgramBuilder) (b : Nat) : QuotientProgramBuilder :=
  appendBytes s [b]

/-- rust: QVM:1811-1815 (push_stack) @formal-baseline. "Record one pushed stack value and
    update the high-water mark." Accounting only: no byte is emitted. -/
def pushStackAcct (s : QuotientProgramBuilder) : QuotientProgramBuilder :=
  { s with stackDepth := s.stackDepth + 1, maxStack := max s.maxStack (s.stackDepth + 1) }

/-- rust: QVM:1817-1820 (pop_stack) @formal-baseline. "Record one consumed stack value."
    The Rust's checked_sub(1).expect("quotient VM stack underflow") is a real panic site
    (R4), so this is fallible. -/
def popStackAcct (s : QuotientProgramBuilder) : M QuotientProgramBuilder :=
  if s.stackDepth == 0 then
    panicAt siteStackUnderflow
  else
    .ok { s with stackDepth := s.stackDepth - 1 }

/-- rust: QVM:1805-1809 (op_binary) @formal-baseline. "Emit a binary stack opcode and
    update stack-depth accounting." -/
def opBinary (s : QuotientProgramBuilder) (op : Nat) : M QuotientProgramBuilder :=
  popStackAcct (op0 s op)

/-- rust: QVM:1822-1826 (u16) @formal-baseline. "Append a big-endian u16 operand." Hazard
    5's first boundary: the assert fires at 65536, not at 65535. -/
def emitU16 (s : QuotientProgramBuilder) (value : Nat) : M QuotientProgramBuilder :=
  if value > 0xffff then
    panicAt siteU16Overflow
  else
    .ok (appendBytes s [value / 256, value % 256])

/-- rust: QVM:1828-1832 (u24) @formal-baseline. "Append a big-endian 24-bit operand." The
    Rust writes the last three bytes of a 4-byte BE encoding; the assert fires at
    0x1000000. -/
def emitU24 (s : QuotientProgramBuilder) (value : Nat) : M QuotientProgramBuilder :=
  if value > 0x00ffffff then
    panicAt siteU24Overflow
  else
    .ok (appendBytes s [value / 65536 % 256, value / 256 % 256, value % 256])

/-- rust: QVM:1834-1837 (u32) @formal-baseline. "Append a big-endian u32 operand." No
    assert: the Rust's parameter is already a u32, so width is enforced by the caller
    (VT's quotientMem_noTruncation_ok records where that happens). -/
def emitU32 (s : QuotientProgramBuilder) (value : Nat) : M QuotientProgramBuilder :=
  .ok (appendBytes s [value / 16777216 % 256, value / 65536 % 256, value / 256 % 256,
    value % 256])

/-- The Rust's const_slots.get(&value) in one place, so the three readers cannot drift. -/
def constSlotOf (s : QuotientProgramBuilder) (value : Word256) : Option Nat :=
  (s.constSlots.find? (fun (k, _) => k == value)).map Prod.snd

/-- rust: QVM:1839-1850 (const_slot) @formal-baseline. "Return the stable constant-table
    slot for value, inserting if needed." Returns the new state and the slot, because the
    Rust mutates through &mut self and still hands a value back. -/
def constSlot (s : QuotientProgramBuilder) (value : Word256) :
    M (QuotientProgramBuilder × Nat) := do
  match constSlotOf s value with
  | some slot => .ok (s, slot)
  | none =>
      let slot := s.consts.length
      if slot > 0xffff then
        panicAt siteTooManyConsts
      else
        let s' : QuotientProgramBuilder :=
          { s with consts := s.consts ++ [value], constSlots := s.constSlots ++ [(value, slot)] }
        .ok (s', slot)

/-- rust: QVM:1852-1856 (const_fits_u8_slot) @formal-baseline. "Check whether value can be
    addressed by a one-byte constant slot." &self: it does NOT insert, which is the whole
    reason hazard 3 holds. The Rust's second arm is guarded by !contains_key, so a value
    already in the table is judged by its OWN slot and never by the table length. -/
def constFitsU8Slot (s : QuotientProgramBuilder) (value : Word256) : Bool :=
  match constSlotOf s value with
  | some slot => slot <= 255
  | none => s.consts.length <= 255

/-- rust: QVM:1858-1881 (peek_u8_const_slots) @formal-baseline. "Predict one-byte constant
    slots for a batch of values without insertion. This lets limb opcode recognition fail
    cleanly before mutating the constant table, so fallback lowering sees the same builder
    state it would have seen if recognition had never been attempted." Hazard 3's mechanism
    in one function: a pure prediction of what constSlot WOULD allocate, including the
    pending duplicates inside the batch. -/
def peekU8ConstSlots (s : QuotientProgramBuilder) (values : List Word256) :
    Option (List Nat) :=
  go s.consts.length values [] []
where
  go : Nat → List Word256 → List (Word256 × Nat) → List Nat → Option (List Nat)
  | _, [], _, slots => some slots.reverse
  | next, value :: rest, pending, slots =>
      match constSlotOf s value with
      | some slot => if slot > 255 then none else go next rest pending (slot :: slots)
      | none =>
          match pending.find? (fun (k, _) => k == value) with
          | some (_, slot) => if slot > 255 then none else go next rest pending (slot :: slots)
          | none =>
              let slot := next
              if slot > 255 then none
              else go (slot + 1) rest (pending ++ [(value, slot)]) (slot :: slots)

/-- rust: QVM:3533-3550 (modarith7_coeffs) @formal-baseline, ported verbatim including the
    != U256::ZERO guard that VT's coefficientOperands drops (header divergence note).
    MOVED into this package because emit_modarith7_shape's preflight needs it. -/
def modarith7Coeffs (shape : QuotientModarith7Shape) : List Word256 :=
  (if shape.constant.toNat == 0 then [] else [shape.constant])
    ++ (shape.lin.flatMap fun terms => terms.map (fun (coeff, _) => coeff))
    ++ (shape.rows.flatMap fun (_, terms) => terms.map (fun (coeff, _) => coeff))
    ++ (shape.pairwise.flatMap fun (_, _, terms) => terms)
    ++ (shape.memTerms.map (fun (coeff, _) => coeff))
    ++ (shape.productTerms.map (fun (coeff, _, _) => coeff))

/-- rust: QVM:1452-1463 (limb_shape_has_u8_const_slots) @formal-baseline. "Check whether
    all coefficients of a recognized limb shape fit u8 constant slots without mutating the
    builder." -/
def limbShapeHasU8ConstSlots (s : QuotientProgramBuilder) (shape : QuotientLimbShape) :
    Bool :=
  (peekU8ConstSlots s (QuotientLimbShape.coefficientOperands shape)).isSome

/-- rust: QVM:1446-1450 (modarith7_shape_has_u8_const_slots) @formal-baseline. "Check
    whether all coefficients of a fused affine limb identity fit one-byte constant slots
    without mutating the builder." -/
def modarith7ShapeHasU8ConstSlots (s : QuotientProgramBuilder)
    (shape : QuotientModarith7Shape) : Bool :=
  (peekU8ConstSlots s (modarith7Coeffs shape)).isSome

/-! ## Leaf flattening (rust: QVM:3093-3121) - MOVED; WHAT MOVED 3 -/

/-- rust: QVM:3093-3099 (quotient_leaf) @formal-baseline. The two non-recursive shapes of
    the grammar. -/
def quotientLeaf (expr : QuotientExpr) : Option QuotientLeaf :=
  match expr with
  | .const value => some (.const value)
  | .mem mem => some (.mem mem)
  | .add _ _ => none
  | .mul _ _ => none
  | .neg _ => none

/-- rust: QVM:3101-3121 (collect_product_leaves) @formal-baseline. "Flatten a pure
    multiplication tree into constant/memory leaves. This intentionally rejects sums and
    negations. Additive structure is handled by sum collection or by the generic emitter;
    fused product-add opcodes need a product that can be encoded directly." The Rust
    accumulates into a &mut Vec and returns a bool; the partial prefix it may have pushed
    before failing is discarded by its only caller (QVM:1622-1625), so Option (List ...)
    observes the same behaviour, and the do-block short-circuits where Rust's && does. -/
def collectProductLeaves (expr : QuotientExpr) : Option (List QuotientLeaf) :=
  match expr with
  | .mul lhs rhs => do
      let l ← collectProductLeaves lhs
      let r ← collectProductLeaves rhs
      some (l ++ r)
  | .const value => some [QuotientLeaf.const value]
  | .mem mem => some [QuotientLeaf.mem mem]
  | .add _ _ => none
  | .neg _ => none

/-! ## The simple emitters (rust: QVM:1597-1618) -/

/-- rust: QVM:1597-1607 (emit_const) @formal-baseline. "Emit a constant load, choosing the
    shortest constant-slot operand." Hazard 5: the choice is u8::try_from(slot), so slot
    255 takes the one-byte form and slot 256 takes the three-byte form. Note the slot is
    allocated BEFORE the encoding is chosen, so this is where a rejected shape could in
    principle leave a constant behind - which is why the preflight predicates must not
    call it. -/
def emitConst (s : QuotientProgramBuilder) (value : Word256) : M QuotientProgramBuilder := do
  let (s, slot) ← constSlot s value
  if slot <= 255 then
    .ok (pushByte (pushByte s qOpPushConstU8) slot)
  else
    emitU16 (pushByte s qOpPushConst) slot

/-- rust: QVM:1609-1618 (emit_mem_literal) @formal-baseline. "Emit a memory load, choosing
    the shortest literal-pointer operand." Hazard 5's second boundary: 0xffff takes
    PUSH_MEM_U16, 0x10000 takes PUSH_MEM_LITERAL. -/
def emitMemLiteral (s : QuotientProgramBuilder) (ptr : Nat) : M QuotientProgramBuilder :=
  if ptr <= 0xffff then
    emitU16 (pushByte s qOpPushMemU16) ptr
  else
    emitU32 (pushByte s qOpPushMemLiteral) ptr

/-! ## The fused product-add path (rust: QVM:1648-1798) -/

/-- rust: QVM:1648-1656 (product_add_fits_u8_slot) @formal-baseline. "Whether the fused
    product-add scalar (if any) still lands in a one-byte constant slot given the current
    constant table." &self, so it cannot insert. -/
def productAddFitsU8Slot (s : QuotientProgramBuilder) (product : QuotientProductAdd) : Bool :=
  match product with
  | .memMemConstU8 _ _ scalar => constFitsU8Slot s scalar
  | .constU8Mem scalar _ => constFitsU8Slot s scalar
  | .memMem _ _ => true

/-- rust: QVM:1658-1699 (product_add_macro) @formal-baseline. "Recognize product leaves
    that can be encoded as one fused add-mul op. The fused forms require literal u16
    memory pointers and, where a constant is present, a coefficient that can fit a u8
    const slot. Token memory is kept on the generic path because the fused byte layout
    stores raw pointers only." &self: the whole function is a predicate plus a shape, and
    that is why hazard 3 holds for try_emit_add_product. -/
def productAddMacro (s : QuotientProgramBuilder) (leaves : List QuotientLeaf) :
    Option QuotientProductAdd :=
  match foldLeftOpt step ([], []) leaves with
  | none => none
  | some (mems, consts) =>
      match mems, consts with
      | [lhs, rhs], [scalar] => some (.memMemConstU8 lhs rhs scalar)
      | [ptr], [scalar] => some (.constU8Mem scalar ptr)
      | [lhs, rhs], [] => some (.memMem lhs rhs)
      | _, _ => none
where
  step (st : List Nat × List Word256) (leaf : QuotientLeaf) :
      Option (List Nat × List Word256) :=
    let (mems, consts) := st
    match leaf with
    | .mem (.literal ptr) => if ptr <= 0xffff then some (mems ++ [ptr], consts) else none
    | .mem _ => none
    | .const value =>
        if constFitsU8Slot s value then some (mems, consts ++ [value]) else none

/-- rust: QVM:1701-1725 (emit_product_add) @formal-baseline. "Emit one fused add-mul
    accumulator operation." Stack effect zero, so no push/pop accounting: the caller's
    accumulator already holds the top. Each expect("const slot checked") is a panic site
    that the caller's product_add_fits_u8_slot re-check is what makes unreachable. -/
def emitProductAdd (s : QuotientProgramBuilder) (product : QuotientProductAdd) :
    M QuotientProgramBuilder :=
  match product with
  | .memMemConstU8 lhs rhs scalar => do
      let (s, slot) ← constSlot s scalar
      if slot > 255 then
        panicAt siteProductAddSlot
      else do
        let s ← emitU16 (pushByte s qOpAddMulMemMemConstU8) lhs
        let s ← emitU16 s rhs
        .ok (pushByte s slot)
  | .constU8Mem scalar ptr => do
      let (s, slot) ← constSlot s scalar
      if slot > 255 then
        panicAt siteProductAddSlot2
      else do
        let s ← emitU16 (pushByte s qOpAddMulConstU8MemU16) ptr
        .ok (pushByte s slot)
  | .memMem lhs rhs => do
      let s ← emitU16 (pushByte s qOpAddMulMemMem) lhs
      emitU16 s rhs

/-- rust: QVM:1766-1798 (emit_acc_leaf) @formal-baseline. "Try to apply a constant or
    short-memory accumulator opcode to q_top." The false arms emit NOTHING: the constant
    arm always returns true (it allocates a slot and emits), and the memory arm returns
    false before touching bytes when the pointer does not fit a u16. -/
def emitAccLeaf (s : QuotientProgramBuilder) (leaf : QuotientLeaf)
    (constU8Op constOp memU16Op : Nat) : M (Bool × QuotientProgramBuilder) :=
  match leaf with
  | .const value => do
      let (s, slot) ← constSlot s value
      if slot <= 255 then
        .ok (true, pushByte (pushByte s constU8Op) slot)
      else do
        let s ← emitU16 (pushByte s constOp) slot
        .ok (true, s)
  | .mem (.literal ptr) =>
      if ptr <= 0xffff then do
        let s ← emitU16 (pushByte s memU16Op) ptr
        .ok (true, s)
      else
        .ok (false, s)
  | .mem _ => .ok (false, s)

/-! ## The limb and MODARITH7 shape emitters (rust: QVM:1465-1595) -/

/-- rust: the inner 'for (coeff, ptr) in terms' bodies of emit_limb_shape and
    emit_modarith7_shape. A fold because the Rust is a loop over a Vec; the slot is
    allocated, then the slot byte, then the u16 pointer, in that order, every time. -/
def termFold (s : QuotientProgramBuilder) (terms : List (Word256 × Nat))
    (site : String) : M QuotientProgramBuilder :=
  foldLeftM (fun (acc : QuotientProgramBuilder) (cp : Word256 × Nat) => do
      let (coeff, ptr) := cp
      let (acc, slot) ← constSlot acc coeff
      if slot > 255 then panicAt site
      else do
        let acc ← emitU16 (pushByte acc slot) ptr
        .ok acc) s terms

/-- rust: QVM:1465-1516 (emit_limb_shape) @formal-baseline. "Emit the byte-level
    representation of a pre-validated limb shape." The three expect("... const slot
    checked") sites are the ones hazard 3's post-residue re-check protects. -/
def emitLimbShape (s : QuotientProgramBuilder) (shape : QuotientLimbShape) :
    M QuotientProgramBuilder := do
  let s ← limbCase s shape
  .ok (pushStackAcct s)
where
  limbCase : QuotientProgramBuilder → QuotientLimbShape → M QuotientProgramBuilder
    | s, .lin7 terms => termFold (pushByte s qOpLin7) terms siteLin7Slot
    | s, .bilin7Row lhs terms => do
        let s ← emitU16 (pushByte s qOpBilin7Row) lhs
        termFold s terms siteBilin7RowSlot
    | s, .bilin7Pairwise lhsBase rhsBase coeffs => do
        let s ← emitU16 (pushByte s qOpBilin7Pairwise) lhsBase
        let s ← emitU16 s rhsBase
        foldLeftM (fun (acc : QuotientProgramBuilder) (coeff : Word256) => do
            let (acc, slot) ← constSlot acc coeff
            if slot > 255 then panicAt siteBilin7PairwiseSlot
            else .ok (pushByte acc slot)) s coeffs

/-- rust: QVM:1518-1595 (emit_modarith7_shape) @formal-baseline. "Emit the dynamic
    byte-level representation of one fused affine foreign-field/ECC identity." The header
    order is the ABI: opcode, flags, optional cond pointer, optional const slot, then the
    five count bytes in lin / row / pairwise / mem / product order, then the five blocks
    in the same order. QVR:488-490 warns that the mem block's (slot, ptr) order is NOT the
    standalone helper's; the interpreter reads it in this order, so a swap here is a
    silent miscompilation the hazard-1 gate would catch. -/
def emitModarith7Shape (s : QuotientProgramBuilder) (shape : QuotientModarith7Shape) :
    M QuotientProgramBuilder :=
  if shape.lin.length > 255 || shape.rows.length > 255 || shape.pairwise.length > 255 ||
      shape.memTerms.length > 255 || shape.productTerms.length > 255 then
    panicAt siteModarith7Count
  else do
    let flags := (if shape.cond.isSome then qModarith7FlagCond else 0) |||
      (if shape.constant.toNat != 0 then qModarith7FlagConst else 0)
    let s := pushByte (pushByte s qOpModarith7) flags
    let condM : M QuotientProgramBuilder := match shape.cond with
      | some cond => emitU16 s cond
      | none => .ok s
    let s ← condM
    let constM : M QuotientProgramBuilder :=
      if shape.constant.toNat != 0 then do
        let (s, slot) ← constSlot s shape.constant
        if slot > 255 then panicAt siteModarith7ConstSlot
        else .ok (pushByte s slot)
      else .ok s
    let s ← constM
    let counts := [shape.lin.length, shape.rows.length, shape.pairwise.length,
      shape.memTerms.length, shape.productTerms.length]
    let s := counts.foldl pushByte s
    let s ← foldLeftM (fun (acc : QuotientProgramBuilder) (terms : List (Word256 × Nat)) =>
      termFold acc terms siteModarith7LinSlot) s shape.lin
    let s ← foldLeftM (fun (acc : QuotientProgramBuilder) (row : Nat × List (Word256 × Nat)) => do
        let (lhs, terms) := row
        let acc ← emitU16 acc lhs
        termFold acc terms siteModarith7RowSlot) s shape.rows
    let s ← foldLeftM (fun (acc : QuotientProgramBuilder) (pw : Nat × Nat × List Word256) => do
        let (lhsBase, rhsBase, coeffs) := pw
        let acc ← emitU16 acc lhsBase
        let acc ← emitU16 acc rhsBase
        foldLeftM (fun (acc' : QuotientProgramBuilder) (coeff : Word256) => do
            let (acc', slot) ← constSlot acc' coeff
            if slot > 255 then panicAt siteModarith7PairwiseSlot
            else .ok (pushByte acc' slot)) acc coeffs) s shape.pairwise
    let s ← termFold s shape.memTerms siteModarith7MemSlot
    let s ← foldLeftM (fun (acc : QuotientProgramBuilder) (tp : Word256 × Nat × Nat) => do
        let (coeff, lhs, rhs) := tp
        let (acc, slot) ← constSlot acc coeff
        if slot > 255 then panicAt siteModarith7ProductSlot
        else do
          let acc ← emitU16 (pushByte acc slot) lhs
          emitU16 acc rhs) s shape.productTerms
    .ok (pushStackAcct s)

/-! ## The expression emitter (rust: QVM:1283-1444) -/

/-- rust: QVM:1406-1426 (try_emit_limb_shape) @formal-baseline. "Try to replace a full
    expression with one limb-specialized opcode. The const-slot preflight is part of the
    ABI justification: limb opcodes carry coefficient slots as single bytes, so either
    every coefficient can be addressed by u8 after deterministic insertion or the
    expression must use the generic VM path." Hazard 6's branch: limb_vm_ops == false
    short-circuits before the recognizer is even consulted. -/
def tryEmitLimbShape (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (expr : QuotientExpr) : M (Bool × QuotientProgramBuilder) :=
  if !s.limbVmOps then
    .ok (false, s)
  else
    match r.limbShape expr with
    | none => .ok (false, s)
    | some shape =>
        if !limbShapeHasU8ConstSlots s shape then
          .ok (false, s)
        else do
          let s ← emitLimbShape s shape
          .ok (true, s)

/-- rust: QVM:1428-1444 (try_emit_modarith7_shape) @formal-baseline. "Try to replace a
    whole affine foreign-field/ECC identity with one dynamic byte-only opcode." -/
def tryEmitModarith7Shape (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (expr : QuotientExpr) : M (Bool × QuotientProgramBuilder) :=
  if !s.limbVmOps then
    .ok (false, s)
  else
    match r.modarith7Shape expr with
    | none => .ok (false, s)
    | some shape =>
        if !modarith7ShapeHasU8ConstSlots s shape then
          .ok (false, s)
        else do
          let s ← emitModarith7Shape s shape
          .ok (true, s)

-- The six mutually recursive emitters. Lean needs the group because emit_expr calls the
-- peepholes and three of the peepholes call emit_expr back; the Rust gets away with it
-- because &mut self is late-bound. Fuel is the first argument of every member so the
-- group has one decreasing measure (header, R10).
mutual

/-- rust: QVM:1283-1349 (emit_expr) @formal-baseline. "Emit a QuotientExpr using ordinary
    VM bytecode plus local peepholes. The method leaves the expression value on top of the
    VM stack. It first tries structural limb compression, then falls back to
    accumulator-leaf and fused product-add opcodes before using generic stack add/mul/
    neg." The four peephole attempts are in the Rust's order: pow5, MODARITH7, the LIN7
    family, then decomposition. -/
def emitExpr (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → QuotientExpr → M QuotientProgramBuilder
  | 0, _, _ => panicAt siteEmitFuel
  | fuel + 1, s, expr => do
      let (hit, s) ← tryEmitPow5 r fuel s expr
      if hit then
        .ok s
      else do
        let (hit, s) ← tryEmitModarith7Shape r s expr
        if hit then
          .ok s
        else do
          let (hit, s) ← tryEmitLimbShape r s expr
          if hit then
            .ok s
          else do
            let (hit, s) ← tryEmitLimbDecomposition r fuel s expr
            if hit then
              .ok s
            else
              match expr with
              | .const value => do let s ← emitConst s value; .ok (pushStackAcct s)
              | .mem (.literal ptr) => do let s ← emitMemLiteral s ptr; .ok (pushStackAcct s)
              | .mem (.token token) =>
                  .ok (pushStackAcct (pushByte (pushByte s qOpPushMemToken) token))
              | .mem (.tokenOffset token offset) => do
                  let s ← emitU32 (pushByte (pushByte s qOpPushMemTokenOffset) token) offset
                  .ok (pushStackAcct s)
              | .add lhs rhs => do
                  let (hit, s) ← tryEmitAddProduct r fuel s lhs rhs
                  if hit then
                    .ok s
                  else do
                    let (hit, s) ← tryEmitAddProduct r fuel s rhs lhs
                    if hit then
                      .ok s
                    else
                      emitBinaryExpr r fuel s lhs rhs qOpAdd qOpAddConstU8 qOpAddConst
                        qOpAddMemU16
              | .mul lhs rhs =>
                  emitBinaryExpr r fuel s lhs rhs qOpMul qOpMulConstU8 qOpMulConst
                    qOpMulMemU16
              | .neg inner => do
                  let s ← emitExpr r fuel s inner
                  .ok (op0 s qOpNeg)
termination_by fuel => fuel

/-- rust: QVM:1351-1359 (try_emit_pow5) @formal-baseline. "Try to replace a repeated-factor
    fifth power with one opcode." The recognizer is a hook; the rejection path touches
    nothing. -/
def tryEmitPow5 (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → QuotientExpr → M (Bool × QuotientProgramBuilder)
  | 0, _, _ => panicAt siteEmitFuel
  | fuel + 1, s, expr =>
      match r.pow5Base expr with
      | none => .ok (false, s)
      | some base => do
          let s ← emitExpr r fuel s base
          .ok (true, pushByte s qOpPow5)
termination_by fuel => fuel

/-- rust: QVM:1361-1387 (try_emit_limb_decomposition) @formal-baseline. "Try to extract one
    limb-specialized subexpression from a larger sum." The double check is the point: the
    preflight runs against the table as it stands, the residue is emitted (which can insert
    constants), and the check runs AGAIN - the comment at QVM:1373-1379 is the Rust
    admitting that a single preflight used to panic. Both arms return true, so this is a
    commit-after-mutation, not a half-emit. -/
def tryEmitLimbDecomposition (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → QuotientExpr → M (Bool × QuotientProgramBuilder)
  | 0, _, _ => panicAt siteEmitFuel
  | fuel + 1, s, expr =>
      if !s.limbVmOps then
        .ok (false, s)
      else
        match r.limbSubshape expr with
        | none => .ok (false, s)
        | some (shape, residue, matched) =>
            if !limbShapeHasU8ConstSlots s shape then
              .ok (false, s)
            else do
              let s ← emitExpr r fuel s residue
              if limbShapeHasU8ConstSlots s shape then do
                let s ← emitLimbShape s shape
                let s ← opBinary s qOpAdd
                .ok (true, s)
              else do
                let s ← emitAffineTerms r fuel s matched
                let s ← opBinary s qOpAdd
                .ok (true, s)
termination_by fuel => fuel

/-- rust: QVM:1389-1404 (emit_affine_terms) @formal-baseline. "Emit the sum of terms with
    generic stack ops, leaving one value on the stack. Each entry is one recognized
    affine/bilinear term (a scaled memory load or product), so emitting it cannot re-enter
    the limb-decomposition peephole, and its coefficients use emit_const's u16-capable
    slots. This is the panic-free fallback for a recognized limb shape whose coefficients
    no longer fit one-byte constant slots after intervening emission. The slice is always
    non-empty (a recognized subshape uses at least one term)." That last sentence is a
    recognizer POSTCONDITION the type does not carry: a hook returning an empty matched
    list makes the following op_binary(ADD) pop a stack that only holds the residue.
    emptyMatchedHookIsAFrontier_ok shows that this is a real contract between the two
    packages rather than something Lean enforces. -/
def emitAffineTerms (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → List QuotientExpr → M QuotientProgramBuilder
  | 0, _, _ => panicAt siteEmitFuel
  | _, s, [] => .ok s
  | fuel + 1, s, term :: rest => do
      let s ← emitExpr r fuel s term
      emitAffineTermsRest r fuel s rest
termination_by fuel => fuel

/-- The tail of emit_affine_terms: every term after the first is followed by ADD, which is
    what the Rust's 'if idx > 0' inside the enumerate loop does. Split out so the
    recursion is on the fuel. -/
def emitAffineTermsRest (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → List QuotientExpr → M QuotientProgramBuilder
  | 0, _, _ => panicAt siteEmitFuel
  | _, s, [] => .ok s
  | fuel + 1, s, term :: rest => do
      let s ← emitExpr r fuel s term
      let s ← opBinary s qOpAdd
      emitAffineTermsRest r fuel s rest
termination_by fuel => fuel

/-- rust: QVM:1620-1646 (try_emit_add_product) @formal-baseline. "Try to emit base +
    product as a fused accumulator opcode." Both rejections happen before any byte is
    written; after emit_expr(base) the decision is already made and the two arms differ
    only in encoding. -/
def tryEmitAddProduct (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → QuotientExpr → QuotientExpr →
    M (Bool × QuotientProgramBuilder)
  | 0, _, _, _ => panicAt siteEmitFuel
  | fuel + 1, s, base, product =>
      match collectProductLeaves product with
      | none => .ok (false, s)
      | some leaves =>
          match productAddMacro s leaves with
          | none => .ok (false, s)
          | some fused => do
              let s ← emitExpr r fuel s base
              if productAddFitsU8Slot s fused then do
                let s ← emitProductAdd s fused
                .ok (true, s)
              else do
                let s ← emitExpr r fuel s product
                let s ← opBinary s qOpAdd
                .ok (true, s)
termination_by fuel => fuel

/-- rust: QVM:1727-1764 (emit_binary_expr) @formal-baseline. "Emit a binary expression with
    accumulator-leaf peepholes. If one side is a constant or short memory load, the VM can
    update the other side's top-of-stack directly with ADD_CONST, MUL_MEM_U16, and related
    opcodes. Otherwise both operands are pushed and a generic stack operation combines
    them." The rhs side is tried first, then lhs. The leaf test is pure, so the only
    mutation before a false from emit_acc_leaf is the emit_expr of the OTHER side, which
    is not a rejection but the fallback path. -/
def emitBinaryExpr (r : QuotientShapeRecognizers) :
    Nat → QuotientProgramBuilder → QuotientExpr → QuotientExpr → Nat → Nat → Nat → Nat →
    M QuotientProgramBuilder
  | 0, _, _, _, _, _, _, _ => panicAt siteEmitFuel
  | fuel + 1, s, lhs, rhs, stackOp, constU8Op, constOp, memU16Op =>
      match quotientLeaf rhs with
      | some leaf => do
          let s ← emitExpr r fuel s lhs
          let res ← emitAccLeaf s leaf constU8Op constOp memU16Op
          match res with
          | (true, s) => .ok s
          | (false, s) => do
              let s ← emitExpr r fuel s rhs
              opBinary s stackOp
      | none =>
          match quotientLeaf lhs with
          | some leaf => do
              let s ← emitExpr r fuel s rhs
              let res ← emitAccLeaf s leaf constU8Op constOp memU16Op
              match res with
              | (true, s) => .ok s
              | (false, s) => do
                  let s ← emitExpr r fuel s lhs
                  opBinary s stackOp
          | none => do
              let s ← emitExpr r fuel s lhs
              let s ← emitExpr r fuel s rhs
              opBinary s stackOp
termination_by fuel => fuel

end

/-- The public entry: emit_expr at the Rust's &mut self call site, with the fuel the Rust
    does not need (header). -/
def emitExprTop (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (expr : QuotientExpr) : M QuotientProgramBuilder :=
  emitExpr r (emitFuel expr) s expr

/-! ## Identity boundaries (rust: QVM:1113-1231) -/

/-- rust: QVM:1137-1163 (fold_identity) @formal-baseline. "Emit the fold opcode for the
    completed top-of-stack identity value." The u24((idx << 16) | gap) packing is the
    selector-fold ABI: 8 bits of selector index over 16 bits of gap. Note the pop happens
    in BOTH arms but is written twice in the Rust - once inside the selector arm and once
    in the trailing 'if matches!(target, Main)' - so exactly one pop per target. -/
def foldIdentity (s : QuotientProgramBuilder) (target : QuotientTarget)
    (selectorGap : Option Nat) : M QuotientProgramBuilder :=
  match target with
  | .main => do
      let s := op0 s qOpFoldMain
      popStackAcct s
  | .selector idx => do
      let gap ← match selectorGap with
        | none => panicAt siteNoSelectorGap
        | some gap => .ok gap
      if idx > 255 then
        panicAt siteSelectorIdxWidth
      else if gap > 0xffff then
        panicAt siteSelectorGapWidth
      else do
        let s := pushByte s qOpFoldSelector
        let s ← emitU24 s ((idx * 65536) ||| gap)
        popStackAcct s

/-- rust: QVM:1113-1135 (identity_expr) @formal-baseline. "Emit one complete quotient
    identity and its fold target. The operand stack is reset at the start and must be empty
    at the end. That invariant is the reason callbacks can share the same stream: the Yul
    interpreter is allowed to clear q_top and reuse q_sp whenever a native marker appears
    between identities." max_stack is deliberately NOT reset: it is the high-water mark of
    the whole program, not of one identity. -/
def identityExpr (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder)
    (expr : QuotientExpr) (target : QuotientTarget) (selectorGap : Option Nat) :
    M QuotientProgramBuilder := do
  let s := { s with vars := [], stackDepth := 0 }
  let s ← emitExprTop r s expr
  let s ← foldIdentity s target selectorGap
  if s.stackDepth != 0 then
    panicAt siteStackLeak
  else
    .ok s

/-- rust: QVM:1165-1179 (native_permutation) @formal-baseline. "Emit the native
    permutation marker." The assert_eq!(stack_depth, 0) is the identity-boundary invariant
    QVM:1125-1127 says lets callbacks share the stream. -/
def nativePermutation (s : QuotientProgramBuilder) : M QuotientProgramBuilder :=
  if s.stackDepth != 0 then
    panicAt siteNativePermStack
  else
    .ok (pushByte s qOpNativePermutation)

/-- rust: QVM:1181-1192 (native_lookup) @formal-baseline. "Emit the native lookup marker." -/
def nativeLookup (s : QuotientProgramBuilder) : M QuotientProgramBuilder :=
  if s.stackDepth != 0 then
    panicAt siteNativeLookupStack
  else
    .ok (pushByte s qOpNativeLookup)

/-- rust: QVM:1194-1209 (native_identity) @formal-baseline. "Emit a native heavy-identity
    marker addressed by native_idx. The marker is an execution-plan choice, not a different
    identity." The u16 width check is u16's own. -/
def nativeIdentity (s : QuotientProgramBuilder) (nativeIdx : Nat) :
    M QuotientProgramBuilder := do
  if s.stackDepth != 0 then
    panicAt siteNativeIdentityStack
  else do
    let s := pushByte s qOpNativeIdentity
    emitU16 s nativeIdx

/-! ## The Yul assignment bridge (rust: QVM:1233-1281, plus its parser helpers) -
    MOVED; WHAT MOVED 4 -/

/-- Rust str::trim_start. The generated Yul this parser sees is ASCII; recorded rather than
    hidden. -/
def trimStartStr (s : String) : String :=
  String.ofList (s.toList.dropWhile (fun c => c.isWhitespace))

/-- The other half of Rust str::trim. -/
def trimEndStr (s : String) : String :=
  String.ofList ((s.toList.reverse).dropWhile (fun c => c.isWhitespace)).reverse

/-- rust: the .trim() calls at QVM:1240, 1251, 1254, 1261, 1268, 4086, 4105, 4111,
    4186-4187, 4238. -/
def trimStr (s : String) : String := trimStartStr (trimEndStr s)

/-- rust: str::strip_prefix as used at QVM:4112, 4177, 4249 and 4250. -/
def dropPrefixStr (pfx : String) (s : String) : Option String :=
  let pc := pfx.toList
  let sc := s.toList
  if pc.isPrefixOf sc then some (String.ofList (sc.drop pc.length)) else none

/-- rust: str::split_once(sep) as used at QVM:4185. Splits on the FIRST occurrence. -/
def splitOnceStr (sep : String) (s : String) : Option (String × String) :=
  go s.toList []
where
  go : List Char → List Char → Option (String × String)
  | cs, acc =>
      if sep.toList.isPrefixOf cs then
        some (String.ofList acc.reverse, String.ofList (cs.drop sep.length))
      else
        match cs with
        | [] => none
        | c :: rest => go rest (c :: acc)

/-- rust: QVM:4257-4275 (split_top_level) @formal-baseline. "Split a comma-separated
    argument list while respecting nested calls." The checked_sub(1).expect("balanced
    quotient expression") on a closing paren is a real panic site: an unbalanced argument
    list aborts codegen rather than mis-parsing. -/
def splitTopLevel (input : String) : M (List String) :=
  go input.toList 0 [] ""
where
  go : List Char → Nat → List String → String → M (List String)
  | [], _, args, cur => .ok (args ++ [trimStr cur])
  | '(' :: rest, depth, args, cur => go rest (depth + 1) args (cur.push '(')
  | ')' :: _, 0, _, _ => panicAt siteUnbalanced
  | ')' :: rest, depth + 1, args, cur => go rest depth args (cur.push ')')
  | ',' :: rest, 0, args, cur => go rest 0 (args ++ [trimStr cur]) ""
  | c :: rest, depth, args, cur => go rest depth args (cur.push c)

/-- rust: QVM:4246-4255 (call_args) @formal-baseline. Returns none when the text is not a
    call of 'name'; a call of 'name' with an unbalanced body is the split_top_level panic,
    which is why the result is M (Option ...). -/
def callArgs (expr name : String) : M (Option (List String)) := do
  let expr := trimStr expr
  match dropPrefixStr name expr with
  | none => .ok none
  | some rest =>
      match dropPrefixStr "(" (trimStartStr rest) with
      | none => .ok none
      | some inner =>
          match inner.toList.reverse with
          | ')' :: _ => do
              let args ← splitTopLevel (String.ofList inner.toList.dropLast)
              .ok (some args)
          | _ => .ok none

/-- rust: QVM:4103-4107 (is_literal) @formal-baseline. "Return whether a string is a
    decimal or hexadecimal integer literal." Note how shallow this is: a leading digit or a
    0x prefix and nothing else, so '1f' counts as a literal and then fails to parse. -/
def isLiteral (value : String) : Bool :=
  let value := trimStr value
  match dropPrefixStr "0x" value with
  | some _ => true
  | none =>
      match value.toList.head? with
      | some c => c >= '0' && c <= '9'
      | none => false

/-- The digit of a radix, or none: U256::from_str_radix's per-character failure. -/
def radixDigit (radix : Nat) (c : Char) : Option Nat :=
  let d :=
    if c >= '0' && c <= '9' then c.toNat - '0'.toNat
    else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
    else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
    else 255
  if d < radix then some d else none

/-- rust: QVM:4109-4119 (parse_u256) @formal-baseline. "Parse a decimal or hexadecimal
    U256 literal." U256::from_str_radix rejects an empty string, a non-digit and any value
    above 2^256-1, and each of those is the unwrap_or_else(panic!). -/
def parseU256 (value : String) : M Word256 :=
  let value := trimStr value
  match dropPrefixStr "0x" value with
  | some hex => go hex.toList 16 0 value
  | none => go value.toList 10 0 value
where
  go : List Char → Nat → Nat → String → M Word256
  | [], _, acc, whole =>
      if acc >= 2^256 then
        panicAt (siteBadLiteral ++ whole ++ ")")
      else
        .ok (BitVec.ofNat 256 acc)
  | c :: rest, radix, acc, whole =>
      match radixDigit radix c with
      | none => panicAt (siteBadLiteral ++ whole ++ ")")
      | some d => go rest radix (acc * radix + d) whole

/-- rust: QVM:4135-4142 (parse_u32_literal) @formal-baseline. "Parse a literal if it fits
    in u32." -/
def parseU32Literal (value : String) : M (Option Nat) :=
  if !isLiteral value then
    .ok none
  else do
    let parsed ← parseU256 value
    .ok (if parsed.toNat < 2^32 then some parsed.toNat else none)

/-- rust: QVM:2845-2850 (quotient_mem_token_from_name) @formal-baseline. "Resolve a
    generated Yul memory symbol name to its compact token." Reads VT's
    quotientMemTokenTable; find_map becomes find?. -/
def quotientMemTokenFromName (name : String) : Option Nat :=
  (quotientMemTokenTable.find? (fun spec => spec.name == name)).map (fun spec => spec.token)

/-- rust: QVM:4153-4156 (mem_token) @formal-baseline. "Resolve a generated Yul memory
    symbol to a VM token." -/
def memToken (name : String) : Option Nat := quotientMemTokenFromName name

/-- rust: QVM:4084-4101 (parse_mem) @formal-baseline. "Parse a generated Yul memory pointer
    expression into a VM memory reference." Three panics: an unsupported base, an
    unsupported offset, and a pointer that is none of the three forms. -/
def parseMem (ptr : String) : M QuotientMem := do
  let ptr := trimStr ptr
  match ← parseU32Literal ptr with
  | some value => .ok (QuotientMem.literal value)
  | none =>
      match memToken ptr with
      | some token => .ok (QuotientMem.token token)
      | none =>
          match ← callArgs ptr "add" with
          | some args =>
              if args.length != 2 then
                panicAt siteAddPointerArity
              else do
                let base := trimStr (args.getD 0 "")
                let offsetText := trimStr (args.getD 1 "")
                match memToken base with
                | none => panicAt (siteMloadBase ++ base ++ ")")
                | some token =>
                    match ← parseU32Literal offsetText with
                    | none => panicAt (siteMloadOffset ++ offsetText ++ ")")
                    | some offset => .ok (QuotientMem.tokenOffset token offset)
          | none => panicAt (siteMloadPointer ++ ptr ++ ")")

/-- rust: QVM:4158-4172 (struct YulAssignment) @formal-baseline. "Parsed form of the
    simple Yul assignments emitted by Evaluator. The parser is deliberately shallow. It is
    not a Yul parser; it accepts only assignment syntax that this generator emits, which
    makes unsupported changes fail loudly during code generation instead of silently
    changing verifier semantics." -/
structure YulAssignment where
  /-- rust: QVM:4166-4167 (dst: String) - "Destination variable name." -/
  dst : String
  /-- rust: QVM:4168-4169 (expr: String) - "Right-hand expression as source text." -/
  expr : String
  /-- rust: QVM:4170-4171 (has_let: bool) - "Whether the assignment was introduced with
      let." -/
  hasLet : Bool
  deriving BEq

/-- rust: QVM:4174-4196 (yul_assignment) @formal-baseline. "Parse a generated Yul
    assignment line." The 'let' keyword must be followed by whitespace, so 'lett' is not an
    assignment; an empty dst or expr is not either. -/
def yulAssignment (line : String) : Option YulAssignment :=
  let line := trimStr line
  let decoded : Option (Bool × String) :=
    match dropPrefixStr "let" line with
    | some rest =>
        match rest.toList.head? with
        | some c => if c.isWhitespace then some (true, trimStartStr rest) else none
        | none => none
    | none => some (false, line)
  match decoded with
  | none => none
  | some (hasLet, rest) =>
      match splitOnceStr ":=" rest with
      | none => none
      | some (dst, expr) =>
          let dst := trimStr dst
          let expr := trimStr expr
          if dst == "" || expr == "" then none
          else some { dst := dst, expr := expr, hasLet := hasLet }

/-- The fuel parse_expr needs because Lean cannot see that an argument list is made of
    strictly shorter strings (header, R10). -/
def parseFuel (expr : String) : Nat := expr.length + 8

/-- rust: QVM:1245-1281 (parse_expr) @formal-baseline. "Parse a generated Yul expression
    into QuotientExpr. Supported operations are exactly the Fr operations emitted by
    Evaluator: addmod(_, _, r), mulmod(_, _, r), sub(r, _), mload(_), literals, and
    previously assigned variables." Takes &self - it reads vars and mutates nothing. The
    arity asserts are panic sites (R4). -/
def parseExpr (s : QuotientProgramBuilder) : Nat → String → M QuotientExpr
  | 0, _ => panicAt siteParseFuel
  | fuel + 1, expr => do
      let expr := trimStr expr
      match ← callArgs expr "addmod" with
      | some args =>
          if args.length != 3 then
            panicAt siteAddmodArity
          else if trimStr (args.getD 2 "") != "r" then
            panicAt siteAddmodModulus
          else do
            let lhs ← parseExpr s fuel (args.getD 0 "")
            let rhs ← parseExpr s fuel (args.getD 1 "")
            .ok (QuotientExpr.add lhs rhs)
      | none =>
          match ← callArgs expr "mulmod" with
          | some args =>
              if args.length != 3 then
                panicAt siteMulmodArity
              else if trimStr (args.getD 2 "") != "r" then
                panicAt siteMulmodModulus
              else do
                let lhs ← parseExpr s fuel (args.getD 0 "")
                let rhs ← parseExpr s fuel (args.getD 1 "")
                .ok (QuotientExpr.mul lhs rhs)
          | none =>
              match ← callArgs expr "sub" with
              | some args =>
                  if args.length != 2 then
                    panicAt siteSubArity
                  else if trimStr (args.getD 0 "") != "r" then
                    panicAt siteSubForm
                  else do
                    let inner ← parseExpr s fuel (args.getD 1 "")
                    .ok (QuotientExpr.neg inner)
              | none =>
                  match ← callArgs expr "mload" with
                  | some args =>
                      if args.length != 1 then
                        panicAt siteMloadArity
                      else
                        parseMem (args.getD 0 "") >>= fun m => .ok (QuotientExpr.mem m)
                  | none =>
                      if isLiteral expr then
                        parseU256 expr >>= fun v => .ok (QuotientExpr.const v)
                      else
                        match s.vars.find? (fun (k, _) => k == expr) with
                        | some (_, value) => .ok value
                        | none => panicAt (siteUnknownVar ++ expr ++ ")")
termination_by fuel => fuel

/-- The public parse_expr. -/
def parseExprTop (s : QuotientProgramBuilder) (expr : String) : M QuotientExpr :=
  parseExpr s (parseFuel expr) expr

/-- rust: QVM:1233-1243 (assignment) @formal-baseline. "Parse and remember one generated
    Yul assignment. This is the bridge for identities that do not yet have typed
    Expression<Fq> lowering. Only the evaluator's simple arithmetic subset is accepted;
    unsupported syntax is rejected during code generation." HashMap::insert REPLACES, so
    the assoc-list insert has to erase the key first. -/
def assignment (s : QuotientProgramBuilder) (line : String) : M QuotientProgramBuilder := do
  let a ← match yulAssignment line with
    | some a => .ok a
    | none => panicAt (siteUnsupportedAssignment ++ trimStr line ++ ")")
  let expr ← parseExprTop s a.expr
  .ok { s with vars := (a.dst, expr) :: (s.vars.filter fun (k, _) => k != a.dst) }

/-! ## Bytecode walking (rust: QVM:3008-3059) - the minimum compaction needs -/

/-- The builder-side byte read. mod.rs:2817-2824 reads operands by direct slice index,
    which PANICS past the end; that is a different fault class from QVR's bounds-checked
    byte_at, and the port keeps the distinction (R4; VT hazard 2's precedent). -/
def walkByte (bytes : List Nat) (idx : Nat) : M Nat :=
  match bytes.drop idx with
  | b :: _ => .ok b
  | [] => panicAt siteWalkRead

/-- rust: QVM:2817-2819 (read_u16) @formal-baseline. -/
def walkReadU16 (bytes : List Nat) (idx : Nat) : M Nat := do
  let b0 ← walkByte bytes idx
  let b1 ← walkByte bytes (idx + 1)
  .ok (b0 * 256 + b1)

/-- rust: QVM:3027-3033 (quotient_affine_sum_op_len) @formal-baseline. "Decode AFFINE_SUM
    length in trusted/internal bytecode walks." -/
def quotientAffineSumOpLen (bytes : List Nat) (idx : Nat) : M Nat := do
  let linCount ← walkReadU16 bytes (idx + 1)
  let productCount ← walkReadU16 bytes (idx + 3)
  .ok (1 + 2 * 2 + linCount * (2 + 1) + productCount * (2 * 2 + 1))

/-- rust: QVM:3036-3059 (quotient_modarith7_op_len) @formal-baseline. "Decode MODARITH7
    length in trusted/internal bytecode walks." The five count bytes and the five block
    widths are the same header emit_modarith7_shape writes; the flag bits decide whether
    the cond pointer and the const slot are present. -/
def quotientModarith7OpLen (bytes : List Nat) (idx : Nat) : M Nat := do
  let flags ← walkByte bytes (idx + 1)
  let afterFlags := idx + 2
  let afterCond := if flags &&& qModarith7FlagCond != 0 then afterFlags + 2 else afterFlags
  let afterConst := if flags &&& qModarith7FlagConst != 0 then afterCond + 1 else afterCond
  let linCount ← walkByte bytes afterConst
  let rowCount ← walkByte bytes (afterConst + 1)
  let pairwiseCount ← walkByte bytes (afterConst + 2)
  let memCount ← walkByte bytes (afterConst + 3)
  let productCount ← walkByte bytes (afterConst + 4)
  let cursor := afterConst + 5
  let cursor := cursor + linCount * quotientVmLimbs * (1 + 2)
  let cursor := cursor + rowCount * (2 + quotientVmLimbs * (1 + 2))
  let cursor := cursor + pairwiseCount * (2 * 2 + quotientVmPairwiseCoeffs)
  let cursor := cursor + memCount * (1 + 2)
  .ok (cursor + productCount * (1 + 2 * 2) - idx)

/-- rust: QVM:3008-3024 (quotient_op_len) @formal-baseline. "Return the byte length of the
    instruction at idx." The four dynamic opcodes are decoded; everything else comes from
    VT's static table, and an opcode with no table entry is the Rust's panic. COMPACT-
    SCOPED COPY: P-09d owns the general walker and should absorb this. -/
def quotientOpLen (bytes : List Nat) (idx : Nat) : M Nat := do
  let op ← walkByte bytes idx
  if op == qOpRunAddMulMemMemConstU8 then do
    let n ← walkReadU16 bytes (idx + 1)
    .ok (1 + 2 + n * (2 * 2 + 1))
  else if op == qOpRunAddMulConstU8MemU16 then do
    let n ← walkReadU16 bytes (idx + 1)
    .ok (1 + 2 + n * (2 + 1))
  else if op == qOpAffineSum then
    quotientAffineSumOpLen bytes idx
  else if op == qOpModarith7 then
    quotientModarith7OpLen bytes idx
  else
    match quotientOpcodeByteLen op with
    | some len => .ok len
    | none =>
        panicAt (siteUnknownOp ++ toString op ++ " at byte " ++ toString idx ++ ")")

/-- rust: QVM:1962-1968 (is_affine_add_op) @formal-baseline. "Whether an opcode contributes
    a fused affine-add term to the current top." Exactly the two fused accumulator opcodes;
    ADD_MUL_MEM_MEM is NOT one of them, which is why a run of unweighted products never
    compacts. -/
def isAffineAddOp (op : Nat) : Bool :=
  op == qOpAddMulMemMemConstU8 || op == qOpAddMulConstU8MemU16

/-- A byte window of the instruction buffer: the Rust's bytes[a..a+len]. -/
def byteSlice (bytes : List Nat) (lo : Nat) (len : Nat) : List Nat :=
  (bytes.drop lo).take len

/-- rust: QVM:1896-1913, the inner run scan of compact_quotient_runs. Returns the cursor
    after the run, the (opcode, operand start, operand length) triples and the two counts.
    The u16::MAX caps are what stop the two count fields overflowing. -/
def compactScan (bytes : List Nat) : Nat → Nat → List (Nat × Nat × Nat) → Nat → Nat →
    M (Nat × List (Nat × Nat × Nat) × Nat × Nat)
  | 0, idx, termOps, lin, prod => .ok (idx, termOps, lin, prod)
  | fuel + 1, idx, termOps, lin, prod =>
      if idx < bytes.length && isAffineAddOp (bytes.getD idx 0) then do
        let termOp := bytes.getD idx 0
        let len ← quotientOpLen bytes idx
        let termOps := termOps ++ [(termOp, idx + 1, len - 1)]
        let lin := if termOp == qOpAddMulConstU8MemU16 then lin + 1 else lin
        let prod := if termOp == qOpAddMulMemMemConstU8 then prod + 1 else prod
        if lin == 65535 || prod == 65535 then
          .ok (idx + len, termOps, lin, prod)
        else
          compactScan bytes fuel (idx + len) termOps lin prod
      else
        .ok (idx, termOps, lin, prod)
termination_by fuel => fuel

/-- rust: QVM:1884-1960 (compact_quotient_runs) @formal-baseline. "Compact long adjacent
    fused-op runs in byte-oriented VM encoding. Run compaction is only a byte-encoding
    optimization. It preserves the logical operation stream by replacing long adjacent
    fused add-mul ops with one counted opcode followed by the same operands. Mixed linear
    and bilinear affine runs use a larger superinstruction because addition is commutative
    and each term only mutates the same accumulator."

    Hazard 4's mechanism. Three things the port keeps exactly: (a) the mixed run emits ALL
    linear terms first and then all product terms, in source order within each group - the
    interpreter's AFFINE_SUM arm depends on that order; (b) the homogeneous run copies
    term_ops[0].2 bytes for EVERY term, i.e. it assumes a fixed operand width per opcode,
    which holds because both fused opcodes have static lengths; (c) the count caps and the
    two run_compaction_min_len thresholds decide when compaction is worth any bytes at all. -/
def compactGo (bytes : List Nat) : Nat → Nat → List Nat → M (List Nat)
  | 0, idx, out =>
      if idx < bytes.length then
        panicAt siteCompactionFuel
      else
        .ok out
  | fuel + 1, idx, out =>
      if idx >= bytes.length then
        .ok out
      else do
        let op := bytes.getD idx 0
        if isAffineAddOp op then do
          let runStart := idx
          let r ← compactScan bytes bytes.length idx [] 0 0
          let idx' := r.1
          let termOps := r.2.1
          let linCount := r.2.2.1
          let productCount := r.2.2.2
          if linCount > 0 && productCount > 0 &&
              linCount + productCount >= quotientVmSpec.runCompactionMinLen then do
            let linOps := termOps.filterMap fun (t, st, ln) =>
              if t == qOpAddMulConstU8MemU16 then some (st, ln) else none
            let prodOps := termOps.filterMap fun (t, st, ln) =>
              if t == qOpAddMulMemMemConstU8 then some (st, ln) else none
            let head := out ++ [qOpAffineSum, linCount / 256, linCount % 256,
              productCount / 256, productCount % 256]
            let out := linOps.foldl (fun acc (st, ln) => acc ++ byteSlice bytes st ln) head
            let out := prodOps.foldl (fun acc (st, ln) => acc ++ byteSlice bytes st ln) out
            compactGo bytes fuel idx' out
          else if termOps.length >= quotientVmSpec.runCompactionMinLen &&
              termOps.all (fun (t, _, _) => t == op) &&
              (op == qOpAddMulMemMemConstU8 || op == qOpAddMulConstU8MemU16) then do
            let runOperandsLen := ((termOps.getD 0 (0, 0, 0)).2).2
            let runOp := if op == qOpAddMulMemMemConstU8 then qOpRunAddMulMemMemConstU8
              else qOpRunAddMulConstU8MemU16
            let n := termOps.length
            let head := out ++ [runOp, n / 256, n % 256]
            let out := termOps.foldl (fun acc (_, st, _) =>
              acc ++ byteSlice bytes st runOperandsLen) head
            compactGo bytes fuel idx' out
          else
            compactGo bytes fuel idx' (out ++ byteSlice bytes runStart (idx' - runStart))
        else do
          let len ← quotientOpLen bytes idx
          compactGo bytes fuel (idx + len) (out ++ byteSlice bytes idx len)
termination_by fuel => fuel

/-- rust: QVM:1884-1960 (compact_quotient_runs), the entry point. -/
def compactQuotientRuns (bytes : List Nat) : M (List Nat) :=
  compactGo bytes bytes.length 0 []

/-! ## Usage and finalization (rust: QVM:1970-1994, 1211-1231) -/

/-- Ascending insertion sort: Lean 4.35 core has no List.qsort (the same note
    Kzg/Utils.lean:71 records), and these lists never exceed 31 entries. -/
def natSortAsc : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (natSortAsc xs)
where
  insertNat : Nat → List Nat → List Nat
    | x, [] => [x]
    | x, y :: ys => if x <= y then x :: y :: ys else y :: insertNat x ys

/-- rust: QVM:1996-2002 (push_unique_u8) @formal-baseline. "Insert a byte once and keep the
    set sorted for deterministic templates." sort_unstable on u8 is an ascending sort, and
    the contains-check before the push is what makes it a set. -/
def pushUniqueU8 (values : List Nat) (value : Nat) : List Nat :=
  if values.any (fun v => v == value) then values else natSortAsc (values ++ [value])

/-- rust: QVM:1976-1994 (quotient_program_usage) @formal-baseline. "Return opcode and
    memory-token usage for a finalized quotient program. This is a code-size optimization
    for the VK-specialized interpreter. The generated evaluator only needs switch arms for
    opcodes that can actually occur in its embedded program; malformed external frames
    still hit the default revert branch." COMPACT-SCOPED COPY: QuotientProgramBuild has no
    other way to be inhabited, so finish needs it; P-09d owns the general walker. -/
def usageGo (bytes : List Nat) : Nat → Nat → List Nat → List Nat → M (List Nat × List Nat)
  | 0, _, ops, tokens => .ok (ops, tokens)
  | fuel + 1, idx, ops, tokens =>
      if idx >= bytes.length then
        .ok (ops, tokens)
      else do
        let op := bytes.getD idx 0
        let len ← quotientOpLen bytes idx
        let tokens :=
          if op == qOpPushMemToken || op == qOpPushMemTokenOffset then
            pushUniqueU8 tokens (bytes.getD (idx + 1) 0)
          else
            tokens
        usageGo bytes fuel (idx + len) (pushUniqueU8 ops op) tokens
termination_by fuel => fuel

/-- rust: QVM:1976-1994 (quotient_program_usage), the entry point. -/
def quotientProgramUsage (bytes : List Nat) : M (List Nat × List Nat) :=
  usageGo bytes bytes.length 0 [] []

/-- What P-09d has to add back at this call site, stated rather than hidden (header). The
    Rust's finish runs validate_quotient_program(&bytes) and panics with "invalid finalized
    quotient VM program: {err}" (QVM:1217-1218), then asserts the depth it computed equals
    the builder's max_stack (QVM:1219-1222). Neither can change a byte of the artifact,
    which is why finish below is still the artifact boundary. -/
def finishValidatorLeg : String :=
  "QVM:1217-1222 validate_quotient_program + assert_eq!(validated_max_stack, self.max_stack)"

/-- rust: QVM:1211-1231 (finish) @formal-baseline. "Finalize byte-oriented bytecode after
    compacting adjacent run opcodes." THE ARTIFACT BOUNDARY (hazard 1): the bytes this
    returns are what the certifier hashes and what the Yul embeds. Hazard 4's ordering
    question, answered from the source: compaction runs FIRST, inside finish, after every
    emit and before validation and usage - and QVM:1223 calls quotient_program_usage on the
    COMPACTED bytes, not on self.bytes. The validator leg is P-09d's and is the one thing
    not ported here (see finishValidatorLeg). -/
def finish (s : QuotientProgramBuilder) : M QuotientProgramBuild := do
  let bytes ← compactQuotientRuns s.bytes
  let u ← quotientProgramUsage bytes
  .ok { bytes := qvmBytesOfNats bytes
        consts := s.consts
        maxStack := s.maxStack
        usedOps := qvmBytesOfNats u.1
        usedMemTokens := qvmBytesOfNats u.2 }

/-- The finalized bytes as the List Nat the interpreter reads, before the Bytes wrap that
    QuotientProgramBuild requires. -/
def finishBytes (s : QuotientProgramBuilder) : M (List Nat) :=
  compactQuotientRuns s.bytes

/-- The identity segment of a finalized program: everything except the trailing fold
    instruction, which is what the certifier hands to the interpreter (identity_segment,
    QVC:228-245). A MODELLING HELPER, not a Rust item: the general segment walker is
    P-09d's. It is sound here because finish emits the fold last and compaction never
    rewrites a fold byte, so the fold occupies the final 1 byte (FOLD_MAIN) or the final 4
    (FOLD_SELECTOR plus its u24). -/
def finalizedIdentitySegment (bytes : List Nat) : Option (List Nat) :=
  let n := bytes.length
  if n == 0 then none
  else if bytes.getD (n - 1) 0 == qOpFoldMain then some (bytes.take (n - 1))
  else if n >= 4 && bytes.getD (n - 4) 0 == qOpFoldSelector then some (bytes.take (n - 4))
  else none

/-- rust: QVM:1219-1222's Lean substitute. The stack high-water mark of one identity
    segment, measured by running P-09b's own step function and taking the maximum stack
    length it ever reaches. This is the validator's invariant - the physical program's
    depth matching the builder's accounting - obtained from the interpreter rather than
    from P-09d's stack-effect table. -/
def segmentMaxStackGo (bytes : List Nat) (consts : List Word256) :
    Nat → Nat → List QVMFr → QuotientRefMemory → Nat → M Nat
  | 0, idx, _, _, _ =>
      if idx < bytes.length then
        panicAt siteDepthFuel
      else
        .ok 0
  | fuel + 1, idx, stack, mem, hi =>
      if idx >= bytes.length then
        .ok hi
      else do
        let st ← evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem
        let hi := max hi st.stack.length
        segmentMaxStackGo bytes consts fuel (idx + st.consumed) st.stack st.mem hi
termination_by fuel => fuel

/-- The entry point of the depth measurement above. -/
def segmentMaxStack (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) : M Nat :=
  segmentMaxStackGo bytes consts bytes.length 0 ([] : List QVMFr) mem 0

end Midfall.Generator.QuotientBuilder

/-! ## Known-answer tests

    Every gate below is a Bool or an IO Bool with a matching '#eval ... -- expect true'
    line at the end of the file, so scripts/kat_gate.py turns each one into a CI
    obligation (docs/REVIEW.md R-38). Each doc names the concrete wrong implementation it
    rules out, and the package report carries the perturbation actually run inside each
    scope (R-41). D-P19 binds the artifact gates: they open vm/mod.rs and
    lowering/config.rs from disk while they evaluate, and the reachability gate is the
    first #eval in the file so a wrong path is diagnosed rather than matched by accident. -/

namespace Midfall.Generator
namespace QuotientVmBuilderKats

open Midfall.Generator.QuotientVmKats (readFileOrEmpty)
open Midfall.Generator.QuotientBuilder

/-! ### Fixtures

    R-48: this package builds its OWN memory and constant fixtures rather than reusing
    VmReference's, and every pointer it compares is pairwise distinct, because the gates
    below compare emitted byte strings and a degenerate fixture makes a byte comparison
    pass for the wrong reason. The seed is 32 bytes and differs from refSeedA and
    refSeedB; the pointers are 0x100..0x1c0 at the 0x20 stride the limb opcodes expect. -/

def bSeed : Bytes := qvmBytesOfNats ((List.range 32).map fun i => (i * 13 + 7) % 256)

def bMem : QuotientRefMemory := quotientRefMemoryNew bSeed

/-- The fixture pointers, all distinct (R-48). -/
def bPtrs : List Nat := [0x100, 0x120, 0x140, 0x160, 0x180, 0x1a0, 0x1c0]

/-- Distinctness asserted before anything compares them (R-48's rule). -/
def bPtrsDistinct : Bool :=
  bPtrs.length == 7 &&
    (bPtrs.foldl (fun acc p => acc && (bPtrs.filter fun q => q == p).length == 1) true)

/-- Big-endian operand encoders, so a pin reads like the instruction it tests. -/
def be16 (x : Nat) : List Nat := [x / 256, x % 256]
def be24 (x : Nat) : List Nat := [x / 65536 % 256, x / 256 % 256, x % 256]
def be32 (x : Nat) : List Nat := [x / 16777216 % 256, x / 65536 % 256, x / 256 % 256, x % 256]

/-- A literal memory leaf. -/
def lit (ptr : Nat) : QuotientExpr := QuotientExpr.mem (.literal ptr)

/-- c * e, the scaled term the recognizers produce. -/
def scaled (c : Word256) (e : QuotientExpr) : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.const c) e

/-- m(a) * m(b) * c - the shape the fused product opcode encodes. -/
def prodTerm (c : Word256) (a b : Nat) : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.mul (lit a) (lit b)) (QuotientExpr.const c)

/-- Left-nested sum: the shape emit_expr peepholes one term at a time. -/
def sumLeft (base : QuotientExpr) (terms : List QuotientExpr) : QuotientExpr :=
  terms.foldl QuotientExpr.add base

/-- The certifier's comparison at the granularity D-P20 says it has: one identity
    expression against the direct evaluation of the tree it was lowered from. -/
def runProg (prog : List Nat) (consts : List Word256) : Except QVMFault QVMFr := do
  let (v, _) ← QVM.run prog consts bMem
  .ok v

/-- The oracle side: evalQuotientExpr, unwrapped. The sentinel is not a field value, so a
    failure can never coincide with a pin. -/
def oracle (e : QuotientExpr) : QVMFr :=
  match evalQuotientExpr e bMem with
  | .ok (v, _) => v
  | .error _ => qvmFrModulus

def okIs {α : Type} [BEq α] (x : Except QVMFault α) (want : α) : Bool :=
  match x with
  | .ok v => v == want
  | .error _ => false

def isPanicClass {α : Type} (x : Except QVMFault α) : Bool :=
  match x with
  | .error (QVMFault.panic _) => true
  | _ => false

/-- The panic carries the site plus, for the format!-style sites, the payload the Rust
    interpolates (a variable name, a pointer, a literal). Matching on containment keeps
    the gate precise about WHICH assert fired while allowing that tail. -/
def isPanicAt {α : Type} (x : Except QVMFault α) (site : String) : Bool :=
  match x with
  | .error (QVMFault.panic s) => s.contains site
  | _ => false

/-- The builder state after emitting one expression with no recognizers, or the panic. -/
def emitOnly (e : QuotientExpr) : Except QVMFault QuotientProgramBuilder :=
  emitExprTop noShapeRecognizers builderDefault e

/-- Everything a rejected try_emit must leave alone: the buffer, the table, the map and
    both depth counters. Hazard 3's equality, as one projection. -/
def builderShape (s : QuotientProgramBuilder) : List Nat × List Word256 × Nat × Nat :=
  (s.bytes, s.consts, s.stackDepth, s.maxStack)

/-! ### The expressions the emitter is tested on -/

/-- m(0x100) + 11 * m(BETA). The same shape VmReference's certExpr uses, with the token
    and the literal on the opposite sides of the sum so the peephole order is exercised
    rather than mirrored. -/
def eCert : QuotientExpr :=
  QuotientExpr.add (lit 0x100) (scaled 11 (QuotientExpr.mem (.token qMemBeta)))

/-- -(3 * m(0x120)). -/
def eNeg : QuotientExpr := QuotientExpr.neg (scaled 3 (lit 0x120))

/-- (-m(0x100) * 5) + (m(BETA+0x20) + m(0x100000)): a token offset and a pointer too big
    for a u16 operand, so PUSH_MEM_TOKEN_OFFSET and PUSH_MEM_LITERAL both appear. -/
def eWide : QuotientExpr :=
  QuotientExpr.add
    (QuotientExpr.mul (QuotientExpr.neg (lit 0x100)) (QuotientExpr.const 5))
    (QuotientExpr.add (QuotientExpr.mem (.tokenOffset qMemBeta 0x20)) (lit 0x100000))

/-- m(0x100) * m(0x120) * 7 + m(0x140): the fused product-add path, rhs-first order. -/
def eFused : QuotientExpr :=
  QuotientExpr.add (prodTerm 7 0x100 0x120) (lit 0x140)

/-- Four scaled loads over a base: an all-linear run of length 4, which is exactly
    QUOTIENT_VM_RUN_COMPACTION_MIN_LEN, so it compacts to one RUN opcode. -/
def eRunLin4 : QuotientExpr :=
  sumLeft (lit 0x100) [scaled 2 (lit 0x120), scaled 3 (lit 0x140),
    scaled 5 (lit 0x160), scaled 7 (lit 0x180)]

/-- Three scaled loads: one short of the threshold, so nothing compacts. -/
def eRunLin3 : QuotientExpr :=
  sumLeft (lit 0x100) [scaled 2 (lit 0x120), scaled 3 (lit 0x140), scaled 5 (lit 0x160)]

/-- Two linear and two bilinear terms: the mixed run that becomes AFFINE_SUM. -/
def eRunMixed : QuotientExpr :=
  sumLeft (lit 0x100) [scaled 2 (lit 0x120), prodTerm 3 0x140 0x160,
    scaled 5 (lit 0x180), prodTerm 7 0x1a0 0x1c0]

/-- A five-fold product of one subexpression: the shape quotient_pow5_base recognizes. -/
def ePow5Base : QuotientExpr := QuotientExpr.add (lit 0x100) (lit 0x120)
def ePow5 : QuotientExpr :=
  QuotientExpr.mul (QuotientExpr.mul ePow5Base ePow5Base)
    (QuotientExpr.mul (QuotientExpr.mul ePow5Base ePow5Base) ePow5Base)

/-- The seven-limb linear form the LIN7 opcode encodes, and the tree that means the same
    thing generically. -/
def lin7Coeffs : List Word256 := [2, 3, 5, 7, 11, 13, 17]
def lin7Shape : QuotientLimbShape := QuotientLimbShape.lin7 (lin7Coeffs.zip bPtrs)
def lin7Expr : QuotientExpr :=
  sumLeft (QuotientExpr.const 0) ((lin7Coeffs.zip bPtrs).map fun (c, p) => scaled c (lit p))

/-- The row form lhs * sum c_i * m(rhs_i). -/
def rowCoeffs : List Word256 := [19, 23, 29, 31, 37, 41, 43]
def rowShape : QuotientLimbShape := QuotientLimbShape.bilin7Row 0x100 (rowCoeffs.zip bPtrs)
def rowExpr : QuotientExpr :=
  QuotientExpr.mul (lit 0x100)
    (sumLeft (QuotientExpr.const 0) ((rowCoeffs.zip bPtrs).map fun (c, p) => scaled c (lit p)))

/-- The 7x7 pairwise convolution and its generic twin: 13 coefficients indexed i + j. -/
def pwCoeffs : List Word256 := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
def pwShape : QuotientLimbShape := QuotientLimbShape.bilin7Pairwise 0x100 0x180 pwCoeffs
def pwTerms : List QuotientExpr :=
  (List.range quotientVmLimbs).flatMap fun i =>
    (List.range quotientVmLimbs).map fun j =>
      QuotientExpr.mul (QuotientExpr.const (pwCoeffs.getD (i + j) 0))
        (QuotientExpr.mul (lit (0x100 + i * 0x20)) (lit (0x180 + j * 0x20)))

def pwExpr : QuotientExpr := sumLeft (QuotientExpr.const 0) pwTerms

/-- A whole MODARITH7 identity: condition, constant, one lin block, one row, one pairwise
    block, one scalar memory term and one product term. -/
def maLinBlock : List (Word256 × Nat) := lin7Coeffs.zip bPtrs
def maRowBlock : List (Word256 × Nat) := rowCoeffs.zip bPtrs
def maShape : QuotientModarith7Shape :=
  { cond := some 0x260
    constant := 5
    lin := [maLinBlock]
    rows := [(0x100, maRowBlock)]
    pairwise := [(0x100, 0x180, pwCoeffs)]
    memTerms := [(23, 0x140)]
    productTerms := [(29, 0x160, 0x180)] }
def maInner : QuotientExpr :=
  sumLeft (QuotientExpr.const 5)
    (lin7Expr :: [rowExpr, pwExpr, scaled 23 (lit 0x140),
      QuotientExpr.mul (QuotientExpr.const 29) (QuotientExpr.mul (lit 0x160) (lit 0x180))])
def maExpr : QuotientExpr := QuotientExpr.mul (lit 0x260) maInner

/-- The hooks the fixture recognizers supply. Each is keyed on ONE expression, so the
    generic path is untouched everywhere else. -/
def lin7Hooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with limbShape := fun e => if e == lin7Expr then some lin7Shape else none }
def rowHooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with limbShape := fun e => if e == rowExpr then some rowShape else none }
def pwHooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with limbShape := fun e => if e == pwExpr then some pwShape else none }
def maHooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with modarith7Shape := fun e => if e == maExpr then some maShape else none }
def pow5Hooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with pow5Base := fun e => if e == ePow5 then some ePow5Base else none }
/-- A decomposition hook: the shape is recognized, the residue is the leftover term and
    the matched list is the shape's own terms. -/
def decompTarget : QuotientExpr := sumLeft lin7Expr [scaled 19 (lit 0x1e0)]
def decompHooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with
    limbSubshape := fun e =>
      if e == decompTarget then
        some (lin7Shape, scaled 19 (lit 0x1e0),
          (lin7Coeffs.zip bPtrs).map fun (c, p) => scaled c (lit p))
      else none }
/-- The contract-violating hook: matched is empty, which QVM:1396 says cannot happen. -/
def emptyMatchedHooks : QuotientShapeRecognizers :=
  { noShapeRecognizers with
    limbSubshape := fun e =>
      if e == decompTarget then some (lin7Shape, scaled 19 (lit 0x1e0), []) else none }

/-- Every expression the gates emit, for the sweeps. -/
def allExprs : List (String × QuotientExpr) :=
  [("eCert", eCert), ("eNeg", eNeg), ("eWide", eWide), ("eFused", eFused),
   ("eRunLin4", eRunLin4), ("eRunLin3", eRunLin3), ("eRunMixed", eRunMixed),
   ("ePow5", ePow5), ("lin7Expr", lin7Expr), ("rowExpr", rowExpr), ("pwExpr", pwExpr),
   ("maExpr", maExpr)]

/-- Every hook set the gates use. -/
def allHooks : List (String × QuotientShapeRecognizers) :=
  [("none", noShapeRecognizers), ("lin7", lin7Hooks), ("row", rowHooks),
   ("pw", pwHooks), ("ma", maHooks), ("pow5", pow5Hooks), ("decomp", decompHooks)]

/-! ### GATE 1 - hazard 1: finish() output executes and agrees with the oracle -/

/-- THE HEADLINE GATE. For every fixture expression: identityExpr, finish, strip the fold,
    and run the finalized bytes through P-09b's interpreter. The field element must equal
    what evalQuotientExpr computes from the tree the identity was lowered from. This is
    the first emitter-vs-interpreter certification leg in the tree, and the Rust only does
    it probabilistically (QVR:12-18: a random challenge derived from the finalized
    bytecode, success 1 - deg/|Fr|); here it is by construction, over every fixture, at
    every #eval.

    Rules out: an emitter that writes an operand in the wrong width or order, a fold that
    pops the wrong number of times, a compaction that reorders terms, and a constant table
    whose slot order disagrees with the bytes. Any of those makes the interpreter disagree
    with the oracle or fault. -/
def finishIdentity_executesAndAgrees_ok : Bool :=
  allExprs.all fun (_, e) =>
    match identityExpr noShapeRecognizers builderDefault e QuotientTarget.main none >>= finish with
    | .error _ => false
    | .ok build =>
        let bytes := qvmBytesToNats build.bytes
        match finalizedIdentitySegment bytes with
        | none => false
        | some seg => seg != [] && okIs (runProg seg build.consts) (oracle e)

/-- HAZARD 2, pinned byte for byte. eCert lowers to exactly nine bytes: PUSH_CONST_U8 0,
    PUSH_MEM_TOKEN BETA, MUL, ADD_MEM_U16 0x100, FOLD_MAIN. This is the gate the brief
    says is worth more than reasoning about the fold: it fixes the order in which the
    peepholes fire (rhs is a leaf, so lhs is emitted first and the accumulator opcode
    second), the slot allocation order, and the fact that the fold is the last byte.
    Rules out: reordering emit_expr's four peephole attempts, a swapped accumulator
    operand, or an emitter that pushes the memory load before the constant. -/
def emitBytes_pinnedForSmallExpression_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault eCert QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      s.bytes == [0x09, 0x00, 0x03, qMemBeta, 0x07, 0x10] ++ be16 0x100 ++ [0x0a] &&
        s.consts == [11] && s.stackDepth == 0 && s.maxStack == 2 && s.bytes.length == 9

/-- HAZARD 2's no-reordering claim across a whole stream: after each identity the earlier
    byte buffer is a PREFIX of the later one, so nothing a previous identity emitted was
    rewritten or moved, and the buffer only ever grows. Rules out: an emitter that
    back-patches, and a compaction that reorders across an identity boundary. -/
def chainSnapshots (steps : List QuotientExpr) :
    M (List (List Nat) × QuotientProgramBuilder) :=
  go steps [] builderDefault
where
  go : List QuotientExpr → List (List Nat) → QuotientProgramBuilder →
      M (List (List Nat) × QuotientProgramBuilder)
  | [], snaps, s => .ok (snaps, s)
  | e :: rest, snaps, s => do
      let s ← identityExpr noShapeRecognizers s e QuotientTarget.main none
      go rest (snaps ++ [s.bytes]) s

def emitChain_isAppendOnly_ok : Bool :=
  let steps : List QuotientExpr := [eCert, eNeg, eRunMixed, eWide, eFused]
  match chainSnapshots steps with
  | .error _ => false
  | .ok (snaps, final) =>
      snaps.length == steps.length &&
        (snaps.all fun p => p.isPrefixOf final.bytes) &&
        (snaps.length == 5 && (snaps.getD 0 []).length > 0 &&
          (List.zip snaps.toArray.toList (snaps.drop 1)).all fun (a, b) => a.length < b.length)

/-- HAZARD 1's second half: the constant table the artifact carries has no duplicate
    entries, because const_slot deduplicates through const_slots before appending. A table
    with a duplicate would mean two slots for one value and a byte addressing the wrong
    one. -/
def finish_constsAreTheSlotTable_ok : Bool :=
  allExprs.all fun (_, e) =>
    match identityExpr noShapeRecognizers builderDefault e QuotientTarget.main none >>= finish with
    | .error _ => false
    | .ok build =>
        let cs := build.consts
        let dedup := cs.foldl (fun acc c => if acc.any fun d => d == c then acc else acc ++ [c]) []
        cs.length == dedup.length

/-! ### GATE 2 - hazard 3: a rejected try_emit leaves the buffer untouched -/

/-- A state with n constants already allocated and an empty slot map, so the next slot is
    exactly n. Used to sit on every width boundary the emitters choose between. -/
def stateWithConsts (n : Nat) : QuotientProgramBuilder :=
  { builderDefault with consts := List.replicate n (1 : Word256) }

/-- The rejection battery. Each row is (hooks, expression, limb_vm_ops): all four
    try_emit_* must return false AND leave bytes, consts, const_slots, stack_depth and
    max_stack bit-identical (builderShape). Rules out: a preflight that allocates a
    constant slot before deciding (peek_u8_const_slots degrading into const_slot), a
    try_emit that emits an opcode and then changes its mind, and a fallback that pops
    without pushing. -/
def tryEmit_rejected_leavesStateUnchanged_ok : Bool :=
  let cases : List (QuotientShapeRecognizers × QuotientExpr × Bool) :=
    [(noShapeRecognizers, eCert, true),
     (pow5Hooks, eCert, true),
     (noShapeRecognizers, lin7Expr, true),
     (lin7Hooks, eCert, true),
     (lin7Hooks, lin7Expr, false),
     (noShapeRecognizers, maExpr, true),
     (maHooks, eCert, true),
     (maHooks, maExpr, false),
     (noShapeRecognizers, decompTarget, true),
     (decompHooks, eCert, true),
     (decompHooks, decompTarget, false)]
  (cases.all fun (r, e, ops) =>
      let s0 := { builderDefault with limbVmOps := ops }
      let checks : List Bool :=
        (match tryEmitPow5 r (emitFuel e) s0 e with
         | .error _ => [false]
         | .ok (hit, s) => [! hit, builderShape s == builderShape s0]) ++
        (match tryEmitLimbShape r s0 e with
         | .error _ => [false]
         | .ok (hit, s) => [! hit, builderShape s == builderShape s0]) ++
        (match tryEmitModarith7Shape r s0 e with
         | .error _ => [false]
         | .ok (hit, s) => [! hit, builderShape s == builderShape s0]) ++
        (match tryEmitLimbDecomposition r (emitFuel e) s0 e with
         | .error _ => [false]
         | .ok (hit, s) => [! hit, builderShape s == builderShape s0])
      checks.all id) &&
    (let s0 := builderDefault
     let badProducts : List QuotientExpr :=
       [QuotientExpr.add (lit 0x100) (lit 0x120),
        QuotientExpr.neg (lit 0x100),
        scaled 3 (QuotientExpr.mem (.token qMemBeta)),
        QuotientExpr.mul (QuotientExpr.mul (lit 0x100) (lit 0x120)) (lit 0x140)]
     badProducts.all fun p =>
       match tryEmitAddProduct noShapeRecognizers (emitFuel p) s0 (lit 0x180) p with
       | .error _ => false
       | .ok (hit, s) => ! hit && builderShape s == builderShape s0) &&
    (let s0 := stateWithConsts 256
     match tryEmitAddProduct noShapeRecognizers 64 s0 (lit 0x100) (scaled 3 (lit 0x120)) with
     | .error _ => false
     | .ok (hit, s) => ! hit && builderShape s == builderShape s0) &&
    (let s0 := builderDefault
     match emitAccLeaf s0 (QuotientLeaf.mem (.literal 0x10000)) qOpAddConstU8 qOpAddConst
         qOpAddMemU16 with
     | .error _ => false
     | .ok (hit, s) => ! hit && builderShape s == builderShape s0) &&
    -- the three PREFLIGHT rejections: the hook fires, the const-slot check refuses, and
    -- the table must come back exactly as it was. These are the arms a perturbation that
    -- lets a preflight allocate (peek degrading into const_slot) actually has to pass.
    (let s0 := { stateWithConsts 250 with limbVmOps := true }
     match tryEmitLimbShape lin7Hooks s0 lin7Expr with
     | .error _ => false
     | .ok (hit, s) => ! hit && builderShape s == builderShape s0) &&
    (let s0 := { stateWithConsts 243 with limbVmOps := true }
     match tryEmitModarith7Shape maHooks s0 maExpr with
     | .error _ => false
     | .ok (hit, s) => ! hit && builderShape s == builderShape s0) &&
    (let s0 := { stateWithConsts 250 with limbVmOps := true }
     match tryEmitLimbDecomposition decompHooks (emitFuel decompTarget) s0 decompTarget with
     | .error _ => false
     | .ok (hit, s) => ! hit && builderShape s == builderShape s0) &&
    -- and the same through emit_expr, where a refused limb shape must fall back to the
    -- generic path with the table untouched apart from what the generic path itself needs
    (let s0 := { stateWithConsts 256 with limbVmOps := true }
     match emitExprTop lin7Hooks s0 lin7Expr with
     | .error _ => false
     | .ok s => (s.consts.length == 264 && s.constSlots.length == 8 &&
         ! (s.bytes.contains qOpLin7)))

/-- The positive control for the gate above (R-41: a rejection test that never sees an
    acceptance is vacuous). Each entry point DOES change the buffer when it succeeds, so
    the equality in the battery is doing real work. -/
def tryEmit_accepted_doesChangeState_ok : Bool :=
  (match tryEmitLimbShape lin7Hooks builderDefault lin7Expr with
   | .error _ => false
   | .ok (hit, s) => hit && s.bytes != [] && s.maxStack == 1) &&
  (match tryEmitModarith7Shape maHooks builderDefault maExpr with
   | .error _ => false
   | .ok (hit, s) => hit && s.bytes != [] && s.maxStack == 1) &&
  (match tryEmitPow5 pow5Hooks (emitFuel ePow5) builderDefault ePow5 with
   | .error _ => false
   | .ok (hit, s) => hit && s.bytes != []) &&
  (match tryEmitLimbDecomposition decompHooks (emitFuel decompTarget) builderDefault
      decompTarget with
   | .error _ => false
   | .ok (hit, s) => hit && s.bytes != []) &&
  (match tryEmitAddProduct noShapeRecognizers 64 builderDefault (lit 0x100)
      (scaled 3 (lit 0x120)) with
   | .error _ => false
   | .ok (hit, s) => hit && s.bytes != [])

/-- The limb preflight at the boundary. lin7Shape has 7 distinct coefficients and maShape
    has 14, so with 249 (resp. 242) constants already allocated the last slot is exactly
    255 and one more already-allocated constant pushes it past a byte. Rules out: an
    off-by-one in peek_u8_const_slots, which would either panic inside emit_limb_shape or
    refuse every shape at the last legal slot. Also pins the F-1 divergence: a zero
    constant must NOT reserve a slot, which is what VT's coefficientOperands gets wrong. -/
def limbPreflight_slotBoundary_ok : Bool :=
  (limbShapeHasU8ConstSlots (stateWithConsts 249) lin7Shape == true) &&
    (limbShapeHasU8ConstSlots (stateWithConsts 250) lin7Shape == false) &&
    (modarith7ShapeHasU8ConstSlots (stateWithConsts 242) maShape == true) &&
    (modarith7ShapeHasU8ConstSlots (stateWithConsts 243) maShape == false) &&
    ((modarith7Coeffs maShape).length == 30) &&
    ((modarith7Coeffs { maShape with constant := 0 }).length == 29) &&
    ((modarith7Coeffs { maShape with constant := 0 }).length < (modarith7Coeffs maShape).length)

/-! ### GATE 3 - hazard 4: compaction preserves the interpreter's result -/

/-- THE OTHER HEADLINE GATE. For every fixture, run the emitted buffer as-is and run the
    compacted buffer, and require the SAME field element - and, since gate 1 already ties
    the compacted side to the oracle, both sides agree with the direct evaluation of the
    tree. The Rust has no such test (see noRustCompactionResultTest_artifact_ok): its only
    compaction test checks the byte layout and the validator's depth. Rules out: AFFINE_SUM
    emitting product terms before linear ones, a run count written little-endian, operands
    copied with the wrong stride, and a compaction that drops or duplicates a term. -/
def compaction_preservesInterpreterResult_ok : Bool :=
  allExprs.all fun (_, e) =>
    match emitExprTop noShapeRecognizers builderDefault e with
    | .error _ => false
    | .ok s =>
        match compactQuotientRuns s.bytes with
        | .error _ => false
        | .ok compacted =>
            let before := runProg s.bytes s.consts
            let after := runProg compacted s.consts
            okIs before (oracle e) && okIs after (oracle e) &&
              (match before, after with
               | .ok x, .ok y => x == y
               | _, _ => false)

/-- The same claim across a multi-identity program, where compaction can change offsets
    between identities rather than only inside one. -/
def segmentDeltas (snaps : List (List Nat)) : List (List Nat) :=
  go snaps 0
where
  go : List (List Nat) → Nat → List (List Nat)
  | [], _ => []
  | s :: rest, startAt => (s.drop startAt) :: go rest s.length

def compaction_preservesResult_multiIdentity_ok : Bool :=
  let steps : List QuotientExpr := [eRunLin4, eRunMixed, eRunLin3]
  match chainSnapshots steps with
  | .error _ => false
  | .ok (snaps, final) =>
      match finish final with
      | .error _ => false
      | .ok build =>
          let deltas := segmentDeltas snaps
          deltas.length == steps.length &&
            (List.zip steps deltas).all fun (e, seg) =>
              -- each identity's bytes end with its FOLD_MAIN, which the interpreter
              -- rejects by design (D-P20 item 1), so the segment is what gets run
              match finalizedIdentitySegment seg with
              | none => false
              | some expr => match compactQuotientRuns expr with
                | .error _ => false
                | .ok c => okIs (runProg expr build.consts) (oracle e) &&
                    okIs (runProg c build.consts) (oracle e)

/-- HAZARD 2 at the operand level: the three fused accumulator forms and the two limb
    forms write their operands in a fixed order that the interpreter's decoders assume.
    Multiplication is commutative, so NO value-level gate can see lhs and rhs swapped in
    ADD_MUL_MEM_MEM_CONST_U8 - only a byte pin can. Rules out: swapping the two pointers,
    putting the const slot before the pointers, and the MODARITH7 mem block's (slot, ptr)
    order drifting to the standalone helper's (ptr, slot) order, which QVR:488-490 warns
    about by name. -/
def fusedOperandOrder_pinned_ok : Bool :=
  (match emitProductAdd builderDefault (QuotientProductAdd.memMemConstU8 0x140 0x160 3) with
   | .error _ => false
   | .ok s => s.bytes == [0x12] ++ be16 0x140 ++ be16 0x160 ++ [0]) &&
  (match emitProductAdd builderDefault (QuotientProductAdd.constU8Mem 3 0x120) with
   | .error _ => false
   | .ok s => s.bytes == [0x13] ++ be16 0x120 ++ [0]) &&
  (match emitProductAdd builderDefault (QuotientProductAdd.memMem 0x140 0x160) with
   | .error _ => false
   | .ok s => s.bytes == [0x14] ++ be16 0x140 ++ be16 0x160) &&
  (match emitLimbShape builderDefault (QuotientLimbShape.bilin7Row 0x100 [(3, 0x120)]) with
   | .error _ => false
   | .ok s => s.bytes == [0x1d] ++ be16 0x100 ++ [0] ++ be16 0x120) &&
  (match emitModarith7Shape builderDefault
      { cond := none, constant := 0, lin := [], rows := [], pairwise := [],
        memTerms := [(5, 0x140)], productTerms := [(7, 0x160, 0x180)] } with
   | .error _ => false
   | .ok s => s.bytes == [0x21, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01,
        0x00, 0x01, 0x40, 0x01, 0x01, 0x60, 0x01, 0x80] && s.bytes.length == 15)

/-- HAZARD 4's byte-level pin, ported from the reference's own test
    (QVM:4280-4320, byte_compaction_groups_mixed_affine_sum_terms): the same input, the
    same expected output, asserted as a whole list rather than index by index. Rules out:
    the AFFINE_SUM header order (lin count before product count) and the term order
    (linear block first, then products) that QVR:280-304 depends on. -/
def compaction_byteLayout_rustTest_ok : Bool :=
  let input : List Nat :=
    [0x09, 0x00,
     0x13] ++ be16 0x120 ++ [1] ++
     [0x12] ++ be16 0x140 ++ be16 0x160 ++ [2] ++
     [0x13] ++ be16 0x180 ++ [3] ++
     [0x12] ++ be16 0x1a0 ++ be16 0x1c0 ++ [4] ++
     [0x0a]
  match compactQuotientRuns input with
  | .error _ => false
  | .ok out =>
      out == [0x09, 0x00, 0x22, 0x00, 0x02, 0x00, 0x02,
        0x01, 0x20, 0x01, 0x01, 0x80, 0x03,
        0x01, 0x40, 0x01, 0x60, 0x02, 0x01, 0xa0, 0x01, 0xc0, 0x04, 0x0a] &&
        out.getD 2 0 == qOpAffineSum && out.getD 4 0 == 2 && out.getD 6 0 == 2 &&
        out.getD 9 0 == 1 && out.getD 12 0 == 3 && out.getD 17 0 == 2 &&
        out.getD 22 0 == 4

/-- The threshold itself, at value-1, value and value+1 (hazard 5 applied to hazard 4):
    three affine terms stay as they were, four become a RUN opcode, five stay a RUN opcode
    with count 5. Rules out: >= becoming > in either of the two length tests. -/
def compaction_thresholdBoundary_ok : Bool :=
  let lin (k : Nat) : List Nat := [0x09, 0x00] ++
    ((List.range k).flatMap fun i => [0x13] ++ be16 (0x100 + i * 0x20) ++ [i])
  match compactQuotientRuns (lin 3), compactQuotientRuns (lin 4),
      compactQuotientRuns (lin 5) with
  | .ok a, .ok b, .ok c =>
      a == lin 3 &&
        b.getD 2 0 == qOpRunAddMulConstU8MemU16 && b.getD 3 0 == 0 && b.getD 4 0 == 4 &&
        c.getD 4 0 == 5 && quotientVmSpec.runCompactionMinLen == 4 &&
        a.length == 2 + 3 * 4 && b.length == 2 + 3 + 4 * 3 &&
        b.length < (lin 4).length &&
        c.length == 2 + 3 + 5 * 3
  | _, _, _ => false

/-- Compaction is a fixed point: compacting an already-compacted program is the identity.
    The Rust never states this - finish compacts once - but it is the property that makes
    the artifact safe to re-derive, and it fails if the walker mis-sizes a RUN, AFFINE_SUM
    or MODARITH7 instruction. Rules out: a quotient_op_len that under-counts a dynamic
    opcode, which would make the second pass cut an instruction in half. -/
def compaction_isIdempotent_ok : Bool :=
  allExprs.all fun (_, e) =>
    match emitExprTop noShapeRecognizers builderDefault e >>= fun s =>
        compactQuotientRuns s.bytes with
    | .error _ => false
    | .ok once =>
        match compactQuotientRuns once with
        | .error _ => false
        | .ok twice => twice == once

/-- The opcode-length walker against the instruction boundaries it has to respect: every
    fixture program walks cleanly to exactly its own length, which for the MODARITH7,
    RUN and AFFINE_SUM fixtures can only come from their dynamic headers (the static
    table gives 0 for all three and would otherwise loop forever). -/
def walkTo (bytes : List Nat) : Nat → Nat → Nat → M Nat
  | 0, _, acc => .ok acc
  | fuel + 1, idx, acc =>
      if idx >= bytes.length then
        .ok acc
      else do
        let len ← quotientOpLen bytes idx
        walkTo bytes fuel (idx + len) (acc + len)
termination_by fuel => fuel

def opLen_walksEveryFixtureExactly_ok : Bool :=
  allExprs.all fun (_, e) =>
    match emitExprTop noShapeRecognizers builderDefault e >>= fun s =>
        compactQuotientRuns s.bytes with
    | .error _ => false
    | .ok prog =>
        match walkTo prog prog.length 0 0 with
        | .error _ => false
        | .ok total => total == prog.length

/-! ### GATE 4 - hazard 5: every width and slot boundary, at value-1, value and value+1 -/

/-- rust: QVM:1822-1826 (u16). 0xfffe and 0xffff append two bytes; 0x10000 is the Rust's
    assert, rendered per R4 as a panic carrying the source line. -/
def u16Boundary_ok : Bool :=
  (match emitU16 builderDefault 0xfffe with
   | .ok s => s.bytes == [0xff, 0xfe]
   | .error _ => false) &&
  (match emitU16 builderDefault 0xffff with
   | .ok s => s.bytes == [0xff, 0xff]
   | .error _ => false) &&
  isPanicAt (emitU16 builderDefault 0x10000) siteU16Overflow

/-- rust: QVM:1828-1832 (u24). The same three points around 0xffffff. -/
def u24Boundary_ok : Bool :=
  (match emitU24 builderDefault 0xfffffe with
   | .ok s => s.bytes == [0xff, 0xff, 0xfe]
   | .error _ => false) &&
  (match emitU24 builderDefault 0xffffff with
   | .ok s => s.bytes == [0xff, 0xff, 0xff]
   | .error _ => false) &&
  isPanicAt (emitU24 builderDefault 0x1000000) siteU24Overflow

/-- rust: QVM:1852-1856 (const_fits_u8_slot). A value already in the table is judged by
    its own slot; a value not in the table is judged by the length the next insert would
    return. The three boundary lengths are 254, 255 (still fits) and 256 (does not). The
    last two rows pin the !contains_key guard: a table longer than a byte does not make an
    EXISTING small slot fail. -/
def constFitsU8SlotBoundary_ok : Bool :=
  (constFitsU8Slot (stateWithConsts 254) 999 == true) &&
    (constFitsU8Slot (stateWithConsts 255) 999 == true) &&
    (constFitsU8Slot (stateWithConsts 256) 999 == false) &&
    (constFitsU8Slot { builderDefault with consts := List.replicate 400 (1 : Word256), constSlots := [(7, 300)] } 7 == false) &&
    (constFitsU8Slot { builderDefault with consts := List.replicate 400 (1 : Word256), constSlots := [(7, 3)] } 7 == true)

/-- rust: QVM:1858-1881 (peek_u8_const_slots). Duplicates inside one batch share a slot,
    a value already in the table uses its own slot, and the batch crosses the byte
    boundary at exactly the point where the next new slot would be 256. -/
def peekU8ConstSlotsBoundary_ok : Bool :=
  (peekU8ConstSlots builderDefault [3, 3, 5] == some [0, 0, 1]) &&
    (peekU8ConstSlots (stateWithConsts 254) [7, 8] == some [254, 255]) &&
    (peekU8ConstSlots (stateWithConsts 255) [7] == some [255]) &&
    (peekU8ConstSlots (stateWithConsts 255) [7, 8] == none) &&
    (peekU8ConstSlots (stateWithConsts 256) [7] == none) &&
    (peekU8ConstSlots { builderDefault with consts := List.replicate 300 (1 : Word256), constSlots := [(9, 2)] } [9] == some [2])

/-- rust: QVM:1597-1607 (emit_const) end to end through the real emitter rather than
    through the predicate: the first 256 distinct constants each take the two-byte
    PUSH_CONST_U8 form, and the 257th is the first that has to use the three-byte
    PUSH_CONST form. Rules out: the u8 test being slot < 255 (which would move the
    boundary one early) or slot <= 256 (one late). -/
def emitConst_encodingBoundary_ok : Bool :=
  match foldLeftM (fun (st : QuotientProgramBuilder) (i : Nat) =>
      emitConst st (BitVec.ofNat 256 (i + 1))) builderDefault (List.range 257) with
  | .error _ => false
  | .ok st =>
      st.consts.length == 257 && st.bytes.length == 256 * 2 + 3 &&
        (st.bytes.take 2 == [0x09, 0x00]) &&
        (st.bytes.drop 512 == [0x01] ++ be16 256)

/-- The memory-pointer half of hazard 5: 0xffff is a u16 operand, 0x10000 is a u32 one,
    and the fused product path refuses the wide pointer outright. -/
def emitMemLiteral_boundary_ok : Bool :=
  (match emitMemLiteral builderDefault 0xffff with
   | .ok s => s.bytes == [0x05] ++ be16 0xffff
   | .error _ => false) &&
  (match emitMemLiteral builderDefault 0x10000 with
   | .ok s => s.bytes == [0x02] ++ be32 0x10000
   | .error _ => false) &&
  (match emitMemLiteral builderDefault 0 with
   | .ok s => s.bytes == [0x05, 0x00, 0x00]
   | .error _ => false) &&
  (productAddMacro builderDefault [QuotientLeaf.mem (.literal 0x10000),
      QuotientLeaf.mem (.literal 0x120)] == none) &&
  (productAddMacro builderDefault [QuotientLeaf.mem (.literal 0xffff),
      QuotientLeaf.mem (.literal 0x120)] != none)

/-- rust: QVM:1839-1850 (const_slot). Slots are stable and deduplicated; the u16 assert
    fires at 65536 entries, not at 65535. -/
def constSlot_dedupAndOverflow_ok : Bool :=
  (match constSlot builderDefault 5 >>= fun (s, _a) =>
        constSlot s 7 >>= fun (s2, _b) => constSlot s2 5 with
   | .ok (s, c) => c == 0 && s.consts.length == 2
   | .error _ => false) &&
  (match constSlot (stateWithConsts 65535) 999 with
   | .ok (_, slot) => slot == 65535
   | .error _ => false) &&
  isPanicAt (constSlot (stateWithConsts 65536) 999) siteTooManyConsts

/-! ### GATE 5 - the finish max_stack claim, measured with the interpreter -/

/-- HAZARD 2 plus the validator leg P-09d owns. The Rust asserts that the physical
    program's stack high-water mark equals the builder's counter (QVM:1219-1222). That
    assertion is reproduced here WITHOUT the validator: segmentMaxStack runs P-09b's own
    step function over the finalized segment and takes the maximum stack length it
    reaches, and it must equal what the builder recorded. Rules out: an emitter that
    forgets push_stack after a fused opcode, a pop_stack missing after a fold, and a
    compaction that changes a run's stack effect. -/
def finishMaxStack_agreesWithInterpreter_ok : Bool :=
  allExprs.all fun (_, e) =>
    match identityExpr noShapeRecognizers builderDefault e QuotientTarget.main none with
    | .error _ => false
    | .ok s =>
        match finish s with
        | .error _ => false
        | .ok build =>
            match finalizedIdentitySegment (qvmBytesToNats build.bytes) with
            | none => false
            | some seg =>
                match segmentMaxStack seg build.consts bMem with
                | .error _ => false
                | .ok measured => measured == s.maxStack && measured >= 1

/-- The underflow panic site: pop_stack at depth 0 (QVM:1819) and the fold applied to an
    empty stack. Both must be panic-class errors here, not silent truncation.

    The OTHER assert in this area, QVM:1134's "quotient VM stack leak" at the end of
    identity_expr, is NOT reachable through the ported API: identity_expr resets
    stack_depth to 0 first (QVM:1129), every expression arm leaves exactly one value, and
    the fold consumes it. The gate pins that too - seeding a non-zero depth and showing
    identity_expr still succeeds with depth 0 - because it is the reset, not the assert,
    that does the work. Finding F-4: QVM:1134 is a tripwire for a misbehaving recognizer,
    not a reachable state, and P-09e inherits that obligation. -/
def stackPanics_ok : Bool :=
  isPanicAt (popStackAcct builderDefault) siteStackUnderflow &&
    isPanicAt (foldIdentity builderDefault QuotientTarget.main none) siteStackUnderflow &&
    (match identityExpr noShapeRecognizers { builderDefault with stackDepth := 1 }
        (lit 0x100) QuotientTarget.main none with
     | .ok s => s.stackDepth == 0
     | .error _ => false) &&
    (match identityExpr noShapeRecognizers builderDefault (lit 0x100)
        (QuotientTarget.selector 0) (some 0) with
     | .ok s => s.stackDepth == 0
     | .error _ => false)

/-! ### GATE 6 - identity boundaries and native markers -/

/-- rust: QVM:1137-1163 (fold_identity), the selector arm. The u24 packs idx in the top 8
    bits and the gap in the low 16, so idx 1 with gap 2 is 0x010002; the boundaries are
    idx 255 (legal) / 256 (assert) and gap 65535 (legal) / 65536 (assert), and a missing
    gap is the expect at QVM:1146. Rules out: the shift being 8 instead of 16, and the
    pop being applied twice for a selector (which the Rust's trailing
    'if matches!(target, Main)' guards against). -/
def foldIdentity_selectorEncoding_ok : Bool :=
  (match foldIdentity { builderDefault with stackDepth := 1 } (QuotientTarget.selector 1)
      (some 2) with
   | .ok s => s.bytes == [0x0b] ++ be24 0x010002 && s.stackDepth == 0
   | .error _ => false) &&
  (match foldIdentity { builderDefault with stackDepth := 1 } (QuotientTarget.selector 255)
      (some 65535) with
   | .ok s => s.bytes == [0x0b] ++ be24 0xffffff && s.stackDepth == 0
   | .error _ => false) &&
  isPanicAt (foldIdentity { builderDefault with stackDepth := 1 }
    (QuotientTarget.selector 1) none) siteNoSelectorGap &&
  isPanicAt (foldIdentity { builderDefault with stackDepth := 1 }
    (QuotientTarget.selector 256) (some 0)) siteSelectorIdxWidth &&
  isPanicAt (foldIdentity { builderDefault with stackDepth := 1 }
    (QuotientTarget.selector 0) (some 65536)) siteSelectorGapWidth &&
  (match foldIdentity { builderDefault with stackDepth := 1 } QuotientTarget.main none with
   | .ok s => s.bytes == [0x0a] && s.stackDepth == 0
   | .error _ => false)

/-- rust: QVM:1165-1209 (native_permutation, native_lookup, native_identity). All three
    assert an empty stack - the identity-boundary invariant - and native_identity appends
    a u16 index, so 65536 is a panic and 65535 is not. -/
def nativeMarkers_ok : Bool :=
  (match nativePermutation builderDefault with
   | .ok s => s.bytes == [0x19] && s.stackDepth == 0
   | .error _ => false) &&
  (match nativeLookup builderDefault with
   | .ok s => s.bytes == [0x1f]
   | .error _ => false) &&
  (match nativeIdentity builderDefault 0x1234 with
   | .ok s => s.bytes == [0x1b] ++ be16 0x1234
   | .error _ => false) &&
  isPanicAt (nativePermutation { builderDefault with stackDepth := 1 }) siteNativePermStack &&
  isPanicAt (nativeLookup { builderDefault with stackDepth := 2 }) siteNativeLookupStack &&
  isPanicAt (nativeIdentity { builderDefault with stackDepth := 1 } 0)
    siteNativeIdentityStack &&
  isPanicAt (nativeIdentity builderDefault 65536) siteU16Overflow &&
  (match nativeIdentity builderDefault 65535 with | .ok _ => true | .error _ => false)

/-- rust: QVM:1128-1129 (identity_expr's reset). vars is cleared and stack_depth goes to
    zero at the start of every identity; max_stack is NOT reset, because it is the
    high-water mark of the whole program. Rules out: a reset that wipes max_stack, which
    would under-size the memory planner's stack allocation. -/
def identityExpr_resetsVarsAndDepth_ok : Bool :=
  match assignment builderDefault "let t0 := mload(256)" with
  | .error _ => false
  | .ok seeded =>
      let seeded' := { seeded with maxStack := 7 }
      match identityExpr noShapeRecognizers seeded' (lit 0x120) QuotientTarget.main none with
      | .error _ => false
      | .ok s => s.stackDepth == 0 && s.maxStack == 7 && s.vars == []

/-! ### GATE 7 - the Yul bridge -/

/-- A panic whose message contains a given fragment. -/
def panicContains {α : Type} (x : Except QVMFault α) (frag : String) : Bool :=
  match x with
  | .error (QVMFault.panic s) => s.contains frag
  | _ => false

/-- rust: QVM:1245-1281 (parse_expr) and QVM:4174-4196 (yul_assignment). The exact subset
    the Evaluator emits, including the token-offset pointer form add(BETA_MPTR, 32), a
    decimal literal, a hex literal, and the nesting the certifier's own generated lines
    use. Rules out: a parser that accepts sub(x, r), an addmod with the wrong modulus, or
    one that drops the has_let distinction. -/
def parseExpr_yulSubset_ok : Bool :=
  (match parseExprTop builderDefault
      "addmod(mload(256), mulmod(3, mload(BETA_MPTR), r), r)" with
   | .ok e => e == QuotientExpr.add (lit 256) (QuotientExpr.mul (QuotientExpr.const 3)
        (QuotientExpr.mem (.token qMemBeta)))
   | .error _ => false) &&
  (match parseExprTop builderDefault "sub(r, mload(add(BETA_MPTR, 32)))" with
   | .ok e => e == QuotientExpr.neg (QuotientExpr.mem (.tokenOffset qMemBeta 32))
   | .error _ => false) &&
  (match parseExprTop builderDefault "0x1f" with
   | .ok e => e == QuotientExpr.const 31
   | .error _ => false) &&
  (match parseExprTop builderDefault "31" with
   | .ok e => e == QuotientExpr.const 31
   | .error _ => false) &&
  (yulAssignment "let t0 := mload(256)" ==
     some { dst := "t0", expr := "mload(256)", hasLet := true }) &&
  (yulAssignment "t0 := mload(256)" ==
     some { dst := "t0", expr := "mload(256)", hasLet := false }) &&
  (yulAssignment "lett t0 := 1" == none) &&
  (yulAssignment "let t0 := " == none) &&
  isPanicAt (parseExprTop builderDefault "addmod(mload(256), 1)") siteAddmodArity &&
  isPanicAt (parseExprTop builderDefault "addmod(mload(256), 1, q)") siteAddmodModulus &&
  isPanicAt (parseExprTop builderDefault "sub(1, 2)") siteSubForm &&
  isPanicAt (parseExprTop builderDefault "nosuchvar") siteUnknownVar &&
  isPanicAt (parseExprTop builderDefault "mload(nosuch)") siteMloadPointer &&
  panicContains (parseExprTop builderDefault "1f") "invalid U256" &&
  (match splitTopLevel "addmod(1, 2)" with
   | .ok xs => xs == ["addmod(1, 2)"]
   | .error _ => false) &&
  (match splitTopLevel "1, addmod(2, 3), 4" with
   | .ok xs => xs == ["1", "addmod(2, 3)", "4"]
   | .error _ => false) &&
  (match callArgs "f(a)" "g" with
   | .ok r => r == none
   | .error _ => false)

/-- rust: QVM:1233-1243 (assignment). The variable is remembered and then usable by name,
    a re-assignment replaces rather than duplicates, and an unparseable line is the expect
    at QVM:1240. -/
def assignment_remembersVars_ok : Bool :=
  match assignment builderDefault "let t0 := mulmod(3, mload(256), r)" with
  | .error _ => false
  | .ok s =>
      s.vars.length == 1 &&
        (match parseExprTop s "t0" with
         | .ok e => e == QuotientExpr.mul (QuotientExpr.const 3) (lit 256)
         | .error _ => false) &&
      (match assignment s "let t0 := mload(288)" with
       | .error _ => false
       | .ok s2 => s2.vars.length == 1) &&
      (match assignment builderDefault "not an assignment" with
       | .error _ => true
       | .ok _ => false)

/-! ### GATE 8 - the hooks, end to end -/

/-- P-09e's contract, tested from this side: with a LIN7 / BILIN7_ROW / BILIN7_PAIRWISE
    recognizer supplied, the fused opcode is emitted AND the interpreter agrees with the
    generic tree the shape denotes. The expectation is computed from the expression, not
    from the opcode, so this is a real cross-check of the byte layout of all three limb
    forms against QVR:377-432. Rules out: slot and pointer swapped, the row's lhs written
    after the block instead of before, and the pairwise coefficient block indexed i * 7 + j
    instead of i + j. -/
def limbHooks_endToEnd_ok : Bool :=
  (match emitExprTop lin7Hooks builderDefault lin7Expr with
   | .error _ => false
   | .ok s => s.bytes.getD 0 0 == qOpLin7 && s.bytes.length == 1 + 7 * 3 &&
       okIs (runProg s.bytes s.consts) (oracle lin7Expr)) &&
  (match emitExprTop rowHooks builderDefault rowExpr with
   | .error _ => false
   | .ok s => s.bytes.getD 0 0 == qOpBilin7Row &&
       okIs (runProg s.bytes s.consts) (oracle rowExpr)) &&
  (match emitExprTop pwHooks builderDefault pwExpr with
   | .error _ => false
   | .ok s => s.bytes.getD 0 0 == qOpBilin7Pairwise && s.bytes.length == 1 + 4 + 13 &&
       okIs (runProg s.bytes s.consts) (oracle pwExpr))

/-- The MODARITH7 form end to end: flags, cond, const, five counts and five blocks,
    checked by running it. This is the densest byte layout in the file and the one most
    likely to be mis-ordered, and the interpreter's own modarith7Form is the reference. -/
def modarith7Hook_endToEnd_ok : Bool :=
  match emitExprTop maHooks builderDefault maExpr with
  | .error _ => false
  | .ok s =>
      s.bytes.getD 0 0 == qOpModarith7 && s.bytes.getD 1 0 == 0x03 &&
        s.bytes.getD 2 0 == 0x02 && s.bytes.getD 3 0 == 0x60 &&
        s.bytes.getD 4 0 == 0 && s.bytes.getD 5 0 == 1 && s.bytes.getD 6 0 == 1 &&
        s.bytes.getD 7 0 == 1 && s.bytes.getD 8 0 == 1 && s.bytes.getD 9 0 == 1 &&
        okIs (runProg s.bytes s.consts) (oracle maExpr)

/-- The pow5 and decomposition hooks, and hazard 6's false branch: with limb_vm_ops off,
    the same hook must NOT fire and the generic path must still evaluate correctly. -/
def pow5DecompAndToggleBranches_ok : Bool :=
  (match emitExprTop pow5Hooks builderDefault ePow5 with
   | .error _ => false
   | .ok s => s.bytes.getD (s.bytes.length - 1) 0 == qOpPow5 &&
       okIs (runProg s.bytes s.consts) (oracle ePow5)) &&
  (match emitExprTop decompHooks builderDefault decompTarget with
   | .error _ => false
   | .ok s => s.bytes.contains qOpLin7 &&
       okIs (runProg s.bytes s.consts) (oracle decompTarget)) &&
  (let off := { builderDefault with limbVmOps := false }
   (match emitExprTop lin7Hooks off lin7Expr with
    | .error _ => false
    | .ok s => s.bytes.getD 0 0 != qOpLin7 && okIs (runProg s.bytes s.consts)
        (oracle lin7Expr)) &&
   (match emitExprTop maHooks off maExpr with
    | .error _ => false
    | .ok s => s.bytes.getD 0 0 != qOpModarith7 && okIs (runProg s.bytes s.consts)
        (oracle maExpr)))

/-- HAZARD 3's frontier, demonstrated rather than asserted away. emit_affine_terms' doc
    (QVM:1396) says the matched slice is always non-empty; nothing in the type enforces it.
    With a hook that returns an empty matched list, the decomposition path emits the
    residue, then op_binary(ADD) pops a stack that holds one value: the BUILDER's counter
    goes 1 -> 0 and reports no problem, while the program it emitted makes the interpreter
    underflow. The gate records that the port does not catch this, which is the honest
    statement of what P-09e owes: a recognizer must never return an empty matched list. -/
def emptyMatchedHookIsAFrontier_ok : Bool :=
  (match emitExprTop emptyMatchedHooks (stateWithConsts 249) decompTarget with
   | .error _ => false
   | .ok s =>
       s.stackDepth == 0 &&
         (match runProg s.bytes s.consts with
          | .error _ => true
          | .ok _ => false)) &&
    (match emitExprTop decompHooks (stateWithConsts 249) decompTarget with
     | .error _ => false
     | .ok s => ! (s.bytes.contains qOpLin7) && s.bytes.contains qOpAdd)

/-! ### GATE 9 - the artifact's usage fields, and the fuel crutch -/

/-- rust: QVM:1976-1994 (quotient_program_usage) on the finalized bytes: opcodes sorted
    ascending and distinct (push_unique_u8 sorts after each insert), and the memory tokens
    collected from the two token opcodes only. Pinned on eCert, whose program is the nine
    bytes gate 2 pins, so the expected set is checkable by hand. Rules out: usage being
    computed on the uncompacted stream (which would list the RUN members instead of the
    RUN opcode), and tokens leaking from unrelated operand bytes. -/
def finish_usageFields_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault eCert QuotientTarget.main none >>= finish with
  | .error _ => false
  | .ok build =>
      qvmBytesToNats build.usedOps == [0x03, 0x07, 0x09, 0x0a, 0x10] &&
        qvmBytesToNats build.usedMemTokens == [qMemBeta] &&
        (qvmBytesToNats build.bytes).length == 9 &&
        build.consts == [11] && build.maxStack == 2

/-- The usage walk on a compacted run program lists the RUN opcode, not the members it
    replaced - which is exactly what finish's ordering guarantees and what the template
    needs to render the right switch arms. -/
def usage_followsCompaction_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault eRunLin4 QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      match quotientProgramUsage s.bytes with
      | .error _ => false
      | .ok (rawOps, _) =>
          match finish s with
          | .error _ => false
          | .ok build =>
              let finOps := qvmBytesToNats build.usedOps
              rawOps.contains qOpAddMulConstU8MemU16 &&
                ! (rawOps.contains qOpRunAddMulConstU8MemU16) &&
                finOps.contains qOpRunAddMulConstU8MemU16 &&
                ! (finOps.contains qOpAddMulConstU8MemU16) &&
                finOps == natSortAsc finOps &&
                finOps.all fun o => o < 256

/-- HAZARD 1 and hazard 4 together, at the artifact boundary: finish must hand back the
    COMPACTED stream, not the buffer it was given. Nothing downstream can tell the
    difference by VALUE (compaction preserves it, which is what gate 3 proves), so this
    is the gate that pins the ordering question - if finish ever stopped compacting, the
    VK payload would grow and the certifier's seed would change. Rules out: finish
    returning self.bytes, and a compaction that becomes a no-op. -/
def finish_actuallyCompacts_ok : Bool :=
  match identityExpr noShapeRecognizers builderDefault eRunLin4 QuotientTarget.main none with
  | .error _ => false
  | .ok s =>
      match finish s with
      | .error _ => false
      | .ok build =>
          let out := qvmBytesToNats build.bytes
          out != s.bytes && out.length < s.bytes.length &&
            out.getD 3 0 == qOpRunAddMulConstU8MemU16 &&
            (match compactQuotientRuns s.bytes with
             | .ok c => out == c
             | .error _ => false)

/-- R10's fuel claim: the emitter bound is never reached by any fixture under any hook set,
    so the fuel is a totality crutch and not a behaviour the port added. -/
def emitterFuelNeverBinds_ok : Bool :=
  allExprs.all fun (_, e) =>
    allHooks.all fun (_, r) =>
      match emitExpr r (emitFuel e) builderDefault e with
      | .error (QVMFault.panic s) => ! (s.contains "fuel exhausted")
      | _ => true

/-- The same claim for parse_expr's fuel. -/
def parseFuelNeverBinds_ok : Bool :=
  ["addmod(mload(256), mulmod(3, mload(BETA_MPTR), r), r)",
   "sub(r, mload(add(BETA_MPTR, 32)))",
   "mulmod(mload(add(X_MPTR, 64)), addmod(1, 2, r), r)",
   "0x1f", "mload(4294967295)"].all fun line =>
    match parseExprTop builderDefault line with
    | .error (QVMFault.panic s) => ! (s.contains "fuel exhausted")
    | _ => true

/-- The compaction walker's own fuel: never binds on any fixture, and a truncated program
    is a panic rather than a hang. -/
def compactionFuelNeverBinds_ok : Bool :=
  allExprs.all fun (_, e) =>
    match emitExprTop noShapeRecognizers builderDefault e with
    | .error _ => false
    | .ok s => match compactQuotientRuns s.bytes with
        | .error (QVMFault.panic msg) => ! (msg.contains "fuel exhausted")
        | _ => true

/-- R-48's distinctness precondition, asserted before the byte-comparison gates are read
    rather than assumed: the fixture pointers are seven distinct values and the two seeds
    differ from VmReference's. -/
def fixturesAreNonDegenerate_ok : Bool :=
  bPtrsDistinct && bSeed != Midfall.Generator.QuotientVmRefKats.refSeedA &&
    bSeed != Midfall.Generator.QuotientVmRefKats.refSeedB &&
    (oracle (lit 0x100)) != (oracle (lit 0x120)) &&
    (oracle (lit 0x100)) != (oracle (QuotientExpr.mem (.token qMemBeta))) &&
    (oracle eCert) != (oracle eNeg) && (oracle eRunLin4) != (oracle eRunLin3)

/-! ### Artifact gates (D-P19: mod.rs and config.rs are opened while these evaluate) -/

/-- The two candidate paths, relative to formal/ (where checks.sh and kat_gate.py run) and
    to the repo root. Same convention as VmTypes' templatePathCandidates and VmReference's
    referencePathCandidates. -/
def vmModPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"]

/-- The lowering config, home of the R8 toggle. -/
def configPathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/config.rs",
   "proofs/solidity-verifier/src/lowering/config.rs"]

/-- A missing or truncated artifact is a RED, never a silent true: mod.rs is 166317 bytes
    at HEAD, so anything much smaller is a wrong path (docs/plans/README.md, D-P19). -/
def vmModReadOk (src : String) : Bool := src.length > 150000
def configReadOk (src : String) : Bool := src.length > 1000

/-- Read mod.rs from either candidate path. -/
def readVmMod : IO String :=
  vmModPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

/-- Read config.rs from either candidate path. -/
def readConfig : IO String :=
  configPathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

/-- REACHABILITY GATE, the first #eval of the section. Rules out: mod.rs or config.rs
    moving, being renamed, or a wrong relative path, which is the failure mode R-38
    finding 1 is about. -/
def artifactReachable_ok : IO Bool := do
  let vm ← readVmMod
  let cfg ← readConfig
  pure (vmModReadOk vm && configReadOk cfg
    && vm.contains "impl QuotientProgramBuilder"
    && vm.contains "pub(crate) fn finish(self) -> QuotientProgramBuild"
    && vm.contains "pub(crate) fn compact_quotient_runs"
    && cfg.contains "DEFAULT_QUOTIENT_LIMB_VM_OPS")

/-- The offset of the first occurrence of needle in hay, in bytes, or none. Built out of
    splitOn so the artifact gates can compare ORDER and not just presence. -/
def offsetOf (needle : String) (hay : String) : Option Nat :=
  if !hay.contains needle then none else some ((hay.splitOn needle).head?.getD hay).length

/-- A window of the artifact starting at the first occurrence of marker, so a gate can talk
    about one Rust item without re-deriving line numbers. String.take puts the length
    first, so this is an application rather than dot notation. -/
def windowAfter (marker : String) (vm : String) (size : Nat) : String :=
  let after := ((vm.splitOn marker).drop 1).head?.getD ""
  (after.take size).toString

/-- rust: QVM:1211-1231 (finish), read back out of the artifact. HAZARD 4's ordering
    question, answered by the source rather than by the port: compaction runs FIRST, then
    validation, then usage, and usage is called on the compacted local bytes and not on
    self.bytes. Rules out: a Rust-side edit that reorders these three, which would change
    what the certifier hashes while leaving every Lean paste intact. -/
def finishOrdering_artifact_ok : IO Bool := do
  let vm ← readVmMod
  let body := windowAfter "pub(crate) fn finish(self) -> QuotientProgramBuild" vm 1200
  pure (vmModReadOk vm && body.contains "compact_quotient_runs"
    && body.contains "validate_quotient_program" && body.contains "quotient_program_usage"
    && (offsetOf "compact_quotient_runs" body).getD 100000 <
        (offsetOf "validate_quotient_program" body).getD 0
    && (offsetOf "validate_quotient_program" body).getD 100000 <
        (offsetOf "quotient_program_usage" body).getD 0
    && body.contains "quotient_program_usage(&bytes)"
    && ! (body.contains "quotient_program_usage(&self.bytes)"))

/-- HAZARD 3, read from the artifact. Every predicate a try_emit consults before it commits
    takes &self, not &mut self, so the borrow checker and not a test is what makes a
    rejected attempt unable to touch the buffer. Rules out: a Rust-side edit that turns one
    of these six into a &mut self predicate (letting peek_u8_const_slots insert, say), which
    would make a rejected limb shape leave constants behind. The Lean port mirrors the same
    discipline: all six are pure functions of the state here. -/
def tryEmitPredicatesAreImmutable_artifact_ok : IO Bool := do
  let vm ← readVmMod
  let needles : List String :=
    ["fn peek_u8_const_slots(&self, values: &[U256]) -> Option<Vec<u8>>",
     "fn const_fits_u8_slot(&self, value: U256) -> bool",
     "fn product_add_macro(&self, leaves: &[QuotientLeaf]) -> Option<QuotientProductAdd>",
     "fn product_add_fits_u8_slot(&self, product: &QuotientProductAdd) -> bool",
     "fn modarith7_shape_has_u8_const_slots(&self, shape: &QuotientModarith7Shape) -> bool",
     "fn limb_shape_has_u8_const_slots(&self, shape: &QuotientLimbShape) -> bool"]
  pure (vmModReadOk vm && needles.all (fun needle => vm.contains needle))

/-- HAZARD 4's "if the Rust has no such test, say so". The reference's only compaction test
    is byte_compaction_groups_mixed_affine_sum_terms (QVM:4280-4320); it asserts the
    AFFINE_SUM byte layout and then calls validate_quotient_program. It never runs the
    compacted program through the interpreter, so the Rust has NO test that compaction
    preserves the evaluated field element, which is what
    compaction_preservesInterpreterResult_ok supplies. Rules out: this finding going stale.
    If a Rust-side test ever evaluates a compacted program this gate goes red and the
    finding has to be withdrawn. -/
def noRustCompactionResultTest_artifact_ok : IO Bool := do
  let vm ← readVmMod
  let test := windowAfter "fn byte_compaction_groups_mixed_affine_sum_terms" vm 2000
  pure (vmModReadOk vm && test.contains "compact_quotient_runs"
    && test.contains "validate_quotient_program" && ! (test.contains "eval_quotient_identity")
    && ! (test.contains "eval_quotient_vm"))

/-- R8 and HAZARD 6: the deployed branch, read from config.rs rather than pasted, and tied
    to the Lean default. Rules out: config.rs flipping the constant while the Lean port keeps
    the old value, which would make the port describe a program the deployed verifier never
    emits. -/
def limbVmOps_deployedBranch_ok : IO Bool := do
  let cfg ← readConfig
  pure (configReadOk cfg
    && cfg.contains "pub(crate) const DEFAULT_QUOTIENT_LIMB_VM_OPS: bool = true;"
    && defaultQuotientLimbVmOps == true && builderDefault.limbVmOps == true
    && (withLimbVmOps true).limbVmOps == true && (withLimbVmOps false).limbVmOps == false)


end QuotientVmBuilderKats

end Midfall.Generator

#eval Midfall.Generator.QuotientVmBuilderKats.artifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.finishOrdering_artifact_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.tryEmitPredicatesAreImmutable_artifact_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.noRustCompactionResultTest_artifact_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.limbVmOps_deployedBranch_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.fixturesAreNonDegenerate_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.finishIdentity_executesAndAgrees_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.emitBytes_pinnedForSmallExpression_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.emitChain_isAppendOnly_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.finish_constsAreTheSlotTable_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.tryEmit_rejected_leavesStateUnchanged_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.tryEmit_accepted_doesChangeState_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.limbPreflight_slotBoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.compaction_preservesInterpreterResult_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.compaction_preservesResult_multiIdentity_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.fusedOperandOrder_pinned_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.compaction_byteLayout_rustTest_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.compaction_thresholdBoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.compaction_isIdempotent_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.opLen_walksEveryFixtureExactly_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.u16Boundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.u24Boundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.constFitsU8SlotBoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.peekU8ConstSlotsBoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.emitConst_encodingBoundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.emitMemLiteral_boundary_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.constSlot_dedupAndOverflow_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.finishMaxStack_agreesWithInterpreter_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.stackPanics_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.foldIdentity_selectorEncoding_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.nativeMarkers_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.identityExpr_resetsVarsAndDepth_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.parseExpr_yulSubset_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.assignment_remembersVars_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.limbHooks_endToEnd_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.modarith7Hook_endToEnd_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.pow5DecompAndToggleBranches_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.emptyMatchedHookIsAFrontier_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.finish_usageFields_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.usage_followsCompaction_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.finish_actuallyCompacts_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.emitterFuelNeverBinds_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.parseFuelNeverBinds_ok -- expect true
#eval Midfall.Generator.QuotientVmBuilderKats.compactionFuelNeverBinds_ok -- expect true
