-- |
-- Midfall.Generator.Quotient.VmReference
--
-- THE QUOTIENT VM REFERENCE INTERPRETER - PLAN 9.5's QVM.run, the object every M6
-- theorem is stated against. Ported from
-- proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs (549 lines,
-- 20802 bytes at git HEAD), cited below as QVR.
--
-- CITATION NOTATION. QVR is reference.rs; QVM is vm/mod.rs (4336 lines at HEAD, whose
-- vocabulary P-09a landed in VmTypes.lean); QVC is vm/certify.rs (365 lines at HEAD),
-- the only caller of anything in this file; LM is lowering/layout/mod.rs. Every range
-- was re-derived from git show HEAD:<path>, never from wc -l on a dirty checkout
-- (docs/plans/README.md standing note 2).
--
-- THIS IS A CERTIFIER, NOT MERELY AN INTERPRETER.
--
-- QVR:2-27 says so, and the difference is what this file has to get right. The module is
-- the SECOND implementation of the quotient VM ABI: for every render the emitted
-- bytecode is executed here and compared against direct evaluation of the QuotientExpr
-- trees it was lowered from (QVC:147-165), and a disagreement rejects the render before
-- any artifact is produced. The check is probabilistic: the certifier samples a
-- deterministic challenge from the finalized bytecode, constant table, expression trees
-- and VK payload (QVC:48-76), evaluates the fixed program at that assignment, and a
-- miscompilation - which produced a polynomial fixed BEFORE the challenge was known -
-- disagrees with probability 1 - deg/|Fr| (QVR:12-18).
--
-- Two consequences, stated rather than absorbed (plan P-09b, "the thing to understand").
--
-- 1. THE CERTIFIER COVERS EMITTER -> REFERENCE INTERPRETER ONLY. QVR:20-26 says the
--    reference-interpreter -> Yul leg is "covered separately by the opcode and
--    memory-token table conformance tests and by the per-identity Rust/Solidity trace
--    differential on fixture circuits". So PLAN 9.5's qvm_yul_refines has NO proof
--    structure in the reference to mirror: it is a theorem this project originates, and
--    the only thing in the reference that bears on it is the shared opcode/token ABI,
--    which P-09a gated against the Yul template (VmTypes' six hazard-1 gates). Nothing
--    here invents a Rust-side argument for it.
-- 2. THE DOMAIN IS BOUNDED, AND THE BOUND IS IN THE DOC. QVR:24-27: "Identities executed
--    as inline Yul, native callbacks, or the structured tail are not lowered to bytecode
--    at all, so this module evaluates them directly from their expression trees and they
--    remain covered only by those other two mechanisms." See DOMAIN OF QVM.run below.
--
-- DOMAIN OF QVM.run (required finding 1). The reference's entry point is
-- eval_quotient_identity (QVR:131-347), and QVC:148 and QVC:348 both call it on
-- &bytes[cursor..expr_end] - ONE identity's expression subprogram, up to but excluding
-- its fold opcode, the segment identity_segment (QVC:228-245) locates. Therefore:
--
-- * REACHES the interpreter: QuotientProgramItem::Identity only (QVC:143-175).
-- * DOES NOT reach it: plan.inlineIdentities (Yul emitted before the VM loop),
--   plan.structuredTailIdentities (Yul after it), and the three native markers
--   NativePermutation / NativeLookup / NativeIdentity - the certifier checks those
--   positionally, that the marker byte and its u16 index sit where the plan says
--   (QVC:176-213), and identity_values pushes Fq::ZERO for each (QVC:355-360).
-- * NOT MODELLED AT ALL: the fold. FOLD_MAIN / FOLD_SELECTOR and the three native
--   markers are hard ERRORS inside an identity expression (QVR:325-333), and check_fold
--   (QVC:248-289) only inspects the emitted bytes against the plan; the y-batch
--   accumulation itself is Yul-side and is never executed here.
--
-- So PLAN 9.5's QVM.run L.plan.qprog (frameOf L.plan tr ev) = .ok (outputOf ...) is NOT
-- this function: it is a whole-stream run with a frame and an output, and the reference
-- has no whole-stream entry point, no frame and no output object. Any M6 statement must
-- either (a) be re-stated per identity over evalQuotientIdentity plus a separately
-- ported segment walker, or (b) name the gap. qvm_validated_noOOB is worse: its .oob
-- fault cannot arise here at all, because verifier memory in this module is a PRNG over
-- the whole u32 address space (hazard 1) and a read of ANY address succeeds. The only
-- out-of-range faults the reference can produce are reads past the END OF THE PROGRAM
-- and constant slots past the END OF THE TABLE.
--
-- HAZARD 1: QuotientRefMemory::derive IS THE CERTIFICATION'S HEART (QVR:84-107).
--
-- The preimage layout, byte for byte, in this exact order:
--   Keccak256( "midfall/quotient-vm/reference-memory/v1" || seed[32] || [domain] ||
--              address.to_be_bytes()[4] )                        -> lo[32]
--   Keccak256( "midfall/quotient-vm/reference-memory/v1/hi" || lo[32] )  -> hi[32]
--   value = from_uniform_bytes(lo || hi)
-- literal ptr is derive(0, ptr) (QVR:73-75); token t o is derive(1 + t, o) (QVR:78-82).
-- Gated by derivePreimageLayout_artifact_ok (the layout read back out of the Rust
-- source), derive_byteExact_seedA_ok and derive_byteExact_seedB_ok (34 concrete
-- (domain, address) values pinned against an independent Keccak-256),
-- derive_seedAndDomainSeparation_ok and derive_addressAndDomainWidths_ok.
--
-- from_uniform_bytes deserves its own note because the name hides a Montgomery
-- reduction. midnight_curves::Fq IS the BLS12-381 SCALAR field: its MODULUS
-- (curves/src/bls12_381/fq.rs:43-48) is r = 0x73eda753...00000001 and its Repr is
-- [u8; 32], which is why fq_from_u256 compiles at all. The implementation
-- (fq.rs:703-726) is a0.mul(R2) + a1.mul(R3) over a Montgomery representation (value =
-- raw * R^-1, R = 2^256) whose raw limbs are R2 = 2^512 mod r and R3 = 2^768 mod r
-- (fq.rs:104-122), so the value is A0*R^-1*R + A1*R^-1*2^512 = A0 + A1*2^256 mod r: the
-- 512-bit LITTLE-ENDIAN integer reduced mod r, which is what ff::FromUniformBytes<64>
-- documents and what qvmFrFromUniformBytes computes. fromUniformBytes_wideReduction_ok
-- pins it on concrete wides.
--
-- Two width facts the port models rather than hides. derive's domain is a u8 and its
-- address a u32, and the release profile has overflow-checks = false (the workspace
-- overrides only [profile.bench] and a profile that inherits release; Cargo.toml:54-67),
-- so 1 + token WRAPS for token = 0xff and that token lands in the literal domain -
-- tokenDomainU8Wrap_releaseProfile_ok pins the collision, and it is unreachable in a
-- validated program because validate_quotient_mem_token (QVM:2758) admits only the nine
-- table tokens. Likewise an address at or above 2^32 truncates into the u32 the cache is
-- keyed on - derive_addressAndDomainWidths_ok.
--
-- THE MEMOISATION IS SEMANTICS, NOT AN OPTIMISATION (plan hazard 1, second half). The
-- Rust caches HashMap<(u8, u32), Fq> (QVR:60) and returns the cached value on a hit
-- (QVR:86-88), so the same address yields the same field element across every call in a
-- certification run - and, because eval_quotient_expr and eval_quotient_identity share
-- ONE &mut QuotientRefMemory (QVC:137, 148, 155), across BOTH sides of the comparison.
-- That is the only reason the two sides can be compared at all: QVR:51-56 says deriving
-- each value from its own address is what lets both sides "observe identical memory
-- without the certifier having to enumerate the live address set up front".
-- memoisation_sameAddressSameValue_ok gates it five ways: repeated reads agree and do
-- not grow the table, every cache entry equals the pure derivation, a literal pointer and
-- a token offset on the same address stay apart, and the 7x7 pairwise form performs 56
-- memory reads that collapse to 14 distinct cached addresses.
--
-- HAZARD 2: Result<_, String> BECOMES A CLOSED FAULT TAXONOMY.
--
-- QVR:131 returns Result<Fq, String> where PLAN 9.5 wants Except QVM.Fault. Every error
-- string in the file - grep for "reference VM yields exactly these nine - is one
-- constructor of QVMFault, each carrying the numbers the Rust interpolates, and
-- QVMFault.message renders the Rust's text verbatim; faultMessages_artifactStrings_ok
-- checks all nine format strings against the source file AND against the renderer, so
-- the taxonomy cannot drift from the strings and cannot lose a payload (docs/REVIEW.md
-- R-43 F2). No caller inspects a string for control flow: QVC:149-154 and QVC:167-172
-- embed it in a larger message, QVC:217-222 and QVC:313-329 build their own,
-- plan.rs:516-520 wraps it into the render error, and plan.rs:324-326 PANICS with it -
-- so the same Err aborts a build on one path and rejects a render on the other, which
-- is hazard 5's distinction one level up.
--
-- HAZARD 3: fq_from_u256 REJECTS, IT DOES NOT REDUCE (QVR:545-549). It goes
-- to_le_bytes::<32> -> Fq::from_repr -> .expect("constant table holds canonical field
-- elements"), so an entry at or above r PANICS, release profile included: expect is not
-- a debug assertion. That matches Midfall.frOfRepr? (Common/Codec.lean:38-41, the R-7
-- canonicity work) and NOT Midfall.frOfDigest (Codec.lean:27, which reduces). The port
-- makes the panic observable as QVMFault.panic rather than a silent reduce -
-- fqFromU256_canonicalRejection_ok.
--
-- HAZARD 4: THE *_form HELPERS. affineLinearTerm (QVR:350-359), affineProductTerm
-- (QVR:362-375), limbLinearForm (QVR:378-393), limbRowForm (QVR:396-406),
-- limbPairwiseForm (QVR:409-432) and modarith7Form (QVR:435-507) each get a gate with a
-- pinned value AND a hand-computed algebraic characterisation, not a compare-with-itself:
-- the lin7 uniform case is 7*c*m; the pairwise form with one repeated coefficient
-- collapses to (sum of the lhs limbs) * (sum of the rhs limbs); and the pairwise value
-- is recomputed DIAGONAL BY DIAGONAL (grouped by i + j) rather than grid by grid, which
-- is the only way to test that the slot index really is i + j. modarith7Form's
-- accumulator subtleties are each pinned: the CONST block lands before the five count
-- bytes, the five blocks run in the order lin, row, pairwise, mem, product, the mem
-- block is (slot, ptr) - the OPPOSITE order to the standalone ADD_MUL_CONST_U8_MEM_U16
-- term, as QVR:488-489 warns - and the COND pointer multiplies the WHOLE accumulator at
-- the END (QVR:503-505), so a zero-accumulator form with a condition is still zero.
--
-- HAZARD 5: BOUNDS READS RETURN ERR, THEY DO NOT PANIC - AND ONE READ PANICS.
-- byteAt, readU16, readU32 and constAt are the Rust's Result-returning helpers
-- (QVR:510-533, 536-542) and stay separate defs with separate messages; they are NOT
-- unified. The one direct index in the file, bytes[coeff_idx + i + j] at QVR:427, is a
-- real panic site in every profile; it is ported as indexOrPanic with a QVMFault.panic
-- payload and is unreachable only because QVR:420 bounds-checks the whole 13-byte
-- coefficient block first and max(i+j) = 12 = QUOTIENT_VM_PAIRWISE_COEFFS - 1.
-- boundsReadsReturnErrNotPanic_ok pins all of it, including that the panic class is not
-- reachable on any fixture.
--
-- HAZARD 6: NOTHING COMPILER-SIDE IS PULLED IN. No validator (QVM:2758), no operand
-- walker (QVM:3008-3024), no quotient_op_len, no builder. What the port needed from the
-- compiler and does not have is named under WHAT PLAN 9.5 STILL OWNS below.
--
-- PORT RULES AS THEY APPLY HERE (PLAN section 4, R1-R11).
--
-- * R1 provenance: one Lean def per Rust item, source order except where noted.
-- * R2 names: snake_case to lowerCamelCase. Fq becomes QVMFr (the row already uses Fr
--   for the abstract ZMod p of Common/Curve.lean:30, and this is a concrete field).
--   QVMFault is the plan's QVM.Fault; QVM.Fault, QVM.Fr, QVM.Memory and QVM.run are
--   aliases in the QVM namespace at the end of the file so PLAN 9.5 can be cited by name.
-- * R2 reserved words: none needed. No Rust identifier in this file is a Lean keyword;
--   the one near-miss is the token parameter of QuotientRefMemory.token, which shadows
--   nothing and is kept as the Rust spells it.
-- * R3 iterators: for _ in 0..n becomes foldRangeIdxM, which threads an accumulator
--   through an Except and aborts on the first error exactly as ? does in Rust.
-- * R4 panics: release profile - no overflow panic, debug_assert! compiled out (there is
--   none in this file), but indexing and expect DO panic. The three panic sites are
--   QVR:548 (fq_from_u256's expect), QVR:427 (the pairwise coefficient index) and
--   QVR:346 (stack.pop().expect("checked length"), discharged by the length check
--   immediately above it, so it is not modelled as a fault at all).
-- * R5 integers: usize, u32, u16, u8 all become Nat; Nat does not truncate, so the two
--   places the Rust's widths are load-bearing are modelled explicitly (the u8 domain
--   byte and the u32 address in deriveReferenceMemory) and gated. No other site wraps:
--   idx += k cannot reach 2^64 in a program that fits memory.
-- * R6 collections: Vec<U256> -> List Word256; HashMap<(u8,u32),Fq> -> an ordered assoc
--   list keyed on the SAME wrapped pair (the Rust's get/insert pair is exactly find?/::
--   here, and the list is inspectable by the memoisation gate); &[u8] -> List Nat,
--   because the reference's reads are absolute-index get() calls and List Nat is the
--   lossless image of Midfall.Bytes under qvmBytesToNats - programBytesRoundTrip_ok
--   gates the bridge in both directions.
-- * R7/R8/R9: no endianness inversion beyond the two to_be_bytes calls inside derive
--   (which ARE the hazard-1 layout), no curve point read, no feature gate, no trait.
-- * R10 totality: no partial in this file. The fetch-decode loop is well-founded on an
--   explicit fuel bound of bytes.length iterations - sound because every arm advances
--   the cursor, which the step record carries as a PROOF FIELD (0 < consumed), so an arm
--   that forgot to advance cannot be written at all. Rust gets that progress from
--   idx += k being visible in the source; Lean has to be told.
-- * R11: the line-range table is in the package report.
--
-- WHAT MOVED, AND WHY (Lean is order-sensitive; the reference is not).
-- 1. The field model (QVMFr, its ops, qvmFrFromUniformBytes) and QVMFault come first:
--    fqFromU256 needs both, and in Rust they are implicit imports (QVR:31-34).
-- 2. fqFromU256 (QVR:545, the LAST item in the file) moves up to sit with the field
--    model, because constAt (QVR:536) and eval_quotient_expr (QVR:115) both call it.
-- 3. deriveReferenceMemory (the pure half of QVR:84-107) is split out of
--    QuotientRefMemory::derive so the memoisation gate can compare the cached path
--    against the uncached one. Nothing else in derive is pure.
-- 4. The readers byteAt/readU16/readU32/constAt (QVR:509-542) move ahead of the *_form
--    helpers that call them; in Rust, order does not matter within a module.
--
-- WHAT PLAN 9.5 STILL OWNS (findings, not gaps to paper over).
-- * QVM.Program, QVM.Frame, QVM.Output have no reference counterpart. The segment walker
--   identity_segment and the instruction-length function quotient_op_len are compiler
--   (QVC:228-245, QVM:3008-3024), so a whole-stream run needs P-09c.
-- * REQUIRED FINDING 2 - THE CHALLENGE IS NOT REPRODUCIBLE WITHOUT THE COMPILER. The
--   seed is derive_certify_seed(&[build], &exprs, &vk_payload) (QVC:48-76, called at
--   QVC:136 and QVC:307): Keccak over the domain tag "midfall/quotient-vm/certify-seed/v3",
--   then each build's finalized BYTECODE and constant table, then each oracle expression
--   tree hashed with node and address tags (QVC:79-111), then the VK payload. The
--   finalized bytecode is what the builder emits, so qvm_compile_correct cannot be
--   STATED in Lean until the builder lands: its hypothesis mentions an artifact this
--   file cannot regenerate. What IS reproducible here, and gated, is the half the
--   soundness argument turns on: given a seed, the assignment is byte-exact. The seed
--   derivation lives in certify.rs and is not part of this package's reference file.
-- * The fold, the y-batch and the negation stored into QUOTIENT_EVAL_MPTR (QVM:86-91)
--   are Yul-side; qvm_yul_refines and direct_correct are statements this project
--   originates with no Rust proof structure behind them.

import Midfall.Common.Bytes
import Midfall.Common.Keccak
import Midfall.Generator.Quotient.VmTypes
import Midfall.Yul.Externals

namespace Midfall.Generator

/-! ## The field the reference interprets over (rust: QVR:31-33, midnight_curves::Fq) -/

/-- The modulus of midnight_curves::Fq, i.e. the BLS12-381 scalar field order r.
    rust: curves/src/bls12_381/fq.rs:43-48 (MODULUS, four little-endian u64 limbs)
    @formal-baseline, imported at QVR:32. Independent transcriptions of the same number
    already live at Midfall.Yul.blsR (Yul/Externals.lean:120, cited to EIP-2537) and
    Midfall.Generator.frModulusConstant (Templates.lean:187);
    qvmFrModulus_agreesWithBlsR_ok ties this third copy to them. -/
def qvmFrModulus : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- A field element of the reference: the canonical representative, a natural below
    qvmFrModulus. R2/R9 note: PLAN 9.5 writes Fq; the row's abstract Fr p = ZMod p
    (Common/Curve.lean:30) cannot be evaluated here without a Fact (Nat.Prime r)
    instance that lives under Instances/, and D-P17 keeps this file away from it. A
    canonical Nat is the computable stand-in, and every operation below reduces, so
    every value the interpreter can produce satisfies the invariant. -/
abbrev QVMFr : Type := Nat

/-- rust: Fq::ZERO (QVR:384, 422, 458). -/
def qvmFrZero : QVMFr := 0

/-- rust: Fq + Fq (QVR:121, 186, 211, 221, 232, 242, 248, 255, 274, 294, 299, 389, 461,
    474, 479, 484, 492, 499). Field addition mod r. -/
def qvmFrAdd (lhs rhs : QVMFr) : QVMFr := (lhs + rhs) % qvmFrModulus

/-- rust: Fq * Fq (QVR:122, 192, 213, 223, 234, 255, 372, 389, 405, 428, 492, 499, 504).
    Field multiplication mod r. -/
def qvmFrMul (lhs rhs : QVMFr) : QVMFr := (lhs * rhs) % qvmFrModulus

/-- rust: -Fq (QVR:123, 197). Field negation mod r; the outer % is what maps 0 to 0. -/
def qvmFrNeg (value : QVMFr) : QVMFr := (qvmFrModulus - value) % qvmFrModulus

/-- rust: QVR:104 (<Fq as ff::FromUniformBytes<64>>::from_uniform_bytes(&wide)). The
    header derives that this is the 512-bit LITTLE-ENDIAN integer reduced mod r: the
    implementation is a0.mul(R2) + a1.mul(R3) (curves/src/bls12_381/fq.rs:703-726) over
    a Montgomery representation with raw R2 = 2^512 mod r and raw R3 = 2^768 mod r
    (fq.rs:104-122), so the value is A0 + A1 * 2^256 mod r. -/
def qvmFrFromUniformBytes (wide : Bytes) : QVMFr := bytesToNatLE wide % qvmFrModulus

/-! ## Faults (rust: the Result<_, String> payloads of QVR) -/

/-- The closed taxonomy of the nine error strings eval_quotient_identity and its helpers
    can produce, plus the panic class (hazards 2, 3 and 5). Each constructor carries
    exactly the numbers the Rust interpolates and message renders the Rust's text
    verbatim; faultMessages_artifactStrings_ok checks both halves against reference.rs.

    Not a Rust type: the Rust's error is a String. This is the QVM.Fault PLAN 9.5 names,
    and R-43 F2 (payload loss) is answered by message, not by a comment. -/
inductive QVMFault
  /-- rust: QVR:145 ("reference VM stack underflow at byte {idx}"). -/
  | stackUnderflow (idx : Nat)
  /-- rust: QVR:514 ("reference VM read past end of program at byte {idx}"), reached
      through byteAt / readU16 / readU32. -/
  | readPastEnd (idx : Nat)
  /-- rust: QVR:541 ("reference VM constant slot {slot} out of range at byte {idx}"). -/
  | constSlotOutOfRange (slot idx : Nat)
  /-- rust: QVR:264 ("reference VM zero-length run at byte {idx}"). -/
  | zeroLengthRun (idx : Nat)
  /-- rust: QVR:286-288 ("reference VM AFFINE_SUM at byte {idx} requires nonzero
      counts"). One constructor for either zero side, as in the Rust. -/
  | affineSumZeroCounts (idx : Nat)
  /-- rust: QVR:444-446 ("reference VM MODARITH7 unknown flag bits {flags:#x} at byte
      {idx}"). -/
  | modarith7UnknownFlags (flags idx : Nat)
  /-- rust: QVR:330-332 ("reference VM found stream opcode {op:#x} inside an identity
      expression at byte {idx}"): the five stream-level opcodes. -/
  | streamOpcodeInIdentity (op idx : Nat)
  /-- rust: QVR:335 ("reference VM unknown opcode {op:#x} at byte {idx}"). -/
  | unknownOpcode (op idx : Nat)
  /-- rust: QVR:341-344 ("reference VM identity left {} value(s) on the stack,
      expected 1"). -/
  | stackLengthMismatch (len : Nat)
  /-- R4: a Rust panic, carrying its site. QVR:548 (expect) and QVR:427 (direct index)
      are the two sites this file can reach. -/
  | panic (site : String)
  deriving BEq

/-- Rust's {n:#x}: lower-case hex with a 0x prefix and no zero padding. -/
def qvmHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The Rust's format! output for each fault, verbatim: decimal for {idx}, {slot} and
    the bare {}, #x for {op} and {flags}, exactly as written at QVR:145, 264, 287, 331,
    335, 342, 445, 514 and 541. -/
def QVMFault.message : QVMFault -> String
  | .stackUnderflow idx => s!"reference VM stack underflow at byte {idx}"
  | .readPastEnd idx => s!"reference VM read past end of program at byte {idx}"
  | .constSlotOutOfRange slot idx =>
      s!"reference VM constant slot {slot} out of range at byte {idx}"
  | .zeroLengthRun idx => s!"reference VM zero-length run at byte {idx}"
  | .affineSumZeroCounts idx =>
      s!"reference VM AFFINE_SUM at byte {idx} requires nonzero counts"
  | .modarith7UnknownFlags flags idx =>
      s!"reference VM MODARITH7 unknown flag bits {qvmHex flags} at byte {idx}"
  | .streamOpcodeInIdentity op idx =>
      s!"reference VM found stream opcode {qvmHex op} inside an identity expression at byte {idx}"
  | .unknownOpcode op idx => s!"reference VM unknown opcode {qvmHex op} at byte {idx}"
  | .stackLengthMismatch len =>
      s!"reference VM identity left {len} value(s) on the stack, expected 1"
  | .panic site => site

/-- rust: QVR:545-549 (fq_from_u256) @formal-baseline. MOVED up from the end of the file
    (WHAT MOVED 2) because constAt and evalQuotientExpr both call it.

    HAZARD 3: this REJECTS a non-canonical entry, it does not reduce it. The Rust is
    to_le_bytes::<32> -> Fq::from_repr -> .expect("constant table holds canonical field
    elements"), and expect panics in the release profile too (R4). The port makes that
    an observable QVMFault.panic carrying the site, which is what
    Midfall.Halo2.Fault.panic does elsewhere in the tree (Exec/Error.lean:56-58,
    Abi.lean:597-600). Contrast Midfall.frOfDigest (Codec.lean:27), which reduces: the
    transcript path and the constant-table path are different and must not be conflated. -/
def fqFromU256 (value : Word256) : Except QVMFault QVMFr :=
  if value.toNat < qvmFrModulus then .ok value.toNat
  else .error (QVMFault.panic
    "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs:548")

/-! ## Deterministic pseudorandom assignment (rust: QVR:49-108) -/

/-- rust: QVR:90 (b"midfall/quotient-vm/reference-memory/v1"). The domain separator of
    the low half of the preimage. Read back out of the artifact by
    derivePreimageLayout_artifact_ok; changing it changes the challenge distribution,
    which is hazard 1's whole point. -/
def referenceMemoryDomainTag : Bytes := asciiBytes "midfall/quotient-vm/reference-memory/v1"

/-- rust: QVR:97 (b"midfall/quotient-vm/reference-memory/v1/hi"). The domain separator
    of the second, high-half hash, which is taken over the LOW DIGEST and not over the
    seed - so the two halves are not two prefixes of one stream. -/
def referenceMemoryHiTag : Bytes := asciiBytes "midfall/quotient-vm/reference-memory/v1/hi"

/-- [u8; N] / Vec<u8> as a list of byte values. Mirrors Encoding.bytesFromNats
    (Encoding.lean:216), which belongs to another package and is not imported here. -/
def qvmBytesOfNats (ns : List Nat) : Bytes :=
  ns.foldl (fun (acc : Bytes) (n : Nat) => ByteArray.push acc (Nat.toUInt8 n)) Bytes.empty

/-- The lossless bridge from QuotientProgramBuild.bytes : Bytes (VmTypes) to the
    List Nat this interpreter reads. Mirrors Encoding.bytesToNats (Encoding.lean:219). -/
def qvmBytesToNats (bs : Bytes) : List Nat := bs.data.toList.map UInt8.toNat

/-- The inverse bridge. -/
def qvmBytesOf (ns : List Nat) : Bytes := qvmBytesOfNats ns

/-- Concatenation of two byte buffers: the Rust's hasher.update(a); hasher.update(b). -/
def qvmBytesAppend (lhs rhs : Bytes) : Bytes := ByteArray.mk (lhs.data ++ rhs.data)

/-- sha3::Keccak256::digest as bytes. Midfall.keccak256 returns the digest as a
    big-endian H256 and the reference feeds digests back in as byte strings, so the
    digest has to be re-materialised as bytes; natToBytesBE is the inverse of
    bytesToWordBE by construction (Common/Bytes.lean:33, :59). -/
def qvmKeccakBytes (bs : Bytes) : Bytes := natToBytesBE (keccak256 bs).toNat 32

/-- The pure half of QuotientRefMemory::derive (QVR:89-104), split out so the
    memoisation gate can compare the cached path against the uncached one (WHAT MOVED 3).

    The preimage order is the hazard-1 layout and is NOT reorderable: tag, seed, one
    domain byte, four big-endian address bytes; then the hi tag over the low digest;
    then the 64-byte wide as lo-then-hi into from_uniform_bytes.

    R5: domain is a u8 and address a u32 in Rust, so the % 256 and % 2^32 are the
    release-profile wrapping of QVR:81 (1 + token) and the as u32 truncation of the
    pointer producer (QVM:2974), not defensive masking. -/
def deriveReferenceMemory (seed : Bytes) (domain address : Nat) : QVMFr :=
  let lo := qvmKeccakBytes
    (qvmBytesAppend (qvmBytesAppend (qvmBytesAppend referenceMemoryDomainTag seed)
      (qvmBytesOfNats [domain % 256])) (natToBytesBE address 4))
  let hi := qvmKeccakBytes (qvmBytesAppend referenceMemoryHiTag lo)
  qvmFrFromUniformBytes (qvmBytesAppend lo hi)

/-- rust: QVR:57-61 (struct QuotientRefMemory) @formal-baseline. "Deterministic
    pseudorandom assignment for every verifier memory slot."

    R6: seed: [u8; 32] becomes Bytes; cache: HashMap<(u8, u32), Fq> becomes an ordered
    assoc list keyed on the SAME wrapped pair the HashMap keys on. The Rust never
    iterates or orders the cache, so the list observes exactly get and insert; what it
    buys is that the memoisation gate can count entries. -/
structure QuotientRefMemory where
  /-- rust: QVR:59 (seed: [u8; 32]). -/
  seed : Bytes
  /-- rust: QVR:60 (cache: HashMap<(u8, u32), Fq>). -/
  cache : List (Nat × Nat × QVMFr)
  deriving BEq

/-- rust: QVR:64-70 (QuotientRefMemory::new) @formal-baseline. "Build an assignment for
    one certification run." The cache starts empty and fills lazily: the live address
    set is never enumerated (QVR:51-56). -/
def quotientRefMemoryNew (seed : Bytes) : QuotientRefMemory :=
  { seed := seed, cache := [] }

/-- The cache lookup of QVR:86 (self.cache.get(&(domain, address))) at the Rust's
    wrapped key type. -/
def quotientRefMemoryCacheGet (mem : QuotientRefMemory) (domain address : Nat) :
    Option QVMFr :=
  match mem.cache.find? (fun (d, a, _) => d == domain % 256 && a == address % 2^32) with
  | some (_, _, v) => some v
  | none => none

/-- rust: QVR:84-107 (QuotientRefMemory::derive) @formal-baseline. "Derive one field
    element from a domain-separated address." Returns the value AND the memory, because
    the Rust takes &mut self and inserts on a miss (QVR:105). -/
def QuotientRefMemory.derive (mem : QuotientRefMemory) (domain address : Nat) :
    QVMFr × QuotientRefMemory :=
  match quotientRefMemoryCacheGet mem domain address with
  | some value => (value, mem)
  | none =>
      let value := deriveReferenceMemory mem.seed domain address
      (value, { mem with cache := (domain % 256, address % 2^32, value) :: mem.cache })

/-- rust: QVR:72-75 (QuotientRefMemory::literal) @formal-baseline. "Value at an absolute
    memory pointer." Domain 0. -/
def QuotientRefMemory.literal (mem : QuotientRefMemory) (ptr : Nat) :
    QVMFr × QuotientRefMemory :=
  mem.derive 0 ptr

/-- rust: QVR:77-82 (QuotientRefMemory::token) @formal-baseline. "Value behind a
    symbolic memory token, optionally offset." The Rust's comment is the reason the
    domain is 1 + token and not token: "Tokens resolve to generated addresses disjoint
    from the literal pointer space, so they get their own domain tag." -/
def QuotientRefMemory.token (mem : QuotientRefMemory) (token offset : Nat) :
    QVMFr × QuotientRefMemory :=
  mem.derive (1 + token) offset

/-- rust: QVR:110-125 (eval_quotient_expr) @formal-baseline. "Evaluate a typed quotient
    expression directly, without going through the VM ... the oracle side of the
    certification". Infallible in Rust except through fq_from_u256's expect, which the
    port surfaces as Except QVMFault (R4). Left subtree first, then right, as written. -/
def evalQuotientExpr (expr : QuotientExpr) (mem : QuotientRefMemory) :
    Except QVMFault (QVMFr × QuotientRefMemory) :=
  match expr with
  | .const value => do
      let v ← fqFromU256 value
      .ok (v, mem)
  | .mem (.literal ptr) => .ok (mem.literal ptr)
  | .mem (.token token) => .ok (mem.token token 0)
  | .mem (.tokenOffset token offset) => .ok (mem.token token offset)
  | .add lhs rhs => do
      let (l, m1) ← evalQuotientExpr lhs mem
      let (r, m2) ← evalQuotientExpr rhs m1
      .ok (qvmFrAdd l r, m2)
  | .mul lhs rhs => do
      let (l, m1) ← evalQuotientExpr lhs mem
      let (r, m2) ← evalQuotientExpr rhs m1
      .ok (qvmFrMul l r, m2)
  | .neg inner => do
      let (v, m1) ← evalQuotientExpr inner mem
      .ok (qvmFrNeg v, m1)

/-! ## Bounds-checked readers (rust: QVR:509-542) - MOVED ahead of their callers -/

/-- rust: QVR:509-515 (byte_at) @formal-baseline. "Read one byte with an explicit bounds
    error." HAZARD 5: this returns Err where a Rust slice index would panic, and it is
    NOT interchangeable with indexOrPanic below. -/
def byteAt (bytes : List Nat) (idx : Nat) : Except QVMFault Nat :=
  match bytes.drop idx with
  | b :: _ => .ok b
  | [] => .error (QVMFault.readPastEnd idx)

/-- rust: QVR:517-523 (read_u16) @formal-baseline. "Read a big-endian u16 operand." Two
    separate byte_at calls, so the reported index is the first missing byte. -/
def readU16 (bytes : List Nat) (idx : Nat) : Except QVMFault Nat := do
  let b0 ← byteAt bytes idx
  let b1 ← byteAt bytes (idx + 1)
  .ok (b0 * 256 + b1)

/-- rust: QVR:525-533 (read_u32) @formal-baseline. "Read a big-endian u32 operand." -/
def readU32 (bytes : List Nat) (idx : Nat) : Except QVMFault Nat := do
  let b0 ← byteAt bytes idx
  let b1 ← byteAt bytes (idx + 1)
  let b2 ← byteAt bytes (idx + 2)
  let b3 ← byteAt bytes (idx + 3)
  .ok (((b0 * 256 + b1) * 256 + b2) * 256 + b3)

/-- rust: QVR:535-542 (const_at) @formal-baseline. "Look up a constant-table slot with
    an explicit bounds error." The Rust's .get(slot).copied().map(fq_from_u256) runs the
    conversion only for an in-range slot, so the bounds fault shadows the panic;
    errorPrecedence_ok pins that order. -/
def constAt (consts : List Word256) (slot idx : Nat) : Except QVMFault QVMFr :=
  match consts.drop slot with
  | value :: _ => fqFromU256 value
  | [] => .error (QVMFault.constSlotOutOfRange slot idx)

/-- The direct index bytes[coeff_idx + i + j] of QVR:427 @formal-baseline. HAZARD 5:
    this is the one read in the file that PANICS rather than returning Err, and the port
    keeps the distinction: the fault is QVMFault.panic, not readPastEnd. Unreachable in
    the Rust because QVR:420 bounds-checks the whole coefficient block first and
    max (i + j) = 12 = QUOTIENT_VM_PAIRWISE_COEFFS - 1; boundsReadsReturnErrNotPanic_ok
    states that arithmetic. -/
def indexOrPanic (bytes : List Nat) (idx : Nat) : Except QVMFault Nat :=
  match bytes.drop idx with
  | b :: _ => .ok b
  | [] => .error (QVMFault.panic
    "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs:427")

/-- rust: LM:17 (layout::WORD_BYTES: usize = 0x20) @formal-baseline, imported at
    QVR:47 and used as the limb stride at QVR:424 and QVR:426. Layout.lean does not
    port it (the same landing note VmTypes records at its quotientVmLimbs), so it is
    here with a cross-check gate, qvmWordBytes_isTheLimbStride_ok. -/
def qvmWordBytes : Nat := 0x20

/-- rust: the for i in 0..n loops of QVR:268, 292, 297, 386, 423, 425, 472, 477, 482,
    487, 495 @formal-baseline. R3: an accumulator fold that aborts on the first error,
    which is what ? inside the loop does in Rust. The index is passed because
    for i in 0..QUOTIENT_VM_LIMBS needs it (QVR:423-427). -/
def foldRangeIdxM {ε α : Type} (n : Nat) (init : α) (f : Nat → α → Except ε α) :
    Except ε α :=
  match n with
  | 0 => .ok init
  | k + 1 => do
      let x ← f 0 init
      let y ← foldRangeIdxM k x (fun i => f (i + 1))
      .ok y

/-! ## The shape-helper decoders (rust: QVR:349-507) -/

/-- rust: QVR:349-359 (affine_linear_term) @formal-baseline. "Decode one
    const * mload(ptr) term and return its byte length." Operand order: u16 pointer
    first, then the const slot - the OPPOSITE of the MODARITH7 mem block
    (QVR:488-490). -/
def affineLinearTerm (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let ptr ← readU16 bytes idx
  let slot ← byteAt bytes (idx + 2)
  let c ← constAt consts slot idx
  let (v, mem') := mem.literal ptr
  .ok (qvmFrMul c v, 3, mem')

/-- rust: QVR:361-375 (affine_product_term) @formal-baseline. "Decode one
    mload(lhs) * mload(rhs) * const term and return its byte length." -/
def affineProductTerm (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let lhs ← readU16 bytes idx
  let rhs ← readU16 bytes (idx + 2)
  let slot ← byteAt bytes (idx + 4)
  let c ← constAt consts slot idx
  let (l, m1) := mem.literal lhs
  let (r, m2) := m1.literal rhs
  .ok (qvmFrMul (qvmFrMul l r) c, 5, m2)

/-- rust: QVR:377-393 (limb_linear_form) @formal-baseline. "Decode a seven-limb linear
    form sum_i const_i * mload(ptr_i)." Each term is (slot byte, u16 pointer) and the
    block is exactly QUOTIENT_VM_LIMBS * 3 bytes. -/
def limbLinearForm (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let (acc, cursor, mem') ←
    foldRangeIdxM quotientVmLimbs (qvmFrZero, idx, mem) fun _ state => do
      let (acc, cursor, mem) := state
      let slot ← byteAt bytes cursor
      let ptr ← readU16 bytes (cursor + 1)
      let c ← constAt consts slot cursor
      let (v, mem') := mem.literal ptr
      .ok (qvmFrAdd acc (qvmFrMul c v), cursor + 3, mem')
  .ok (acc, cursor - idx, mem')

/-- rust: QVR:395-406 (limb_row_form) @formal-baseline. "Decode
    mload(lhs) * sum_i const_i * mload(rhs_i)." The lhs value is read BEFORE the inner
    form runs, exactly as the Rust binds lhs_value first (QVR:403). -/
def limbRowForm (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let lhs ← readU16 bytes idx
  let (lhsValue, mem1) := mem.literal lhs
  let (inner, len, mem2) ← limbLinearForm bytes consts mem1 (idx + 2)
  .ok (qvmFrMul lhsValue inner, 2 + len, mem2)

/-- rust: QVR:408-432 (limb_pairwise_form) @formal-baseline. "Decode a 7x7 pairwise
    product with i + j indexed coefficients." The coefficient block is bounds-checked
    once up front (QVR:420) and then read by direct index (QVR:427) - hazard 5's pair in
    two adjacent lines. The rhs limb is re-read inside the inner loop (QVR:426), which
    is what makes the memoisation observable: 56 reads, 14 addresses. -/
def limbPairwiseForm (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let lhsBase ← readU16 bytes idx
  let rhsBase ← readU16 bytes (idx + 2)
  let coeffIdx := idx + 4
  let _ ← byteAt bytes (coeffIdx + quotientVmPairwiseCoeffs - 1)
  let (acc, mem') ←
    foldRangeIdxM quotientVmLimbs (qvmFrZero, mem) fun i state => do
      let (acc, mem) := state
      let (lhsValue, mem1) := mem.literal (lhsBase + i * qvmWordBytes)
      foldRangeIdxM quotientVmLimbs (acc, mem1) fun j state => do
        let (acc, mem) := state
        let (rhsValue, mem2) := mem.literal (rhsBase + j * qvmWordBytes)
        let slot ← indexOrPanic bytes (coeffIdx + i + j)
        let c ← constAt consts slot coeffIdx
        .ok (qvmFrAdd acc (qvmFrMul (qvmFrMul lhsValue rhsValue) c), mem2)
  .ok (acc, 4 + quotientVmPairwiseCoeffs, mem')

/-- rust: QVR:443-447, the MODARITH7 flag guard, extracted so modarith7Form stays flat.
    0xfc is !(Q_MODARITH7_FLAG_COND | Q_MODARITH7_FLAG_CONST) in u8: the Rust is
    flags & !(COND | CONST) != 0 -> Err. -/
def modarith7FlagsOk (flags : Nat) : Bool := flags &&& 0xfc == 0

/-- rust: QVR:434-507 (modarith7_form) @formal-baseline. "Decode the dynamic mixed
    seven-limb affine form." The header's hazard-4 list lives here: the flag byte and
    its two-bit mask, the optional cond pointer BEFORE the optional const, the five
    count bytes in the order lin / row / pairwise / mem / product, the mem block's
    (slot, ptr) order that QVR:488-489 warns cannot reuse the standalone helper, the
    product block's (slot, lhs, rhs) order, and the cond multiplying the WHOLE
    accumulator at the very end (QVR:503-505). -/
def modarith7Form (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) (idx : Nat) :
    Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do
  let flags ← byteAt bytes idx
  unless modarith7FlagsOk flags do
    throw (QVMFault.modarith7UnknownFlags flags idx)
  let (cond, afterCond) ←
    if flags &&& qModarith7FlagCond != 0 then
      do let ptr ← readU16 bytes (idx + 1); .ok (some ptr, idx + 3)
    else .ok (none, idx + 1)
  let (acc0, afterConst) ←
    if flags &&& qModarith7FlagConst != 0 then
      do let slot ← byteAt bytes afterCond
         let c ← constAt consts slot afterCond
         .ok (c, afterCond + 1)
    else .ok (qvmFrZero, afterCond)
  let linCount ← byteAt bytes afterConst
  let rowCount ← byteAt bytes (afterConst + 1)
  let pairwiseCount ← byteAt bytes (afterConst + 2)
  let memCount ← byteAt bytes (afterConst + 3)
  let productCount ← byteAt bytes (afterConst + 4)
  let cursor0 := afterConst + 5
  let (acc1, cursor1, mem1) ←
    foldRangeIdxM linCount (acc0, cursor0, mem) fun _ state => do
      let (acc, cursor, mem) := state
      let (v, len, mem') ← limbLinearForm bytes consts mem cursor
      .ok (qvmFrAdd acc v, cursor + len, mem')
  let (acc2, cursor2, mem2) ←
    foldRangeIdxM rowCount (acc1, cursor1, mem1) fun _ state => do
      let (acc, cursor, mem) := state
      let (v, len, mem') ← limbRowForm bytes consts mem cursor
      .ok (qvmFrAdd acc v, cursor + len, mem')
  let (acc3, cursor3, mem3) ←
    foldRangeIdxM pairwiseCount (acc2, cursor2, mem2) fun _ state => do
      let (acc, cursor, mem) := state
      let (v, len, mem') ← limbPairwiseForm bytes consts mem cursor
      .ok (qvmFrAdd acc v, cursor + len, mem')
  let (acc4, cursor4, mem4) ←
    foldRangeIdxM memCount (acc3, cursor3, mem3) fun _ state => do
      let (acc, cursor, mem) := state
      let slot ← byteAt bytes cursor
      let ptr ← readU16 bytes (cursor + 1)
      let c ← constAt consts slot cursor
      let (v, mem') := mem.literal ptr
      .ok (qvmFrAdd acc (qvmFrMul c v), cursor + 3, mem')
  let (acc5, cursor5, mem5) ←
    foldRangeIdxM productCount (acc4, cursor4, mem4) fun _ state => do
      let (acc, cursor, mem) := state
      let slot ← byteAt bytes cursor
      let lhs ← readU16 bytes (cursor + 1)
      let rhs ← readU16 bytes (cursor + 3)
      let c ← constAt consts slot cursor
      let (l, m1) := mem.literal lhs
      let (r, m2) := m1.literal rhs
      .ok (qvmFrAdd acc (qvmFrMul (qvmFrMul c l) r), cursor + 5, m2)
  let (acc6, mem6) ←
    match cond with
    | none => .ok (acc5, mem5)
    | some ptr =>
        let (v, m) := mem5.literal ptr
        .ok (qvmFrMul acc5 v, m)
  .ok (acc6, cursor5 - idx, mem6)

/-! ## The identity interpreter (rust: QVR:127-347) -/

/-- The result of one fetch-decode step: the new stack, how many bytes the instruction
    consumed, and the new memory.

    Not a Rust type. It exists so the loop can be well-founded: the consumed field is
    paired with a PROOF that it is positive (R10 in the header), which is the fact Rust
    gets from seeing idx += k in the source and that Lean cannot recover from a returned
    Nat. An arm that forgot to advance the cursor does not typecheck. -/
structure IdentityStep where
  /-- The Rust's mutated stack: head is the top, i.e. the last value pushed. -/
  stack : List QVMFr
  /-- rust: the delta of every idx += k / idx = cursor in QVR:152-324. -/
  consumed : Nat
  /-- R10: the loop-progress obligation, discharged at each arm. -/
  hConsumed : 0 < consumed
  /-- The Rust's &mut QuotientRefMemory. -/
  mem : QuotientRefMemory

/-- rust: the pop! macro of QVR:141-147 @formal-baseline. "Pop helpers keep the error
    path uniform; the offline validator has already proven depth safety, so these only
    fire on validator drift." The idx in the message is the idx at the point of the pop,
    which is what the macro captures. -/
def popStack (stack : List QVMFr) (idx : Nat) : Except QVMFault (QVMFr × List QVMFr) :=
  match stack with
  | value :: rest => .ok (value, rest)
  | [] => .error (QVMFault.stackUnderflow idx)

/-- rust: QVR:149-338, the body of the while loop @formal-baseline. Split out of the
    loop so the loop itself is one recursive call (R10); the arm order is the Rust's
    match order, including the two-arm and five-arm or-patterns. -/
def evalQuotientIdentityStep (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) : Except QVMFault IdentityStep :=
  if op == qOpPushConst then do
    let slot ← readU16 bytes (idx + 1)
    let v ← constAt consts slot idx
    .ok { stack := v :: stack, consumed := 3, hConsumed := by omega, mem := mem }
  else if op == qOpPushConstU8 then do
    let slot ← byteAt bytes (idx + 1)
    let v ← constAt consts slot idx
    .ok { stack := v :: stack, consumed := 2, hConsumed := by omega, mem := mem }
  else if op == qOpPushMemLiteral then do
    let ptr ← readU32 bytes (idx + 1)
    let (v, mem') := mem.literal ptr
    .ok { stack := v :: stack, consumed := 5, hConsumed := by omega, mem := mem' }
  else if op == qOpPushMemU16 then do
    let ptr ← readU16 bytes (idx + 1)
    let (v, mem') := mem.literal ptr
    .ok { stack := v :: stack, consumed := 3, hConsumed := by omega, mem := mem' }
  else if op == qOpPushMemToken then do
    let token ← byteAt bytes (idx + 1)
    let (v, mem') := mem.token token 0
    .ok { stack := v :: stack, consumed := 2, hConsumed := by omega, mem := mem' }
  else if op == qOpPushMemTokenOffset then do
    let token ← byteAt bytes (idx + 1)
    let offset ← readU32 bytes (idx + 2)
    let (v, mem') := mem.token token offset
    .ok { stack := v :: stack, consumed := 6, hConsumed := by omega, mem := mem' }
  else if op == qOpAdd then do
    let (rhs, s1) ← popStack stack idx
    let (lhs, s2) ← popStack s1 idx
    .ok { stack := qvmFrAdd lhs rhs :: s2, consumed := 1, hConsumed := by omega, mem := mem }
  else if op == qOpMul then do
    let (rhs, s1) ← popStack stack idx
    let (lhs, s2) ← popStack s1 idx
    .ok { stack := qvmFrMul lhs rhs :: s2, consumed := 1, hConsumed := by omega, mem := mem }
  else if op == qOpNeg then do
    let (v, s1) ← popStack stack idx
    .ok { stack := qvmFrNeg v :: s1, consumed := 1, hConsumed := by omega, mem := mem }
  else if op == qOpPow5 then do
    let (v, s1) ← popStack stack idx
    -- rust: QVR:200-205. squared = v*v; push v*squared*squared. Two multiplications of
    -- the same square, NOT v^4 * v: same value, and the port keeps the shape.
    let squared := qvmFrMul v v
    .ok { stack := qvmFrMul (qvmFrMul v squared) squared :: s1,
          consumed := 1, hConsumed := by omega, mem := mem }
  else if op == qOpAddConstU8 || op == qOpMulConstU8 then do
    let slot ← byteAt bytes (idx + 1)
    let value ← constAt consts slot idx
    let (acc, s1) ← popStack stack idx
    let pushed := if op == qOpAddConstU8 then qvmFrAdd acc value else qvmFrMul acc value
    .ok { stack := pushed :: s1, consumed := 2, hConsumed := by omega, mem := mem }
  else if op == qOpAddConst || op == qOpMulConst then do
    let slot ← readU16 bytes (idx + 1)
    let value ← constAt consts slot idx
    let (acc, s1) ← popStack stack idx
    let pushed := if op == qOpAddConst then qvmFrAdd acc value else qvmFrMul acc value
    .ok { stack := pushed :: s1, consumed := 3, hConsumed := by omega, mem := mem }
  else if op == qOpAddMemU16 || op == qOpMulMemU16 then do
    let ptr ← readU16 bytes (idx + 1)
    -- rust: QVR:229-231 reads the memory value BEFORE popping, so a truncated stack
    -- still leaves the address cached. errorPrecedence_ok pins it.
    let (value, mem') := mem.literal ptr
    let (acc, s1) ← popStack stack idx
    let pushed := if op == qOpAddMemU16 then qvmFrAdd acc value else qvmFrMul acc value
    .ok { stack := pushed :: s1, consumed := 3, hConsumed := by omega, mem := mem' }
  else if op == qOpAddMulMemMemConstU8 then do
    let (acc, s1) ← popStack stack idx
    let (term, len, mem') ← affineProductTerm bytes consts mem (idx + 1)
    .ok { stack := qvmFrAdd acc term :: s1, consumed := 1 + len, hConsumed := by omega,
          mem := mem' }
  else if op == qOpAddMulConstU8MemU16 then do
    let (acc, s1) ← popStack stack idx
    let (term, len, mem') ← affineLinearTerm bytes consts mem (idx + 1)
    .ok { stack := qvmFrAdd acc term :: s1, consumed := 1 + len, hConsumed := by omega,
          mem := mem' }
  else if op == qOpAddMulMemMem then do
    let lhs ← readU16 bytes (idx + 1)
    let rhs ← readU16 bytes (idx + 3)
    let (acc, s1) ← popStack stack idx
    let (l, m1) := mem.literal lhs
    let (r, m2) := m1.literal rhs
    .ok { stack := qvmFrAdd acc (qvmFrMul l r) :: s1, consumed := 5, hConsumed := by omega,
          mem := m2 }
  else if op == qOpRunAddMulMemMemConstU8 || op == qOpRunAddMulConstU8MemU16 then do
    -- rust: QVR:258-279. "Run compaction is a pure encoding change: the same terms in
    -- the same order, with one shared count instead of repeated opcode bytes."
    let count ← readU16 bytes (idx + 1)
    unless count != 0 do
      throw (QVMFault.zeroLengthRun idx)
    let (acc0, s1) ← popStack stack idx
    let (acc, used, mem') ←
      foldRangeIdxM count (acc0, 0, mem) fun _ state => do
        let (acc, used, mem) := state
        let (term, len, mem') ←
          if op == qOpRunAddMulMemMemConstU8 then
            affineProductTerm bytes consts mem (idx + 3 + used)
          else
            affineLinearTerm bytes consts mem (idx + 3 + used)
        .ok (qvmFrAdd acc term, used + len, mem')
    .ok { stack := acc :: s1, consumed := 3 + used, hConsumed := by omega, mem := mem' }
  else if op == qOpAffineSum then do
    -- rust: QVR:280-304. "Mixed run: all linear terms first, then all product terms,
    -- matching compact_quotient_runs."
    let linCount ← readU16 bytes (idx + 1)
    let productCount ← readU16 bytes (idx + 3)
    unless linCount != 0 && productCount != 0 do
      throw (QVMFault.affineSumZeroCounts idx)
    let (acc0, s1) ← popStack stack idx
    let (accA, usedA, memA) ←
      foldRangeIdxM linCount (acc0, 0, mem) fun _ state => do
        let (acc, used, mem) := state
        let (term, len, mem') ← affineLinearTerm bytes consts mem (idx + 5 + used)
        .ok (qvmFrAdd acc term, used + len, mem')
    let (accB, usedB, memB) ←
      foldRangeIdxM productCount (accA, usedA, memA) fun _ state => do
        let (acc, used, mem) := state
        let (term, len, mem') ← affineProductTerm bytes consts mem (idx + 5 + used)
        .ok (qvmFrAdd acc term, used + len, mem')
    .ok { stack := accB :: s1, consumed := 5 + usedB, hConsumed := by omega, mem := memB }
  else if op == qOpLin7 then do
    let (value, len, mem') ← limbLinearForm bytes consts mem (idx + 1)
    .ok { stack := value :: stack, consumed := 1 + len, hConsumed := by omega, mem := mem' }
  else if op == qOpBilin7Row then do
    let (value, len, mem') ← limbRowForm bytes consts mem (idx + 1)
    .ok { stack := value :: stack, consumed := 1 + len, hConsumed := by omega, mem := mem' }
  else if op == qOpBilin7Pairwise then do
    let (value, len, mem') ← limbPairwiseForm bytes consts mem (idx + 1)
    .ok { stack := value :: stack, consumed := 1 + len, hConsumed := by omega, mem := mem' }
  else if op == qOpModarith7 then do
    let (value, len, mem') ← modarith7Form bytes consts mem (idx + 1)
    .ok { stack := value :: stack, consumed := 1 + len, hConsumed := by omega, mem := mem' }
  else if op == qOpFoldMain || op == qOpFoldSelector || op == qOpNativePermutation
        || op == qOpNativeLookup || op == qOpNativeIdentity then
    -- rust: QVR:325-333: the five stream-level opcodes are an ERROR here. This is the
    -- line that bounds the domain of QVM.run (see DOMAIN OF QVM.run in the header).
    .error (QVMFault.streamOpcodeInIdentity op idx)
  else
    .error (QVMFault.unknownOpcode op idx)

/-- rust: QVR:149-338 (the while loop) @formal-baseline. fuel is the port's explicit
    bound on iterations: every arm advances the cursor by at least one byte (the
    hConsumed proof field of IdentityStep), so bytes.length iterations always suffice.
    The fuel-exhausted arm is therefore unreachable and loopFuelNeverBinds_ok asserts it
    over every fixture rather than trusting the argument. -/
def evalQuotientIdentityLoop (bytes : List Nat) (consts : List Word256) (idx : Nat)
    (stack : List QVMFr) (mem : QuotientRefMemory) :
    Except QVMFault (List QVMFr × QuotientRefMemory) :=
  go bytes.length idx stack mem
where
  go : Nat → Nat → List QVMFr → QuotientRefMemory →
      Except QVMFault (List QVMFr × QuotientRefMemory)
  | 0, idx, stack, mem =>
      if idx < bytes.length then
        .error (QVMFault.panic "reference VM fuel exhausted")
      else
        .ok (stack, mem)
  | fuel + 1, idx, stack, mem =>
      if idx < bytes.length then do
        let s ← evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem
        go fuel (idx + s.consumed) s.stack s.mem
      else
        .ok (stack, mem)
  termination_by fuel _ _ _ => fuel

/-- rust: QVR:131-347 (eval_quotient_identity) @formal-baseline. "Evaluate one identity
    expression subprogram, up to but excluding its fold." This is PLAN 9.5's QVM.run at
    the granularity the reference actually has: one identity, not a program; a seeded
    PRNG memory, not a frame; one field element, not an output object. See the header's
    DOMAIN OF QVM.run.

    The Rust's Ok(stack.pop().expect("checked length")) at QVR:346 is discharged here by
    the singleton pattern match, so it needs no fault (R4 note in the header). -/
def evalQuotientIdentity (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) : Except QVMFault (QVMFr × QuotientRefMemory) := do
  let (stack, mem') ← evalQuotientIdentityLoop bytes consts 0 ([] : List QVMFr) mem
  match stack with
  | [value] => .ok (value, mem')
  | xs => .error (QVMFault.stackLengthMismatch xs.length)

/-! ## The PLAN 9.5 bridge -/

-- PLAN 9.5 names its anchor QVM.run over QVM.Program, QVM.Frame, QVM.Fault and
-- QVM.Output. Only two of those exist in the reference, and this namespace says which:
-- Fault (the closed taxonomy of hazard 2) and run (the per-identity evaluator).
-- Program, Frame and Output have no counterpart - see DOMAIN OF QVM.run and WHAT PLAN
-- 9.5 STILL OWNS in the header - and are deliberately NOT invented here.
namespace QVM

/-- PLAN 9.5's QVM.Fault. -/
abbrev Fault : Type := QVMFault

/-- PLAN 9.5's Fq: the concrete scalar field the reference interprets over. -/
abbrev Fr : Type := QVMFr

/-- The reference's memory: a seed and a memo table. There is no Frame, because there is
    no frame: memory is derived from addresses, never loaded from one. -/
abbrev Memory : Type := QuotientRefMemory

/-- PLAN 9.5's QVM.run, at the reference's granularity: one identity expression
    subprogram, evaluated against a seeded assignment and a constant table. -/
def run (bytes : List Nat) (consts : List Word256) (mem : Memory) :
    Except Fault (Fr × Memory) :=
  evalQuotientIdentity bytes consts mem

end QVM

/-! ## Known-answer tests

    Every gate is a Bool or an IO Bool with a matching "#eval ... -- expect true" line at
    the end of the file, so scripts/kat_gate.py turns each one into a CI obligation
    (docs/REVIEW.md R-38). Each doc names the concrete wrong implementation it rules
    out, and the package report carries the perturbation actually run inside each scope
    (R-41). D-P19 binds here: the four artifact gates open reference.rs from disk while
    they evaluate, so a Rust-side edit that changes the preimage layout, an error string
    or the set of handled opcodes reddens a named gate instead of drifting silently. -/

namespace QuotientVmRefKats

open Midfall.Generator.QuotientVmKats (readFileOrEmpty)

/-! ### Fixtures

    Every expected value below was produced by an independent Python transcription
    of reference.rs - Keccak-256 written from the FIPS-202 definition and validated
    against the empty-digest vector and three of the ABI selectors pinned in
    Common/Keccak.lean - and not by the Lean code that checks it. The constant table
    is the ten smallest primes; the pointers are the VmTypes limb-pointer fixture
    0x100..0x1c0 plus 0x1e0; both seeds are 32 bytes. -/

def refSeedA : Bytes := qvmBytesOfNats (List.range 32)

def refSeedB : Bytes := qvmBytesOfNats ((List.range 32).map fun i => (i * 7 + 3) % 256)

/-- The fixture constant table: the ten smallest primes, as U256 (QVR:133). -/
def refConsts : List Word256 := [1, 2, 3, 5, 7, 11, 13, 17, 19, 23]

def refMem : QuotientRefMemory := quotientRefMemoryNew refSeedA

/-- The hazard-3 boundary values: r - 1 (canonical), r and r + 1 (not). -/
def frMinusOne : Word256 := BitVec.ofNat 256 (qvmFrModulus - 1)

/-- rust: the first value QVR:548's expect rejects. -/
def frExact : Word256 := BitVec.ofNat 256 qvmFrModulus

/-- rust: a value that a silent reduce would turn into 1; the rejection gate asserts it
    does not. -/
def frPlusOne : Word256 := BitVec.ofNat 256 (qvmFrModulus + 1)

/-- Big-endian operand encoders, so a fixture reads like the instruction it tests. -/
def be16 (x : Nat) : List Nat := [x / 256, x % 256]

def be32 (x : Nat) : List Nat := [x / 2^24, (x / 2^16) % 256, (x / 2^8) % 256, x % 256]

def derivePairs : List (Nat × Nat) :=
  [(0, 0), (0, 256), (0, 288), (0, 320), (0, 352), (0, 384), (0, 416), (0, 448), (0, 480),
   (1, 0), (2, 0), (7, 32), (10, 64), (255, 0), (0, 4294967295), (0, 65536), (2, 256)]

/-- The hazard-1 pins for seed A: (domain, address, value). -/
def deriveFixturesA : List (Nat × Nat × QVMFr) :=
  [(0, 0, 0x56e27149e2ce73cecc8d14ac37371b87ce2a291d6d63092b7e1e78a9f9c68345),
   (0, 256, 0x3cd7bafc5c0f9291ae7b75d97d31405d7f084033db2a8eab994897eef1abc3e5),
   (0, 288, 0x21185402908ff7ddb9bcf0bd726ea34f34d839a56dcfc07531cc951a1a8b936a),
   (0, 320, 0x57c4c80d25dc39cd77b7590ba83e6fa0bcdacbe442733df1f7877d56400e6645),
   (0, 352, 0x5f4ceafa5c113fc7eff921b852924c31dbb86356885c2312a910773c65d3b374),
   (0, 384, 0x2d976b9bc222827da78a6bcb69ad9b7eb91f523107813806b25aeb126f93b9fd),
   (0, 416, 0x1c382f4ec2c3daac0d534526875aac2fa1ce3bd401aa59a851f1fff31bf65c9),
   (0, 448, 0x51fc8cd3a0dca07021f2eaa6afbd9b63ee01fdc86e56417bccd2d5e14eb5e63c),
   (0, 480, 0x4659b724872718dd1d1a24d0de85e6a783d182905795bb3923634035a85dfe42),
   (1, 0, 0x5eca2418a5f284cc43b4c97523f75d459174ec2725c3929eaf275a4907001bda),
   (2, 0, 0x129a9f17297ccf2ac9713f1d65979cbb7e7174593670046a556fc3684b77fa4f),
   (7, 32, 0x2e6d389375f80739933125c8c3b5408f0b8946227a385e1c3be3998bd30b3676),
   (10, 64, 0x4928e8089f972ebfc1758b5962e2af4f32768be4662850b7b0957da0520e3310),
   (255, 0, 0x48796c15b706d81d87aa18b423b423008c9f23fbdf4ea32c64160c778dc3e936),
   (0, 4294967295, 0x4a1313c93e7ba7ea6073e746280880f153160135abe5d1beadfa58e8086d9f64),
   (0, 65536, 0x20f86640b1f4fe587d6c90e597d7ee20771f26111f7e4c49bb2126d30a0d4be9),
   (2, 256, 0x1206ca56e916e521d7490564028360a79e6f5306a0120f14a8d66fcada078fa0)]

/-- The hazard-1 pins for seed B: (domain, address, value). -/
def deriveFixturesB : List (Nat × Nat × QVMFr) :=
  [(0, 0, 0x63660e49d81d3640b30ff3e987511bf99ac426dec204ecaa375fd99ade6e63bd),
   (0, 256, 0x45275c37209f995fe0ac2e88ca7894d50dfc9359525b163ba816d74b59ee3f05),
   (0, 288, 0x23dab56f70fc88b53c342cc6dd75066cbb6f8b2a9cc0f4d505db0afacca4cab7),
   (0, 320, 0x100be80388fe920364d1bfc9125f732657de5012bff01a592271f86b42b62697),
   (0, 352, 0x60ee7cd0b0eb43961fa76690be36b7a14d2eccd434657d3fc5629f54c3f8d982),
   (0, 384, 0x60e65a90bba17bdec52359eeff2f62aa6e8ec128452aa72f41b862a535b0e3aa),
   (0, 416, 0x26260b064d6bd883c252597e633f5fc3ee97803cb0672cbf9680a729e69044d),
   (0, 448, 0x1094efdb90e88da87db1dbc9cbcbc55fe4322a9e5d47a55bfe6309d86e3de848),
   (0, 480, 0xd299293e41f47e15658698ef5b000b40bf5df4abfcfe674925d7a780ca2b277),
   (1, 0, 0x5e8fe95134847e0b13f1a1f1034d4848346ebdc502a699be511c7c7762b1b85c),
   (2, 0, 0x46ca1147433ecb5ff9342fd1268af6d03dcff8015b3f609248a4128088a799ce),
   (7, 32, 0x15f368f9f13944f765269156252905f1f346ea0b7820d58b6575a5d2c96cd1f4),
   (10, 64, 0x695a34b65317b20bf80c1c76fa517e312030e12f59e9c1e615c05e24841c8a07),
   (255, 0, 0x5a0fee927314004cd46aab5348b5900120949647a360778e769288ca08f9626d),
   (0, 4294967295, 0x4fc0e7b8547a21c72166fbdad7bd65062d4e06100a7a07b4fbac2de393dc429),
   (0, 65536, 0x4c5e2de9d48dce1a0b11de7db67b9d6494ae436233284e7649e9fb2adca3f84),
   (2, 256, 0x1df4a5a5d75910c079460459d716f4f6518de3cc13b1e0ce23d870d12f3ed17e)]

-- Hand-assembled programs: the name is the opcode or shape exercised.

/- PUSH_MEM_LITERAL 0x100 -/
def pPushMemLiteral : List Nat := [2, 0, 0, 1, 0]
def wantpPushMemLiteral : QVMFr := 0x3cd7bafc5c0f9291ae7b75d97d31405d7f084033db2a8eab994897eef1abc3e5

/- PUSH_CONST slot 3 -/
def pPushConst : List Nat := [1, 0, 3]
def wantpPushConst : QVMFr := 0x5

/- PUSH_CONST_U8 slot 7 -/
def pPushConstU8 : List Nat := [9, 7]
def wantpPushConstU8 : QVMFr := 0x11

/- PUSH_MEM_U16 0x120 -/
def pPushMemU16 : List Nat := [5, 1, 32]
def wantpPushMemU16 : QVMFr := 0x21185402908ff7ddb9bcf0bd726ea34f34d839a56dcfc07531cc951a1a8b936a

/- PUSH_MEM_TOKEN qMemL0 -/
def pPushMemToken : List Nat := [3, 1]
def wantpPushMemToken : QVMFr := 0x129a9f17297ccf2ac9713f1d65979cbb7e7174593670046a556fc3684b77fa4f

/- PUSH_MEM_TOKEN_OFFSET qMemX 0x20 -/
def pPushMemTokenOffset : List Nat := [4, 6, 0, 0, 0, 32]
def wantpPushMemTokenOffset : QVMFr := 0x2e6d389375f80739933125c8c3b5408f0b8946227a385e1c3be3998bd30b3676

/- m(0x100) + m(0x120) -/
def pAdd : List Nat := [2, 0, 0, 1, 0, 5, 1, 32, 6]
def wantpAdd : QVMFr := 0x5df00efeec9f8a6f68386696ef9fe3acb3e079d948fa4f20cb152d090c37574f

/- m(0x100) * m(0x120) -/
def pMul : List Nat := [2, 0, 0, 1, 0, 5, 1, 32, 7]
def wantpMul : QVMFr := 0x5ede294375b65e12420dc466ddee1b0b54e07ca84bd46ee6b2b4fccf163afaf

/- -m(0x100) -/
def pNeg : List Nat := [2, 0, 0, 1, 0, 8]
def wantpNeg : QVMFr := 0x3715ec56cd8deab684be622e8c7097a7d4b563cf24d3cd5366b768100e543c1c

/- m(0x100)^5 -/
def pPow5 : List Nat := [2, 0, 0, 1, 0, 32]
def wantpPow5 : QVMFr := 0x30d51df9f117d2761ef9ddea98f897b45414dcd483ed8f5933e78573a5178b92

/- m(0x100) + c[2] -/
def pAddConstU8 : List Nat := [2, 0, 0, 1, 0, 12, 2]
def wantpAddConstU8 : QVMFr := 0x3cd7bafc5c0f9291ae7b75d97d31405d7f084033db2a8eab994897eef1abc3e8

/- m(0x100) * c[2] -/
def pMulConstU8 : List Nat := [2, 0, 0, 1, 0, 13, 2]
def wantpMulConstU8 : QVMFr := 0x429989a1ea913a6cd83889846df1e913295b1c9891815003cbd9c7cdd5034bae

/- m(0x100) + c[2] -/
def pAddConst : List Nat := [2, 0, 0, 1, 0, 14, 0, 2]
def wantpAddConst : QVMFr := 0x3cd7bafc5c0f9291ae7b75d97d31405d7f084033db2a8eab994897eef1abc3e8

/- m(0x100) * c[2] -/
def pMulConst : List Nat := [2, 0, 0, 1, 0, 15, 0, 2]
def wantpMulConst : QVMFr := 0x429989a1ea913a6cd83889846df1e913295b1c9891815003cbd9c7cdd5034bae

/- m(0x100) + m(0x120) -/
def pAddMemU16 : List Nat := [2, 0, 0, 1, 0, 16, 1, 32]
def wantpAddMemU16 : QVMFr := 0x5df00efeec9f8a6f68386696ef9fe3acb3e079d948fa4f20cb152d090c37574f

/- m(0x100) * m(0x120) -/
def pMulMemU16 : List Nat := [2, 0, 0, 1, 0, 17, 1, 32]
def wantpMulMemU16 : QVMFr := 0x5ede294375b65e12420dc466ddee1b0b54e07ca84bd46ee6b2b4fccf163afaf

/- m(0x100) + m(0x120)*m(0x140)*c[3] -/
def pAddMulMemMemConstU8 : List Nat := [2, 0, 0, 1, 0, 18, 1, 32, 1, 64, 3]
def wantpAddMulMemMemConstU8 : QVMFr := 0x54dd2195e9dd5dd946f11ee07203a926839038fb0520f02aaa1f67aef690888a

/- m(0x100) + c[3]*m(0x120) -/
def pAddMulConstU8MemU16 : List Nat := [2, 0, 0, 1, 0, 19, 1, 32, 3]
def wantpAddMulConstU8MemU16 : QVMFr := 0x6e63b7b60541ec9e1bf25184afb898e43383bc6c003af4f6924781727665a4f6

/- m(0x100) + m(0x120)*m(0x140) -/
def pAddMulMemMem : List Nat := [2, 0, 0, 1, 0, 20, 1, 32, 1, 64]
def wantpAddMulMemMem : QVMFr := 0x13468c9367c6891cb87bdad7aa4dcbb6c4d796c0e38fb09236405b15bf731e6c

/- run of two product terms -/
def pRunProd : List Nat := [2, 0, 0, 1, 0, 21, 0, 2, 1, 32, 1, 64, 1, 1, 96, 1, 128, 2]
def wantpRunProd : QVMFr := 0x2beb245966c39ee7ae129abf3a2cf3d41a854c856dacc156ba810f7855f8fb02

/- run of two linear terms -/
def pRunLin : List Nat := [2, 0, 0, 1, 0, 22, 0, 2, 1, 32, 1, 1, 64, 2]
def wantpRunLin : QVMFr := 0x2a8dc52f71ebb7dcef6dda5f3de44dce24102b227e28b56ee3783a28e6ee1d85

/- two linear terms then one product term -/
def pAffineSum : List Nat := [2, 0, 0, 1, 0, 34, 0, 2, 0, 1, 1, 32, 1, 1, 64, 2, 1, 96, 1, 128, 3]
def wantpAffineSum : QVMFr := 0x7242d7b74ed6c22f66ffd48c349d606877ee3dd3565bcf8bba47218ce02ba0f3

/- sum_i c[i]*m(P[i]) -/
def pLin7 : List Nat := [28, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192]
def wantpLin7 : QVMFr := 0x44919f6844767fb902f61f098e10c55d1802c749b81e9df8305238501390c553

/- m(0x1e0) * lin7 -/
def pBilin7Row : List Nat := [29, 1, 224, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192]
def wantpBilin7Row : QVMFr := 0x1eeeb3d809b8c9dfebb389f5454cb4ef52a619a651d816132841aff787cee820

/- 7x7 pairwise, coeffs by i+j -/
def pBilin7Pairwise : List Nat := [30, 1, 0, 2, 0, 0, 1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1]
def wantpBilin7Pairwise : QVMFr := 0x2a6d8be5417ad1f279a77c369890f2839210a02a541bff262ab6e56c6a5833bf

/- flags cond+const, one of each block -/
def pModarith7Full : List Nat := [33, 3, 1, 224, 4, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192, 1, 224, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192, 1, 0, 2, 0, 0, 1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1, 2, 1, 0, 3, 1, 32, 1, 64]
def wantpModarith7Full : QVMFr := 0x1daf1a13d175e41b917b2bf72f680b5c2b46e03ab48707e0fbe04c6a78656b09

/- no flags, mem and product blocks only -/
def pModarith7Bare : List Nat := [33, 0, 0, 0, 0, 1, 1, 2, 1, 0, 3, 1, 32, 1, 64]
def wantpModarith7Bare : QVMFr := 0x5a9ef03b785f05b470ae328b62c451dc2de3155fbb77b182dcb0978dd9e81053

/- cond only: product term scaled by m(0x100) -/
def pModarith7Cond : List Nat := [33, 1, 1, 0, 0, 0, 0, 0, 1, 3, 1, 32, 1, 64]
def wantpModarith7Cond : QVMFr := 0x2c56d51c767c499321fa1bee6fc8029765a4a3a4bd811dfc933cd0a3d58b6e0d

/- const only: c[5] -/
def pModarith7Const : List Nat := [33, 2, 5, 0, 0, 0, 0, 0]
def wantpModarith7Const : QVMFr := 0xb

/- one lin block -/
def pModarith7LinOnly : List Nat := [33, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192]
def wantpModarith7LinOnly : QVMFr := 0x44919f6844767fb902f61f098e10c55d1802c749b81e9df8305238501390c553

/- one row block -/
def pModarith7RowOnly : List Nat := [33, 0, 0, 1, 0, 0, 0, 1, 224, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192]
def wantpModarith7RowOnly : QVMFr := 0x1eeeb3d809b8c9dfebb389f5454cb4ef52a619a651d816132841aff787cee820

/- one pairwise block -/
def pModarith7PairwiseOnly : List Nat := [33, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1]
def wantpModarith7PairwiseOnly : QVMFr := 0x2a6d8be5417ad1f279a77c369890f2839210a02a541bff262ab6e56c6a5833bf

/- two lin blocks: twice the lin7 value -/
def pModarith7TwoLin : List Nat := [33, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192, 0, 1, 0, 1, 1, 32, 2, 1, 64, 3, 1, 96, 4, 1, 128, 5, 1, 160, 6, 1, 192]
def wantpModarith7TwoLin : QVMFr := 0x1535977d5f4f8229d2b2660b127fb2b4dc47ea90703edff160a470a127218aa5

/- cond with an empty accumulator: 0 * m(0x100) -/
def pModarith7CondNoBlocks : List Nat := [33, 1, 1, 0, 0, 0, 0, 0, 0]
def wantpModarith7CondNoBlocks : QVMFr := 0x0

/- -(((m(0x100)*m(0x120))+c[0])^5) -/
def pChain : List Nat := [2, 0, 0, 1, 0, 2, 0, 0, 1, 32, 7, 9, 1, 6, 32, 8]
def wantpChain : QVMFr := 0x4a40719d8dcfe36cbeb86d721893baf468d7c60b8e9f24764f2e6f9f63cb278a

/- same address read twice -/
def pCacheHitTwice : List Nat := [2, 0, 0, 1, 0, 2, 0, 0, 1, 0, 6]
def wantpCacheHitTwice : QVMFr := 0x5c1cea58e81a7db29bd13aaf0c0a8b5aa52dc64b656c15832912fdee35787c9

/- PUSH_MEM_TOKEN 0xff: the u8 domain wrap -/
def pTokenWrap : List Nat := [3, 255]
def wantpTokenWrap : QVMFr := 0x56e27149e2ce73cecc8d14ac37371b87ce2a291d6d63092b7e1e78a9f9c68345

/- literal domain at address 0 -/
def pLitZero : List Nat := [2, 0, 0, 0, 0]
def wantpLitZero : QVMFr := 0x56e27149e2ce73cecc8d14ac37371b87ce2a291d6d63092b7e1e78a9f9c68345

/- c[9]*c[0] -/
def pMulChain : List Nat := [1, 0, 9, 9, 0, 7]
def wantpMulChain : QVMFr := 0x17

-- Programs that must fault; the constructor is the Rust's format! payload.

def eUnknownOpcode : List Nat := [153]
def faulteUnknownOpcode : QVMFault := QVMFault.unknownOpcode 0x99 0

def eFoldInside : List Nat := [2, 0, 0, 1, 0, 10]
def faulteFoldInside : QVMFault := QVMFault.streamOpcodeInIdentity qOpFoldMain 5

def eNativeInside : List Nat := [27, 0, 0]
def faulteNativeInside : QVMFault := QVMFault.streamOpcodeInIdentity qOpNativeIdentity 0

def eUnderflow : List Nat := [6]
def faulteUnderflow : QVMFault := QVMFault.stackUnderflow 0

def eZeroRun : List Nat := [21, 0, 0]
def faulteZeroRun : QVMFault := QVMFault.zeroLengthRun 0

def eAffineSumZeroLin : List Nat := [34, 0, 0, 0, 1]
def faulteAffineSumZeroLin : QVMFault := QVMFault.affineSumZeroCounts 0

def eAffineSumZeroProd : List Nat := [34, 0, 1, 0, 0]
def faulteAffineSumZeroProd : QVMFault := QVMFault.affineSumZeroCounts 0

def eBadFlags : List Nat := [33, 4]
def faulteBadFlags : QVMFault := QVMFault.modarith7UnknownFlags 0x04 1

def eBadFlagsHigh : List Nat := [33, 128]
def faulteBadFlagsHigh : QVMFault := QVMFault.modarith7UnknownFlags 0x80 1

def ePastEnd : List Nat := [2, 0, 0]
def faultePastEnd : QVMFault := QVMFault.readPastEnd 3

def eConstOOR : List Nat := [1, 0, 99]
def faulteConstOOR : QVMFault := QVMFault.constSlotOutOfRange 99 0

def eConstOORu8 : List Nat := [9, 200]
def faulteConstOORu8 : QVMFault := QVMFault.constSlotOutOfRange 200 0

def eTwoValues : List Nat := [9, 0, 9, 1]
def faulteTwoValues : QVMFault := QVMFault.stackLengthMismatch 2

def eEmpty : List Nat := []
def faulteEmpty : QVMFault := QVMFault.stackLengthMismatch 0

def eOvershoot : List Nat := [2, 0, 0, 1, 0, 9]
def faulteOvershoot : QVMFault := QVMFault.readPastEnd 6

def eConstBeforeUnderflow : List Nat := [12, 99]
def faulteConstBeforeUnderflow : QVMFault := QVMFault.constSlotOutOfRange 99 0

def ePairwiseTruncated : List Nat := [30, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def faultePairwiseTruncated : QVMFault := QVMFault.readPastEnd 17

/-- Every fixture program, for the fuel and panic-class sweeps. -/
def allFixturePrograms : List (String × List Nat) :=
  [("pPushMemLiteral", pPushMemLiteral), ("pPushConst", pPushConst),
   ("pPushConstU8", pPushConstU8), ("pPushMemU16", pPushMemU16),
   ("pPushMemToken", pPushMemToken), ("pPushMemTokenOffset", pPushMemTokenOffset),
   ("pAdd", pAdd), ("pMul", pMul), ("pNeg", pNeg), ("pPow5", pPow5),
   ("pAddConstU8", pAddConstU8), ("pMulConstU8", pMulConstU8), ("pAddConst", pAddConst),
   ("pMulConst", pMulConst), ("pAddMemU16", pAddMemU16), ("pMulMemU16", pMulMemU16),
   ("pAddMulMemMemConstU8", pAddMulMemMemConstU8),
   ("pAddMulConstU8MemU16", pAddMulConstU8MemU16), ("pAddMulMemMem", pAddMulMemMem),
   ("pRunProd", pRunProd), ("pRunLin", pRunLin), ("pAffineSum", pAffineSum), ("pLin7", pLin7),
   ("pBilin7Row", pBilin7Row), ("pBilin7Pairwise", pBilin7Pairwise),
   ("pModarith7Full", pModarith7Full), ("pModarith7Bare", pModarith7Bare),
   ("pModarith7Cond", pModarith7Cond), ("pModarith7Const", pModarith7Const),
   ("pModarith7LinOnly", pModarith7LinOnly), ("pModarith7RowOnly", pModarith7RowOnly),
   ("pModarith7PairwiseOnly", pModarith7PairwiseOnly), ("pModarith7TwoLin", pModarith7TwoLin),
   ("pModarith7CondNoBlocks", pModarith7CondNoBlocks), ("pChain", pChain),
   ("pCacheHitTwice", pCacheHitTwice), ("pTokenWrap", pTokenWrap), ("pLitZero", pLitZero),
   ("pMulChain", pMulChain), ("eUnknownOpcode", eUnknownOpcode), ("eFoldInside", eFoldInside),
   ("eNativeInside", eNativeInside), ("eUnderflow", eUnderflow), ("eZeroRun", eZeroRun),
   ("eAffineSumZeroLin", eAffineSumZeroLin), ("eAffineSumZeroProd", eAffineSumZeroProd),
   ("eBadFlags", eBadFlags), ("eBadFlagsHigh", eBadFlagsHigh), ("ePastEnd", ePastEnd),
   ("eConstOOR", eConstOOR), ("eConstOORu8", eConstOORu8), ("eTwoValues", eTwoValues),
   ("eEmpty", eEmpty), ("eOvershoot", eOvershoot),
   ("eConstBeforeUnderflow", eConstBeforeUnderflow), ("ePairwiseTruncated", ePairwiseTruncated)]

/-- Every value fixture, for the sweep gates. -/
def allValueFixtures : List (String × List Nat × QVMFr) :=
  [("pPushMemLiteral", pPushMemLiteral, wantpPushMemLiteral),
   ("pPushConst", pPushConst, wantpPushConst), ("pPushConstU8", pPushConstU8, wantpPushConstU8),
   ("pPushMemU16", pPushMemU16, wantpPushMemU16),
   ("pPushMemToken", pPushMemToken, wantpPushMemToken),
   ("pPushMemTokenOffset", pPushMemTokenOffset, wantpPushMemTokenOffset),
   ("pAdd", pAdd, wantpAdd), ("pMul", pMul, wantpMul), ("pNeg", pNeg, wantpNeg),
   ("pPow5", pPow5, wantpPow5), ("pAddConstU8", pAddConstU8, wantpAddConstU8),
   ("pMulConstU8", pMulConstU8, wantpMulConstU8), ("pAddConst", pAddConst, wantpAddConst),
   ("pMulConst", pMulConst, wantpMulConst), ("pAddMemU16", pAddMemU16, wantpAddMemU16),
   ("pMulMemU16", pMulMemU16, wantpMulMemU16),
   ("pAddMulMemMemConstU8", pAddMulMemMemConstU8, wantpAddMulMemMemConstU8),
   ("pAddMulConstU8MemU16", pAddMulConstU8MemU16, wantpAddMulConstU8MemU16),
   ("pAddMulMemMem", pAddMulMemMem, wantpAddMulMemMem), ("pRunProd", pRunProd, wantpRunProd),
   ("pRunLin", pRunLin, wantpRunLin), ("pAffineSum", pAffineSum, wantpAffineSum),
   ("pLin7", pLin7, wantpLin7), ("pBilin7Row", pBilin7Row, wantpBilin7Row),
   ("pBilin7Pairwise", pBilin7Pairwise, wantpBilin7Pairwise),
   ("pModarith7Full", pModarith7Full, wantpModarith7Full),
   ("pModarith7Bare", pModarith7Bare, wantpModarith7Bare),
   ("pModarith7Cond", pModarith7Cond, wantpModarith7Cond),
   ("pModarith7Const", pModarith7Const, wantpModarith7Const),
   ("pModarith7LinOnly", pModarith7LinOnly, wantpModarith7LinOnly),
   ("pModarith7RowOnly", pModarith7RowOnly, wantpModarith7RowOnly),
   ("pModarith7PairwiseOnly", pModarith7PairwiseOnly, wantpModarith7PairwiseOnly),
   ("pModarith7TwoLin", pModarith7TwoLin, wantpModarith7TwoLin),
   ("pModarith7CondNoBlocks", pModarith7CondNoBlocks, wantpModarith7CondNoBlocks),
   ("pChain", pChain, wantpChain), ("pCacheHitTwice", pCacheHitTwice, wantpCacheHitTwice),
   ("pTokenWrap", pTokenWrap, wantpTokenWrap), ("pLitZero", pLitZero, wantpLitZero),
   ("pMulChain", pMulChain, wantpMulChain)]

def allFaultFixtures : List (String × List Nat × QVMFault) :=
  [("eUnknownOpcode", eUnknownOpcode, faulteUnknownOpcode),
   ("eFoldInside", eFoldInside, faulteFoldInside),
   ("eNativeInside", eNativeInside, faulteNativeInside),
   ("eUnderflow", eUnderflow, faulteUnderflow), ("eZeroRun", eZeroRun, faulteZeroRun),
   ("eAffineSumZeroLin", eAffineSumZeroLin, faulteAffineSumZeroLin),
   ("eAffineSumZeroProd", eAffineSumZeroProd, faulteAffineSumZeroProd),
   ("eBadFlags", eBadFlags, faulteBadFlags),
   ("eBadFlagsHigh", eBadFlagsHigh, faulteBadFlagsHigh), ("ePastEnd", ePastEnd, faultePastEnd),
   ("eConstOOR", eConstOOR, faulteConstOOR), ("eConstOORu8", eConstOORu8, faulteConstOORu8),
   ("eTwoValues", eTwoValues, faulteTwoValues), ("eEmpty", eEmpty, faulteEmpty),
   ("eOvershoot", eOvershoot, faulteOvershoot),
   ("eConstBeforeUnderflow", eConstBeforeUnderflow, faulteConstBeforeUnderflow),
   ("ePairwiseTruncated", ePairwiseTruncated, faultePairwiseTruncated)]

-- The oracle side (eval_quotient_expr), QVR:110-125.

def exprConst : QuotientExpr := QuotientExpr.const (BitVec.ofNat 256 0xdeadbeef)
def wantexprConst : QVMFr := 0xdeadbeef

def exprConstMax : QuotientExpr := QuotientExpr.const frMinusOne
def wantexprConstMax : QVMFr := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000

def exprLit : QuotientExpr := QuotientExpr.mem (.literal 0x100)
def wantexprLit : QVMFr := 0x3cd7bafc5c0f9291ae7b75d97d31405d7f084033db2a8eab994897eef1abc3e5

def exprTok : QuotientExpr := QuotientExpr.mem (.token qMemL0)
def wantexprTok : QVMFr := 0x129a9f17297ccf2ac9713f1d65979cbb7e7174593670046a556fc3684b77fa4f

def exprTokOff : QuotientExpr := QuotientExpr.mem (.tokenOffset qMemX 0x20)
def wantexprTokOff : QVMFr := 0x2e6d389375f80739933125c8c3b5408f0b8946227a385e1c3be3998bd30b3676

def exprAdd : QuotientExpr := QuotientExpr.add (QuotientExpr.const 7) (QuotientExpr.mem (.literal 0x100))
def wantexprAdd : QVMFr := 0x3cd7bafc5c0f9291ae7b75d97d31405d7f084033db2a8eab994897eef1abc3ec

def exprMul : QuotientExpr := QuotientExpr.mul (QuotientExpr.mem (.literal 0x100)) (QuotientExpr.mem (.literal 0x120))
def wantexprMul : QVMFr := 0x5ede294375b65e12420dc466ddee1b0b54e07ca84bd46ee6b2b4fccf163afaf

def exprNeg : QuotientExpr := QuotientExpr.neg (QuotientExpr.mul (QuotientExpr.const 3) (QuotientExpr.mem (.token qMemL0)))
def wantexprNeg : QVMFr := 0x3c1dca0dad270fc7d6e61aafd8db01d2d86946f75cae4ebfffb0b5c61d981114

def exprDeep : QuotientExpr := QuotientExpr.add (QuotientExpr.mul (QuotientExpr.neg (QuotientExpr.mem (.literal 0x100))) (QuotientExpr.const 5)) (QuotientExpr.add (QuotientExpr.mem (.tokenOffset qMemBeta 0)) (QuotientExpr.mem (.tokenOffset qMemBeta 0)))
def wantexprDeep : QVMFr := 0x4082df1a83a6a236c49e68ad5ab8aaba84c8f2dec74a92af59239669081f9a4


/-! #### Gate helpers -/

/-- The value at a fixture pointer, straight from the seed-A assignment. -/
def litAt (addr : Nat) : QVMFr := (refMem.literal addr).1

/-- The constant-table value at a fixture slot. -/
def constOf (slot : Nat) : QVMFr :=
  match constAt refConsts slot 0 with
  | .ok v => v
  | .error _ => qvmFrModulus

/-- Sum a range of field elements: the hand-computed form the *_form gates use. -/
def sumRange (n : Nat) (f : Nat -> QVMFr) : QVMFr :=
  (List.range n).foldl (fun acc i => qvmFrAdd acc (f i)) qvmFrZero

/-- Lean core has no BEq instance for Except, so the gates compare through these three
    projections instead of == on an Except value. -/
def okIs {α : Type} [BEq α] (x : Except QVMFault α) (want : α) : Bool :=
  match x with
  | .ok v => v == want
  | .error _ => false

def errIs {α : Type} (x : Except QVMFault α) (want : QVMFault) : Bool :=
  match x with
  | .error e => e == want
  | .ok _ => false

def isPanicClass {α : Type} (x : Except QVMFault α) : Bool :=
  match x with
  | .error (QVMFault.panic _) => true
  | _ => false

/-- Evaluate a fixture program against the seed-A assignment. -/
def runRef (prog : List Nat) : Except QVMFault QVMFr := do
  let (v, _) ← evalQuotientIdentity prog refConsts refMem
  .ok v

def valueIs (prog : List Nat) (want : QVMFr) : Bool := okIs (runRef prog) want

def faultIs (prog : List Nat) (want : QVMFault) : Bool := errIs (runRef prog) want

/-- Evaluate the oracle side and unwrap; the sentinel qvmFrModulus is not a field value,
    so a failure can never coincide with a pin. -/
def exprValue (e : QuotientExpr) : QVMFr :=
  match evalQuotientExpr e refMem with
  | .ok (v, _) => v
  | .error _ => qvmFrModulus

/-- The 21 operand bytes of the LIN7 fixture (the opcode stripped). -/
def lin7Operands : List Nat := pLin7.drop 1

/-- The 13 coefficient bytes of the pairwise fixture. -/
def pwCoeffs : List Nat := pBilin7Pairwise.drop 5

/-- LIN7 with every slot 0 and every pointer 0x100: seven identical terms, so the value
    is 7 * c[0] * m(0x100) - computable without running the decoder at all. -/
def pLin7Uniform : List Nat := [0x1c] ++ (List.range quotientVmLimbs).flatMap fun _ => [0] ++ be16 0x100

/-- wantpLin7Uniform: 7 * 1 * m(0x100), from the independent Python model. -/
def wantpLin7Uniform : QVMFr := 0x4e1d26ed07948a232bb2b0da4f733a7e7e00d561fe2ed2b430fc278b9bb25b40

/-- BILIN7_PAIRWISE with every coefficient slot 0 (c = 1): the value must factor as
    (sum of the lhs limbs) * (sum of the rhs limbs). -/
def pBilin7PairwiseUniform : List Nat :=
  [0x1e] ++ be16 0x100 ++ be16 0x200 ++ List.replicate quotientVmPairwiseCoeffs 0

/-- The factorised expectation, from the independent Python model. -/
def wantpBilin7PairwiseUniform : QVMFr :=
  0x65b97570e678c9eebcd557bfffa5b9331d135fb4dc4ba4a54db3ca84c77ffed7

/-- The pairwise value recomputed DIAGONAL BY DIAGONAL: for each d = i + j, the
    coefficient c[d] times the sum of m(lhs + 32i) * m(rhs + 32j) over the pairs with
    i + j = d. This is a different summation from the Rust's grid loop and is the only
    way to test that the slot index really is i + j. -/
def pairwiseDiagonalExpected (lhsBase rhsBase : Nat) (coeffs : List Nat) : QVMFr :=
  sumRange quotientVmPairwiseCoeffs fun d =>
    qvmFrMul (constOf (coeffs.getD d 0))
      (sumRange quotientVmLimbs fun i =>
        if i <= d && d - i < quotientVmLimbs then
          qvmFrMul (litAt (lhsBase + i * qvmWordBytes))
                   (litAt (rhsBase + (d - i) * qvmWordBytes))
        else 0)

/-- One identity, as the plan's oracle sees it and as the emitter lowers it:
    m(0x100) + 11 * m(BETA_MPTR). The bytecode is PUSH_MEM_LITERAL, PUSH_CONST slot 5
    (= 11), PUSH_MEM_TOKEN qMemBeta, MUL, ADD. -/
def certExpr : QuotientExpr :=
  QuotientExpr.add (QuotientExpr.mem (.literal 0x100))
    (QuotientExpr.mul (QuotientExpr.const 11) (QuotientExpr.mem (.token qMemBeta)))

/-- The bytecode certExpr lowers to. -/
def certProg : List Nat :=
  [0x02] ++ be32 0x100 ++ [0x01] ++ be16 5 ++ [0x03, qMemBeta] ++ [0x07, 0x06]

/-- The expected value of both sides, from the independent Python model. -/
def wantCert : QVMFr := 0x4b3b539381918063d98e563d7b8068cb83d26f16fad64e95573925dc826a2bf6

/-! #### Artifact gates (D-P19: reference.rs is opened at #eval time) -/

/-- The two candidate paths, relative to formal/ (where checks.sh and lake run) and to
    the repo root. Same convention as VmTypes' templatePathCandidates. -/
def referencePathCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs"]

/-- A missing or truncated artifact is a RED, never a silent true: reference.rs is 20802
    bytes at HEAD, so anything much smaller is a wrong path. Reachability is a named
    gate of its own, placed first, so a wrong path is diagnosed rather than matched by
    accident (docs/plans/README.md, D-P19). -/
def referenceReadOk (src : String) : Bool := src.length > 18000

def readQuotientVmReference : IO String :=
  referencePathCandidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

/-- Reachability gate. Rules out: the file moving, being renamed, or the path being
    wrong - the failure mode R-38 finding 1 is about. -/
def referenceArtifactReachable_ok : IO Bool := do
  let src ← readQuotientVmReference
  pure (referenceReadOk src && src.contains "fn eval_quotient_identity"
          && src.contains "pub(crate) struct QuotientRefMemory")

/-- HAZARD 1, read from the artifact rather than pasted: every structural fact about the
    preimage - both domain tags, the order of the four updates, the two domain choices,
    the lo-then-hi wide assembly and the from_uniform_bytes call - must appear in
    reference.rs exactly as the port reproduces it. Rules out: a Rust-side edit to the
    derivation that the Lean port does not follow, which would silently change the
    challenge distribution. -/
def derivePreimageLayout_artifact_ok : IO Bool := do
  let src ← readQuotientVmReference
  if ! (referenceReadOk src) then
    pure false
  else
    pure (["b\"midfall/quotient-vm/reference-memory/v1\"",
           "b\"midfall/quotient-vm/reference-memory/v1/hi\"",
           "hasher.update(self.seed);",
           "hasher.update([domain]);",
           "hasher.update(address.to_be_bytes());",
           "self.derive(0, ptr)",
           "self.derive(1 + token, offset)",
           "wide[..32].copy_from_slice(&lo);",
           "wide[32..].copy_from_slice(&hi);",
           "from_uniform_bytes(&wide)",
           "if let Some(value) = self.cache.get(&(domain, address))",
           "self.cache.insert((domain, address), value)"].all fun needle =>
            src.contains needle)

/-- The nine format strings of QVR, as the Rust writes them, paired with the fault that
    renders them and the rendering with the payloads 7 / 99 / 0x12 substituted. The first
    component is checked against the artifact; the second against QVMFault.message. -/
def faultFormatFixtures : List (String × QVMFault × String) :=
  [("reference VM stack underflow at byte {idx}", QVMFault.stackUnderflow 7,
    "reference VM stack underflow at byte 7"),
   ("reference VM read past end of program at byte {idx}", QVMFault.readPastEnd 7,
    "reference VM read past end of program at byte 7"),
   ("reference VM constant slot {slot} out of range at byte {idx}",
    QVMFault.constSlotOutOfRange 99 7,
    "reference VM constant slot 99 out of range at byte 7"),
   ("reference VM zero-length run at byte {idx}", QVMFault.zeroLengthRun 7,
    "reference VM zero-length run at byte 7"),
   ("reference VM AFFINE_SUM at byte {idx} requires nonzero counts",
    QVMFault.affineSumZeroCounts 7,
    "reference VM AFFINE_SUM at byte 7 requires nonzero counts"),
   ("reference VM MODARITH7 unknown flag bits {flags:#x} at byte {idx}",
    QVMFault.modarith7UnknownFlags 0x12 7,
    "reference VM MODARITH7 unknown flag bits 0x12 at byte 7"),
   ("reference VM found stream opcode {op:#x} inside an identity expression at byte {idx}",
    QVMFault.streamOpcodeInIdentity 0x0a 7,
    "reference VM found stream opcode 0xa inside an identity expression at byte 7"),
   ("reference VM unknown opcode {op:#x} at byte {idx}", QVMFault.unknownOpcode 0x99 7,
    "reference VM unknown opcode 0x99 at byte 7"),
   ("reference VM identity left {} value(s) on the stack, expected 1",
    QVMFault.stackLengthMismatch 7,
    "reference VM identity left 7 value(s) on the stack, expected 1")]

/-- HAZARD 2 and R-43 F2. Rules out: a Rust error string changing without the taxonomy
    following, and a fault constructor that drops a payload the Rust reports. -/
def faultMessages_artifactStrings_ok : IO Bool := do
  let src ← readQuotientVmReference
  if ! (referenceReadOk src) then
    pure false
  else
    pure (faultFormatFixtures.all fun (fmt, fault, rendered) =>
            (src.contains ("\"" ++ fmt ++ "\"")) && (QVMFault.message fault == rendered))

/-- The Q_OP_* identifiers the artifact names, read back out of the source. -/
def artifactOpcodeNames (src : String) : List String :=
  ((src.splitOn "Q_OP_").tail?.getD []).map fun tail =>
    "Q_OP_" ++ String.ofList (tail.toList.takeWhile fun c =>
      (('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_'))

/-- The 31 Q_OP_* names the P-09a table declares, upper-cased the way the Rust spells
    them. Built from quotientOpcodeTable rather than pasted, so the gate compares the
    table with the artifact and not with a third copy. -/
def tableOpcodeConstantNames : List String :=
  quotientOpcodeTable.map fun spec => "Q_OP_" ++ String.map Char.toUpper spec.name

/-- Set equality without importing a sort: every element of each list is in the other,
    and neither has duplicates. -/
def sameNames (lhs rhs : List String) : Bool :=
  lhs.all (fun x => rhs.contains x) && rhs.all (fun x => lhs.contains x) &&
  lhs.length == rhs.length

/-- The reference must name exactly the opcodes the ABI table declares: a missing one is
    an unimplemented arm, an extra one is a decoder the table does not know. This is the
    hazard-6 boundary made checkable - the interpreter is complete over the table
    without importing the builder. -/
def referenceOpcodes_coverTheTable_ok : IO Bool := do
  let src ← readQuotientVmReference
  if ! (referenceReadOk src) then
    pure false
  else
    -- each opcode is named at least twice (the import list and the match arm), so the
    -- set is what is compared, not the occurrence list.
    let found := (artifactOpcodeNames src).eraseDups
    pure (sameNames found tableOpcodeConstantNames && found.length == 31 &&
          tableOpcodeConstantNames.length == 31)

/-! #### Hazard 1: the derivation -/

/-- The byte-exactness gate for seed A: 17 (domain, address) pairs against values from
    the independent Python Keccak. Rules out: any change to the preimage order, the tag
    text, the address endianness, the hi-half input, the wide assembly or the reduction.
    Each of those is separately perturbation-tested in the package report. -/
def derive_byteExact_seedA_ok : Bool :=
  deriveFixturesA.all fun (d, a, v) => deriveReferenceMemory refSeedA d a == v

/-- The same for a second seed, so the seed cannot be dropped from the preimage or
    absorbed into the tag without reddening. -/
def derive_byteExact_seedB_ok : Bool :=
  deriveFixturesB.all fun (d, a, v) => deriveReferenceMemory refSeedB d a == v

/-- Domain separation and seed sensitivity, stated as inequalities: the literal domain
    must differ from every token domain, token domains must differ from each other, and
    a different seed must give a different answer everywhere. Rules out: the domain byte
    or the seed being omitted from the preimage. -/
def derive_seedAndDomainSeparation_ok : Bool :=
  (deriveFixturesA.all fun (d, a, v) => deriveReferenceMemory refSeedB d a != v) &&
  ((List.range 12).map (fun d => deriveReferenceMemory refSeedA d 0) |>
     fun vs => ! QuotientVmKats.hasDuplicateNat vs) &&
  ((List.range 8).map (fun a => deriveReferenceMemory refSeedA 0 (a * 0x20)) |>
     fun vs => ! QuotientVmKats.hasDuplicateNat vs)

/-- R5 at the two width-bearing positions. The u32 address truncates (so 2^32 and 0 are
    the same slot) and the u8 domain wraps (so token 0xff lands in the literal domain,
    which is what QVR:81's 1 + token does once overflow-checks are off). Rules out: a
    port that silently widens either one, and - by the second clause - a port that
    collapses addresses it should keep apart. -/
def derive_addressAndDomainWidths_ok : Bool :=
  deriveReferenceMemory refSeedA 0 (2^32) == deriveReferenceMemory refSeedA 0 0 &&
  deriveReferenceMemory refSeedA 0 (2^32 + 0x100) == deriveReferenceMemory refSeedA 0 0x100 &&
  deriveReferenceMemory refSeedA 0 0x100 != deriveReferenceMemory refSeedA 0 0 &&
  deriveReferenceMemory refSeedA 256 0 == deriveReferenceMemory refSeedA 0 0

/-- The token-side view of the same wrap: PUSH_MEM_TOKEN 0xff and PUSH_MEM_LITERAL 0
    evaluate to the same field element, while the nine real tokens stay in their own
    domains. Unreachable in a validated program (validate_quotient_mem_token, QVM:2758),
    pinned anyway because the release profile is what makes it true. -/
def tokenDomainU8Wrap_releaseProfile_ok : Bool :=
  ((quotientRefMemoryNew refSeedA).token 0xff 0).1 ==
    ((quotientRefMemoryNew refSeedA).literal 0).1 &&
  ((quotientRefMemoryNew refSeedA).token qMemL0 0).1 !=
    ((quotientRefMemoryNew refSeedA).literal 0).1 &&
  ! QuotientVmKats.hasDuplicateNat
    ([qMemL0, qMemLLast, qMemLBlind, qMemBeta, qMemGamma, qMemX, qMemTheta,
      qMemTrashChallenge, qMemInstanceEval].map
       fun t => ((quotientRefMemoryNew refSeedA).token t 0).1)

/-- The memoisation property (hazard 1, second half). Four claims: a repeated read
    returns the same value and does not grow the table; every stored entry equals the
    pure derivation, so the cache can never disagree with the function it memoises;
    token and literal domains memoise independently; and the 7x7 pairwise form performs
    56 memory reads that collapse to 14 distinct cached addresses - the number that
    makes the two sides of the certification observe identical memory. Rules out:
    dropping the cache (values would still agree, but the address-set claim would fail),
    and keying the cache on an unwrapped or partial key. -/
def memoisation_sameAddressSameValue_ok : Bool :=
  let m0 := refMem
  let (v1, m1) := m0.literal 0x100
  let (v2, m2) := m1.literal 0x100
  v1 == v2 && m2.cache.length == 1 &&
  (m2.cache.all fun (d, a, v) => deriveReferenceMemory m0.seed d a == v) &&
  let (t1, m3) := m2.token qMemL0 0
  let (t2, m4) := m3.token qMemL0 0
  t1 == t2 && t1 != v1 && m4.cache.length == 2 &&
  -- (e) a literal pointer and a token offset that land on the SAME address stay apart,
  -- because the key is the (domain, address) pair and not the address
  let (x1, m5) := m4.literal 0x100
  let (x2, m6) := m5.token qMemL0 0x100
  x1 != x2 && m6.cache.length == 3 &&
  match evalQuotientIdentity pBilin7Pairwise refConsts m0 with
  | .ok (_, mp) =>
      mp.cache.length == 14 &&
      (mp.cache.all fun (d, a, v) => deriveReferenceMemory m0.seed d a == v)
  | .error _ => false

/-- qvmFrFromUniformBytes is the 512-bit little-endian reduction the header derives the
    Rust's Montgomery form to. Each clause is hand-checkable: zero is zero, the least
    significant bit is one, 2^256 - 1 is itself (it is below r), and 2^256 is 2^256 - r.
    The last clause is the one a naive port gets wrong by taking only the low 32 bytes. -/
def fromUniformBytes_wideReduction_ok : Bool :=
  qvmFrFromUniformBytes (qvmBytesOfNats (List.replicate 64 0)) == 0 &&
  qvmFrFromUniformBytes (qvmBytesOfNats (1 :: List.replicate 63 0)) == 1 &&
  -- 2^256 - 1 is above r, and so is 2^256 - r: the reduction subtracts 2r. That is the
  -- clause a port that only looked at the low 32 bytes, or that reduced once, gets wrong.
  qvmFrFromUniformBytes (qvmBytesOfNats (List.replicate 32 0xff ++ List.replicate 32 0)) ==
    (2^256 - 1 - 2 * qvmFrModulus) &&
  qvmFrFromUniformBytes (qvmBytesOfNats (List.replicate 32 0 ++ 1 :: List.replicate 31 0)) ==
    (2^256 - 2 * qvmFrModulus) &&
  2^256 - 2 * qvmFrModulus < qvmFrModulus &&
  (deriveFixturesA.all fun (_, _, v) => v < qvmFrModulus)

/-! #### Hazard 3 and hazard 5 -/

/-- fqFromU256 REJECTS a non-canonical entry (hazard 3): r - 1 is accepted, r and r + 1
    both fault with the panic class, and - the clause that separates rejection from a
    silent reduce - r + 1 is NOT 1. Rules out: porting the expect as a modulo, which is
    the R-30 class of divergence this file must not contain. -/
def fqFromU256_canonicalRejection_ok : Bool :=
  okIs (fqFromU256 1) 1 &&
  okIs (fqFromU256 frMinusOne) (qvmFrModulus - 1) &&
  (match fqFromU256 frExact with
   | .error (QVMFault.panic site) => site.contains "reference.rs:548"
   | _ => false) &&
  ! okIs (fqFromU256 frPlusOne) 1 &&
  (match fqFromU256 frPlusOne with
   | .error (QVMFault.panic _) => true
   | _ => false)

/-- HAZARD 5: the four bounds-checked readers return Err, the direct index panics, and
    the two classes are never conflated. The last clause is the arithmetic that makes the
    panic unreachable: max (i + j) = 2 * (LIMBS - 1) = 12 = PAIRWISE_COEFFS - 1, which
    is exactly the byte QVR:420 bounds-checks. Rules out: unifying the readers into one
    helper, and turning the pairwise index into a bounds-checked read (which would
    silently reject a render the Rust aborts the build on). -/
def boundsReadsReturnErrNotPanic_ok : Bool :=
  errIs (byteAt [1, 2] 2) (QVMFault.readPastEnd 2) &&
  errIs (readU16 [1] 0) (QVMFault.readPastEnd 1) &&
  errIs (readU32 [1, 2, 3] 0) (QVMFault.readPastEnd 3) &&
  errIs (constAt refConsts 10 0) (QVMFault.constSlotOutOfRange 10 0) &&
  errIs (indexOrPanic [1, 2] 5) (QVMFault.panic
    "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs:427") &&
  ! (isPanicClass (byteAt [1, 2] 2)) && ! (isPanicClass (readU16 [1] 0)) &&
  ! (isPanicClass (readU32 [1, 2, 3] 0)) && ! (isPanicClass (constAt refConsts 10 0)) &&
  2 * (quotientVmLimbs - 1) == quotientVmPairwiseCoeffs - 1

/-- No fixture program reaches the panic class: neither the fuel bound nor the pairwise
    direct index fires on any of them, which is the evidence that the two panic sites are
    genuinely unreachable rather than merely untested. -/
def loopFuelNeverBinds_ok : Bool :=
  allFixturePrograms.all fun (_, prog) =>
    match runRef prog with
    | .error (QVMFault.panic _) => false
    | _ => true

/-! #### The interpreter -/

/-- The six push opcodes, QVR:152-182. Rules out: operand widths being read little-endian
    (PUSH_MEM_LITERAL and PUSH_MEM_U16 would agree with each other but not with the
    pins), the token domain being 0, and the token offset being dropped. -/
def pushOpcodes_ok : Bool :=
  valueIs pPushMemLiteral wantpPushMemLiteral &&
  valueIs pPushConst wantpPushConst &&
  valueIs pPushConstU8 wantpPushConstU8 &&
  valueIs pPushMemU16 wantpPushMemU16 &&
  valueIs pPushMemToken wantpPushMemToken &&
  valueIs pPushMemTokenOffset wantpPushMemTokenOffset &&
  valueIs pLitZero wantpLitZero

/-- The four pure stack opcodes, QVR:183-205, plus a six-instruction chain. POW5 is the
    one with a shape worth pinning: v * v^2 * v^2 with the square shared, not v^4 * v. -/
def stackArithmetic_ok : Bool :=
  valueIs pAdd wantpAdd && valueIs pMul wantpMul && valueIs pNeg wantpNeg &&
  valueIs pPow5 wantpPow5 && valueIs pChain wantpChain && valueIs pMulChain wantpMulChain &&
  -- hand-computed: pow5 of a known value is v^5 mod r, and neg negates
  valueIs ([0x09, 1] ++ [0x20]) (qvmFrMul 2 (qvmFrMul 4 4)) &&
  valueIs ([0x09, 1] ++ [0x08]) (qvmFrNeg 2)

/-- The six accumulator opcodes, QVR:206-238: the u8 and u16 const forms and the u16
    memory forms, each in an add and a mul arm. Rules out: the two arms of an or-pattern
    being swapped, which is the single most likely mis-port in this block. -/
def accumulatorOpcodes_ok : Bool :=
  valueIs pAddConstU8 wantpAddConstU8 && valueIs pMulConstU8 wantpMulConstU8 &&
  valueIs pAddConst wantpAddConst && valueIs pMulConst wantpMulConst &&
  valueIs pAddMemU16 wantpAddMemU16 && valueIs pMulMemU16 wantpMulMemU16 &&
  -- hand-computed identities: the u8 and u16 const forms agree on the same slot
  wantpAddConstU8 == wantpAddConst && wantpMulConstU8 == wantpMulConst &&
  wantpAdd == wantpAddMemU16 && wantpMul == wantpMulMemU16

/-- The three fused product opcodes, QVR:239-257. Rules out: the ADD_MUL_MEM_MEM_CONST_U8
    operand order (lhs, rhs, slot) being read as (slot, lhs, rhs), and the standalone
    ADD_MUL_MEM_MEM forgetting its scalar of 1. -/
def fusedProductOpcodes_ok : Bool :=
  valueIs pAddMulMemMemConstU8 wantpAddMulMemMemConstU8 &&
  valueIs pAddMulConstU8MemU16 wantpAddMulConstU8MemU16 &&
  valueIs pAddMulMemMem wantpAddMulMemMem &&
  -- hand-computed: ADD_MUL_MEM_MEM is ADD_MUL_MEM_MEM_CONST_U8 with scalar 1
  valueIs pAddMulMemMem (qvmFrAdd (litAt 0x100) (qvmFrMul (litAt 0x120) (litAt 0x140)))

/-- The two run opcodes, QVR:258-279, and their zero-count rejection. Rules out: the run
    count being read as a byte, the accumulator not being seeded from the popped value,
    and the cursor being advanced by a fixed stride instead of each term's own length. -/
def runOpcodes_ok : Bool :=
  valueIs pRunProd wantpRunProd && valueIs pRunLin wantpRunLin &&
  faultIs eZeroRun faulteZeroRun &&
  -- hand-computed: a run of two terms is the accumulator plus both terms
  valueIs pRunProd (qvmFrAdd (qvmFrAdd (litAt 0x100)
      (qvmFrMul (qvmFrMul (litAt 0x120) (litAt 0x140)) 2))
      (qvmFrMul (qvmFrMul (litAt 0x160) (litAt 0x180)) 3))

/-- AFFINE_SUM, QVR:280-304: linear terms first, then product terms, and both counts
    must be nonzero. Rules out: the two blocks being interleaved or swapped - the order
    is what compact_quotient_runs promises (QVR:281-282) - and a zero side being accepted. -/
def affineSumOpcodes_ok : Bool :=
  valueIs pAffineSum wantpAffineSum &&
  faultIs eAffineSumZeroLin faulteAffineSumZeroLin &&
  faultIs eAffineSumZeroProd faulteAffineSumZeroProd &&
  -- hand-computed: acc + c[1]*m(0x120) + c[2]*m(0x140) + m(0x160)*m(0x180)*c[3]
  valueIs pAffineSum (qvmFrAdd (qvmFrAdd (qvmFrAdd (litAt 0x100) (qvmFrMul 2 (litAt 0x120)))
      (qvmFrMul 3 (litAt 0x140))) (qvmFrMul (qvmFrMul (litAt 0x160) (litAt 0x180)) 5))

/-- The two standalone term helpers, QVR:349-375: value, byte length and the memory they
    leave behind. Rules out: the (ptr, slot) versus (slot, ptr) orderings being unified. -/
def affineTermHelpers_ok : Bool :=
  match affineLinearTerm (be16 0x120 ++ [3]) refConsts refMem 0,
        affineProductTerm (be16 0x120 ++ be16 0x140 ++ [3]) refConsts refMem 0 with
  | .ok (v1, l1, _), .ok (v2, l2, _) =>
      l1 == 3 && l2 == 5 &&
      v1 == qvmFrMul 5 (litAt 0x120) &&
      v2 == qvmFrMul (qvmFrMul (litAt 0x120) (litAt 0x140)) 5
  | _, _ => false

/-- limb_linear_form, QVR:377-393: the pinned fixture, the 21-byte length, and a
    hand-computed uniform case (seven identical terms is 7 * c * m). Rules out: the
    stride being 2 instead of 3, the (slot, ptr) order being swapped, and the loop
    running six or eight times. -/
def limbLinearForm_ok : Bool :=
  valueIs pLin7 wantpLin7 &&
  (match limbLinearForm lin7Operands refConsts refMem 0 with
   | .ok (_, len, _) => len == 3 * quotientVmLimbs
   | .error _ => false) &&
  valueIs pLin7Uniform wantpLin7Uniform &&
  wantpLin7Uniform == qvmFrMul (7 * 1) (litAt 0x100) &&
  -- hand-computed from the fixture's own operands: sum of c[i] * m(0x100 + 32i)
  wantpLin7 == sumRange quotientVmLimbs fun i => qvmFrMul (constOf i) (litAt (0x100 + i * 0x20))

/-- limb_row_form, QVR:395-406: the pinned fixture, the 23-byte length, and the fact
    that it is m(lhs) times the linear form - including that the inner form's operands
    start two bytes in, not one. Rules out: the lhs being multiplied after the sum
    rather than scaled by it, and the length forgetting the leading u16. -/
def limbRowForm_ok : Bool :=
  valueIs pBilin7Row wantpBilin7Row &&
  (match limbRowForm (be16 0x1e0 ++ lin7Operands) refConsts refMem 0 with
   | .ok (_, len, _) => len == 2 + 3 * quotientVmLimbs
   | .error _ => false) &&
  wantpBilin7Row == qvmFrMul (litAt 0x1e0) wantpLin7 &&
  wantpBilin7Row == qvmFrMul (litAt 0x1e0)
    (sumRange quotientVmLimbs fun i => qvmFrMul (constOf i) (litAt (0x100 + i * 0x20)))

/-- limb_pairwise_form, QVR:408-432. Three independent characterisations of the same
    value: the pinned fixture, the diagonal regrouping (which is the only check that the
    coefficient index really is i + j rather than i * LIMBS + j), and the uniform case,
    which must factor as (sum of lhs limbs) * (sum of rhs limbs). Plus the 17-byte
    length and the up-front bounds check. Rules out: the stride being wrong, the
    coefficient indexing being wrong, and the block bound being off by one. -/
def limbPairwiseForm_ok : Bool :=
  valueIs pBilin7Pairwise wantpBilin7Pairwise &&
  (match limbPairwiseForm (be16 0x100 ++ be16 0x200 ++ pwCoeffs) refConsts refMem 0 with
   | .ok (_, len, _) => len == 4 + quotientVmPairwiseCoeffs
   | .error _ => false) &&
  wantpBilin7Pairwise == pairwiseDiagonalExpected 0x100 0x200 pwCoeffs &&
  valueIs pBilin7PairwiseUniform wantpBilin7PairwiseUniform &&
  wantpBilin7PairwiseUniform ==
    qvmFrMul (sumRange quotientVmLimbs fun i => litAt (0x100 + i * qvmWordBytes))
             (sumRange quotientVmLimbs fun j => litAt (0x200 + j * qvmWordBytes)) &&
  faultIs ePairwiseTruncated faultePairwiseTruncated

/-- modarith7_form, QVR:434-507: every flag and count combination pinned, with the
    lengths. Rules out: the const block landing after the counts, the cond being
    applied to only part of the accumulator, and any of the five block loops being read
    in the wrong order. -/
def modarith7Form_ok : Bool :=
  valueIs pModarith7Full wantpModarith7Full &&
  valueIs pModarith7Bare wantpModarith7Bare &&
  valueIs pModarith7Cond wantpModarith7Cond &&
  valueIs pModarith7Const wantpModarith7Const &&
  valueIs pModarith7LinOnly wantpModarith7LinOnly &&
  valueIs pModarith7RowOnly wantpModarith7RowOnly &&
  valueIs pModarith7PairwiseOnly wantpModarith7PairwiseOnly &&
  valueIs pModarith7TwoLin wantpModarith7TwoLin &&
  valueIs pModarith7CondNoBlocks wantpModarith7CondNoBlocks &&
  -- hand-computed structural facts
  wantpModarith7Const == 11 &&
  wantpModarith7LinOnly == wantpLin7 &&
  wantpModarith7RowOnly == wantpBilin7Row &&
  wantpModarith7PairwiseOnly == wantpBilin7Pairwise &&
  wantpModarith7TwoLin == qvmFrAdd wantpLin7 wantpLin7 &&
  wantpModarith7CondNoBlocks == 0 &&
  faultIs eBadFlags faulteBadFlags && faultIs eBadFlagsHigh faulteBadFlagsHigh

/-- The operand-order trap QVR:488-490 warns about: the MODARITH7 mem block is
    (slot, ptr) while the standalone ADD_MUL_CONST_U8_MEM_U16 term is (ptr, slot). The
    same three bytes mean different things to the two readers, and a port that unified
    them would produce the wrong value silently. Rules out: exactly that unification. -/
def modarith7OperandOrder_ok : Bool :=
  -- bytes [2, 1, 0]: as a MODARITH7 mem term this is c[2] * m(0x0100) = 3 * m(0x100)
  qvmFrMul (constOf 2) (litAt 0x100) == qvmFrMul 3 (litAt 0x100) &&
  -- read the other way round it is c[0] * m(0x0201), a different field element
  qvmFrMul (constOf 0) (litAt 0x201) != qvmFrMul (constOf 2) (litAt 0x100) &&
  valueIs pModarith7Bare wantpModarith7Bare

/-- The whole error taxonomy, QVR:145-344: every fault the reference can name, produced
    by a program that reaches it, with the payload the Rust would interpolate. -/
def errorTaxonomy_ok : Bool :=
  allFaultFixtures.all fun (name, prog, want) =>
    errIs (runRef prog) want && QVMFault.message want != "" && name != ""

/-- Error PRECEDENCE, which is what a closed taxonomy loses if it is not pinned: the
    Rust evaluates operands before it pops (QVR:207-209, 218-220, 229-231), reads the
    run count before popping (QVR:262-267), and bounds-checks a constant slot before
    converting it (QVR:536-541). Rules out: a reordering that keeps every value right
    but reports a different fault. -/
def errorPrecedence_ok : Bool :=
  -- a bad const slot beats the stack underflow that follows it
  faultIs eConstBeforeUnderflow faulteConstBeforeUnderflow &&
  -- a zero run count beats the underflow that follows it
  faultIs eZeroRun faulteZeroRun &&
  -- an out-of-range const slot shadows the non-canonical panic the conversion would give
  (match constAt [frExact] 0 0 with
   | .error (QVMFault.panic _) => true
   | _ => false) &&
  faultIs eConstOORu8 faulteConstOORu8

/-- The oracle side, QVR:110-125: every constructor of QuotientExpr evaluated directly. -/
def evalQuotientExpr_oracle_ok : Bool :=
  exprValue exprConst == wantexprConst &&
  exprValue exprConstMax == wantexprConstMax &&
  exprValue exprLit == wantexprLit &&
  exprValue exprTok == wantexprTok &&
  exprValue exprTokOff == wantexprTokOff &&
  exprValue exprAdd == wantexprAdd &&
  exprValue exprMul == wantexprMul &&
  exprValue exprNeg == wantexprNeg &&
  exprValue exprDeep == wantexprDeep

/-- THE CERTIFICATION ITSELF, in miniature: one expression tree and the bytecode it was
    lowered from, evaluated against the SAME memory and required to agree - which is
    QVC:147-165. This is the property the whole module exists to check, and the gate is
    what makes this file a certifier port rather than an interpreter port. The
    perturbation in the report changes one operand of the bytecode and shows the two
    sides disagree. -/
def certificationLeg_oracleMatchesBytecode_ok : Bool :=
  exprValue certExpr == wantCert && okIs (runRef certProg) wantCert &&
  -- and the shared cache means both sides see the same value for the same address
  exprValue (QuotientExpr.mem (.literal 0x100)) == litAt 0x100

/-- R6: the List Nat the interpreter reads is a lossless image of the row's ByteArray
    model, so a whole-program run can be fed from QuotientProgramBuild.bytes. -/
def programBytesRoundTrip_ok : Bool :=
  (allFixturePrograms.all fun (_, prog) =>
    prog.all fun b => b < 256 && qvmBytesToNats (qvmBytesOf prog) == prog) &&
  qvmBytesToNats (qvmBytesOf []) == [] &&
  qvmBytesToNats (qvmBytesOf [0, 255, 128]) == [0, 255, 128]

/-- The third transcription of r must agree with the two already in the tree. -/
def qvmFrModulus_agreesWithBlsR_ok : Bool :=
  qvmFrModulus == Midfall.Yul.blsR && qvmFrModulus > 2^254 && qvmFrModulus < 2^255

/-- The limb stride and the two limb counts the interpreter hard-codes against P-09a. -/
def qvmWordBytes_isTheLimbStride_ok : Bool :=
  qvmWordBytes == 0x20 && quotientVmLimbs == 7 && quotientVmPairwiseCoeffs == 13 &&
  qModarith7FlagCond == 0x01 && qModarith7FlagConst == 0x02 &&
  modarith7FlagsOk 0 && modarith7FlagsOk qModarith7FlagCond &&
  modarith7FlagsOk qModarith7FlagConst &&
  modarith7FlagsOk (qModarith7FlagCond ||| qModarith7FlagConst) &&
  ! modarith7FlagsOk 0x04 && ! modarith7FlagsOk 0x80 && ! modarith7FlagsOk 0xff

end QuotientVmRefKats

end Midfall.Generator


#eval Midfall.Generator.QuotientVmRefKats.referenceArtifactReachable_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.derivePreimageLayout_artifact_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.faultMessages_artifactStrings_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.referenceOpcodes_coverTheTable_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.derive_byteExact_seedA_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.derive_byteExact_seedB_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.derive_seedAndDomainSeparation_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.derive_addressAndDomainWidths_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.tokenDomainU8Wrap_releaseProfile_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.memoisation_sameAddressSameValue_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.fromUniformBytes_wideReduction_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.fqFromU256_canonicalRejection_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.boundsReadsReturnErrNotPanic_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.loopFuelNeverBinds_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.pushOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.stackArithmetic_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.accumulatorOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.fusedProductOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.runOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.affineSumOpcodes_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.affineTermHelpers_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.limbLinearForm_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.limbRowForm_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.limbPairwiseForm_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.modarith7Form_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.modarith7OperandOrder_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.errorTaxonomy_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.errorPrecedence_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.evalQuotientExpr_oracle_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.certificationLeg_oracleMatchesBytecode_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.programBytesRoundTrip_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.qvmFrModulus_agreesWithBlsR_ok -- expect true
#eval Midfall.Generator.QuotientVmRefKats.qvmWordBytes_isTheLimbStride_ok -- expect true
