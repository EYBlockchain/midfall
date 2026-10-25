-- |
-- Midfall.Generator.Models
--
-- The Askama data models the Rust generator hands to its templates: a port of
-- `proofs/solidity-verifier/src/lowering/render/models.rs` (1494 lines) plus the
-- module surface of `lowering/render/mod.rs` (11 lines, which only declares
-- `models` and `yul` and re-exports `models::*`; the re-export is what
-- `Midfall/Generator/Templates.lean` stands in for, and `yul.rs` is a five-line
-- reserved placeholder that defines nothing - recorded, not invented around).
--
-- This is the DATA side of M3. Package 1 landed the renderer (Render.lean), the
-- Jinja filters (Filters.lean) and the golden harness (YulGolden.lean); nothing
-- there had anything to render. The equality of record stays
-- `YulSemantics.SyntaxEq.stmtsBeq` over the vendored AST (D-P13). No Yul node
-- type is defined here, per D-P2: the only Yul that appears at all is in the
-- gates, borrowed from the provenance-checked fixtures in YulGolden.lean.
--
-- CITATION NOTATION. This package cites four Rust files and two artifacts, all
-- of whose line numbers are four digits, so every cite names its file (R-38
-- finding 3 was a checklist that silently cited the wrong one):
--
--   M:    proofs/solidity-verifier/src/lowering/render/models.rs (1494 lines)
--   MR:   proofs/solidity-verifier/src/lowering/render/mod.rs (11 lines)
--   LM:   proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines)
--   ENC:  proofs/solidity-verifier/src/lowering/encoding/mod.rs
--   QVM:  proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs
--   QDIR: proofs/solidity-verifier/src/lowering/quotient_direct.rs
--   T:    proofs/solidity-verifier/templates/
--   D:    the TRACKED dump proofs/solidity-verifier/target/
--         poseidon-fixture-dump/Halo2Verifier.sol, 3024 lines, no trailing LF
--   DVK:  the same directory's Halo2VerifyingKey.sol, 271 lines
--   P:    the DEPLOYED artifact under deployments/sepolia/moonlight-wrap/, which
--         R-36 shows is five months stale. NOT used here: no cite below is a P:
--         cite.
--
-- WHAT THIS PACKAGE DOES NOT PORT, AND WHY. Eight Rust fns take or return a type
-- that plan Section 8 assigns to a DIFFERENT row of the module map, and rule R1
-- forbids inventing a parallel copy of it here:
--
--   * M:344-378 `payload_layout` and M:381-399 `validate_payload_layout` need
--     `VkPayloadLayout` / `PayloadSectionKind` (layout/vk_payload.rs) and
--     `VkConstructorMemoryLayout` (layout/memory.rs) - the `Layout/*` row.
--   * M:830-952 `Halo2Verifier::validate_layout` and M:965-1005
--     `Halo2QuotientEvaluator::validate_layout` need `VerifierMemoryLayout`
--     (layout/memory.rs) and `ProofCalldataLayout` (abi/proof.rs) - the
--     `Layout/*` and `Abi` rows. Their `QuotientExternal` helpers, which are
--     self-contained, ARE ported, so the deferred part is the field access, not
--     the range logic.
--   * M:820-825, M:955-960, M:1008-1013 `render` are Askama `render_into`
--     wrappers; their Lean counterparts are the template renderers in
--     Templates.lean, where only the verifying-key one is written in this
--     package.
--   * M:178-181 `g1_words` takes a `G1Affine`. The coordinate split it performs
--     is ported as `g1Words`; the point-to-coordinates step belongs to the curve
--     codec (ENC:835-858).
--
-- The three records whose fields contain those foreign types
-- (`VerifierCodegenLayout`, `Halo2Verifier`, `Halo2QuotientEvaluator`) are
-- parameterised over them instead of redefining them: every Rust field is
-- present, in Rust order, named per R2, and only the two types owned by other
-- packages are variables.
--
-- DECLARATION ORDER DEVIATES FROM RUST ORDER IN ONE WAY. Rust resolves a field
-- type through its module system, so M:497 `Halo2Verifier` may mention
-- `QuotientProgram` declared at M:716. Lean is order-sensitive, so the
-- sub-records that `Halo2Verifier` and `TemplateConstants` refer to are
-- declared before their parents. Nothing else moves.
--
-- THE CONSTANT VALUES ARE NOT PASTED BLIND. `TemplateConstants::default` reads
-- about seventy literals out of `layout::*` and `quotient_numerator::vm::*`.
-- Each is cited to its own definition site, and the gates cross-check them
-- against sources this file does not control: the four precompile addresses and
-- four gas bounds against `Midfall.Yul` (a separate port, cited to the EIPs),
-- the derived widths against their derivations, the generator words against the
-- curve equation and the group law, and - in Templates.lean - against the
-- literal numbers inside the provenance-pinned golden fixtures, which is the
-- only channel in this tree that reaches the committed bytes.

import Midfall.Common.Bytes
import Midfall.Generator.Filters
import Midfall.Yul.Externals

namespace Midfall.Generator
open Midfall

/-- rust: M:28 (`pub(crate) type G1Words = (U256, U256, U256, U256)`)
    @formal-baseline. A G1 point in EIP-2537 padded encoding. The Rust is a bare
    4-tuple whose order its doc comment names; Lean names the projections, in
    that same order, because a four-deep `Prod` is unusable at call sites. -/
structure G1Words where
  xHi : Word256
  xLo : Word256
  yHi : Word256
  yLo : Word256

/-- rust: M:56-69 (`struct Eip2537TemplateConstants`) @formal-baseline. -/
structure Eip2537TemplateConstants where
  /-- LM:133 `G1ADD_ADDRESS`. -/
  g1addAddress : Nat
  /-- LM:135 `G1MSM_ADDRESS`. -/
  g1msmAddress : Nat
  /-- LM:137 `PAIRING_ADDRESS`. -/
  pairingAddress : Nat
  /-- M:198: set to `PAIRING_TWO_PAIR_BYTES`, not to a scratch size of its own. -/
  smokeScratchBytes : Nat
  /-- M:199 `g1_words(G1Affine::generator())`. -/
  g1Generator : G1Words
  /-- M:200-203: `g1_words((g + g).to_affine())` for the projective generator. -/
  g1DoubleGenerator : G1Words

/-- rust: M:78-87 (`struct GasTemplateConstants`) @formal-baseline. -/
structure GasTemplateConstants where
  /-- LM:171 `G1ADD_GAS`. -/
  g1add : Nat
  /-- LM:192-200 `g1msm_gas(1)`. -/
  g1msmOnePair : Nat
  /-- LM:203-205 `pairing_gas(2)`. -/
  pairingTwoPair : Nat
  /-- LM:237-267 `modexp_gas_word_frame()`. -/
  modexp : Nat

/-- rust: M:91-101 (`struct ModexpTemplateConstants`) @formal-baseline. -/
structure ModexpTemplateConstants where
  /-- LM:131 `MODEXP_ADDRESS`. -/
  address : Nat
  /-- LM:87 `MODEXP_FRAME_BYTES`. -/
  frameBytes : Nat
  /-- M:214: `WORD_BYTES`, i.e. the output is one word. -/
  outputBytes : Nat
  /-- LM:275 `BASE_LEN_OFFSET`. -/
  baseLenOffset : Nat
  /-- LM:277 `EXP_LEN_OFFSET`. -/
  expLenOffset : Nat
  /-- LM:279 `MOD_LEN_OFFSET`. -/
  modLenOffset : Nat
  /-- LM:281 `BASE_OFFSET`. -/
  baseOffset : Nat
  /-- LM:283 `EXP_OFFSET`. -/
  expOffset : Nat
  /-- LM:285 `MOD_OFFSET`. -/
  modOffset : Nat

/-- rust: M:105-115 (`struct AccumulatorTemplateConstants`) @formal-baseline. -/
structure AccumulatorTemplateConstants where
  /-- LM:299 `LIMBS_PER_WORD`. -/
  limbsPerWord : Nat
  /-- LM:302 `IDENTITY_FLAG_WORDS`. -/
  identityFlagWords : Nat
  /-- LM:330-331 `PAIRING_BATCH_DOMAIN_TAG_HEX`. -/
  pairingBatchDomainTagHex : String
  /-- LM:338 `PAIRING_BATCH_VK_DIGEST_OFFSET`. -/
  pairingBatchVkDigestOffset : Nat
  /-- LM:340 `PAIRING_BATCH_RHS_OFFSET`. -/
  pairingBatchRhsOffset : Nat
  /-- LM:342 `PAIRING_BATCH_LHS_OFFSET`. -/
  pairingBatchLhsOffset : Nat
  /-- LM:344 `PAIRING_BATCH_ACC_RHS_OFFSET`. -/
  pairingBatchAccRhsOffset : Nat
  /-- LM:346 `PAIRING_BATCH_ACC_LHS_OFFSET`. -/
  pairingBatchAccLhsOffset : Nat
  /-- LM:348 `PAIRING_BATCH_HASH_BYTES`. -/
  pairingBatchHashBytes : Nat

/-- rust: M:119-151 (`struct QuotientVmOpcodeTemplateConstants`)
    @formal-baseline. Field order is the Rust's, which is the order the
    interpreter's switch arms are emitted in. -/
structure QuotientVmOpcodeTemplateConstants where
  pushConst : Nat
  pushMemLiteral : Nat
  pushMemToken : Nat
  pushMemTokenOffset : Nat
  pushMemU16 : Nat
  add : Nat
  mul : Nat
  neg : Nat
  pushConstU8 : Nat
  foldMain : Nat
  foldSelector : Nat
  addConstU8 : Nat
  mulConstU8 : Nat
  addConst : Nat
  mulConst : Nat
  addMemU16 : Nat
  mulMemU16 : Nat
  addMulMemMemConstU8 : Nat
  addMulConstU8MemU16 : Nat
  addMulMemMem : Nat
  runAddMulMemMemConstU8 : Nat
  runAddMulConstU8MemU16 : Nat
  affineSum : Nat
  nativePermutation : Nat
  nativeLookup : Nat
  nativeIdentity : Nat
  lin7 : Nat
  bilin7Row : Nat
  bilin7Pairwise : Nat
  modarith7 : Nat
  pow5 : Nat

/-- rust: M:155-165 (`struct QuotientVmMemTokenTemplateConstants`)
    @formal-baseline. -/
structure QuotientVmMemTokenTemplateConstants where
  l0 : Nat
  lLast : Nat
  lBlind : Nat
  beta : Nat
  gamma : Nat
  x : Nat
  theta : Nat
  trashChallenge : Nat
  instanceEval : Nat

/-- rust: M:169-175 (`struct QuotientVmTemplateConstants`) @formal-baseline. -/
structure QuotientVmTemplateConstants where
  op : QuotientVmOpcodeTemplateConstants
  mem : QuotientVmMemTokenTemplateConstants
  /-- QVM:546 `QUOTIENT_VM_BYTE_U32_BYTES`. -/
  byteU32Bytes : Nat
  /-- QVM:548 `QUOTIENT_VM_LIMBS`. -/
  limbCount : Nat
  /-- QVM:552 `QUOTIENT_VM_PAIRWISE_COEFFS`. -/
  limbPairwiseCoeffs : Nat

/-- rust: M:31-52 (`struct TemplateConstants`) @formal-baseline. Declared after
    its five sub-records only because Lean resolves a field type eagerly. -/
structure TemplateConstants where
  /-- LM:17 `WORD_BYTES`. -/
  wordBytes : Nat
  /-- LM:69 `G1_BYTES`. -/
  g1Bytes : Nat
  /-- LM:80 `G1_MSM_PAIR_BYTES`. -/
  g1MsmPairBytes : Nat
  /-- LM:82 `G1ADD_INPUT_BYTES`. -/
  g1addInputBytes : Nat
  /-- LM:97 `PAIRING_TWO_PAIR_BYTES`. -/
  pairingTwoPairBytes : Nat
  eip2537 : Eip2537TemplateConstants
  gas : GasTemplateConstants
  modexp : ModexpTemplateConstants
  accumulator : AccumulatorTemplateConstants
  quotientVm : QuotientVmTemplateConstants

/-- rust: ENC:821-828 (`fp48_be_to_hi_lo`) @formal-baseline. The Rust copies the
    first 16 bytes of a 48-byte big-endian coordinate into the LOW end of a
    zero-filled 32-byte array and the last 32 bytes into a second word, so the
    high word is the top 16 bytes right-aligned and the low word is the bottom
    32 bytes. -/
def fp48ToHiLo (coord : Nat) : Word256 × Word256 :=
  (BitVec.ofNat 256 (coord / 2 ^ 256), BitVec.ofNat 256 (coord % 2 ^ 256))

/-- rust: M:178-181 (`g1_words`) over ENC:835-858 (`g1_to_u256s`)
    @formal-baseline. The Rust takes a `G1Affine`, asserts the identity when
    `coordinates()` is `None`, and refuses an off-curve point rather than
    silently encoding it as the identity; the point-to-coordinates step belongs
    to the curve codec, so this takes the two 48-bit coordinates directly. -/
def g1Words (x y : Nat) : G1Words :=
  { xHi := (fp48ToHiLo x).1, xLo := (fp48ToHiLo x).2,
    yHi := (fp48ToHiLo y).1, yLo := (fp48ToHiLo y).2 }

/-- The 48-bit x of the BLS12-381 G1 generator the Rust reads from
    `G1Affine::generator()` at M:199, as it is rendered in the artifact at
    D:392-393 (x_hi then x_lo). `g1Generator_onCurve_ok` below is what makes
    this number evidence rather than a copy: it satisfies y^2 = x^3 + 4 over the
    base field `Midfall.Yul.blsP`, which this file does not define. -/
def g1GeneratorX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb

/-- The y of the same generator, D:394-395. -/
def g1GeneratorY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

/-- The 48-bit coordinates of twice the generator, i.e. M:200-203's
    `g1_words((g + g).to_affine())`, as rendered at D:401-406 and re-pinned as
    the `spread` fixture in YulGolden.lean. `g1Generator_doubles_ok` derives it
    from `g1GeneratorX/Y` with the affine group law. -/
def g1DoubleGeneratorX : Nat :=
  0x0572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e

/-- The y of 2G, D:405-406. -/
def g1DoubleGeneratorY : Nat :=
  0x166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28

/-- rust: M:183-284 (`impl Default for TemplateConstants`) @formal-baseline.
    Every field is the literal the Rust reads from LM: or QVM:; the cite on each
    field of the structure above is the definition site of that literal. -/
def templateConstantsDefault : TemplateConstants := {
  wordBytes := 0x20
  g1Bytes := 128
  g1MsmPairBytes := 160
  g1addInputBytes := 256
  pairingTwoPairBytes := 768
  eip2537 := {
    g1addAddress := 0x0b
    g1msmAddress := 0x0c
    pairingAddress := 0x0f
    smokeScratchBytes := 768
    g1Generator := g1Words g1GeneratorX g1GeneratorY
    g1DoubleGenerator := g1Words g1DoubleGeneratorX g1DoubleGeneratorY
  }
  gas := {
    g1add := 375
    g1msmOnePair := 12000
    pairingTwoPair := 102900
    modexp := 4080
  }
  modexp := {
    address := 0x05
    frameBytes := 192
    outputBytes := 32
    baseLenOffset := 0
    expLenOffset := 32
    modLenOffset := 64
    baseOffset := 96
    expOffset := 128
    modOffset := 160
  }
  accumulator := {
    limbsPerWord := 4
    identityFlagWords := 1
    pairingBatchDomainTagHex := "0x70616972696e672d62617463682d6163632d6b7a670000000000000000"
    pairingBatchVkDigestOffset := 32
    pairingBatchRhsOffset := 64
    pairingBatchLhsOffset := 192
    pairingBatchAccRhsOffset := 320
    pairingBatchAccLhsOffset := 448
    pairingBatchHashBytes := 576
  }
  quotientVm := {
    op := {
      pushConst := 0x01
      pushMemLiteral := 0x02
      pushMemToken := 0x03
      pushMemTokenOffset := 0x04
      pushMemU16 := 0x05
      add := 0x06
      mul := 0x07
      neg := 0x08
      pushConstU8 := 0x09
      foldMain := 0x0a
      foldSelector := 0x0b
      addConstU8 := 0x0c
      mulConstU8 := 0x0d
      addConst := 0x0e
      mulConst := 0x0f
      addMemU16 := 0x10
      mulMemU16 := 0x11
      addMulMemMemConstU8 := 0x12
      addMulConstU8MemU16 := 0x13
      addMulMemMem := 0x14
      runAddMulMemMemConstU8 := 0x15
      runAddMulConstU8MemU16 := 0x16
      affineSum := 0x22
      nativePermutation := 0x19
      nativeLookup := 0x1f
      nativeIdentity := 0x1b
      lin7 := 0x1c
      bilin7Row := 0x1d
      bilin7Pairwise := 0x1e
      modarith7 := 0x21
      pow5 := 0x20
    }
    mem := {
      l0 := 0x01
      lLast := 0x02
      lBlind := 0x03
      beta := 0x04
      gamma := 0x05
      x := 0x06
      theta := 0x07
      trashChallenge := 0x08
      instanceEval := 0x09
    }
    byteU32Bytes := 4
    limbCount := 7
    limbPairwiseCoeffs := 13
  }
}

/-- rust: M:288-311 (`struct Halo2VerifyingKey`, the Askama model for
    T:contracts/Halo2VerifyingKey.sol per M:286-287) @formal-baseline. -/
structure Halo2VerifyingKey where
  /-- M:290: constructor memory base used while returning VK bytes. -/
  constructorPayloadMptr : Nat
  /-- M:292: header constants, then optional quotient constant/program words. -/
  constants : List (String × Word256)
  /-- M:294: EIP-2537-padded fixed commitments. -/
  fixedComms : List G1Words
  /-- M:296: EIP-2537-padded permutation commitments. -/
  permutationComms : List G1Words
  /-- M:298: word offset of quotient constants, when present. -/
  quotientConstOffsetWords : Option Nat
  /-- M:300: number of quotient constant words. -/
  quotientConstWords : Nat
  /-- M:302: word offset of quotient program words, when present. -/
  quotientProgramOffsetWords : Option Nat
  /-- M:304: number of quotient program words. -/
  quotientProgramWords : Nat
  /-- M:307: direct lowering - trailing comment of each quotient-constant word. -/
  quotientConstLabels : List String
  /-- M:310: direct lowering - comment lines before quotient-constant words,
      keyed by the word index inside that section. -/
  quotientConstHeaders : List (Nat × List String)

/-- rust: M:314 (`const VK_RUNTIME_PREFIX: u8 = 0xfe`) @formal-baseline. The
    INVALID byte that prefixes the separate VK runtime payload. Note that the
    template does NOT interpolate this constant:
    T:contracts/Halo2VerifyingKey.sol:64 writes `mstore8(runtime, 0xfe)`
    literally, so the two agree only by hand. `vkConstructor_matchesGolden_ok`
    in Templates.lean is what keeps them from drifting apart silently. -/
def vkRuntimePrefix : Nat := 0xfe

/-- rust: M:316 (`const VK_RUNTIME_PREFIX_LEN: usize = 1`) @formal-baseline.
    Also hard-coded in the template as `add(runtime, 0x01)`. -/
def vkRuntimePrefixLen : Nat := 1

/-- Indexing helper: `List.get?` does not exist at this toolchain, and the Rust
    uses `Vec::get` (which returns `None` past the end) in two places that must
    stay total. -/
def listNth {α : Type} : List α → Nat → Option α
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listNth xs k
  | [], _ => none

/-- rust: M:320-327 (`Halo2VerifyingKey::word_comment`) @formal-baseline. The
    trailing comment of payload word `idx`. The Rust chain is
    `checked_sub(offset)` then `Vec::get(rel)` then `unwrap_or_else` on the
    constant's own name, so a word index BELOW the quotient section, and any
    index past the end of the label table, both fall back to the name. The
    Rust's `self.constants[idx]` is an indexing panic past the end (rule R4);
    this returns the empty string there instead, which is the one place the port
    is total where the Rust is not - recorded in the report. -/
def Halo2VerifyingKey.wordComment (self : Halo2VerifyingKey) (idx : Nat) : String :=
  let fallback := (self.constants.getD idx ("", 0)).1
  match self.quotientConstOffsetWords with
  | none => fallback
  | some offset =>
    if idx < offset then fallback
    else match listNth self.quotientConstLabels (idx - offset) with
         | some label => label
         | none => fallback

/-- rust: M:330-341 (`Halo2VerifyingKey::word_headers`) @formal-baseline.
    Comment lines emitted before payload word `idx`; the Rust's `find` matches
    the FIRST entry whose word index equals the section-relative index. -/
def Halo2VerifyingKey.wordHeaders (self : Halo2VerifyingKey) (idx : Nat) : List String :=
  match self.quotientConstOffsetWords with
  | none => []
  | some offset =>
    if idx < offset then []
    else match listNth
        (self.quotientConstHeaders.filterMap fun (word, lines) =>
          if word == idx - offset then some lines else none) 0 with
         | some lines => lines
         | none => []

/-- rust: M:402-406 (`Halo2VerifyingKey::len`) @formal-baseline: 32 bytes per
    scalar constant plus 128 bytes per EIP-2537-padded G1. -/
def Halo2VerifyingKey.len (self : Halo2VerifyingKey) : Nat :=
  self.constants.length * 32 + (self.fixedComms.length + self.permutationComms.length) * 128

/-- rust: M:409-411 (`Halo2VerifyingKey::runtime_len`) @formal-baseline. -/
def Halo2VerifyingKey.runtimeLen (self : Halo2VerifyingKey) : Nat :=
  vkRuntimePrefixLen + self.len

/-- rust: M:414-422 (`Halo2VerifyingKey::bytes`) @formal-baseline. The exact
    contract return order: every scalar constant, then the four words of each
    fixed commitment, then the four words of each permutation commitment, each
    U256 as 32 big-endian bytes. The two appends are the Rust's two `chain`s and
    the `flatMap` over the 4-tuple is the Rust's `flat_map([(a, b, c, d)])`. -/
def Halo2VerifyingKey.bytes (self : Halo2VerifyingKey) : Bytes :=
  let words :=
    self.constants.map (·.2) ++
    self.fixedComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo]) ++
    self.permutationComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])
  words.foldl (fun (acc : Bytes) (w : Word256) => ByteArray.append acc (wordToBytesBE w))
    Bytes.empty

/-- rust: M:426-431 (`Halo2VerifyingKey::runtime_bytes`) @formal-baseline: the
    INVALID prefix byte, then the payload. -/
def Halo2VerifyingKey.runtimeBytes (self : Halo2VerifyingKey) : Bytes :=
  (ByteArray.push Bytes.empty (Nat.toUInt8 vkRuntimePrefix)).append self.bytes

/-- rust: M:438-444 (`struct UserPhase`) @formal-baseline. -/
structure UserPhase where
  adviceBytes : Nat
  numChallenges : Nat
  /-- M:441-443: starting offset, in 32-byte words, into CHALLENGE_MPTR. -/
  challengeOffset : Nat

/-- rust: ENC:680-684 (`struct Ptr { loc, value }`) @formal-baseline.
    Filters.lean already ports the Display side (`printPtr`, which drops the
    location exactly as the Rust Display at ENC:716-721 does) but not the
    record, and M:539-542, M:555, M:570, M:575 carry it as a field type, so the
    record lives here. -/
structure Ptr where
  loc : Location
  value : Value

/-- rust: ENC:696-698 (`Ptr::memory`) @formal-baseline. -/
def ptrMemory (v : Value) : Ptr := { loc := Location.memory, value := v }

/-- rust: ENC:701-703 (`Ptr::calldata`) @formal-baseline. -/
def ptrCalldata (v : Value) : Ptr := { loc := Location.calldata, value := v }

/-- rust: ENC:706-708 (`Ptr::loc`) @formal-baseline. -/
def ptrLoc (p : Ptr) : Location := p.loc

/-- rust: ENC:711-713 (`Ptr::value`) @formal-baseline. The Rust also has
    `Value::as_usize` (ENC:596-601), which `unreachable!()`s on a symbolic
    identifier; its only callers in models.rs are inside `validate_layout`, so
    it is deferred with them rather than ported with a panic nothing reaches. -/
def ptrValue (p : Ptr) : Value := p.value

/-- rust: ENC:618-623 (`impl From<usize> for Value`) @formal-baseline. The
    Rust casts `usize` to `isize`; `Int.ofNat` is the same injection, and
    rule R5 emulates wrapping only where it can occur. -/
def valueFromNat (n : Nat) : Value := Value.integer (Int.ofNat n)

/-- rust: M:640-649 (`struct QuotientExternal`) @formal-baseline. -/
structure QuotientExternal where
  /-- M:642: base of the copied frame supplied to the external evaluator. -/
  frameBase : Nat
  /-- M:644: length of the copied frame in bytes. -/
  frameLen : Nat
  /-- M:646: expected return payload length in bytes. -/
  outputLen : Nat
  /-- M:648: magic version tag checked between verifier and evaluator; the
      value comes from QVM:516 `QUOTIENT_EXTERNAL_MAGIC`. -/
  magic : Nat

/-- rust: M:653-655 (`QuotientExternal::frame_end`) @formal-baseline. -/
def QuotientExternal.frameEnd (self : QuotientExternal) : Nat :=
  self.frameBase + self.frameLen

/-- rust: M:658-661 (`QuotientExternal::contains_range`) @formal-baseline. The
    Rust saturates the end so a huge `len` cannot wrap past the frame; on `Nat`
    addition cannot wrap at all, so the saturating add is a no-op here and is
    NOT emulated (rule R5). -/
def QuotientExternal.containsRange (self : QuotientExternal) (start len : Nat) : Bool :=
  start >= self.frameBase && start + len <= self.frameEnd

/-- rust: M:664-667 (`QuotientExternal::disjoint_range`) @formal-baseline, with
    the same no-wrap note. -/
def QuotientExternal.disjointRange (self : QuotientExternal) (start len : Nat) : Bool :=
  start + len <= self.frameBase || start >= self.frameEnd

/-- Rust's `{n:#x}` on an integer: `0x` plus minimal lowercase hex, with NO
    even-width pad. This is a THIRD hex formatter in the generator, distinct
    from the Askama `hex` filter (Filters.lean `hexFilter`, which pads odd
    widths to keep byte alignment) and from `fmt_hex` (ENC:626-633, also
    padded). The difference is only visible in error strings - which is exactly
    where a reviewer reads them - so it is ported rather than normalised onto
    one of the others. -/
def hashHex (n : Nat) : String := "0x" ++ hexDigits n

/-- rust: M:670-681 (`QuotientExternal::validate_contains`) @formal-baseline.
    The message is the Rust's `format!` with `{:#x}` on every address, i.e.
    `hashHex` and not the padded filters. -/
def QuotientExternal.validateContains (self : QuotientExternal) (name : String)
    (start len : Nat) : Except String Unit :=
  if self.containsRange start len then .ok ()
  else .error ("external quotient frame does not contain " ++ name
    ++ ": range " ++ hashHex start ++ ".." ++ hashHex (start + len)
    ++ ", frame " ++ hashHex self.frameBase ++ ".." ++ hashHex self.frameEnd)

/-- rust: M:751-760 (`struct QuotientVmGuards`) @formal-baseline. The
    interpreter's runtime structural checks (QVM-01). The Rust derives
    `Eq`/`PartialEq` here and nowhere else in models.rs, so `BEq` is derived on
    the Lean record too - see R-18 for why a derived `BEq` is the faithful
    reading rather than an extra. -/
structure QuotientVmGuards where
  /-- M:754: largest valid constant-table slot, `num_consts - 1`. -/
  constMax : Nat
  /-- M:756: number of simple-selector accumulator buckets. -/
  numSelectorBuckets : Nat
  /-- M:759: highest address a spill may write, `stack_hi - 0x20`. -/
  stackLast : Nat
deriving BEq

/-- rust: M:763-768 (`struct QuotientSelectorTail`) @formal-baseline. -/
structure QuotientSelectorTail where
  /-- M:765: byte offset of the selector bucket under SELECTOR_ACC_MPTR. -/
  selectorOffset : Nat
  /-- M:767: byte offset of the tail power under selector_power_mptr. -/
  powerOffset : Nat

/-- rust: M:771-803 (`struct QuotientVmOpcodeUsage`, `#[derive(Default)]`)
    @formal-baseline: one flag per switch arm the generated program needs. -/
structure QuotientVmOpcodeUsage where
  pushConst : Bool
  pushMemLiteral : Bool
  pushMemToken : Bool
  pushMemTokenOffset : Bool
  pushMemU16 : Bool
  add : Bool
  mul : Bool
  neg : Bool
  pushConstU8 : Bool
  foldMain : Bool
  foldSelector : Bool
  addConstU8 : Bool
  mulConstU8 : Bool
  addConst : Bool
  mulConst : Bool
  addMemU16 : Bool
  mulMemU16 : Bool
  addMulMemMemConstU8 : Bool
  addMulConstU8MemU16 : Bool
  addMulMemMem : Bool
  runAddMulMemMemConstU8 : Bool
  runAddMulConstU8MemU16 : Bool
  affineSum : Bool
  nativePermutation : Bool
  nativeLookup : Bool
  nativeIdentity : Bool
  lin7 : Bool
  bilin7Row : Bool
  bilin7Pairwise : Bool
  modarith7 : Bool
  pow5 : Bool

/-- rust: the `Default` derive on M:770. Every arm off: a program that needs no
    switch arm at all. -/
def quotientVmOpcodeUsageDefault : QuotientVmOpcodeUsage :=
  { pushConst := false, pushMemLiteral := false, pushMemToken := false,
    pushMemTokenOffset := false, pushMemU16 := false, add := false, mul := false,
    neg := false, pushConstU8 := false, foldMain := false, foldSelector := false,
    addConstU8 := false, mulConstU8 := false, addConst := false, mulConst := false,
    addMemU16 := false, mulMemU16 := false, addMulMemMemConstU8 := false,
    addMulConstU8MemU16 := false, addMulMemMem := false,
    runAddMulMemMemConstU8 := false, runAddMulConstU8MemU16 := false,
    affineSum := false, nativePermutation := false, nativeLookup := false,
    nativeIdentity := false, lin7 := false, bilin7Row := false,
    bilin7Pairwise := false, modarith7 := false, pow5 := false }

/-- rust: M:806-816 (`struct QuotientVmMemUsage`, `#[derive(Default)]`)
    @formal-baseline. -/
structure QuotientVmMemUsage where
  l0 : Bool
  lLast : Bool
  lBlind : Bool
  beta : Bool
  gamma : Bool
  x : Bool
  theta : Bool
  trashChallenge : Bool
  instanceEval : Bool

/-- rust: the `Default` derive on M:805. -/
def quotientVmMemUsageDefault : QuotientVmMemUsage :=
  { l0 := false, lLast := false, lBlind := false, beta := false, gamma := false,
    x := false, theta := false, trashChallenge := false, instanceEval := false }

/-- rust: M:716-741 (`struct QuotientProgram`) @formal-baseline. -/
structure QuotientProgram where
  /-- M:718: program length in bytes before word padding. -/
  len : Nat
  /-- M:720: opcode switch arms this program needs. -/
  opUsage : QuotientVmOpcodeUsage
  /-- M:722: memory-token switch arms this program needs. -/
  memUsage : QuotientVmMemUsage
  /-- M:724: memory pointer to the first constant word. -/
  constMptr : Nat
  /-- M:726: persistent quotient numerator accumulator word. -/
  evalNumerMptr : Nat
  /-- M:728: persistent trace-id word. -/
  traceIdMptr : Nat
  /-- M:730: first word of the optional selector y^k power table. -/
  selectorPowerMptr : Nat
  /-- M:732: highest selector gap/tail exponent referenced by generated code. -/
  selectorMaxPower : Nat
  /-- M:734: non-zero final selector y-power tail updates. -/
  selectorTailUpdates : List QuotientSelectorTail
  /-- M:736: operand stack / callback scratch base. -/
  stackMptr : Nat
  /-- M:738: memory pointer to the first encoded program word. -/
  programMptr : Nat
  /-- M:740: runtime structural checks rendered into the interpreter (QVM-01). -/
  guards : QuotientVmGuards

/-- rust: QDIR:56-65 (`struct DirectQuotientRendering`) @formal-baseline. Three
    lists of already-rendered text; the emitter that fills them belongs to the
    `Direct` row of plan Section 8, but `Halo2Verifier::quotient_direct` needs
    the record now, and it is self-contained, so it is ported rather than
    parameterised away. -/
structure DirectQuotientRendering where
  /-- QDIR:59: contract-level Solidity constant declarations. -/
  constants : List String
  /-- QDIR:62: Yul function definitions for the top of the assembly block. -/
  functions : List String
  /-- QDIR:64: the quotient section block. -/
  block : List String

/-- rust: M:447-450 (`struct VerifierCodegenLayout`) @formal-baseline.
    Parameterised over `ProofCalldataLayout` (abi/proof.rs), which the `Abi`
    row of plan Section 8 owns; the Rust field is `proof`. -/
structure VerifierCodegenLayout (Proof : Type) where
  proof : Proof

/-- rust: M:454-469 (`struct VkHeaderTemplateSlots`) @formal-baseline. Word
    offsets of the VK header fields, rendered into the `*_MPTR` constants. -/
structure VkHeaderTemplateSlots where
  vkDigest : Nat
  numInstances : Nat
  k : Nat
  nInv : Nat
  omega : Nat
  omegaInv : Nat
  omegaInvToL : Nat
  hasAccumulator : Nat
  accOffset : Nat
  numAccLimbs : Nat
  numAccLimbBits : Nat
  g1Base : Nat
  g2Base : Nat
  negSG2Base : Nat

/-- rust: M:471-493 (`impl Default for VkHeaderTemplateSlots`) @formal-baseline.
    Each slot is `VkHeaderLayout::field(Slot::X).slot.word()`, i.e. the
    discriminant of LM:406-435: the eleven scalars are 0..10, then
    LM:395-401 derives G1_BASE = 11, G2_BASE = 11 + G1_WORDS(4) = 15 and
    NEG_S_G2_BASE = 15 + G2_WORDS(8) = 23. -/
def vkHeaderTemplateSlotsDefault : VkHeaderTemplateSlots := {
  vkDigest := 0
  numInstances := 1
  k := 2
  nInv := 3
  omega := 4
  omegaInv := 5
  omegaInvToL := 6
  hasAccumulator := 7
  accOffset := 8
  numAccLimbs := 9
  numAccLimbBits := 10
  g1Base := 11
  g2Base := 15
  negSG2Base := 23
}

/-- rust: M:497-637 (`struct Halo2Verifier`, the Askama model for
    T:contracts/Halo2Verifier.sol per M:495-496) @formal-baseline. Field order
    is the Rust's, field for field. `Memory` stands for `VerifierMemoryLayout`
    (layout/memory.rs) and `Proof` for `ProofCalldataLayout` (abi/proof.rs);
    both belong to other rows of plan Section 8, so they are parameters rather
    than a second definition of someone else's type. -/
structure Halo2Verifier (Memory Proof : Type) where
  templateConstants : TemplateConstants
  trace : Bool
  /-- M:500-502: emit LOG1 gas() checkpoints at section boundaries. -/
  gasCheckpoints : Bool
  /-- M:503-506: test-only quotient probe; never set by `render`. -/
  quotientProbe : Bool
  quotientPow5Helper : Bool
  quotientLimb7Helper : Bool
  quotientWideLimb7Helper : Bool
  /-- M:510-511: largest generated G1MSM input, smoke-tested at deployment. -/
  constructorG1msmSmokeInputBytes : Nat
  /-- M:512-514: exact G1MSM cost for that smoke probe. -/
  constructorG1msmSmokeGas : Nat
  /-- M:515-520: worst-case G1MSM bound for the accumulator RHS MSM; 0 with no
      public accumulator. -/
  accRhsMsmGas : Nat
  /-- M:521: `[&str; LIN_COEFFS]` (LM:357 - six coefficients). Ported as a Lean
      list, which drops the length guarantee the Rust array type carried: a list
      here can be any length and nothing in the port would notice. The ported
      tables `limb7YulCoeffsTable` / `wideLimb7YulCoeffsTable` and the gate
      `limbCoeffArrays_length_ok` are what put that guarantee back. Note the
      guarantee is on the TABLES, not on this field: no Lean code fills this
      field from them (the renderer that would is a later package), so the field
      is still free. -/
  limb7YulCoeffs : List String
  wideLimb7YulCoeffs : List String
  /-- M:523. -/
  frDelta : String
  /-- M:524. -/
  embeddedVk : Option Halo2VerifyingKey
  expectedVkCodehash : Option Word256
  /-- M:526-529: keccak over the build's identity components; the public
      BUILD_ID constant. -/
  buildId : Word256
  vkLen : Nat
  /-- M:531-532: generated public-instance count. -/
  numInstances : Nat
  /-- M:533-534: evaluation domain size exponent. -/
  k : Nat
  proofLen : Nat
  codegenLayout : VerifierCodegenLayout Proof
  memory : Memory
  vkHeader : VkHeaderTemplateSlots
  vkMptr : Ptr
  challengeMptr : Ptr
  thetaMptr : Ptr
  proofCptr : Ptr
  abiSelectorBytes : Nat
  abiProofHeadOffset : Nat
  abiInstancesHeadCptr : Nat
  /-- M:546-551: calldata offset of the `num_instances` length-prefix word. -/
  numInstanceCptr : Nat
  /-- M:552-554: calldata offset of the first instance value. -/
  instanceCptr : Nat
  quotientCommCptr : Ptr
  numNegLagranges : Nat
  /-- M:557-558: per-user-phase advice + challenge counts, excluding theta. -/
  userPhases : List UserPhase
  numUserChallenges : Nat
  numLookups : Nat
  numPermutationZs : Nat
  lookupHPlusAcc : Nat
  numTrashcans : Nat
  numQuotients : Nat
  numEvals : Nat
  /-- M:566-570: base of the first padded advice commitment. -/
  commsMptrBase : Ptr
  /-- M:571-575: memory base of the decoded-evals buffer (Optimisation H3). -/
  reversedEvalsMptr : Ptr
  /-- M:576-580: scratch base for simple-selector linearization accumulators. -/
  selectorAccMptr : Nat
  quotientExternal : Option QuotientExternal
  expectedQuotientLen : Option Nat
  expectedQuotientCodehash : Option Word256
  quotientInlineComputations : List (List String)
  quotientEvalNumerComputations : List (List String)
  quotientPostVmComputations : List (List String)
  quotientNativePermutationComputation : List String
  quotientNativeLookupComputation : List String
  quotientNativeIdentityComputations : List (List String)
  quotientProgram : Option QuotientProgram
  /-- M:591-594: direct lowering; mutually exclusive with `quotientProgram` and
      `quotientExternal`. The exclusivity is enforced by `validate_layout`,
      which is deferred (see the header), so nothing here checks it yet. -/
  quotientDirect : Option DirectQuotientRendering
  pcsComputations : List (List String)
  /-- M:596-599: sorted simple-selector fixed-column indices. -/
  simpleSelectorCols : List Nat
  proofCommitTraceBase : Nat
  proofEvalTraceBase : Nat
  quotientIdentityTraceBase : Nat
  selectorTraceBase : Nat
  /-- M:604-606: memory pointer base for the embedded VK fixed commitments. -/
  fixedCommMptr : Nat
  /-- M:607-614: mirrors midnight-proofs/truncated-challenges; driven by
      `cfg!(feature = "truncated-challenges")`. Rule R8 makes the flag data,
      not a compile-time split: both branches live in the templates. -/
  truncatedChallenges : Bool
  /-- M:615-624: accumulator metadata this verifier expects, checked against the
      VK header after materialisation. -/
  expectedHasAccumulator : Bool
  expectedHasAccumulatorWord : Nat
  expectedAccOffset : Nat
  expectedNumAccLimbs : Nat
  expectedNumAccLimbBits : Nat
  /-- M:625-628: whether the public accumulator carries explicit LHS/RHS
      scalars; Moonlight wraps do not. -/
  expectedAccHasCarriedScalars : Bool
  /-- M:629-636: fixed bases for the RHS accumulator MSM in BTreeMap order, each
      `(point_mptr, negate_scalar)`. -/
  accFixedBases : List (Nat × Bool)

/-- rust: M:686-713 (`struct Halo2QuotientEvaluator`, the Askama model for
    T:contracts/Halo2QuotientEvaluator.sol per M:684-685) @formal-baseline.
    Unlike the verifier's, its `quotient_external` is NOT optional. -/
structure Halo2QuotientEvaluator (Memory : Type) where
  templateConstants : TemplateConstants
  trace : Bool
  quotientPow5Helper : Bool
  quotientLimb7Helper : Bool
  quotientWideLimb7Helper : Bool
  limb7YulCoeffs : List String
  wideLimb7YulCoeffs : List String
  frDelta : String
  memory : Memory
  vkMptr : Ptr
  vkLen : Nat
  challengeMptr : Ptr
  numUserChallenges : Nat
  thetaMptr : Ptr
  reversedEvalsMptr : Ptr
  numEvals : Nat
  quotientExternal : QuotientExternal
  quotientInlineComputations : List (List String)
  quotientEvalNumerComputations : List (List String)
  quotientPostVmComputations : List (List String)
  quotientNativePermutationComputation : List String
  quotientNativeLookupComputation : List String
  quotientNativeIdentityComputations : List (List String)
  quotientProgram : Option QuotientProgram
  simpleSelectorCols : List Nat
  quotientIdentityTraceBase : Nat

/-- rust: `LIMB7_YUL_COEFFS` at
    src/lowering/quotient_numerator/vm/mod.rs:521-528 @formal-baseline, typed
    `[&'static str; LIN_COEFFS]` where `LIN_COEFFS = LIMBS - 1` and
    `LIMBS = 7` (LM:355-357), i.e. six entries. Transcribed as a Lean list, so
    the length the Rust type enforced is now a fact this tree has to assert:
    `limbCoeffArrays_length_ok`. The VALUES are a transcription and nothing here
    re-derives them - they appear in no pinned artifact slice - so the gate is
    about length and shape, not about nibbles. -/
def limb7YulCoeffsTable : List String :=
  [ "0x100000000000000",
    "0x10000000000000000000000000000",
    "0x400000000",
    "0x40000000000000000000000",
    "0x1000",
    "0x100000000000000000" ]

/-- rust: `WIDE_LIMB7_YUL_COEFFS` at
    src/lowering/quotient_numerator/vm/mod.rs:530-537 @formal-baseline, the same
    `[&str; LIN_COEFFS]` type and so the same length as
    `limb7YulCoeffsTable`. -/
def wideLimb7YulCoeffsTable : List String :=
  [ "0x100000000000000",
    "0x10000000000000000000000000000",
    "0x1000000000000000000000000000000000000000000",
    "0x100000000000000000000000000000000000000000000000000000000",
    "0x6bc66e553973f396854f5626172ba135587d41e37a68209402355093fdcaaf6c",
    "0x63f31e3f446953960c9d6964474300df43ab29179970f642a28e39d6c883c74b" ]

end Midfall.Generator


/-! # Known-answer tests for the ported models

Every gate names the concrete wrong implementation it rules out, per the rule
docs/REVIEW.md R-38 states at the end of its entry: a KAT whose failure mode
cannot be stated is decoration and does not belong here. Where the expected side
is a literal this file also defines, the gate is a transcription check and says
so; where it is a value computed from a source this file does not control - the
EIP-derived constants in `Midfall.Yul`, the curve equation, the group law,
or the assertions in the Rust test module - the gate is evidence. The numeric
gates below are all of the second kind except where noted. -/

namespace Midfall.Generator.ModelKats

open Midfall Midfall.Generator

/-- The base-field modulus, taken from the independent port at
    Midfall/Yul/Externals.lean:114, which cites EIP-2537 rather than this Rust.
    That is what makes the curve gates below cross-checks and not tautologies. -/
def P : Nat := Midfall.Yul.blsP

/-- Inversion in the prime base field by Fermat little theorem, so the gate needs
    no typeclass search: x inverse = x^(p-2) mod p. -/
def fpInv (x : Nat) : Nat := Nat.powMod x (P - 2) P

/-- y^2 = x^3 + 4 over Fp, the curve EIP-2537 implements
    (Midfall/Yul/Externals.lean:124 `g1B`). -/
def onCurve (x y : Nat) : Bool :=
  (y * y - (x * x % P * x % P + 4)) % P == 0

/-- Affine doubling along the chord tangent: the arithmetic the G1ADD precompile
    performs on the smoke-test input at D:396-397. -/
def g1DoubleXY (x y : Nat) : Nat × Nat :=
  let lam := (3 * x * x % P) * fpInv (2 * y % P) % P
  let x2 := (lam * lam % P + P - (2 * x % P)) % P
  let y2 := (lam * ((x + P - x2) % P) % P + P - y) % P
  (x2, y2)

/-- THE GENERATOR WORDS ARE A REAL POINT. Rules out a mistyped coordinate: one
    wrong nibble in the 96-hex-digit x or y puts the pair off the curve, and the
    constructor smoke probe those words are embedded into (D:392-397) would then
    assert something no conformant precompile returns. The modulus comes from
    `Midfall.Yul`, not from this file, so the check is not self-referential. -/
def g1Generator_onCurve_ok : Bool :=
  onCurve g1GeneratorX g1GeneratorY && onCurve g1DoubleGeneratorX g1DoubleGeneratorY

/-- THE DOUBLE IS THE DOUBLE. Derives 2G from G with the group law and compares
    against the ported g1_double_generator (M:200-203). Rules out a stale or
    copied second generator - writing the G words into both fields, which every
    shape check on the record would still pass, and which turns the one probe a
    stub precompile cannot fake into a tautology. -/
def g1Generator_doubles_ok : Bool :=
  g1DoubleXY g1GeneratorX g1GeneratorY == (g1DoubleGeneratorX, g1DoubleGeneratorY)

/-- The padded split itself: hi is the top 16 bytes right-aligned, lo the bottom
    32, and the two recombine to the coordinate. Rules out swapping hi and lo,
    which would put the 16-byte pad on the wrong side of every EIP-2537 point
    the generator emits, and rules out a hi word wider than 16 bytes. -/
def g1Words_split_ok : Bool :=
  let w := g1Words g1GeneratorX g1GeneratorY
  w.xHi.toNat == g1GeneratorX / 2 ^ 256
    && w.xLo.toNat == g1GeneratorX % 2 ^ 256
    && w.xHi.toNat * 2 ^ 256 + w.xLo.toNat == g1GeneratorX
    && w.xHi.toNat < 2 ^ 128

/-- The words the record carries are the words the split produces, i.e.
    templateConstantsDefault.eip2537.g1Generator really is `g1Words` of the
    generator coordinates and not a second hand-written copy that could drift
    from it. Compared field by field because `G1Words` has no derived `BEq` -
    the Rust derives only Clone/Copy/Debug on these records. -/
def g1Generator_record_ok : Bool :=
  let g := templateConstantsDefault.eip2537.g1Generator
  let d := templateConstantsDefault.eip2537.g1DoubleGenerator
  [g.xHi.toNat, g.xLo.toNat, g.yHi.toNat, g.yLo.toNat]
    == [g1GeneratorX / 2 ^ 256, g1GeneratorX % 2 ^ 256,
        g1GeneratorY / 2 ^ 256, g1GeneratorY % 2 ^ 256]
    && [d.xHi.toNat, d.xLo.toNat, d.yHi.toNat, d.yLo.toNat]
    == [g1DoubleGeneratorX / 2 ^ 256, g1DoubleGeneratorX % 2 ^ 256,
        g1DoubleGeneratorY / 2 ^ 256, g1DoubleGeneratorY % 2 ^ 256]

/-- DERIVED WIDTHS AGREE WITH THEIR DERIVATION. LM:69, 80, 82, 97 and 87 define
    g1_bytes, g1_msm_pair_bytes, g1add_input_bytes, pairing_two_pair_bytes and
    the modexp frame size as expressions over WORD_BYTES / FR_BYTES / G1_WORDS /
    G2_WORDS, and LM:275-285 defines the six frame offsets as multiples of
    WORD_BYTES. The Rust compiler checks that arithmetic; a Lean port does not,
    so it has to. Rules out one width being edited without the others - a
    G1_BYTES of 64 beside a PAIRING_TWO_PAIR_BYTES of 768 is exactly the shape
    of that mistake, and it mis-sizes every precompile frame. -/
def templateConstants_widths_ok : Bool :=
  let c := templateConstantsDefault
  c.g1Bytes == 4 * c.wordBytes
    && c.g1MsmPairBytes == c.g1Bytes + c.wordBytes
    && c.g1addInputBytes == 2 * c.g1Bytes
    && c.pairingTwoPairBytes == 2 * (c.g1Bytes + 8 * c.wordBytes)
    && c.modexp.frameBytes == 6 * c.wordBytes
    && c.modexp.outputBytes == c.wordBytes
    && c.modexp.baseLenOffset == 0
    && c.modexp.expLenOffset == c.wordBytes
    && c.modexp.modLenOffset == 2 * c.wordBytes
    && c.modexp.baseOffset == 3 * c.wordBytes
    && c.modexp.expOffset == 4 * c.wordBytes
    && c.modexp.modOffset == 5 * c.wordBytes

/-- THE SAME FACTS, FROM THE OTHER PORT. Midfall/Yul/Externals.lean ports the
    four precompile addresses and the four scheduled gas bounds from the EIPs
    (Externals.lean:133-150, 612-719); models.rs reads them from
    `layout::precompile` and `layout::gas`. Two independent ports of one
    fact, compared. Rules out this file having copied a wrong literal from a
    stale reading of the Rust: a typo in `0x0b`, in 375, or in 102900 reddens
    exactly one conjunct, and the gate cannot be satisfied by editing both sides
    because only one of them is in this file. -/
def templateConstants_matchYulExternals_ok : Bool :=
  let c := templateConstantsDefault
  c.eip2537.g1addAddress == Midfall.Yul.g1AddAddress.toNat
    && c.eip2537.g1msmAddress == Midfall.Yul.g1MsmAddress.toNat
    && c.eip2537.pairingAddress == Midfall.Yul.pairingAddress.toNat
    && c.modexp.address == Midfall.Yul.modexpAddress.toNat
    && c.gas.g1add == Midfall.Yul.g1AddGasScheduled
    && c.gas.g1msmOnePair == Midfall.Yul.g1MsmOnePairGasScheduled
    && c.gas.pairingTwoPair == Midfall.Yul.pairingTwoPairGasScheduled
    && c.gas.modexp == Midfall.Yul.modexpGasScheduled

/-- The gas bounds are the SCHEDULE FORMULAS evaluated at the pair counts the
    model uses - `g1msm_gas(1)` and `pairing_gas(2)` (M:207-208) - not
    free-floating numbers. `Midfall.Yul.g1MsmGasPairs` / `pairingGasPairs` are
    the EIP formulas including the 128-entry discount table. Rules out a bound
    being transcribed from the rendered artifact instead of from the schedule,
    which is the direction of error that survives a re-render. -/
def templateConstants_gasFormulas_ok : Bool :=
  let c := templateConstantsDefault
  c.gas.g1msmOnePair == Midfall.Yul.g1MsmGasPairs 1
    && c.gas.pairingTwoPair == Midfall.Yul.pairingGasPairs 2

/-- MF-1 (LM:220-236): the modexp bound is the MAXIMUM over the two live
    schedules, so it must be the EIP-7883 price 4080 and strictly above the
    EIP-2565 price 1360 it replaced. Rules out the port reverting to the
    pre-MF-1 reading, which deploys fine and then reverts every proof on a
    repriced chain. -/
def templateConstants_modexpGasIsMaxSchedule_ok : Bool :=
  templateConstantsDefault.gas.modexp == 4080 && templateConstantsDefault.gas.modexp > 1360

/-- The accumulator batch frame is a layout, not nine independent numbers:
    LM:338-348 derives every offset from WORD_BYTES and G1_BYTES and the hash
    length is the frame size. Rules out an offset being edited without the frame
    length following, which changes the alpha preimage the pairing batch hashes
    - the class of bug R-26 records on the accumulator path. -/
def templateConstants_accumulatorFrame_ok : Bool :=
  let c := templateConstantsDefault
  let a := c.accumulator
  let w := c.wordBytes
  a.pairingBatchVkDigestOffset == w
    && a.pairingBatchRhsOffset == 2 * w
    && a.pairingBatchLhsOffset == a.pairingBatchRhsOffset + c.g1Bytes
    && a.pairingBatchAccRhsOffset == a.pairingBatchLhsOffset + c.g1Bytes
    && a.pairingBatchAccLhsOffset == a.pairingBatchAccRhsOffset + c.g1Bytes
    && a.pairingBatchHashBytes == 2 * w + 4 * c.g1Bytes
    && a.pairingBatchHashBytes == a.pairingBatchAccLhsOffset + c.g1Bytes
    && a.limbsPerWord == 4 && a.identityFlagWords == 1

/-- Two hex nibbles of a char list as one byte, by character code so that no char
    literals are needed. -/
def hexByteAt (cs : List Char) (pos : Nat) : Nat :=
  let nib (c : Char) : Nat :=
    if c.toNat >= 48 && c.toNat <= 57 then c.toNat - 48
    else if c.toNat >= 97 && c.toNat <= 102 then c.toNat - 87
    else c.toNat - 55
  nib (cs.getD pos (Char.ofNat 48)) * 16 + nib (cs.getD (pos + 1) (Char.ofNat 48))

/-- The domain tag decodes to ASCII "pairing-batch-acc-kzg" followed by eight
    zero bytes - 29 bytes, 58 nibbles - exactly as LM:314-331 documents,
    including that comment's correction: the literal is a 29-byte NUMBER that
    `mstore` left-pads to a word, so the hashed bytes are 00*3 || tag || 00*8,
    not right-padded ASCII. Rules out the tag being re-padded or one nibble
    mistyped; the decode compares bytes, not the hex string, so swapping two
    nibbles inside the ASCII run fails. -/
def templateConstants_domainTag_isAscii_ok : Bool :=
  let body := (templateConstantsDefault.accumulator.pairingBatchDomainTagHex).drop 2
  let cs := body.toString.toList
  let tag := "pairing-batch-acc-kzg".toUTF8
  cs.length == 58
    && tag.size == 21
    && (List.range 21).all fun i => hexByteAt cs (i * 2) == tag[i]!.toNat
    && (List.range 8).all fun i => hexByteAt cs (42 + i * 2) == 0

/-- The QVM opcode byte is the switch label the interpreter dispatches on, so
    two opcodes sharing one value silently execute the wrong instruction.
    Rules out a transcription collision in the 31-entry table - the Rust cannot
    catch that either, since it names each constant separately and only the
    rendered switch would show the clash. 0x17, 0x18 and 0x1a are deliberately
    unused (QVM:564-565 keeps 0x1a reserved for a retired native trash
    callback), so distinctness and range are the properties, not density. -/
def qvmOpcodes_distinct_ok : Bool :=
  let o := templateConstantsDefault.quotientVm.op
  let vals := [o.pushConst, o.pushMemLiteral, o.pushMemToken, o.pushMemTokenOffset,
    o.pushMemU16, o.add, o.mul, o.neg, o.pushConstU8, o.foldMain, o.foldSelector,
    o.addConstU8, o.mulConstU8, o.addConst, o.mulConst, o.addMemU16, o.mulMemU16,
    o.addMulMemMemConstU8, o.addMulConstU8MemU16, o.addMulMemMem,
    o.runAddMulMemMemConstU8, o.runAddMulConstU8MemU16, o.affineSum,
    o.nativePermutation, o.nativeLookup, o.nativeIdentity, o.lin7, o.bilin7Row,
    o.bilin7Pairwise, o.modarith7, o.pow5]
  vals.length == 31
    && vals.all (fun v => v > 0 && v < 256)
    && vals.all (fun v => vals.count v == 1)
    && ! vals.any (fun v => [0x17, 0x18, 0x1a].contains v)

/-- The memory tokens are the dense run 1..9 (QVM:608-616) and the table-level
    constants are the quotient-limb shapes LM:355-361 derives: LIMBS = 7,
    PAIRWISE_COEFFS = 2 * LIMBS - 1 = 13. Rules out a limb count being changed
    in one place only, which desynchronises the operand decoder from the emitted
    switch, and rules out the token numbering drifting. -/
def qvmMemTokens_and_tableShapes_ok : Bool :=
  let m := templateConstantsDefault.quotientVm.mem
  let q := templateConstantsDefault.quotientVm
  [m.l0, m.lLast, m.lBlind, m.beta, m.gamma, m.x, m.theta, m.trashChallenge,
    m.instanceEval] == [1, 2, 3, 4, 5, 6, 7, 8, 9]
    && q.limbCount == 7
    && q.limbPairwiseCoeffs == 2 * q.limbCount - 1
    && q.byteU32Bytes == 4

/-- The VK header slots are the discriminants LM:395-435 derives: eleven scalars
    at 0..10, then G1 at 11, G2 at 11 + 4, -sG2 at 15 + 8. Rules out a slot
    being renumbered without the widths moving with it - the shape of error that
    makes the verifier read `omega` where the VK contract wrote `k`. -/
def vkHeaderSlots_derivation_ok : Bool :=
  let s := vkHeaderTemplateSlotsDefault
  [s.vkDigest, s.numInstances, s.k, s.nInv, s.omega, s.omegaInv, s.omegaInvToL,
    s.hasAccumulator, s.accOffset, s.numAccLimbs, s.numAccLimbBits]
    == List.range 11
    && s.g1Base == 11
    && s.g2Base == s.g1Base + 4
    && s.negSG2Base == s.g2Base + 8
    && s.negSG2Base == 23

/-- The synthetic VK the Rust test builds at M:1069-1107: 11 named scalars + 4
    g1 + 8 g2 + 8 neg_s_g2 = 31 constants. Ported so the byte-order gates below
    check this file against the Rust own fixture rather than against a fixture
    invented here. -/
def syntheticVkConstants : List (String × Word256) :=
  [("vk_digest", 0xde), ("num_instances", 1), ("k", 8), ("n_inv", 0x1234),
   ("omega", 0x5678), ("omega_inv", 0x9abc), ("omega_inv_to_l", 0xdef0),
   ("has_accumulator", 0), ("acc_offset", 0), ("num_acc_limbs", 0),
   ("num_acc_limb_bits", 0), ("g1_x_hi", 0x10), ("g1_x_lo", 0x11),
   ("g1_y_hi", 0x12), ("g1_y_lo", 0x13), ("g2_x_c0_hi", 0x20), ("g2_x_c0_lo", 0x21),
   ("g2_x_c1_hi", 0x22), ("g2_x_c1_lo", 0x23), ("g2_y_c0_hi", 0x24),
   ("g2_y_c0_lo", 0x25), ("g2_y_c1_hi", 0x26), ("g2_y_c1_lo", 0x27),
   ("neg_s_g2_x_c0_hi", 0x30), ("neg_s_g2_x_c0_lo", 0x31), ("neg_s_g2_x_c1_hi", 0x32),
   ("neg_s_g2_x_c1_lo", 0x33), ("neg_s_g2_y_c0_hi", 0x34), ("neg_s_g2_y_c0_lo", 0x35),
   ("neg_s_g2_y_c1_hi", 0x36), ("neg_s_g2_y_c1_lo", 0x37)]

/-- The commitment builders of M:1109-1130: base 0x40 + 4i for fixed, 0x80 + 4i
    for permutation, each expanded to (base, base+1, base+2, base+3). -/
def syntheticG1s (start : Nat) (n : Nat) : List G1Words :=
  (List.range n).map fun i =>
    { xHi := start + i * 4, xLo := start + i * 4 + 1,
      yHi := start + i * 4 + 2, yLo := start + i * 4 + 3 }

/-- A synthetic VK with `nFixed` fixed and `nPerm` permutation commitments,
    mirroring `synthetic_vk` at M:1064-1146. The constructor pointer is left at
    0: `VkConstructorMemoryLayout` belongs to the deferred Layout row. -/
def syntheticVk (nFixed nPerm : Nat) : Halo2VerifyingKey := {
  constructorPayloadMptr := 0
  constants := syntheticVkConstants
  fixedComms := syntheticG1s 0x40 nFixed
  permutationComms := syntheticG1s 0x80 nPerm
  quotientConstOffsetWords := none
  quotientConstWords := 0
  quotientProgramOffsetWords := none
  quotientProgramWords := 0
  quotientConstLabels := []
  quotientConstHeaders := []
}

/-- rust: M:1343-1352 (`vk_layout_byte_consistency`). The Rust asserts
    len() == 31*32 + (2+3)*4*32 == 1632 and bytes().len() == len(). Rules out
    `len` counting a G1 as one word, or as 4 words instead of 4*32 bytes - the
    first makes EXPECTED_VK_LENGTH wrong and the deployment guard then rejects
    every VK. -/
def vkLen_matchesRustTest_ok : Bool :=
  let vk := syntheticVk 2 3
  vk.len == 31 * 32 + (2 + 3) * 4 * 32 && vk.len == 1632 && vk.bytes.size == vk.len

/-- rust: M:1354-1379, the byte-order half of the same test: word 0 is
    `vk_digest` = 0xde, word 23 is `neg_s_g2_x_c0_hi` = 0x30, word 31 the first
    fixed commitment = 0x40, word 39 the first permutation commitment = 0x80.
    This is the only thing that pins the payload return order, and the verifier
    copies these bytes by offset, so a reordering is a deployment fault, not a
    cosmetic one. Rules out the two appends being swapped, or a G1 four words
    being flattened in a different order. -/
def vkBytes_order_matchesRustTest_ok : Bool :=
  let bs := (syntheticVk 2 3).bytes
  [(0, 0xde), (23, 0x30), (31, 0x40), (39, 0x80)].all fun (w, want) =>
    match bytesTake bs (w * 32) 32 with
    | some slice => bytesToNatBE slice == want
    | none => false

/-- The header slot numbering and the constant table agree: slot 11 is the first
    g1 word, slot 15 the first g2 word, slot 23 the first neg_s_g2 word. Ties
    `vkHeaderSlots_derivation_ok` to `syntheticVkConstants`, so a width change
    in one of the two is caught by the other. -/
def vkHeaderSlot_agreesWithConstantTable_ok : Bool :=
  (syntheticVkConstants.getD vkHeaderTemplateSlotsDefault.negSG2Base ("", 0)).1
    == "neg_s_g2_x_c0_hi"
    && (syntheticVkConstants.getD vkHeaderTemplateSlotsDefault.g1Base ("", 0)).1
      == "g1_x_hi"
    && (syntheticVkConstants.getD vkHeaderTemplateSlotsDefault.g2Base ("", 0)).1
      == "g2_x_c0_hi"

/-- rust: M:409-411 and M:426-431, with the assertions at M:1454-1457: the
    runtime is one INVALID byte followed by the payload, so its length is
    len + 1 and its tail is the payload exactly. Rules out the prefix being
    appended after the payload instead of before it, which would make the
    verifier `extcodecopy(vk, VK_MPTR, 0x01, ...)` drop a byte and shift every
    word of the payload by one. -/
def vkRuntime_prefix_ok : Bool :=
  let vk := syntheticVk 2 3
  vk.runtimeLen == vk.len + 1
    && vk.runtimeBytes.size == vk.runtimeLen
    && vk.runtimeBytes.data[0]!.toNat == 0xfe
    && (match bytesTake vk.runtimeBytes 1 vk.len with
        | some t => t == vk.bytes
        | none => false)

/-- The Rust test runtime length is 1633 = 0x661, and the comment at
    M:1452-1453 says the `hex` filter renders that as `0x0661` because the
    nibble count is odd. Ties the model to the filter port in Filters.lean: an
    odd-width value is the only case where `hex()` pads, and this is a real one. -/
def vkRuntimeLen_hexRendering_ok : Bool :=
  (syntheticVk 2 3).runtimeLen == 0x661 && hexFilter 0x661 == "0x0661"

/-- `syntheticVk 0 0`, named because Lean record update needs a name as its
    base, not an application. -/
def vkPlain : Halo2VerifyingKey := syntheticVk 0 0

/-- M:322-326 with two labels and the offset at the end of the header. -/
def vkLabeled : Halo2VerifyingKey :=
  { vkPlain with
    quotientConstOffsetWords := (some 31),
    quotientConstLabels := ["q_const_0", "q_const_1"] }

/-- The same, with the label table one entry short of the section: the Rust
    `Vec::get` returns None and the name comes back. -/
def vkShortLabels : Halo2VerifyingKey :=
  { vkPlain with
    quotientConstOffsetWords := (some 31),
    quotientConstLabels := ["q_const_0"] }

/-- M:330-341 with two coefficient-run headers keyed by section-relative index. -/
def vkHeaded : Halo2VerifyingKey :=
  { vkPlain with
    quotientConstOffsetWords := (some 31),
    quotientConstHeaders := [(0, ["run A", "line"]), (2, ["run B"])] }

/-- rust: M:320-327 (`word_comment`). Without a quotient section every word is
    named from `constants`; with one, words at or past the offset take the
    label, and an index past the end of the label table falls back to the name
    (the Rust `unwrap_or_else`). Rules out the offset comparison being
    inverted, which would name every header word after a quotient label and
    every quotient word after its header name - and rules out `checked_sub`
    being ported as saturating subtraction, which would send header words to
    label 0 instead of to the fallback. -/
def wordComment_ok : Bool :=
  let vk := syntheticVk 0 0
  vk.wordComment 0 == "vk_digest" && vk.wordComment 30 == "neg_s_g2_y_c1_lo"
    && vkLabeled.wordComment 31 == "q_const_0"
    && vkLabeled.wordComment 32 == "q_const_1"
    && vkShortLabels.wordComment 32 == ""
    && vkShortLabels.wordComment 5 == "omega_inv"

/-- rust: M:330-341 (`word_headers`). Headers appear only at the section-relative
    index they are keyed by, and only at or past the quotient offset. Rules out
    `find` matching on the absolute index instead of the relative one, which
    would put the run header at the wrong word. -/
def wordHeaders_ok : Bool :=
  (syntheticVk 0 0).wordHeaders 0 == []
    && vkHeaded.wordHeaders 31 == ["run A", "line"]
    && vkHeaded.wordHeaders 32 == []
    && vkHeaded.wordHeaders 30 == []
    && vkHeaded.wordHeaders 33 == ["run B"]

/-- A frame at 0x100..0x140, the shape the external quotient tests use. -/
def qext : QuotientExternal :=
  { frameBase := 0x100, frameLen := 0x40, outputLen := 0x20, magic := 1 }

/-- rust: M:653-667 (`frame_end`, `contains_range`, `disjoint_range`). The
    boundaries are the whole content of this gate: containment is inclusive at
    both ends, and disjointness is `end <= base || start >= frame_end`, so a
    range ending exactly at the frame base is disjoint and one starting inside
    it is not. Rules out `>` where the Rust has `>=` - the difference is
    whether the output buffer may start at the byte the frame ends at, which
    validate_layout then accepts or rejects. -/
def quotientExternal_ranges_ok : Bool :=
  qext.frameEnd == 0x140
    && qext.containsRange 0x100 0x40
    && qext.containsRange 0x110 0x10
    && ! qext.containsRange 0x0ff 0x10
    && ! qext.containsRange 0x101 0x40
    && qext.disjointRange 0x0e0 0x20
    && qext.disjointRange 0x140 0x20
    && ! qext.disjointRange 0x13f 0x20
    && ! qext.disjointRange 0x100 0x1

/-- The Rust `saturating_add` (M:659, M:665) is load-bearing there: a length
    that overflows `usize` must not wrap the end below the frame and make an
    out-of-frame range look contained. On `Nat` there is no wrap to emulate
    (rule R5), and this pins that the port neither gains one nor needs one: a
    2^200-byte range is neither contained nor disjoint. A port that modelled
    offsets as `UInt64` would answer `containsRange = true` here. -/
def quotientExternal_noWrap_ok : Bool :=
  ! qext.containsRange 0x100 (2 ^ 200) && ! qext.disjointRange 0x100 (2 ^ 200)

/-- rust: M:670-681 (`validate_contains`). The Ok/Err split and the message
    shape: every address in hex, none in decimal, and NOT the even-width padded
    hex the Askama filter uses - `{:#x}` on a usize gives `0x100`, not
    `0x0100`. Rules out the message being built with decimal offsets (which is
    what a reviewer greps for when a build fails and the log is the only
    evidence left), and rules out the three hex formatters being collapsed into
    one. -/
def quotientExternal_validateContains_ok : Bool :=
  qext.validateContains "VK payload" 0x100 0x20 == .ok ()
    && qext.validateContains "VK payload" 0x200 0x20
        == .error "external quotient frame does not contain VK payload: range 0x200..0x220, frame 0x100..0x140"

/-- rust: the `#[derive(Default)]`s on M:770 and M:805. A usage record with any
    arm set emits a switch arm the program never reaches; the Rust default is
    all-false by construction, and the Lean port has no derive, so the literal
    written out here is the contract. Rules out a field being added to the
    record with a `true` default, which is what a derive would silently do. -/
def usageDefaults_ok : Bool :=
  quotientVmOpcodeUsageDefault.add == false
    && quotientVmOpcodeUsageDefault.pow5 == false
    && quotientVmMemUsageDefault.x == false
    && quotientVmMemUsageDefault.instanceEval == false

/-- `Ptr.loc` as a boolean, without needing a `BEq Location` the Rust never
    derives for the Lean port: the `Location` in Filters.lean derives nothing,
    and this package does not edit that file. -/
def ptrIsMemory (p : Ptr) : Bool :=
  match ptrLoc p with
  | Location.memory => true
  | Location.calldata => false

/-- The integer arm of a `Value`, likewise compared by matching. -/
def ptrValueIsInt (v : Value) (n : Int) : Bool :=
  match v with
  | Value.integer i => i == n
  | Value.identifier _ _ => false

/-- `Ptr` carries a location and a value and the two constructors must not
    collapse them: `printPtr` ignores the location exactly as the Rust Display
    does (ENC:716-721), so the ONLY thing distinguishing a calldata pointer from
    a memory pointer is this field, and no printer gate can see it. Rules out
    `ptrCalldata` being a copy of `ptrMemory` - a mistake that would survive
    every text comparison in this tree and only surface when Phase 5 asks whether
    a load is `calldataload` or `mload`. -/
def ptr_locations_differ_ok : Bool :=
  ptrIsMemory (ptrMemory (valueFromNat 0x2000))
    && ! ptrIsMemory (ptrCalldata (valueFromNat 0x64))
    && ptrValueIsInt (ptrValue (ptrCalldata (valueFromNat 0x64))) 100
    && printPtr (ptrValue (ptrCalldata (valueFromNat 0x64))) == "0x64"
    && printPtr (ptrValue (ptrMemory (Value.identifier "p" 32))) == "add(p, 0x20)"

/-- THE COEFFICIENT ARRAYS HAVE THE LENGTH THE RUST TYPE GUARANTEES. The Rust
    declares both tables as `[&str; LIN_COEFFS]` (M:521-522, M:692-693), so the
    compiler there enforces six; the Lean port uses `List String`, which
    enforces nothing, and R-40 F3 found that the comment naming this gate was
    citing a declaration that did not exist. It exists now, and it asserts the
    length against `quotientVm.limbCount` - ported independently from LM:355 -
    rather than against the literal 6 alone, so the two sources have to agree.
    Concretely it rules out: a coefficient dropped or duplicated while
    transcribing either table (both reddened: deleting one entry from either list
    fails it); the two tables disagreeing about length; a limb count changing
    without the coefficient tables following; and an entry that is not a hex
    literal at all. What it CANNOT see: the VALUES of the coefficients - they are
    transcribed from vm/mod.rs and no artifact slice in this tree re-derives them
    - and the `limb7YulCoeffs` field of `Halo2Verifier`, which is still a free
    list that nothing here fills from these tables. -/
def limbCoeffArrays_length_ok : Bool :=
  let q := templateConstantsDefault.quotientVm
  limb7YulCoeffsTable.length == q.limbCount - 1
    && wideLimb7YulCoeffsTable.length == q.limbCount - 1
    && limb7YulCoeffsTable.length == 6
    && limb7YulCoeffsTable.Nodup && wideLimb7YulCoeffsTable.Nodup
    && (limb7YulCoeffsTable ++ wideLimb7YulCoeffsTable).all
         (fun c => c.startsWith "0x" && c.length > 3)

end Midfall.Generator.ModelKats

#eval Midfall.Generator.ModelKats.g1Generator_onCurve_ok -- expect true
#eval Midfall.Generator.ModelKats.g1Generator_doubles_ok -- expect true
#eval Midfall.Generator.ModelKats.g1Words_split_ok -- expect true
#eval Midfall.Generator.ModelKats.g1Generator_record_ok -- expect true
#eval Midfall.Generator.ModelKats.templateConstants_widths_ok -- expect true
#eval Midfall.Generator.ModelKats.templateConstants_matchYulExternals_ok -- expect true
#eval Midfall.Generator.ModelKats.templateConstants_gasFormulas_ok -- expect true
#eval Midfall.Generator.ModelKats.templateConstants_modexpGasIsMaxSchedule_ok -- expect true
#eval Midfall.Generator.ModelKats.templateConstants_accumulatorFrame_ok -- expect true
#eval Midfall.Generator.ModelKats.templateConstants_domainTag_isAscii_ok -- expect true
#eval Midfall.Generator.ModelKats.qvmOpcodes_distinct_ok -- expect true
#eval Midfall.Generator.ModelKats.qvmMemTokens_and_tableShapes_ok -- expect true
#eval Midfall.Generator.ModelKats.vkHeaderSlots_derivation_ok -- expect true
#eval Midfall.Generator.ModelKats.vkLen_matchesRustTest_ok -- expect true
#eval Midfall.Generator.ModelKats.vkBytes_order_matchesRustTest_ok -- expect true
#eval Midfall.Generator.ModelKats.vkHeaderSlot_agreesWithConstantTable_ok -- expect true
#eval Midfall.Generator.ModelKats.vkRuntime_prefix_ok -- expect true
#eval Midfall.Generator.ModelKats.vkRuntimeLen_hexRendering_ok -- expect true
#eval Midfall.Generator.ModelKats.wordComment_ok -- expect true
#eval Midfall.Generator.ModelKats.wordHeaders_ok -- expect true
#eval Midfall.Generator.ModelKats.quotientExternal_ranges_ok -- expect true
#eval Midfall.Generator.ModelKats.quotientExternal_noWrap_ok -- expect true
#eval Midfall.Generator.ModelKats.quotientExternal_validateContains_ok -- expect true
#eval Midfall.Generator.ModelKats.usageDefaults_ok -- expect true
#eval Midfall.Generator.ModelKats.ptr_locations_differ_ok -- expect true
#eval Midfall.Generator.ModelKats.limbCoeffArrays_length_ok -- expect true
