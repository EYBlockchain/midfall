-- |
-- Midfall.Generator.Evm
--
-- The EVM-facing WIRE layer: the verifyProof selector, the ABI encoder that turns
-- a repacked proof plus instance words into calldata, and the one pure byte-level
-- helper the solc-prologue reader is. Ported from
-- proofs/solidity-verifier/src/evm.rs (656 lines at HEAD, cited below as EVM).
-- Work package P-12.
--
-- CITATION NOTATION (docs/plans/README.md standing note 2: every range below was
-- re-derived from `git show HEAD:<path>`, never from wc -l on a dirty checkout).
-- * EVM:  proofs/solidity-verifier/src/evm.rs (656 lines at HEAD) - this file's
--   subject. Working copy and HEAD agree here.
-- * CD:   proofs/solidity-verifier/src/lowering/calldata.rs (160 lines at HEAD) -
--   the producer of the `proof` argument EVM:22 receives; ported in Calldata.lean.
-- * TPLV: proofs/solidity-verifier/templates/contracts/Halo2Verifier.sol (tracked)
--   and the generated dump
--   proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol
--   (tracked) - the CONTRACT side of the same ABI, which the selector and head
--   gates read at #eval time (D-P19).
--
-- WHAT IS AND IS NOT PORTED FROM EVM.RS, AND WHY (plan R1 vs the M3 scope cut).
--
-- EVM:1-39 is the production surface: `FN_SIG_VERIFY_PROOF` (EVM:15) and
-- `encode_calldata` (EVM:22-39). Both are here.
--
-- EVM:41-656 is `#[cfg(feature = "evm")] pub(crate) mod test`: a pinned-solc
-- subprocess wrapper and a revm harness (compile_solidity, Evm, CallOutcome,
-- PrecompileInspector, run_tx and the create/call family). Those are an in-process
-- ETHEREUM NODE plus a COMPILER INVOCATION, not verifier logic: they shell out to
-- solc and drive revm's handler, neither of which has a Lean denotation, and
-- PLAN 14.8's M3 cut does not ask for them. They are NOT ported and no gate
-- pretends otherwise. ONE item in that module is pure byte arithmetic and is
-- therefore portable on its own merits: `runtime_free_memory_pointer_init`
-- (EVM:250-272), which reads the solc prologue out of a runtime bytecode prefix.
-- It is ported below with its EVM cite; the rest of the module stays unported.
--
-- DEVIATIONS AND HAZARD NOTES.
-- * R9 / generic instantiation. EVM:22-26 is `encode_calldata<F> where F:
--   PrimeField, F::Repr: AsRef<[u8]>`. The body only ever applies
--   `fe_to_u256::<F>` (the LE repr as a U256) and then `to_u256_be_bytes`, so the
--   port takes the image of that composition - a `List Word256` - and the repr leg
--   stays where Encoding.lean:1008 already put it (`feToU256`, whose own header
--   records the same decision for the same reason: "the only thing done with the
--   field element is to_repr()"). A caller holding reprs maps them through
--   `feToU256` first; `encodeCalldata_reversesTheRepr_ok` pins that the two-step
--   composition is exactly the reverse of the LE repr, which is what the Rust's
--   `map(fe_to_u256).flat_map(to_u256_be_bytes)` chain computes.
-- * EVM:32 is `offset + 0x20 + proof.len()` in `usize`. R5: no wrapping is
--   emulated, because a proof slice that long cannot exist (2^64 - 0x60 bytes of
--   calldata is not reachable in a Rust `&[u8]`), and `encodeCalldata_headWords_ok`
--   pins the three head words on a fixture whose proof length is the real
--   generated one (0x10e0), where the arithmetic is far from any boundary.
-- * Hazard 4 (the brief) is answered by `fnSig_matchesComputedAbiSelector_ok`: the
--   four bytes of `fnSigVerifyProof` are compared against `abiSelector` of the
--   signature string, i.e. against a COMPUTED keccak, and the signature string is
--   itself tied to the tracked template by `verifyProofSignature_matchesTemplate_ok`.
--   Nothing in this file's gates compares the selector against a pasted literal
--   alone - docs/REVIEW.md R-38 finding 1 is exactly that failure class.
-- * Vec -> List (PLAN R6 as amended by plans/README.md standing note 4).
-- * D-P17: this file imports neither `Generator.Vk` nor `Midfall.Instances/`, so
--   P-SE's stage-2 files can import it.

import Midfall.Common.Bytes
import Midfall.Common.Keccak
import Midfall.Common.Word
import Midfall.Generator.Encoding

namespace Midfall.Generator

/-! ## The verifyProof selector (rust: EVM:14-15) -/

/-- rust: EVM:14-15 (`pub const FN_SIG_VERIFY_PROOF: [u8; 4]`) @formal-baseline.
    "Function signature of `verifyProof(bytes,uint256[])`." The Rust is a
    `[u8; 4]` literal; the port keeps the four BYTES (that is what the reference
    stores and what EVM:30 splices at the front of the calldata) and gates them
    against a computed keccak of the signature string rather than against a
    pasted 32-bit literal - hazard 4. -/
def fnSigVerifyProof : Bytes := bytesFromNats [0x1e, 0x8e, 0x1e, 0x13]

/-- The canonical ABI signature whose first four keccak256 bytes are
    `fnSigVerifyProof`. EVM:14's doc comment names it; the template declares it
    (TPLV:136-139 renders `function verifyProof(bytes calldata proof,
    uint256[] calldata instances)`), and `verifyProofSignature_matchesTemplate_ok`
    reads that declaration from the tracked template at #eval time so this string
    is tied to the contract rather than pasted next to the constant it explains. -/
def verifyProofSignature : String := "verifyProof(bytes,uint256[])"

/-! ## encode_calldata (rust: EVM:17-39) -/

/-- rust: EVM:17-39 (`encode_calldata`) @formal-baseline. "Encode proof into
    calldata to invoke `Halo2Verifier.verifyProof`."

    The seven `chain!` terms (EVM:30-36) appear in the same order, with the proof
    bytes in the middle exactly where the Rust puts them: selector, proof head,
    instances head, proof length, proof, instance count, instances. EVM:36's
    `map(fe_to_u256).flat_map(to_u256_be_bytes)` is the header's R9 note: the
    instances arrive as the words `feToU256` produces, so the leg here is the
    `to_u256_be_bytes` half. -/
def encodeCalldata (proof : Bytes) (instances : List Word256) : Bytes :=
  let offset : Nat := 0x40
  let numInstances : Nat := instances.length
  let head : List Nat :=
    bytesToNats fnSigVerifyProof
      -- EVM:31-32: offset of proof, then offset of instances.
      ++ toU256BeBytes offset
      ++ toU256BeBytes (offset + 0x20 + proof.size)
      -- EVM:33: length of proof.
      ++ toU256BeBytes proof.size
  let tail : List Nat :=
    -- EVM:35: length of instances.
    toU256BeBytes numInstances
      -- EVM:36: the instances themselves, big-endian.
      ++ instances.flatMap fun w => toU256BeBytes w.toNat
  bytesFromNats (head ++ bytesToNats proof ++ tail)

/-! ## runtime_free_memory_pointer_init (rust: EVM:236-272) -/

/-- rust: EVM:236-272 (`runtime_free_memory_pointer_init`) @formal-baseline.
    "Read the free-memory-pointer initializer from a runtime bytecode prefix."
    The only portable item inside `#[cfg(feature = "evm")] mod test` (header):
    pure byte arithmetic over the solc prologue, with no revm or subprocess
    dependency. Recognises `PUSH1 v` / `PUSH2 v_hi v_lo` then an optional `DUP1`
    then `PUSH1 0x40 MSTORE`, and returns `none` when the prefix does not match -
    EVM:247-248 states that `none` must distinguish "no reservation found" from
    "reservation is 0x80", which is why the return is `Option Nat` and not 0.
    R4: every `runtime.get(..)?` in the Rust is a `none` here, not a panic; the
    `*runtime.first()?` at EVM:252 is the same. -/
def runtimeFreeMemoryPointerInit (runtime : Bytes) : Option Nat :=
  let bs := runtime.data.toList
  -- EVM:253, EVM:255, EVM:261, EVM:265-267: a read past the end is `None`.
  let byteAt (n : Nat) : Option Nat := (bs.drop n).head?.map UInt8.toNat
  let head : Option (Nat × Nat) :=
    match bs.head?.map UInt8.toNat with
    | some 0x60 => match byteAt 1 with
      | some v => some (v, 2)
      | none => none
    | some 0x61 => match byteAt 1, byteAt 2 with
      | some hi, some lo => some (hi * 256 + lo, 3)
      | _, _ => none
    | some _ => none
    | none => none
  match head with
  | none => none
  | some (value, i0) =>
    -- EVM:260-263: an optional DUP1 when solc reuses the value.
    let i := if byteAt i0 == some 0x80 then i0 + 1 else i0
    -- EVM:264-271: PUSH1 0x40 MSTORE.
    if byteAt i == some 0x60 && byteAt (i + 1) == some 0x40 && byteAt (i + 2) == some 0x52 then
      some value
    else none

end Midfall.Generator

/-! # Known-answer tests

    Two TRACKED artifact oracles, both read at #eval time (D-P19):

    * the generated contract
      `proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol`,
      whose ABI constants (`PROOF_LEN_CPTR`, `PROOF_CPTR`, `NUM_INSTANCE_CPTR`,
      `INSTANCE_CPTR`, the pinned proof length and instance count) are the Rust
      generator's own output. `encodeCalldata` must reproduce that envelope from
      the proof length alone - a cross-implementation tie, not a self-round-trip.
    * the template `templates/contracts/Halo2Verifier.sol`, which is where the
      signature string the selector hashes comes from.

    A third oracle - the fixture dump's `calldata.bin` - is used by Calldata.lean
    for the byte-exact round trip; see the finding recorded there that it is
    gitignored, unlike these two. -/

namespace Midfall.Generator.EvmKats

/-- A missing artifact is a RED, never a silent true (the VmTypes.lean:1279
    precedent, re-declared here rather than imported: importing the quotient VM
    for a five-line file reader would put QVM vocabulary into the imports of the
    wire layer, which D-P17 argues against for everything downstream). -/
def readFileOrEmpty (path : String) : IO String := do
  try
    IO.FS.readFile path
  catch _e =>
    pure ""

/-- Try each candidate path in order; the first non-empty read wins. Relative
    paths resolve from `formal/` (where checks.sh and lake run) and from the repo
    root, the FoldTypes.lean:798 pattern. -/
def readFirst (candidates : List String) : IO String :=
  candidates.foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got => if got != "" then pure got else readFileOrEmpty path)
    (pure "")

def generatedVerifierCandidates : List String :=
  ["../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol",
   "proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol"]

def templateVerifierCandidates : List String :=
  ["../proofs/solidity-verifier/templates/contracts/Halo2Verifier.sol",
   "proofs/solidity-verifier/templates/contracts/Halo2Verifier.sol"]

def readGeneratedVerifier : IO String := readFirst generatedVerifierCandidates
def readTemplateVerifier : IO String := readFirst templateVerifierCandidates

/-- The generated contract is ~176 KB; anything much smaller is a wrong path and
    must not be allowed to satisfy a needle check by accident. -/
def generatedReadOk (src : String) : Bool := src.length > 100000

/-- The template is ~200 lines of Askama. -/
def templateReadOk (src : String) : Bool := src.length > 4000

/-- A lowercase hex literal as a Nat, so no gate needs a pasted 0x constant that
    the artifact did not supply. -/
def hexNat (digits : List Char) : Nat :=
  digits.foldl (fun (acc : Nat) (c : Char) =>
    match c with
    | '0' => acc * 16 + 0 | '1' => acc * 16 + 1 | '2' => acc * 16 + 2
    | '3' => acc * 16 + 3 | '4' => acc * 16 + 4 | '5' => acc * 16 + 5
    | '6' => acc * 16 + 6 | '7' => acc * 16 + 7 | '8' => acc * 16 + 8
    | '9' => acc * 16 + 9 | 'a' => acc * 16 + 10 | 'b' => acc * 16 + 11
    | 'c' => acc * 16 + 12 | 'd' => acc * 16 + 13 | 'e' => acc * 16 + 14
    | 'f' => acc * 16 + 15 | _ => acc) 0

/-- A hex literal taken from a string: leading spaces dropped, hex digits kept. -/
def hexNatOf (s : String) : Nat :=
  hexNat ((s.toList.dropWhile (fun c => c == ' ')).takeWhile Char.isHexDigit)

/-- The first line containing `needle`. -/
def solLineWith (src : String) (needle : String) : Option String :=
  (src.splitOn "\n").find? (fun l => l.contains needle)

/-- The value of a generated `uint256 internal constant NAME = 0x..;` line, read
    from the contract rather than repeated here. -/
def solConstant (src : String) (name : String) : Option Nat :=
  -- The leading space is load-bearing: "INSTANCE_CPTR" is a substring of
  -- "NUM_INSTANCE_CPTR", so without it the first match is the wrong constant.
  match solLineWith src (" " ++ name ++ " = 0x") with
  | some l => some (hexNatOf ((l.splitOn "= 0x").drop 1 |>.head?.getD ""))
  | none => none

/-- The proof byte length the generated contract pins at
    `eq(0x..., calldataload(PROOF_LEN_CPTR))`. -/
def solPinnedProofLen (src : String) : Option Nat :=
  match solLineWith src "calldataload(PROOF_LEN_CPTR)" with
  | some l => some (hexNatOf ((l.splitOn "eq(0x").drop 1 |>.head?.getD ""))
  | none => none

/-- The instance count the generated contract pins at
    `eq(N, calldataload(NUM_INSTANCE_CPTR))`. -/
def solPinnedNumInstances (src : String) : Option Nat :=
  match solLineWith src "calldataload(NUM_INSTANCE_CPTR)" with
  | some l =>
      match ((l.splitOn "eq(").drop 1 |>.head?.getD "").splitOn "," |>.head? with
      | some n => some (hexNatOf n)
      | none => none
  | none => none

/-- GATE 1 (reachability, FIRST #eval in the section, per the standing D-P19
    note): both artifacts must actually be openable, so a wrong path is a named
    red rather than a vacuous needle match. -/
def evmArtifactsReachable_ok : IO Bool :=
  readGeneratedVerifier >>= fun gen =>
  readTemplateVerifier >>= fun tpl =>
  pure (generatedReadOk gen && templateReadOk tpl)

/-- GATE 2 (HAZARD 4). The selector is gated against a COMPUTED abiSelector of the
    signature string, not against a pasted literal: `abiSelector` runs the same
    Keccak-256 (VCVio's, already tied to the Rust's sha3 by Keccak.lean:47's seven
    error-selector KATs) over the signature and takes the top four bytes. The
    four-byte constant and the 32-bit hash agree only if BOTH are right, and the
    signature string is tied to the contract by the next gate. -/
def fnSig_matchesComputedAbiSelector_ok : Bool :=
  bytesToNatBE fnSigVerifyProof == (abiSelector verifyProofSignature).toNat
    && fnSigVerifyProof.size == 4

/-- GATE 3 (hazard 4, second half). The signature string is not a guess: the
    tracked template declares exactly this function with exactly these two
    parameter types, which is what the canonical ABI signature is built from.
    Read at #eval time. -/
def verifyProofSignature_matchesTemplate_ok : IO Bool :=
  readTemplateVerifier >>= fun src => pure (templateReadOk src
    && src.contains "function verifyProof("
    && src.contains "bytes calldata proof,"
    && src.contains "uint256[] calldata instances")

/-- GATE 4. The generated contract's own ABI head, read from the tracked dump:
    PROOF_LEN_CPTR = 0x44, PROOF_CPTR = 0x64, NUM_INSTANCE_CPTR = INSTANCE_CPTR -
    0x20, and the pinned proof length and instance count. `encodeCalldata` must
    reproduce every one of them from the proof length alone. -/
def encodeCalldata_matchesGeneratedHead_ok : IO Bool :=
  readGeneratedVerifier >>= fun src =>
  pure (match solConstant src "PROOF_LEN_CPTR", solConstant src "PROOF_CPTR",
            solConstant src "NUM_INSTANCE_CPTR", solConstant src "INSTANCE_CPTR",
            solPinnedProofLen src, solPinnedNumInstances src with
    | some proofLenCptr, some proofCptr, some numInstCptr, some instCptr,
      some pinnedLen, some pinnedN =>
        let cd := encodeCalldata (bytesFromNats (List.replicate pinnedLen 0x77))
          (List.replicate pinnedN (1 : Word256))
        proofLenCptr == 0x44 && proofCptr == 0x64
          && numInstCptr == instCptr - 0x20
          && pinnedLen > 0 && pinnedN > 0
          -- EVM:30: the selector is the first four bytes.
          && bytesTake cd 0 4 == some fnSigVerifyProof
          -- EVM:31: the proof head is 0x40.
          && bytesToNatBE (bytesTake cd 0x04 0x20 |>.getD Bytes.empty) == 0x40
          -- EVM:32: the instances head is NUM_INSTANCE_CPTR - 4, the guard at
          -- the contract's own early shape check.
          && bytesToNatBE (bytesTake cd 0x24 0x20 |>.getD Bytes.empty)
               == numInstCptr - 4
          -- EVM:33: the proof length, at the contract's PROOF_LEN_CPTR.
          && bytesToNatBE (bytesTake cd proofLenCptr 0x20 |>.getD Bytes.empty) == pinnedLen
          -- EVM:34: the proof payload itself.
          && bytesTake cd proofCptr pinnedLen
               == some (bytesFromNats (List.replicate pinnedLen 0x77))
          -- EVM:35: the instance count, at NUM_INSTANCE_CPTR.
          && bytesToNatBE (bytesTake cd numInstCptr 0x20 |>.getD Bytes.empty) == pinnedN
          -- and the envelope is exactly the contract's calldatasize pin.
          && cd.size == instCptr + 0x20
    | _, _, _, _, _, _ => false)

/-- GATE 5. Total length is exactly the Rust's chain: 4 + 32 + 32 + 32 + |proof|
    + 32 + 32 * |instances|. Probed at five distinct (proof, instance) shapes so a
    dropped term cannot hide behind another one (R-48). -/
def encodeCalldata_totalLen_ok : Bool :=
  [ (0, 0), (1, 1), (48, 3), (0x10e0, 1), (0x10e0, 53) ].all fun (plen, n) =>
    (encodeCalldata (bytesFromNats (List.replicate plen 0xab))
      (List.replicate n (1 : Word256))).size == 4 + 3 * 32 + plen + 32 + 32 * n

/-- GATE 6. EVM:36's `map(fe_to_u256).flat_map(to_u256_be_bytes)` composition is
    the REVERSE of the 32-byte little-endian repr - the property the poseidon
    fixture shows on real bytes (its `instance.be` is a `to_repr`, i.e. LE, and
    the calldata tail is its reverse). Gated through `feToU256` so the two legs
    cannot drift apart. -/
def encodeCalldata_reversesTheRepr_ok : Bool :=
  let repr : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
  match feToU256 repr with
  | .ok w =>
      let cd := encodeCalldata Bytes.empty [w]
      cd.size == 4 + 4 * 32 + 32
        && (cd.data.toList.drop (cd.size - 32)).reverse.map UInt8.toNat == repr
  | .error _ => false

/-- GATE 7. Round trip through a decoder written here (R-48: own fixture, and the
    inverse reads the offsets out of the envelope rather than assuming them). Two
    distinct proofs and two distinct instance lists, so a constant output cannot
    satisfy it. -/
def encodeCalldata_roundtrip_ok : Bool :=
  let cases : List (Nat × List Word256) :=
    [ (0x10e0, [0xdeadbeef, 0, 7]), (96, [1]) ]
  cases.all fun (plen, inst) =>
    let proof := bytesFromNats ((List.range plen).map fun i => (i % 251) + 1)
    let cd := encodeCalldata proof inst
    match bytesTake cd 4 0x20, bytesTake cd 0x24 0x20, bytesTake cd 0x44 0x20 with
    | some h1, some h2, some h3 =>
        let proofOff := bytesToNatBE h1
        let instOff := bytesToNatBE h2
        let proofLen := bytesToNatBE h3
        -- An ABI offset is relative to the start of the head section, i.e. to
        -- byte 4; the proof payload sits one word after the length word it
        -- points at, and the instance words one word after the count word.
        match bytesTake cd (proofOff + 4 + 0x20) proofLen, bytesTake cd (instOff + 4) 0x20 with
        | some proof', some n =>
            proof' == proof && bytesToNatBE n == inst.length
              && (inst.zipIdx).all fun (w, i) =>
                  bytesToNatBE (bytesTake cd (instOff + 4 + 32 + 32 * i) 32
                    |>.getD Bytes.empty) == w.toNat
        | _, _ => false
    | _, _, _ => false

/-- GATE 8. The two head offsets differ by exactly 0x20 + proof length (EVM:32)
    and the proof payload sits between them: swapping the two heads is the mistake
    this pins, and it is invisible to the total-length gate. -/
def encodeCalldata_headOffsetsDiffer_ok : Bool :=
  let proof := bytesFromNats (List.replicate 300 0x5a)
  let cd := encodeCalldata proof [0xabcd]
  let pOff := bytesToNatBE (bytesTake cd 0x04 0x20 |>.getD Bytes.empty)
  let iOff := bytesToNatBE (bytesTake cd 0x24 0x20 |>.getD Bytes.empty)
  let pLen := bytesToNatBE (bytesTake cd 0x44 0x20 |>.getD Bytes.empty)
  pOff == 0x40 && iOff == pOff + 0x20 + pLen && pLen == 300
    && iOff != pOff && bytesTake cd (pOff + 4 + 0x20) 300 == some proof

/-- GATE 9. `runtime_free_memory_pointer_init`: the two prologue shapes EVM:244-248
    recognises, with and without the DUP1, plus the ways it must return none. The
    accepted cases carry pairwise DISTINCT values so a constant cannot satisfy the
    gate (R-48). -/
def runtimeFreeMemoryPointerInit_prologues_ok : Bool :=
  -- PUSH1 0x80 | PUSH1 0x40 MSTORE
  let a := bytesFromNats [0x60, 0x80, 0x60, 0x40, 0x52]
  -- PUSH1 0x80 | DUP1 | PUSH1 0x40 MSTORE
  let b := bytesFromNats [0x60, 0x80, 0x80, 0x60, 0x40, 0x52]
  -- PUSH2 0x1234 | PUSH1 0x40 MSTORE
  let c := bytesFromNats [0x61, 0x12, 0x34, 0x60, 0x40, 0x52]
  -- PUSH2 0x0a00 | DUP1 | PUSH1 0x40 MSTORE
  let d := bytesFromNats [0x61, 0x0a, 0x00, 0x80, 0x60, 0x40, 0x52]
  runtimeFreeMemoryPointerInit a == some 0x80
    && runtimeFreeMemoryPointerInit b == some 0x80
    && runtimeFreeMemoryPointerInit c == some 0x1234
    && runtimeFreeMemoryPointerInit d == some 0x0a00
    -- the reader distinguishes 0x80 from 0x1234 from 0x0a00, so it is reading
    && runtimeFreeMemoryPointerInit c != runtimeFreeMemoryPointerInit d
    && runtimeFreeMemoryPointerInit c != runtimeFreeMemoryPointerInit a
    -- and the rejections:
    && runtimeFreeMemoryPointerInit Bytes.empty == none
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x60]) == none
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x61, 0x12]) == none
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x62, 0x00, 0x80, 0x60, 0x40, 0x52]) == none
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x60, 0x80, 0x60, 0x40]) == none
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x60, 0x80, 0x60, 0x60, 0x52]) == none

/-- GATE 10. The memoryguard window the prologue reader exists for: the generated
    contract asserts `mload(0x40) <= TRANSCRIPT_MPTR) on entry (EVM:239-242 says
    memoryguard raises the pointer above 0x80), and the reader must report the
    raised value rather than the default. Read from the tracked contract. -/
def runtimeFreeMemoryPointerInit_memoryguardWindow_ok : IO Bool :=
  readGeneratedVerifier >>= fun src => pure (generatedReadOk src
    && src.contains "if gt(mload(0x40), TRANSCRIPT_MPTR)"
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x60, 0x80, 0x60, 0x40, 0x52]) == some 0x80
    && runtimeFreeMemoryPointerInit (bytesFromNats [0x61, 0x01, 0x00, 0x60, 0x40, 0x52]) == some 0x100)

end Midfall.Generator.EvmKats

#eval Midfall.Generator.EvmKats.evmArtifactsReachable_ok -- expect true
#eval Midfall.Generator.EvmKats.fnSig_matchesComputedAbiSelector_ok -- expect true
#eval Midfall.Generator.EvmKats.verifyProofSignature_matchesTemplate_ok -- expect true
#eval Midfall.Generator.EvmKats.encodeCalldata_matchesGeneratedHead_ok -- expect true
#eval Midfall.Generator.EvmKats.encodeCalldata_totalLen_ok -- expect true
#eval Midfall.Generator.EvmKats.encodeCalldata_reversesTheRepr_ok -- expect true
#eval Midfall.Generator.EvmKats.encodeCalldata_roundtrip_ok -- expect true
#eval Midfall.Generator.EvmKats.encodeCalldata_headOffsetsDiffer_ok -- expect true
#eval Midfall.Generator.EvmKats.runtimeFreeMemoryPointerInit_prologues_ok -- expect true
#eval Midfall.Generator.EvmKats.runtimeFreeMemoryPointerInit_memoryguardWindow_ok -- expect true
