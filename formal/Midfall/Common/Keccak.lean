-- |
-- Midfall.Common.Keccak
--
-- Concrete Keccak-256 for the execution layer, taken from VCVio's executable
-- pure-Lean implementation (VCVio/Algorithms/Keccak.lean:127, FFI-free
-- Keccak-f[1600]). The security proofs use the same function as a random
-- oracle (see Security/ROM).

import VCVio.Algorithms.Keccak
import Midfall.Common.Bytes

namespace Midfall

/-- EVM `keccak256`: rate 136, pad 0x01, 32-byte digest. -/
def keccak256 (bs : Bytes) : H256 :=
  bytesToWordBE (VCVio.Algorithms.Keccak.keccak256 bs)

/-- Known-answer vectors, as decidable booleans rather than kernel proofs:
    `decide` on a digest fails with `maximum recursion depth has been reached
    because the kernel cannot reduce Keccak-f[1600] economically. The
    conformance executable evaluates these and fails the build on mismatch. -/
def keccak256_kats : List (Bytes × H256) :=
  [
    (Bytes.empty,
     0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470),
  ]

def keccak256_kats_ok : Bool :=
  keccak256_kats.all (fun (bs, want) => keccak256 bs == want)


/-- Bytes of an ASCII string (the ABI signature inputs are ASCII). -/
def asciiBytes (s : String) : Bytes :=
  s.toList.foldl (fun (acc : Bytes) (c : Char) =>
    ByteArray.push acc (Nat.toUInt8 c.toNat)) Bytes.empty

def abiSelector (s : String) : BitVec 32 :=
  BitVec.ofNat 32 ((keccak256 (asciiBytes s)).toNat / 2 ^ 224)

/-- Cross-implementation known-answer check. The expected selectors are the
    constants pinned in
    proofs/solidity-verifier/templates/partials/verifier/Constants.sol, which
    the Rust generator computes with the sha3 crate and the test
    p4_error_selectors_match_declared_errors re-derives. Agreement ties VCVio's
    Lean Keccak to the Rust Keccak the verifier is built with, on inputs that
    matter to the port. -/
def abiSelectors_ok : Bool :=
  [
    ("BadCalldataShape()", 0x1b99e37c),
    ("VkMismatch()", 0xa447d73e),
    ("NonCanonicalScalar()", 0x77530042),
    ("BadPointEncoding()", 0xf27905ec),
    ("PrecompileFailed()", 0x84e81692),
    ("ProofRejected()", 0xc3b0d8cd),
    ("QuotientProgramInvalid()", 0x3cc81b89),
    ("MemoryLayoutViolated()", 0xc9888d23),
  ].all (fun (sig, sel) => abiSelector sig == sel)

end Midfall
