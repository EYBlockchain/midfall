-- |
-- Midfall.Instances.ObjectFingerprint
--
-- OBJ.5 (PLAN-V3 V3 row 39). THE FINGERPRINT OF THE OBJECT THE HEADLINE IS ABOUT.
--
-- WHY THIS GATE EXISTS. `Frozen.sha256` hashes three FILES - `LoweringV2/Program.lean`,
-- `LoweringV2/Shared.lean` and `LoweringV2/Statements.lean`. The program the theorem runs is not
-- stored in any of them: it is COMPUTED, by `asmOf poseidonPv poseidonM 0 0`, out of the AST
-- emitters under `Midfall/Lowering/GenAst*.lean` and out of the render model under
-- `Midfall/Generator/`. An edit to any emitter - one literal in one `yblock` - changes what the
-- headline is about and leaves every frozen hash untouched. W15's "frozen means the meaning" has no
-- teeth against that: a file hash pins the text of a program SURFACE, not the program. This file
-- closes the gap by pinning a digest of the thing the statements quantify over.
--
-- WHAT IS PINNED, AND WHY BOTH HALVES.
--
--   * `objectTokens.length = 14109`: the token count of `EVM.print (asmOf poseidonPv poseidonM 0 0)` -
--     the CLOSED (constant-inlined) program at the deployment addresses `vkAddr = qAddr = 0`. This is
--     the POST-M2 number, measured here and not copied: `mainAsmRaw` alone is 74 statements over
--     14,054 tokens (OBJ.2), and the program is 76 statements over 14,109 tokens once the ABI-shape
--     guard and the `vk` wrapper local are spliced in and the contract constants are substituted. The
--     card's guidance is followed - the INLINED program is the object, because the constant table is
--     part of what the theorem runs - and `objectIsTheInlinedProgram_ok` is the gate that says so.
--   * `objectKeccak = 0x3149ae4f...bef176`: `keccak256` of the printed string, i.e. of the exact bytes
--     of the program text - whitespace, indentation and literal spelling included. A token COUNT is
--     blind to a change of a literal's VALUE (`32` and `33` are one token each); the digest is not.
--     `objectFingerprintTeeth_ok` measures that asymmetry in-tree, so the second half is demonstrably
--     load-bearing and not a decoration bolted onto the first.
--
-- WHY `keccak256` IS USABLE UNDER `native_decide`. PLAN-V3 section 4 corrects V2's rule 9: the in-tree
-- `Midfall.keccak256` (`Common/Keccak.lean:15`) is a PURE LEAN definition - `bytesToWordBE
-- (VCVio.Algorithms.Keccak.keccak256 bs)`, VCVio's FFI-free Keccak-f[1600] - and NOT an `@[extern]`
-- binding to a C implementation. So `native_decide` here runs compiled code for the SAME definition
-- the statement names: there is no second implementation for the gate and the theorem to disagree
-- about, which is what makes a digest a pin rather than a promise. There is no FFI keccak in this
-- tree and none is wanted.
--
-- WHY HERE AND NOT IN A FROZEN FILE. D-P17 confines `native_decide` to `Midfall/Instances/`
-- (checks.sh enforces it), and a digest of ONE concrete render is an instance fact about poseidon,
-- not a clause of the theorem. Nothing in the cone of `lowering_equivalence_poseidon` may rest on
-- this declaration. The `#eval` gates above are the same facts as VM booleans, so a regression is
-- reported by `scripts/kat_gate.py` with a line naming the value that moved and not only as a
-- tactic failure.

import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Program
import Midfall.Common.Keccak

set_option autoImplicit false

namespace Midfall.Instances.ObjectFingerprint

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.LoweringV2 Midfall.Lowering YulSemantics YulSemantics.EVM

/-- THE OBJECT. The closed program the V2 headline runs: the ABI-shape guard, the wrapper locals at
    the deployment addresses `0 0`, and the main block - with the render's contract constants
    substituted at their use sites, which is what the Solidity language does with constants. -/
def objectProgram : YulBlock := asmOf poseidonPv poseidonM 0 0

/-- The program as the vendored printer writes it: the exact text whose digest is the pin. -/
def objectPrinted : String := EVM.print objectProgram

/-- That text as a token stream, normalised the way D-P13 normalises it (`yulTokens`: comments and
    whitespace dropped, punctuation padded out). -/
def objectTokens : List String := yulTokens objectPrinted

/-- The digest of the printed text. `asciiBytes` is the byte map the program needs - the printer
    emits ASCII only - so this is the EVM `keccak256` of the program bytes. -/
def objectKeccak : H256 := keccak256 (asciiBytes objectPrinted)

-- Gate 1, the first literal: the token count of the printed program.
#eval objectTokens.length -- expect 14109

-- Gate 2, the second literal: the same digest as a hex string, so a regression prints the value
-- that moved instead of a bare `false`.
#eval objectKeccak.toHex -- expect "3149ae4fa6733f4f6e9df8a68ef58afce365cfa456fe5073225ba44fe3bef176"

/-- Gate 3: the two halves together, as the VM computes them - the same fact as `object_fingerprint`
    below, in the form `scripts/kat_gate.py` can name. -/
def objectFingerprint_ok : Bool :=
  (objectTokens.length, objectKeccak) ==
    (14109, 0x3149ae4fa6733f4f6e9df8a68ef58afce365cfa456fe5073225ba44fe3bef176)
#eval objectFingerprint_ok -- expect true

/-- Gate 4, THE TEETH, IN-TREE. The card's falsifier as a permanent gate rather than a one-off edit:
    the `0x20` word offset of the linearization payload store - `GenAst.emitQuotientLinAt`, whose
    `mstore(add(QUOTIENT_MPTR, 0x20), one_minus_x_n)` the inliner prints as
    `mstore(add(16128, 32), one_minus_x_n)` - changed to `0x21`. The token COUNT does not move; the
    digest does. Without this gate the digest half could be a second copy of the count half and
    nothing would say which of the two has the teeth. -/
def objectFingerprintTeeth_ok : Bool :=
  let mutated := objectPrinted.replace "mstore(add(16128, 32), one_minus_x_n)"
    "mstore(add(16128, 33), one_minus_x_n)"
  mutated != objectPrinted &&
    (yulTokens mutated).length == objectTokens.length &&
      keccak256 (asciiBytes mutated) != objectKeccak
#eval objectFingerprintTeeth_ok -- expect true

/-- Gate 5: THE OBJECT IS THE INLINED PROGRAM, NOT THE RAW BLOCK (the card's guidance).
    `mainAsmRaw` is the same render with the contract constant NAMES still in it - 74 statements,
    14,054 tokens, a different digest. If a later card re-points the fingerprint at the un-inlined
    block, which is NOT what the theorem runs, this reddens. -/
def objectIsTheInlinedProgram_ok : Bool :=
  let raw := EVM.print (mainAsmRaw poseidonPv poseidonM)
  objectKeccak != keccak256 (asciiBytes raw) &&
    objectTokens.length != (yulTokens raw).length
#eval objectIsTheInlinedProgram_ok -- expect true

/-- **THE OBJECT FINGERPRINT.** What the headline's "frozen means the meaning" leans on: the closed
    program `asmOf poseidonPv poseidonM 0 0` prints to exactly 14,109 Yul tokens whose bytes hash to
    exactly this digest. Any edit to any emitter, inliner, model field or plan view that changes that
    program reddens this declaration - and, unlike `Frozen.sha256`, it cannot be satisfied by a
    paraphrase of a file.

    `native_decide` is legitimate here and confined here (D-P17): the decision is a `Bool` over
    `Nat x BitVec 256`, and every function it runs - the emitters, the inliner, the printer, the
    tokeniser and `keccak256` - is a pure Lean definition in this tree, so the compiled code the
    tactic evaluates is the code the statement names. -/
theorem object_fingerprint :
    (objectTokens.length, objectKeccak) =
      (14109, 0x3149ae4fa6733f4f6e9df8a68ef58afce365cfa456fe5073225ba44fe3bef176) := by
  native_decide

#print axioms object_fingerprint

end Midfall.Instances.ObjectFingerprint
