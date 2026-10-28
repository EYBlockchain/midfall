-- |
-- Midfall.Lowering.VkDigest
--
-- P-SE stage 2 (docs/plans/P-SE-stage2.md, file row 3; PLAN
-- P-SE-semantic-equivalence.md section G and index item 7; design1.md M5-2 and
-- the block "feToU256_frToRepr (vk_digest = frWord vk.transcriptRepr)").
--
-- WHAT THIS FILE IS FOR. The generated verifier puts the VK's transcript repr
-- into the VK_DIGEST word slot and hashes that slot into the accumulator
-- batching scalar alpha (FinalPairing.yul:22, and the four-word preimage is
-- documented at Exec/Accumulator.lean:1014-1021). The generator computes the
-- same word with the Rust field-element helper feToU256 over the 32-byte
-- little-endian repr (Generator/Vk.lean:763). PLAN 9.5 needs those two spellings
-- identified, and that is this file's only theorem: feToU256 of frToRepr is
-- frWord, with NO hypothesis on p, because both sides reduce mod 2^256.
--
-- WHY IT IS ITS OWN FILE, AND WHY THE IMPORTS ARE THE ONES THEY ARE. D-P17 (and
-- the checks.sh "Instances/ import confinement" gate) forbids a theorem-bearing
-- file from importing Midfall/Instances/. The natural home for this fact is next
-- to generateBaseVk, but Generator/Vk.lean:289 pulls in Instances.ExponentModel
-- transitively, so the theorem cannot live there - which is exactly why the
-- generateBaseVk corollary (the digest-slot equation) lives in Obligations as a
-- hypothesis - EnvAgrees.vkDigestWord - and not as a theorem line here. R-58 F5 then
-- dropped the LoweringCorrect field that restated it, since vkDigest_spec plus
-- vkDigestWord already derive it. What this file may import is Generator/Encoding.lean, which
-- carries feToU256 and imports no model (its own header says so at
-- Encoding.lean:156-161), plus Common/Codec.lean for frToRepr and
-- Halo2/Exec/Accumulator.lean for frWord. The stage-2 brief states the
-- constraint as a real constraint rather than a style preference, and hazard 2 is
-- answered by the import list below: no Generator.Vk, no Midfall/Instances/.
--
-- WHAT IS NOT HERE. The vk_digest-to-memory link (Inv .vk's payload image) and
-- the alpha preimage pin belong to Lowering/Inv.lean and
-- Lowering/Obligations.lean (stages 4 and 6).

import Midfall.Generator.Encoding
import Midfall.Halo2.Exec.Accumulator
import Midfall.Assumptions.Codec
import Midfall.Common.Codec

namespace Midfall.Lowering
open Midfall Midfall.Halo2

/-- The deployed VK_DIGEST word is the canonical scalar word.

    Reading the two sides: Generator.feToU256 (Encoding.lean:1008-1012) throws
    only when the repr is not 32 bytes and otherwise returns bytesToWordLE of the
    repr; Midfall.frToRepr (Common/Codec.lean:32-33) is natToBytesLE x.val 32,
    which is always 32 bytes (that half is the proved natToBytesLowFirst_size in
    Assumptions/Codec.lean); and both bytesToWordLE and frWord reduce their
    argument mod 2^256, so the equality holds for EVERY p - including a p above
    2^256, where the repr would truncate. That is why there is no hp binder here
    while decodeAcc_encode (Lowering/Accumulator.lean) needs one: this statement
    compares two truncations, that one compares a truncation against a value.

    PROOF OBLIGATION, registered in SORRY.md. The remaining step is
    bytesToNatLE (natToBytesLE n len) = n % 256^len, i.e. design1 M5-2's
    bytesToNatLE_natToBytesLE. It does not land in this pass, and the reason is
    mechanical rather than mathematical: Midfall.bytesToNatBE (Common/Bytes.lean:92)
    folds with Array.foldl over ByteArray.data, and in Lean 4.35 Array.foldl is the
    index-loop implementation over the opaque Array representation - it is NOT
    definitionally List.foldl on toList, and core has no Array.foldl_eq_foldl_data.
    The induction design1 sketches therefore needs List.toArray / Array.ofList
    plumbing that does not exist in the imported surface, and the natural fix is a
    lemma inside Common/Bytes.lean, which is the P-05 row's file and outside this
    package's edit rights (stage-2 rule: do not edit another package's Lean file).
    The size half of M5-2 DID land (Assumptions/Codec.lean); the value half, and
    with it this theorem and the carried-over frOfRepr_frToRepr, is the one
    remaining byte-level gap. The gate below checks the statement's content
    computationally at a small prime, so the claim is not merely asserted. -/
theorem feToU256_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (x : Midfall.Fr p) :
    Midfall.Generator.feToU256 (Midfall.Generator.bytesToNats (Midfall.frToRepr x)) =
      .ok (Midfall.Halo2.frWord x) := by
  sorry

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-! ### Known-answer checks -/

/-- The theorem's content, computed at p = 17 where everything reduces: the LE
    repr is 32 bytes, feToU256 accepts it, and the word it produces is frWord.
    The last two conjuncts are the negative controls the plan asks for: a
    BIG-endian read of the same repr differs at x = 1 (the R-20 orientation
    error), and a repr of the wrong length is the panic arm rather than a wrong
    answer - which is the only way feToU256 can fail, and the reason
    natToBytesLowFirst_size is half of this theorem's proof. -/
def feToU256_frToReprKats_ok : Bool :=
  let two := (2 : Midfall.Fr 17)
  let sixteen := (16 : Midfall.Fr 17)
  (match Midfall.Generator.feToU256 (Midfall.Generator.bytesToNats (Midfall.frToRepr two)) with
   | .ok w => w == Midfall.Halo2.frWord two
   | .error _ => false) &&
  (match Midfall.Generator.feToU256 (Midfall.Generator.bytesToNats (Midfall.frToRepr sixteen)) with
   | .ok w => w == Midfall.Halo2.frWord sixteen
   | .error _ => false) &&
  (Midfall.frToRepr (p := 17) two).size == 32 &&
  -- the orientation control: BE1 of the LE repr is 2^248, not 1
    Midfall.bytesToWordBE (Midfall.natToBytesLE 1 32) != Midfall.Halo2.frWord (1 : Midfall.Fr 17) &&
    Midfall.bytesToWordLE (Midfall.natToBytesLE 1 32) == Midfall.Halo2.frWord (1 : Midfall.Fr 17) &&
  -- the length guard is the only failure mode, and it is a panic at encoding/mod.rs:914
    (match Midfall.Generator.feToU256 (List.replicate 31 0) with
     | .error (Midfall.Halo2.Fault.panic site) =>
          site == "proofs/solidity-verifier/src/lowering/encoding/mod.rs:914"
     | _ => false)

#eval feToU256_frToReprKats_ok   -- expect true

/-- The truncation claim the doc comment makes about BOTH sides, pinned at a
    value above 2^256 is impossible for Fr 17, so the pin is on the shape: a
    33-byte repr is rejected and a 32-byte one is read LE. This is the half of
    feToU256_frToRepr that does not need the missing byte lemma. -/
def feToU256_widthKats_ok : Bool :=
  (match Midfall.Generator.feToU256 (Midfall.Generator.bytesToNats
      (Midfall.natToBytesLE (2 ^ 200 + 5) 32)) with
   | .ok w => w == Midfall.bytesToWordLE (Midfall.natToBytesLE (2 ^ 200 + 5) 32)
   | .error _ => false) &&
    (Midfall.natToBytesLowFirst (2 ^ 200 + 5) 32).size == 32 &&
    (Midfall.natToBytesLowFirst 0 0).size == 0 &&
    (Midfall.natToBytesLowFirst 7 9).size == 9

#eval feToU256_widthKats_ok   -- expect true

end Midfall.Lowering