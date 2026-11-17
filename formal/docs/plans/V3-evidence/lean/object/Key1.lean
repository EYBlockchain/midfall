import Midfall.Instances.PoseidonValid
set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonFixture
open Midfall.LoweringV2 Midfall.Lowering

def g1WordsBytes (w : G1Words) : Bytes :=
  (wordToBytesBE w.xHi).append ((wordToBytesBE w.xLo).append
    ((wordToBytesBE w.yHi).append (wordToBytesBE w.yLo)))
def pw (i : Nat) : Word256 := (poseidonVkGen.constants.getD i ("", 0)).2

-- 1. the eleven header scalar words of the PAYLOAD against the Lean key (PayloadAgrees, scalar half)
#eval (pw 0 == frWord poseidonVkExec.transcriptRepr,
       (pw 1).toNat == 1, (pw 2).toNat == poseidonVkExec.domain.k,
       pw 3 == frWord (((2 ^ poseidonVkExec.domain.k : ℕ) : Fr Yul.blsR)⁻¹),
       pw 4 == frWord poseidonVkExec.domain.omega,
       pw 5 == frWord poseidonVkExec.domain.omegaInv,
       pw 6 == frWord (poseidonVkExec.domain.omegaInv ^ poseidonPlanV2.meta_.rotationLast.natAbs),
       ((pw 7).toNat, (pw 8).toNat, (pw 9).toNat, (pw 10).toNat) == accWordsOfEncoding none)

-- 2. the 19 + 8 commitment words of the PAYLOAD against vk.json's compressed points, through the
--    tree's own computable decompression and EIP-2537 encoder
def decomp (hs : Array Bytes) : List (Option Bytes) :=
  hs.toList.map fun h => (G1Affine.ofCompressed? h).map G1Affine.toEip
#eval (poseidonVkData.fixedCommitmentHex.size, poseidonVkGen.fixedComms.length)
#eval decomp poseidonVkData.fixedCommitmentHex == poseidonVkGen.fixedComms.map (fun w => some (g1WordsBytes w))
#eval (decomp poseidonVkData.fixedCommitmentHex).filter (·.isNone) |>.length
-- how many of the fixed commitments are the identity (review fact 3a: 8,10,11,12,16)
#eval (poseidonVkGen.fixedComms.zipIdx.filter fun (w, _) => w.xHi == 0 && w.xLo == 0 && w.yHi == 0 && w.yLo == 0).map (·.2)
-- 3. what the Lean-side key carries instead (placeholders)
#eval (poseidonVkExec.fixedCommitments.size, poseidonVkExec.permutation.commitments.size)
-- 4. permutation commitments, same check
#eval decomp poseidonVkData.permutationCommitmentHex == poseidonVkGen.permutationComms.map (fun w => some (g1WordsBytes w))
-- 5. G1 base words (header words 11..14) against params.json g1
#eval ((G1Affine.ofCompressed? poseidonParamsData.g1Hex).map G1Affine.toEip) ==
        some ((wordToBytesBE (pw 11)).append ((wordToBytesBE (pw 12)).append ((wordToBytesBE (pw 13)).append (wordToBytesBE (pw 14)))))
