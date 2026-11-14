-- |
-- Midfall/Instances/G2Kernel
--
-- P-G2B STEP 3: the two HEAVY kernel computations about the published G2 generator, moved out of
-- Instances/G2Agreement.lean into a file that carries NO '#eval' line, so that 'scripts/kat_gate.py'
-- never re-elaborates them.
--
-- WHY THIS FILE EXISTS, MEASURED. 'kat_gate.py' runs 'lake env lean' on every file that contains an
-- '#eval' line - it has to, because that is the only way to see what the gate prints - and 'lake env
-- lean' re-elaborates the whole file from source: the cached '.olean' of THAT file is not used, only
-- the cached oleans of what it imports. So a 'decide' that 'lake build' runs once and stores costs
-- its full price on EVERY gate pass if it sits in a '#eval'-bearing file. Measured on this tree:
-- 'h2Pair_r_smul_zero' costs 16.2 s of the 20.3 s it takes to re-elaborate G2Agreement.lean (the
-- '#eval' lines themselves cost 0.4 s - the fold is much cheaper interpreted than as a kernel
-- 'decide', which is worth knowing because the obvious guess was the other way round), and
-- 'h2Pair_onCurve' is under 0.5 s. Moving the two 'decide's here takes 'checks.sh' off the 16 s.
--
-- THE RULE THIS FILE ENFORCES: a heavy 'decide' lives in a file with no '#eval' line, and the gate
-- file CITES it. That is the same rule Instances/G2Agreement.lean's header already states for the
-- computation itself ('it is a theorem and appears in no #eval, so no gate pass re-runs it'); what
-- P-G2 had not noticed is that being in the same FILE as an '#eval' breaks it.
--
-- D-P23: the witnesses and falsifications that depend on these two theorems are in
-- Instances/G2Agreement.lean and Instances/G2Codec.lean, as theorems. No gate in the tree deletes a
-- falsification theorem and reddens; that limit is measured, not assumed.

import Midfall.Instances.Fp2

namespace Midfall.Instances
open Midfall Midfall.Yul

/-- x_c0 of EIP-2537's H2, as 'katG2GenWords' renders it (PrecompileSmoke.sol:161-168). -/
def h2x0 : Nat :=
  0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8

/-- x_c1 of H2. -/
def h2x1 : Nat :=
  0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e

/-- y_c0 of H2. -/
def h2y0 : Nat :=
  0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801

/-- y_c1 of H2. -/
def h2y1 : Nat :=
  0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be

/-- The published H2 as a byte point: ((x_c0, x_c1), (y_c0, y_c1)), the order 'g2Of?' decodes. -/
def h2Pair : AffinePt (Nat × Nat) := ((h2x0, h2x1), (h2y0, h2y1))

/-- **H2 IS ON THE CURVE** y^2 = x^3 + 4(u+1) over Fp2, as a kernel theorem: 'affineOnCurve fp2Ops'
    at the real 381-bit modulus, computed by the same integer arithmetic the precompile model uses.
    Independently confirmed in Python bignum arithmetic over Fp[u]/(u^2+1) before this was written. -/
theorem h2Pair_onCurve : affineOnCurve fp2Ops h2Pair = true := by decide

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 100000 in
/-- **THE EXPENSIVE KERNEL COMPUTATION, MEASURED.** 'affineSmul fp2Ops blsR h2Pair = ((0,0),(0,0))':
    the published H2 is killed by the precompile's own 255-step double-and-add. MEASURED HERE:
    8.6 s of kernel reduction, largest single process 4.42 GiB, at maxRecDepth 100000 and
    maxHeartbeats 4e9. THE BRIEF BUDGETED ~4x the G1 fold's 16.6 s and the estimate was WRONG IN
    THE PESSIMISTIC DIRECTION by about 2x: the fold's cost is the 'modPow' inside 'fpInv', and
    'fp2Ops.inv' calls 'fpInv' exactly once per inverse (on the norm, a 381-bit natural), so a G2
    step costs one G1-sized modPow plus cheap pair arithmetic. It is a theorem and appears in no
    '#eval' - and, after P-G2B step 3, in no file that does - so no gate pass re-runs it. MEASURED
    HERE: 16.2 s of the 20.3 s it costs to re-elaborate Instances/G2Agreement.lean, which is the
    whole reason this file exists. -/
theorem h2Pair_r_smul_zero : affineSmul fp2Ops blsR h2Pair = ((0, 0), (0, 0)) := by decide
