-- |
-- Midfall.Assumptions.CurvePairing
--
-- P-HOLDS-FINAL STEP 1: D-P36a INSTALLED. The one named hypothesis that stands between the
-- staged landmark (Instances/HoldsStaging.lean, 'holds_staged') and a real unconditional
-- 'Eip2537.Holds' term.
--
-- WHAT IS ASSUMED, IN FULL AND WITHOUT DRESSING. There is a target group for the two carriers
-- the tree already exhibits - 'G₁z' (Instances/G1Agreement.lean, the r-torsion carrier of the
-- published H1, real curve points) and 'G2fold' (Instances/G2Codec.lean, the exponent-fold
-- carrier) - and an admissible pairing on the triple. That is five constants, listed below,
-- and they are the whole content of this file: 'blsGT' (a carrier), the three instance
-- structures 'AdmissiblePairing' requires of it, and the pairing itself.
--
-- WHAT IS NOT ASSUMED, which is the part a reader needs in order to know what the verification
-- is relative to:
--   * No Fp12, no tower, no ate or Miller loop, no line function. D-P36 rejected construction
--     (option (b)) because building a provably bilinear non-degenerate pairing in Lean is a
--     project larger than this one (docs/design.md D-P36).
--   * Nothing about the PRECOMPILE is assumed. Every one of the six 'Holds' clauses is a
--     theorem of this tree once the pairing exists: 'g1Valid', 'g1Add', 'g1Msm1', 'g1Decodes'
--     from P-G1CODEC and P-POINTCOUNT, 'g2Valid' from P-G2B, and 'pairing2' from
--     'pairingProductOf_pairing2', which agrees with the precompile by DEFINITION of the
--     product (D-P1's design). D-P36's third condition is that the assumption be one line and
--     not a shield for work not done; the work is on the other side of it.
--   * The assumption is NOT 'Holds', and not a restatement of it. Assuming the conclusion would
--     be the defect this project has recorded fourteen times in other forms.
--   * No Surface is claimed to satisfy anything. 'realSurface' installs the EXPONENT codec as
--     its G1 encoder and 'VerifierEnv.g1' is typed over the Surface's own pairing, so
--     'bundle_holds_empty' still refutes the four-way bundle at the fixture. That is a separate
--     fact and it is kept: Instances/ObligationsGates.lean's gap_holds_unexhibited is now closed
--     AS A TERM and still open AT THE FIXTURE.
--
-- WHY THIS FILE IMPORTS Midfall/Instances/, and why that is not the gate being evaded.
-- D-P17's confinement rule (scripts/checks.sh) refuses a file that imports a concrete model
-- AND STATES THEOREMS, because a proof parked next to a KAT would silently acquire a dependence
-- on that model. This file states no theorem and contains no proof: every declaration in it is
-- an axiom or an instance built from one. It has to name 'G₁z' and 'G2fold' because the decision
-- it implements is precisely 'assume the pairing ON THE EXHIBITED GROUPS' (D-P36a) - a generic
-- version over any three groups would not discharge 'holds_staged', whose binder is already
-- pinned to these two carriers. Every proof that USES the assumption lives in
-- Midfall/Instances/HoldsFinal.lean, which is where the confinement rule wants them.
--
-- GATE ENFORCEMENT, so this cannot silently widen. Three layers, none of them prose:
--   1. 'assumption_dP36a' in Instances/ObligationsGates.lean is a registry record naming the
--      five constants and the two carriers; scripts/check_hypothesis_bundles.py requires its
--      tokens and forbids the retired blame - the same mechanism that protects the gap records.
--   2. scripts/check_frozen_axioms.py probes '#print axioms' on 'holds_exhibited' and requires
--      EXACTLY the standard three plus these five, so a sixth axiom, a native_decide, or a
--      'sorry' anywhere in the exhibit's dependency set reddens the gate.
--   3. The exhibit is a term. D-P23's witness half in Instances/HoldsFinal.lean is the positive
--      check that the class being assumed is not an empty one, and its falsification halves are
--      the checks that the exhibit constrains the product it exhibits.
--
-- TRUSTED BASE: docs/PLAN.md section 1 lists this alongside the EIP-2537 semantics, p = r, the
-- pairing-by-type, and the solc compiler hop, so a reader can see exactly what is relative to
-- what.

import Midfall.Instances.G1Agreement
import Midfall.Instances.G2Codec

namespace Midfall.Assumptions
open Midfall Midfall.Yul Midfall.Instances

/-- **D-P36a, CONSTANT 1 OF 5: THE TARGET CARRIER.** The group the pairing lands in. It is a
    bare 'Type' and nothing computes it: what is claimed about it is exactly the four constants
    below and nothing else. 'Gₜ' is an 'outParam' of 'AdmissiblePairing', which is why the
    carrier has to be named rather than inferred. -/
axiom blsGT : Type

/-- **D-P36a, CONSTANT 2 OF 5: 'blsGT' is a group.** Declared as an axiom and re-exported as the
    instance, because 'AdmissiblePairing' takes its three group structures as instance
    parameters. -/
axiom blsGT_group : Group blsGT

noncomputable instance : Group blsGT := blsGT_group

/-- **D-P36a, CONSTANT 3 OF 5: 'blsGT' has prime order 'blsR'.** The same 'blsR' the two exhibited
    carriers have, so the pairing is between groups of one common prime order - which is what
    the 'outParam p' of 'AdmissiblePairing' is pinned to at the use site in 'holds_staged'. -/
axiom blsGT_primeOrder : PrimeOrderWith blsGT blsR

instance : PrimeOrderWith blsGT blsR := blsGT_primeOrder

/-- **D-P36a, CONSTANT 4 OF 5: 'blsGT' is a 'ZMod blsR'-module in additive form.** Bilinearity is
    carried by the TYPE in this project (D-P1: 'e' is a curried 'LinearMap'), so the module
    structure is part of what an admissible pairing needs and not an extra claim. -/
axiom blsGT_module : Module (ZMod blsR) (Additive blsGT)

noncomputable instance : Module (ZMod blsR) (Additive blsGT) := blsGT_module

/-- **D-P36a, CONSTANT 5 OF 5, AND THE WHOLE POINT: AN ADMISSIBLE PAIRING ON THE EXHIBITED
    GROUPS.** Bilinear by type, non-degenerate on the distinguished generators, with decidable
    equality on 'G₁z' and on 'blsGT' ('AdmissiblePairing.decEqG₁' and 'decEqGₜ', which is what
    'pairingProductOf' needs in order to make the precompile oracle computable).

    This is the binder 'holds_staged' was written against, and it is the only thing P-HOLDS-FINAL
    adds. Nothing here says the pairing is the BLS12-381 ate pairing, or that 'blsGT' is the
    r-th roots of unity in Fp12, or that its generators are the published ones: those are claims
    about a CONSTRUCTION, and D-P36 chose not to make them. -/
axiom bls12_381Pairing : AdmissiblePairing G₁z G2fold blsGT

noncomputable instance : AdmissiblePairing G₁z G2fold blsGT := bls12_381Pairing

end Midfall.Assumptions
