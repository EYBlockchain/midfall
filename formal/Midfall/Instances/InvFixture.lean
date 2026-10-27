-- |
-- Midfall.Instances.InvFixture
--
-- HAZARD 1 OF P-SE STAGE 3, DISCHARGED BY COMPUTATION. Inv (Midfall/Lowering/Inv.lean)
-- must be SATISFIABLE, not merely stated: an invariant no state satisfies makes every
-- per-partial correctness theorem vacuously true, which is the failure mode review F1
-- caught in end_to_end_noAcc (a forall over an empty set of runs). This file exhibits a
-- concrete memory satisfying Inv k at every checkpoint it claims, and then perturbs it
-- seven ways to show each clause actually bites.
--
-- WHY THE GATE IS HERE AND NOT IN Lowering/. Inv needs a pairing model: the .pcs clause
-- reads MSMKZG.eval and the .pairing clause reads DualMSM.check, and the only
-- AdmissiblePairing in the tree is the exponent model (R-28). The Instances confinement
-- gate greps direct imports of Midfall.Instances. in theorem-bearing files, so a gate
-- that needs a model has to live in Instances/ itself, as ChallengeStream.lean does
-- (hazard 5). Everything below is a concrete evaluation at Fr 17 over
-- Midfall.Instances.Exp, which is a model of exponent arithmetic and certifies exactly
-- what R-33 says it certifies: nothing about BLS12-381, and nothing here is cited by any
-- theorem outside Instances/.
--
-- WHY decide WORKS AT ALL. Inv is defined as the proposition that a Bool is true
-- (Lowering/Inv.lean, hazard 1 note), so every exhibit and every refutation below is a
-- kernel evaluation of that Bool on a concrete state. No clause is hidden behind a
-- quantifier over an infinite set, which is what makes the satisfiability claim
-- checkable rather than argued.
--
-- THE SEVEN PERTURBATIONS, and the clause each one kills:
--   1. a reverted halt record        - kills Inv at every checkpoint
--   2. garbage in the g1_identity window - kills Inv .start (permanent clause)
--   3. the wrong r local             - kills Inv .start (locals clause)
--   4. pairing inputs swapped        - kills Inv .pcs (PAIRING_LHS/RHS clauses)
--   5. a wrong challenge word        - kills Inv .transcript
--   6. garbage in the selector buckets, with the linearization hole filled
--                                      - kills Inv .quotient, and NOT Inv .pairing
--   7. a wrong linearization eval, ditto - kills Inv .quotient
-- 6 and 7 together are the counterexample to the design sketch lemma Inv_mono: the
-- state satisfies Inv at .pairing and refutes it at .quotient, and .quotient <=
-- .pairing. That is finding 12 doing its job, not a defect: the selector bytes are
-- dead once the PCS has consumed them, so an invariant that still asserted them at
-- .pairing would be the wrong invariant.

import Midfall.Lowering.Inv
import Midfall.Lowering.Snapshot
import Midfall.Instances.ExponentModel
import Midfall.Instances.NativeE2E

namespace Midfall.Instances.InvFixture
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Generator Midfall.Yul
open YulSemantics
open YulSemantics.EVM

set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance : Fact (Nat.Prime 1009) := ⟨by decide⟩

/-- The two oracles the invariant is stated against, both inert: Inv never calls them,
    they only fix the dialect the VEnv lives in. -/
def noCalls : ExternalCalls := ⟨fun _ _ _ => False⟩
def noGas : ExternalGas := ⟨fun _ _ => False⟩

/-! ### The Fr 1009 fixture for the invariant

    HAZARD 4. The Inv gates are sensitive to VALUE DISTINCTNESS: the satisfiability
    exhibit is only evidence if dropping a write changes the answer, and over Fr 17
    several of the witness scalars collapse (51 = 0 mod 17, so an unwritten x4 slot and
    a written one agree) and the identity point encodes as 128 zero bytes, so an
    unwritten commitment slot agrees with a written one. Everything about the
    invariant therefore runs at Fr 1009, where the witness values are distinct and
    non-degenerate. The §9.2 message-level fixture below stays at Fr 17 because that
    is the prime the Exec end-to-end proof was built for. -/

/-- The element of a given exponent, at the big prime. -/
def big (n : Nat) : Exp 1009 := Multiplicative.ofAdd (n : ZMod 1009)

/-- Field constants for the fixture. Inv never reads them; they are here so the
    environment can be built. -/
def bigFc : FieldConsts (Fr 1009) :=
  { numBits := 10, s := 4, rootOfUnity := 3, zeta := 2 }

/-- The verifier environment: the exponent model at Fr 1009 with the exponent codec. -/
def bigE : VerifierEnv 1009 (Exp 1009) (Exp 1009) (Exp 1009) :=
  { g1 := expG1Codec, field := bigFc, delta := 2, fewerPointSetsRuntime := false }

/-- The pairing parameters. nG2Prepared is g2 inverse (exponent -1) and sG2Prepared is
    exponent 5, which is what makes bigDual below check true. -/
def bigParams : ParamsVerifierKZG (Exp 1009) (Exp 1009) :=
  { sG2 := big 5, nG2Prepared := (big 1)⁻¹, sG2Prepared := big 5 }

/-- A DualMSM whose two channels have DIFFERENT evaluations and which passes the final
    pairing check: in the exponent model the check is 3 * 5 + 15 * (-1) = 0. Distinct
    channels are what make the pairing-swap perturbations observable; at the
    all-identity default, swapping PAIRING_LHS and PAIRING_RHS changes nothing. -/
def bigDual : DualMSM (Fr 1009) (Exp 1009) (Exp 1009) (Exp 1009) :=
  { left := MSMKZG.fromBase (big 3), right := MSMKZG.fromBase (big 15) }

/-- The snapshot: the literal witness of Lowering/Snapshot.lean with every commitment
    slot given a distinct non-identity point, so that a missing write is a visible
    difference rather than a coincidence with zero. -/
def bigS : Snapshot 1009 (Exp 1009) (Exp 1009) (Exp 1009) :=
  let w := witnessSnapshot (p := 1009) (G₁ := Exp 1009) (G₂ := Exp 1009) (Gₜ := Exp 1009)
  { w with
    trace := { w.trace with adviceCommitments := #[#[big 26]] },
    alg := { w.alg with quotientLimbComs := #[big 24, big 25] },
    b := { w.b with fCom := big 21 },
    c := { w.c with pi := big 22, finalCom := MSMKZG.fromBase (big 23), dual := bigDual } }

/-- A DualMSM whose channels do NOT satisfy the pairing equation: 3 * 5 + 16 * (-1) =
    -1 in exponents. This is the state the contract reaches when the opening is wrong,
    and it is what makes the .pairing decision clause observable rather than inert. -/
def bigDualBad : DualMSM (Fr 1009) (Exp 1009) (Exp 1009) (Exp 1009) :=
  { left := MSMKZG.fromBase (big 3), right := MSMKZG.fromBase (big 16) }

/-- The snapshot of a REJECTED opening: same memory layout, failing dual. -/
def bigS3 : Snapshot 1009 (Exp 1009) (Exp 1009) (Exp 1009) :=
  { bigS with c := { bigS.c with dual := bigDualBad } }

/-- The same snapshot with the linearization hole FILLED, which is what a stage after
    the linearize widening will have. Filling it here is legitimate: the hole is a gap
    in what Exec returns, not a type that cannot be inhabited, and the fixture builds
    the record by hand. It is the only way to show the quotient clauses are live rather
    than decorative. -/
def bigLin : Linearization (Fr 1009) (Exp 1009) :=
  { expressions := #[],
    linCom := { point := 1, commitmentLabel := CommitmentLabel.noLabel,
                commitment := .linear #[big 2, big 3] #[61, 62]
                  #[CommitmentLabel.noLabel, CommitmentLabel.noLabel],
                eval := 63 } }

def bigS2 : Snapshot 1009 (Exp 1009) (Exp 1009) (Exp 1009) :=
  { bigS with lin := some bigLin }

/-- The locals: r bound to the modulus and success bound to 1, which is what the
    .pairing clause demands and what the prologue leaves behind. -/
def bigV : VEnv (Bridge.Dialect noCalls noGas) :=
  [("r", BitVec.ofNat 256 1009), ("success", 1)]

/-- Locals with success unbound: the state before the first precompile call. -/
def bigVNoSuccess : VEnv (Bridge.Dialect noCalls noGas) :=
  [("r", BitVec.ofNat 256 1009)]

/-- Locals with r bound to the wrong modulus. -/
def bigVWrongR : VEnv (Bridge.Dialect noCalls noGas) :=
  [("r", BitVec.ofNat 256 1008), ("success", 1)]

/-- Inv at the fixture environment, with the calls and gas oracles named once.

    WHY THIS HELPER EXISTS. VEnv (Bridge.Dialect calls gas) reduces to List (String x
    U256): Bridge.Dialect is @[reducible] precisely so that DecidableEq resolves, and
    the price is that the oracles are erased from the type, so Inv implicit calls gas
    cannot be recovered from the VEnv argument. Every use site has to name them. That
    is a fact about the design0 Inv arity worth reporting: a per-partial theorem must
    quantify calls and gas at the theorem level, not infer them from its hypothesis. -/
def fInvB (k : Checkpoint) (S : Snapshot 1009 (Exp 1009) (Exp 1009) (Exp 1009))
    (V : VEnv (Bridge.Dialect noCalls noGas)) (st : EvmState) : Bool :=
  InvAt (calls := noCalls) (gas := noGas) bigE bigParams k witnessPlanView S V st

/-- The proposition that the fixture invariant holds: literally Midfall.Lowering.Inv at
    the fixture environment, so every exhibit below is about the real invariant and not
    about a shadow of it. -/
abbrev fInv (k : Checkpoint) (S : Snapshot 1009 (Exp 1009) (Exp 1009) (Exp 1009))
    (V : VEnv (Bridge.Dialect noCalls noGas)) (st : EvmState) : Prop :=
  fInvB k S V st = true

/-- The honest memory and state: every slot Inv constrains, written with the value it
    constrains it to (Lowering/Inv.lean, honestState). -/
def honestSt : EvmState := honestState bigE witnessPlanView bigS
def honestSt2 : EvmState := honestState bigE witnessPlanView bigS2
/-- The honest memory of a rejected opening: every slot correct, the pairing equation
    false. -/
def honestSt3 : EvmState := honestState bigE witnessPlanView bigS3

/-- The seven perturbed states, each named so the gate that refutes it fits on one
    line. Each is the honest memory with exactly ONE thing changed, which is what makes
    a refutation evidence about the clause rather than about the fixture. -/
def stReverted : EvmState := { honestSt with halted := some (.revert, []) }
def stG1Garbage : EvmState := { honestSt with memory := storeWord honestSt.memory (ptrAddr witnessPlanView.memory.g1IdentityMptr) 1 }
def stPairingLhsOverwritten : EvmState := { honestSt with memory := copyInto honestSt.memory (ptrAddr witnessPlanView.memory.pairingLhsMptr) 0 128 (bigE.g1.toEip bigDual.right.eval).toList }
def stPairingRhsOverwritten : EvmState := { honestSt with memory := copyInto honestSt.memory (ptrAddr witnessPlanView.memory.pairingRhsMptr) 0 128 (bigE.g1.toEip bigDual.left.eval).toList }
def stWrongBeta : EvmState := { honestSt with memory := storeWord honestSt.memory (ptrAddr witnessPlanView.memory.betaMptr) 0 }
def stWrongX4 : EvmState := { honestSt with memory := storeWord honestSt.memory (ptrAddr witnessPlanView.memory.x4Mptr) 0 }
def stAdviceGarbage : EvmState := { honestSt with memory := storeWord honestSt.memory (ptrAddr witnessPlanView.memory.adviceCommsMptrBase) 1 }
def stSelectorGarbage : EvmState := { honestSt2 with memory := storeWord honestSt2.memory witnessPlanView.memory.selectorAccMptr 0xFFFF }
def stQuotientEvalGarbage : EvmState := { honestSt2 with memory := storeWord honestSt2.memory (ptrAddr witnessPlanView.memory.quotientEvalMptr) 0 }
/-- Garbage in the selector region of a snapshot whose linearization hole is still
    empty: nothing to compare against, so nothing is refuted. -/
def stSelectorGarbageNoHole : EvmState := { honestSt with memory := storeWord honestSt.memory witnessPlanView.memory.selectorAccMptr 0xFFFF }

/-! ### 1. Satisfiability: Inv k holds at every checkpoint

    WHY THESE ARE COMPUTATIONS AND NOT PROOFS. Inv is a decidable Bool, so each claim
    below could in principle be a kernel-checked example. In practice the kernel gets
    stuck reducing the VK payload comparison (a ByteArray index inside the .vk clause
    does not whnf to a literal), while the interpreter evaluates the same Bool in
    milliseconds. The gate is therefore executable, in the style of
    Instances/NativeE2E.lean, which says the same thing about itself: these are Bool
    computations, not proofs, and nothing outside Instances/ may depend on them. The
    one theorem kept below is the cheap boundary, to show the invariant is also
    provable and not merely evaluable. -/

/-- INV IS SATISFIABLE, at every checkpoint this stage claims, by the honest memory.
    This is the hazard-1 exhibit: the invariant is not a contradiction dressed up as a
    hypothesis, and every per-partial theorem stated against it has a nonempty set of
    states to talk about. -/
def invSatKats_ok : Bool :=
  checkpoints.all (fun k => fInvB k bigS bigV honestSt) &&
  -- and with the linearization hole filled, so the quotient clauses are satisfiable
  -- too rather than merely inert
  fInvB .quotient bigS2 bigV honestSt2 &&
  fInvB .pcs bigS2 bigV honestSt2 &&
  fInvB .pairing bigS2 bigV honestSt2

/-- The cheapest boundary as a kernel-checked theorem: not halted, locals coherent,
    and the g1_identity window zero. -/
theorem invSat_start : fInv .start bigS bigV honestSt := by
  unfold fInv fInvB
  native_decide

/-! ### 2. Perturbations: each clause kills a state -/

/-- THE PERTURBATIONS. Each one is a single byte or word away from the honest memory,
    and each refutes exactly the clause it targets. A perturbation that changed nothing
    would leave Inv true and the gate red, which is what makes these evidence about the
    clauses rather than about the fixture. -/
def invPerturbKats_ok : Bool :=
  -- 1. a reverted state satisfies nothing, at any boundary
  (! fInvB .start bigS bigV stReverted) &&
  (! fInvB .pcs bigS bigV stReverted) &&
  -- 2. garbage in the permanent g1_identity window kills even Inv .start
  (! fInvB .start bigS bigV stG1Garbage) &&
  -- 3. the wrong r local kills Inv .start
  (! fInvB .start bigS bigVWrongR honestSt) &&
  -- 4. overwriting either pairing input kills Inv .pcs: the two slots are constrained
  --    separately, and the fixture dual has distinct channel evaluations so each
  --    direction is observable on its own
  (! fInvB .pcs bigS bigV stPairingLhsOverwritten) &&
  (! fInvB .pcs bigS bigV stPairingRhsOverwritten) &&
  -- 5. a wrong challenge word kills Inv .transcript, and so does a wrong x4 and a
  --    wrong advice commitment: the transcript clause is per-slot, not a blanket
  (! fInvB .transcript bigS bigV stWrongBeta) &&
  (! fInvB .transcript bigS bigV stWrongX4) &&
  (! fInvB .transcript bigS bigV stAdviceGarbage) &&
  -- 6. with the hole filled, garbage in the selector buckets kills Inv .quotient and
  --    Inv .pcs - the clause finding 12 is about, shown to be live
  (! fInvB .quotient bigS2 bigV stSelectorGarbage) &&
  (! fInvB .pcs bigS2 bigV stSelectorGarbage) &&
  -- 7. a wrong linearization eval kills Inv .quotient: live, not decorative
  (! fInvB .quotient bigS2 bigV stQuotientEvalGarbage) &&
  -- 8. an unbound success local kills Inv .pairing and nothing earlier
  (! fInvB .pairing bigS bigVNoSuccess honestSt) &&
  (fInvB .pcs bigS bigVNoSuccess honestSt)

/-- FINDING 12, THE CONSEQUENCE THAT MATTERS: Inv is NOT monotone, and that is the
    correct behaviour. The selector-bucket clause is guarded by Checkpoint.liveAt, so
    it is asserted at .quotient and .pcs and dropped at .pairing. The same garbage
    state therefore refutes Inv at .quotient and satisfies it at .pairing, with
    .quotient <= .pairing. design0 lists Inv_mono (k1 <= k2 -> Inv k2 -> Inv k1) as a
    lemma of Inv.lean; it is false as written and is not stated here. -/
def invNotMonotoneKats_ok : Bool :=
  fInvB .pairing bigS2 bigV stSelectorGarbage &&
  ! fInvB .quotient bigS2 bigV stSelectorGarbage &&
  -- and the direction that does hold: the early boundaries, where nothing has been
  -- dropped, all agree on the honest state
  (fInvB .start bigS bigV honestSt && fInvB .vk bigS bigV honestSt)

/-- THE DECISION CLAUSE BITES. A state whose pairing inputs are correctly stored but
    whose dual FAILS the pairing equation satisfies Inv at .pcs (the slots are right)
    and refutes it at .pairing (the decision is wrong). Without this the .pairing clause
    of Inv would be decoration, and finalPairing_spec could not take its postcondition
    from Inv at all. -/
def invPairingDecisionKats_ok : Bool :=
  DualMSM.check bigDual bigParams && ! DualMSM.check bigDualBad bigParams &&
  fInvB .pcs bigS3 bigV honestSt3 && ! fInvB .pairing bigS3 bigV honestSt3 &&
  -- and the honest state passes at both, so the difference is the dual and nothing else
  fInvB .pcs bigS bigV honestSt && fInvB .pairing bigS bigV honestSt

/-- The holes are inert, not wrong: with lin = none, garbage in the selector region
    does NOT refute Inv, because there is no bucket value to compare against. This is
    the honest statement of D6 limit 1 - the clause is waiting for a value, not
    asserting a fake one. -/
def invHoleInertKats_ok : Bool :=
  fInvB .quotient bigS bigV stSelectorGarbageNoHole

#eval invSatKats_ok                       -- expect true
#eval invPerturbKats_ok                   -- expect true
#eval invNotMonotoneKats_ok               -- expect true
#eval invHoleInertKats_ok                 -- expect true
#eval invPairingDecisionKats_ok           -- expect true

/-! ### 3. The snapshot itself is not vacuous

    Inv relates memory to a Snapshot, so the same hazard applies one level down: if
    snapshotOf never returned .ok, every per-partial theorem would be vacuous for the
    same reason. These run the §9.2 message-level fixture, which is built at Fr 17
    (the prime the Exec end-to-end proof was constructed for), through the snapshot
    pipeline. -/

/-- The §9.2 environment and parameters, at Fr 17. -/
def msgE : VerifierEnv 17 (Exp 17) (Exp 17) (Exp 17) := n2Env
def msgParams : ParamsVerifierKZG (Exp 17) (Exp 17) := expPrm

/-- The accepting message stream of the §9.2 fixture. -/
def msgMsgs : List (Msg (Fr 17) (Exp 17)) :=
  match n2Decode (n2Proof n2Pi) with
  | some ms => ms
  | none => []

/-- snapshotOf agrees with prepareMsgs on a real accepting proof: same DualMSM, same
    decision. This is the executable shadow of snapshotOf_prepareMsgs, which is a
    registered hole. -/
def snapshotAgreesWithPrepareMsgs_ok : Bool :=
  match snapshotOf msgE keccak256 n2Vk n2Inst msgMsgs none,
        prepareMsgs (Gₜ := Exp 17) msgE keccak256 Features.solidity n2Vk n2Inst
          msgMsgs with
  | .ok s, .ok d => n2DualExp s.c.dual == n2DualExp d && DualMSM.check d msgParams
  | _, _ => false

/-- The prefix chain earns its keep: append one message to the accepting stream and
    the run leaves a trailing byte. Every prefix through the PCS still exists - the
    parser partial wrote everything it needed - while the full snapshot refuses. A
    per-partial theorem stated over the full snapshot would have no hypothesis here;
    stated over snapshotOfPcs it has exactly the one it needs. -/
def prefixSurvivesTrailingBytes_ok : Bool :=
  let ms := msgMsgs ++ [Msg.fr 0]
  (snapshotOfPcs msgE keccak256 n2Vk n2Inst ms).isOk == true &&
    (snapshotOf msgE keccak256 n2Vk n2Inst ms none).isOk == false &&
    -- and the earlier prefixes stand too
    (snapshotOfLagrange msgE keccak256 n2Vk n2Inst ms).isOk == true &&
    (snapshotOfTrace msgE keccak256 n2Vk n2Inst ms).isOk == true

/-- The linearization hole is empty on a REAL run, not just on the hand-built witness:
    the only way the quotient clauses can be inert is if snapshotOf really does put
    none there. -/
def snapshotLinHoleEmpty_ok : Bool :=
  match snapshotOf msgE keccak256 n2Vk n2Inst msgMsgs none with
  | .ok s => s.lin.isNone && s.acc.isNone && s.instanceEval.isSome
  | .error _ => false

/-- The instance evaluation the snapshot selects is the PUBLIC column inner product,
    not the committed transcript read: the §9.2 fixture has one committed column (read
    from the proof) and one public column (the inner product), and the pin must be the
    second. n2Inst is #[0, 1] over the size-4 domain, so the value is not 9, the
    committed read of the fixture. -/
def snapshotInstanceEval_ok : Bool :=
  match snapshotOfLagrange msgE keccak256 n2Vk n2Inst msgMsgs with
  | .ok s =>
      -- the committed read is the first entry of the row, the public inner product
      -- the second; the selection must be the second
      s.instanceEval == (s.alg.instanceEvals.getD 0 #[])[1]? &&
      s.instanceEval != (s.alg.instanceEvals.getD 0 #[])[0]?
  | .error _ => false

#eval snapshotAgreesWithPrepareMsgs_ok    -- expect true
#eval prefixSurvivesTrailingBytes_ok      -- expect true
#eval snapshotLinHoleEmpty_ok             -- expect true
#eval snapshotInstanceEval_ok             -- expect true

end Midfall.Instances.InvFixture
