-- |
-- Midfall.Lowering.Types
--
-- The lowering surface (plan Section 9.5): what a render produces, what has to
-- hold for a render to be provable about, and what a deployment must look like.
-- Placeholders for the Phase 6 port; writing them now is what lets L1-L6 and E1
-- be stated, frozen and hash-checked before the port exists.

import Midfall.Common.Bytes
import Midfall.Common.Curve
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Types
import Midfall.Halo2.Exec.Features
import YulSemantics
import YulSemantics.Dialect.EVM

namespace Midfall.Lowering

open Midfall Midfall.Halo2

/-- The builtin operation type of the EVM dialect we instantiate the semantics at. -/
abbrev Op := YulSemantics.EVM.Op

/-- A Yul statement block in that dialect. -/
abbrev YulBlock := YulSemantics.Block Op

/-- A Yul object (contract), in that dialect. -/
abbrev YulObject := YulSemantics.Object Op

/-- Everything one render produces, before any text is printed: the two Yul
    blocks that make up the entry path, the VK runtime image, and the optional
    standalone quotient evaluator object (plan 9.5 Lowered). The plan's `plan`,
    `shell` and `consts` fields arrive with the Phase 6 port. -/
structure Lowered where
  headGuard : YulBlock
  main : YulBlock
  vkRuntime : Bytes
  evaluator : Option YulObject

/-- Placeholder for the generator error type (rust: api.rs GeneratorError). -/
inductive GeneratorError where
  | planning (stage message : String)
  | render (artifact : String)

/-- The hypotheses the lowering theorems carry: what try_new checks plus what the
    proofs need, and decidable (plan 9.5 Supported). Each field names where it
    comes from; `hLimbs` is design assessment F7 and `qvm` is QVM-01. The plan's
    remaining fields (noRotInst, acc, vkPoints, layout) are stated over ported
    types and arrive with the Phase 6 port; they are NOT dropped, only not yet
    nameable. -/
structure Supported
    (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat)
    (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where
  /-- rust: try_new rejects a circuit with no advice columns. -/
  advice : numAdvice ≠ 0
  /-- rust: exactly two instance columns, one of them committed. -/
  instShape : numInstances = 2
  /-- Multi-phase circuits are out of scope (plan Section 13). -/
  singlePhase : numChallenges = 0
  /-- Assessment F7: the quotient limb count is exactly degree - 1. -/
  hLimbs : numQuotientLimbs = csDegree - 1
  /-- QVM-01: validate_quotient_program_operands accepts the plan. -/
  qvm : qvmValidated
  /-- Production renders only: no trace, no gas checkpoints. -/
  production : trace = false ∧ gasCheckpoints = false

/-- What must hold of the world a verifier is deployed into: the VK and the
    quotient evaluator are present at the pinned addresses with the pinned
    codehashes (plan 9.5 Deployment). The address and world-model parameters
    arrive with Midfall/Yul, so this placeholder carries only the facts. -/
structure Deployment (vkRuntime : Bytes) (evaluator : Option YulObject)
    (vkCodehash quotientCodehash : H256) : Prop where
  vkCode : True
  vkHash : True
  qObj : True
  qHash : True

/-- The reference acceptance predicate the contract is proved against: the
    message-level verifier, plus accumulator batching when the generator was
    configured with an accumulator encoding (plan 9.5 ContractRef). The
    accumulator arm is a placeholder until Exec/Accumulator lands, so this is
    currently the no-accumulator reading of the plan's definition. -/
def ContractRefAccepts {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [AdmissiblePairing G₁ G₂ Gₜ]
    (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool :=
  match prepareMsgs H Features.solidity vk inst ms with
  | .error _ => false
  | .ok d => DualMSM.check d params

end Midfall.Lowering
