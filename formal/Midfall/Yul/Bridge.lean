-- |
-- Midfall.Yul.Bridge
--
-- P-SE stage 1 (docs/plans/P-SE-stage1.md, file row 1; PLAN
-- P-SE-semantic-equivalence.md section B and index item 2; docs/plans/
-- P-BR-bridge-run.md, which planned this same object and located the gap it
-- closes; design2.md 'Bridge core' and 'Externals fold').
--
-- WHAT THIS FILE IS FOR: it resolves finding Y-3. The vendored big-step
-- semantics is fully dialect-parameterised (YulSemantics.Run, BigStep.lean:366),
-- but the COMMITTED-run layer is not: YulSemantics.RunCommitted (Observation.lean:39)
-- is hard-wired to the closed EVM.evm dialect and to VEnv EVM.evm, and in that
-- dialect stepOp returns none for gas/call/callcode/delegatecall/staticcall/
-- create/create2 (EVMExec.lean:883-921 route those through the external
-- relations instead). So every precompile call the generated verifier makes is
-- STUCK there, and any soundness statement of the form 'for all observations,
-- RunCommitted ... implies ...' over the verifier is vacuously true. PLAN 9.5
-- RunVerifier / RunContractIR need a committed run over
-- evmWithExternal calls ExternalCreates.none gas with a configurable keccak
-- oracle. That is what Bridge.Run / Bridge.RunCommitted are. D-P10 chose to
-- define our own rather than wait upstream; nothing here invents a second
-- semantics - every definition is a name over the vendored one.
--
-- DETERMINISM IS NOT ASSUMED, IT IS HYPOTHESISED (D-P10, P-BR item 3). A generic
-- external-call relation is NOT deterministic: ExternalCalls.Call is a ternary
-- relation and the EVM step existentially picks a response (externalCall,
-- EVMExec.lean:852-862), as does the gas oracle for gas() (:926-928). So the
-- layer carries two named conditions - ExternalCalls.Functional and
-- ExternalGas.Functional - and dialect_deterministic proves per-op determinism
-- from them, whence Run.det and RunCommitted.det follow. twoResponses_nondet is
-- the counterexample that keeps the hypothesis load-bearing rather than
-- decorative (the dualMsm_scale_check hc pattern in Spec/Lemmas.lean).
--
-- WORLD-LOCAL CALL RELATIONS (attack.md line 36 FIX, BINDING). ir_refines
-- compares the via-ir runtime against the shell model, whose memory and
-- activeWords differ. ExternalCalls.Call receives the whole pre-call EvmState
-- (EVMExec.lean:472-474, and externalCall passes st at :852-862), so a relation
-- that reads st.memory 0x40 - the free-memory pointer the IR prologue writes -
-- makes the two sides answer differently and refutes the equivalence for reasons
-- that have nothing to do with the optimisation. The fix is built in from the
-- start: ExternalCalls.WorldLocal says the response set depends on the caller
-- only through CallWorld.ofState, and honestCalls and permissive are proved
-- world-local here, with the gas oracle pinned to ExternalGas.ofFun (fun _ => g0)
-- wherever a run is compared across two frames. Retrofitting this is what the FIX
-- line exists to prevent.
--
-- THE KECCAK HOOK (finding Y-2). The hash is a STATE field, ExecEnv.keccakOf :
-- List UInt8 -> U256 (EVMExec.lean:160), not a dialect parameter. So
-- hash-agnosticism is achieved by installing H into the frame (withKeccak) and
-- the honest statement about it is keccakOf_invariant: no Step of the open
-- dialect changes it. PLAN 10.3 all-lowering-proofs-are-hash-agnostic is true at
-- this layer only in that sense: DeploymentW.vkHash (stage 2) still pins H at the
-- two runtime byte strings the contract compares extcodehash against.
--
-- WHAT THIS FILE MUST NOT IMPORT (design2 hazard list, honoured): no
-- Midfall.Halo2.Exec (the Yul layer must not depend on L0, so Hash is written out
-- as its type rather than borrowed from Native.lean:50), no Midfall/Instances/
-- (D-P17), and Midfall.Generator is NOT opened because Midfall.Yul.modexpFrameBytes
-- and Midfall.Generator.modexpFrameBytes collide. The forall-runs contract layer
-- lives in Midfall/Yul/Contracts.lean, not here: attack.md line 171 FIX says one
-- copy, the generic one.

import YulSemantics
import YulSemantics.Dialect.EVM
import YulSemantics.Contract
import YulSemantics.Observation
import YulSemantics.Object
import YulSemantics.ObjectRun
import Midfall.Common.Bytes
import Midfall.Common.Keccak
import Midfall.Yul.Externals
import Midfall.Yul.Contracts

namespace YulSemantics.EVM

/-- D-P10 determinism condition on the call relation: at most one response per
    request AND pre-state. Declared in YulSemantics.EVM (attack.md line 92 FIX,
    binding) so that dot notation resolves on a client value c : ExternalCalls -
    a def inside Midfall.Yul.Bridge would have created a name no projection finds.
    Note the condition is on the TRIPLE: the same request answered differently in
    two states is exactly what a world-local relation must not do either, but
    functionality is the weaker condition determinism needs and WorldLocal below is
    the stronger one equivalence needs. -/
def ExternalCalls.Functional (c : ExternalCalls) : Prop :=
  ∀ req st r₁ r₂, c.Call req st r₁ → c.Call req st r₂ → r₁ = r₂

/-- The matching condition on the gas oracle: at most one remaining-gas word per
    state. ExternalGas.ofFun f satisfies it by construction; ExternalGas.any does
    not, and with .any the gas() op has no Deterministic proof (ecosystem Y-5),
    which is why the layer takes the oracle as a parameter rather than hard-coding
    the open one. -/
def ExternalGas.Functional (g : ExternalGas) : Prop :=
  ∀ st g₁ g₂, g.Gas st g₁ → g.Gas st g₂ → g₁ = g₂

/-- WORLD-LOCALITY (attack.md line 36 FIX, binding): the set of permitted
    responses depends on the caller frame only through its world projection
    CallWorld.ofState, never through memory, activeWords, returndata or halted.
    This is the hypothesis that lets ir_refines compare an IR whose memory layout
    differs from the shell model: without it a relation reading st.memory 0x40
    separates the two sides for a reason that is not the optimisation. -/
def ExternalCalls.WorldLocal (c : ExternalCalls) : Prop :=
  ∀ req st st' r, CallWorld.ofState st = CallWorld.ofState st' → (c.Call req st r ↔ c.Call req st' r)

end YulSemantics.EVM

namespace Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

/-! ### The open-dialect run layer -/

/-- The open EVM dialect the generated verifier runs in: external calls answered
    by calls, no contract creation (PLAN noCreates), gas() answered by gas.
    Nothing is added over the vendored evmWithExternal (EVMExec.lean:953-961);
    this is a name, not a second semantics. @[reducible] so that Value := U256 is
    transparent to DecidableEq search, which every Step lemma needs. -/
@[reducible] def Dialect (calls : ExternalCalls) (gas : ExternalGas) : YulSemantics.Dialect :=
  evmWithExternal calls ExternalCreates.none gas

/-- Raw whole-program run at the open dialect. The explicit Dialect application
    matters: Dialect.Op is a structure field, so Block Op does not determine the
    dialect and every use site must name it (design2 hazard 1). -/
def Run (calls : ExternalCalls) (gas : ExternalGas) (prog : Block Op) (st0 : EvmState)
    (V' : VEnv (Dialect calls gas)) (st' : EvmState) (o : Outcome) : Prop :=
  YulSemantics.Run (Dialect calls gas) prog st0 V' st' o

/-- Observed run: the frame-boundary commit/rollback applied to a raw run. This is
    the Y-3 fix: the same shape as Observation.lean:39 but at the open dialect.
    committedState is STATE-typed (EVMExec.lean:262-267), so the vendored commit
    map is reused unchanged - P-BR item 2 asked whether it was op-typed, and it is
    not. -/
def RunCommitted (calls : ExternalCalls) (gas : ExternalGas) (prog : Block Op) (st0 : EvmState)
    (V' : VEnv (Dialect calls gas)) (stObs : EvmState) (o : Outcome) : Prop :=
  ∃ st', Run calls gas prog st0 V' st' o ∧ stObs = committedState st0 st'

/-- ofFun is functional: the oracle answer is literally f st. The one-line proof
    is the reason the determinism condition on gas is not a new assumption, just a
    restriction of the parameter. -/
theorem ofFun_functional (f : EvmState -> U256) : ExternalGas.Functional (ExternalGas.ofFun f) := by
  intro st g₁ g₂ h₁ h₂
  simp [ExternalGas.ofFun] at h₁ h₂
  rw [h₁, h₂]

/-- Every built-in of the open dialect is deterministic once both oracles are
    functional. The op split (design2: 70 trivial cases plus 7 external ones):
    the call family goes through externalCall, whose response is unique under hc
    and whose caller-side consequences are the FUNCTION finishCall; create and
    create2 under ExternalCreates.none have only the static-violation halt, so
    they are deterministic or stuck; gas is unique under hg; every other op is
    stepOp op args st = some r, a function graph (the EVM.evm_deterministic
    argument, Determinism.lean:419).

    PROOF OBLIGATION, registered in SORRY.md: cases on Op is 77 constructors and
    each needs the match form of builtinWithExternal unfolded (EVMExec.lean:878-929).
    This is the single hole standing between stage 1 and every determinism
    corollary; nothing downstream is restated to avoid it. -/
theorem dialect_deterministic {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional) (op : Op) :
    (Dialect c g).Deterministic op := by
  sorry

/-- Whole-program determinism at the open dialect, inherited from the generic
    Run.det (Determinism.lean:411). Both hypotheses are load-bearing - see
    twoResponses_nondet for hc and ExternalGas.any for hg. -/
theorem Run.det {c g prog st0 V₁ st₁ o₁ V₂ st₂ o₂} (hc : c.Functional) (hg : g.Functional)
    (h₁ : Run c g prog st0 V₁ st₁ o₁) (h₂ : Run c g prog st0 V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  YulSemantics.Run.det (dialect_deterministic hc hg) h₁ h₂

/-- The committed run is deterministic too: committedState is a function of the
    unique raw run. This is the lemma P-BR item 3 asked for, and the reason the
    determinism condition had to be named rather than assumed - the vendored
    RunCommitted.det gets its determinism free from EVM.run_det, which does not
    exist for the open dialect. -/
theorem RunCommitted.det {c g prog st0 V₁ s₁ o₁ V₂ s₂ o₂} (hc : c.Functional) (hg : g.Functional)
    (h₁ : RunCommitted c g prog st0 V₁ s₁ o₁) (h₂ : RunCommitted c g prog st0 V₂ s₂ o₂) :
    V₁ = V₂ ∧ s₁ = s₂ ∧ o₁ = o₂ := by
  obtain ⟨t₁, r₁, rfl⟩ := h₁
  obtain ⟨t₂, r₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl, rfl⟩ := Run.det hc hg r₁ r₂
  exact ⟨rfl, rfl, rfl⟩

/-- hc is not decorative (P-BR acceptance item 4; the R-30/R-32 anti-pattern is a
    lemma whose hypothesis is never used). The relation below answers the pairing
    precompile with BOTH success values; the staticcall then writes 1 or 0 into
    memory, so two runs of the same program from the same state end in different
    memories. PROOF OBLIGATION, registered in SORRY.md: the two derivations are
    hand-built Step terms (builtinOk over the staticcall, then letVal, then the
    mstore), which is mechanical but not short. -/
theorem twoResponses_nondet :
    let c : ExternalCalls :=
      ⟨fun req st r => req.target = 0x0f ∧ r.world = CallWorld.ofState st ∧
        r.returndata = [] ∧ (r.success = true ∨ r.success = false)⟩
    ∃ (V₁ V₂ : VEnv (Dialect c (ExternalGas.ofFun fun _ => 0))) (st₁ st₂ : EvmState),
      Run c (ExternalGas.ofFun fun _ => 0)
        (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₁ st₁ .normal ∧
      Run c (ExternalGas.ofFun fun _ => 0)
        (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₂ st₂ .normal ∧
      st₁.memory 0 ≠ st₂.memory 0 := by
  sorry

/-! ### The keccak hook -/

/-- The List UInt8 to ByteArray and U256 to H256 adapter: a Midfall hash
    (Bytes -> H256, the type Native.lean:50 abbreviates - not imported here, so
    the type is written out) as the vendored oracle. -/
def hashOfBytes (H : Midfall.Bytes -> Midfall.H256) : List UInt8 -> U256 :=
  fun l => H (ByteArray.mk l.toArray)

/-- Install H as the frame keccak oracle (finding Y-2: the hash lives in the
    state, not the dialect, which is what makes a forall-H statement expressible at
    all). -/
def withKeccak (H : Midfall.Bytes -> Midfall.H256) (st : EvmState) : EvmState :=
  { st with env := { st.env with keccakOf := hashOfBytes H } }

@[simp] theorem hashOfBytes_apply (H) (l : List UInt8) :
    hashOfBytes H l = H (ByteArray.mk l.toArray) := rfl

/-- The adapter round-trips: hashing the memory slice the EVM reads is hashing the
    ByteArray the Lean transcript builds from the same bytes. rfl by construction,
    stated because every keccak-vs-H agreement lemma in stage 2 rewrites through it. -/
theorem hashOfBytes_readBytes (H) (mem : Nat -> UInt8) (p n : Nat) :
    hashOfBytes H (readBytes mem p n) = H (ByteArray.mk (readBytes mem p n).toArray) := rfl

/-- The state component a Res carries. Needed because Step results hide the state
    inside either an EResult or an sres. -/
def Res.state {D : YulSemantics.Dialect} : Res D -> D.State
  | .eres (.vals _ st) => st
  | .eres (.halt st) => st
  | .sres _ st _ => st

/-- No step of the open dialect changes env.keccakOf: stepOp touches other env
    fields, finishCall routes a response world through CallWorld.install
    (EVMExec.lean:571-584), which rewrites balance, code, nonce, storage and
    transient fields but not keccakOf, finishSelfdestruct touches balances only,
    and creates are absent from this dialect. PROOF OBLIGATION, registered in
    SORRY.md: rule induction on Step, about 45 constructors, each simp [Res.state]
    plus the recursive calls. No hypothesis on calls is needed, which is the point:
    the hash cannot be swapped by an adversarial callee. -/
theorem keccakOf_invariant {c g funs V st code res}
    (h : Step (Dialect c g) funs V st code res) :
    (Res.state res).env.keccakOf = st.env.keccakOf := by
  sorry

/-- So no observed run changes it either. PROOF OBLIGATION, registered in SORRY.md
    (one line once keccakOf_invariant lands, plus committedState case split). -/
theorem RunCommitted_keccakOf {c g prog st0 V' stObs o}
    (h : RunCommitted c g prog st0 V' stObs o) :
    stObs.env.keccakOf = st0.env.keccakOf := by
  sorry

/-! ### Observations -/

/-- What a caller observes: the committed state and the control-flow outcome. The
    vendored observation is exactly this pair; there is no payload on Outcome
    (Ast.lean:353), so nothing is lost by not carrying one. -/
structure Obs where
  state : EvmState
  outcome : Outcome

/-- The caller-visible projection. Memory, activeWords and the variable environment
    are deliberately NOT part of it: an IR whose memory layout differs from the shell
    model must still be ObsEquiv to it, which is the whole point of comparing at view
    level (PLAN 10.3, design2 disagreement on obs = .return abiTrue not being a state
    equality).

    R-60 S6 ADDED `selfBalance` AND `extCodeHashOf`. The view used to carry nine of
    the eleven components `WorldEq` compares, so `worldUnchanged` - the third
    conjunct of `lowering_equivalence` and of `only_two_outcomes` - was NOT
    determined by the view, and an `ObsEquiv` could not transport it. That was the
    real blocker for that conjunct, and it was never named before R-60: the previous
    report blamed `dialect_deterministic`, which the four view-transport lemmas below
    show is not needed. With these two fields the view carries every `WorldEq`
    component and `worldEq_of_view_eq` proves the transport outright.

    Note the view carries `halted`, so returnData, isReturn and isRevertOrHalt were
    ALREADY view-determined; the repair brief's "returndata is excluded" reading of
    the old docstring was stale - the exclusion is of the frame's RETURNDATA buffer
    (state.returndata), not of the halt payload, and `Obs.returnData` reads the halt
    payload. -/
structure ObsView where
  outcome : Outcome
  halted : Option (HaltKind × List UInt8)
  storage : U256 -> U256
  transient : U256 -> U256
  logs : List LogEntry
  selfdestructs : List (U256 × Bool)
  balanceOf : U256 -> U256
  /-- R-60 S6: `WorldEq` compares it, so the view has to carry it or
      `worldUnchanged` is not view-determined. -/
  selfBalance : U256
  extCodeOf : U256 -> List UInt8
  /-- R-60 S6: the second `WorldEq` component the view was missing. An IR that
      deploys different code has a different hash map, and a view that could not see
      that could not be used to transport "the world is unchanged". -/
  extCodeHashOf : U256 -> U256
  nonceOf : U256 -> U256
  storageOf : U256 -> U256 -> U256
  transientOf : U256 -> U256 -> U256

def Obs.view (o : Obs) : ObsView :=
  { outcome := o.outcome, halted := o.state.halted, storage := o.state.storage,
    transient := o.state.transient, logs := o.state.logs,
    selfdestructs := o.state.selfdestructs, balanceOf := o.state.env.balanceOf,
    selfBalance := o.state.env.selfBalance,
    extCodeOf := o.state.env.extCodeOf,
    extCodeHashOf := o.state.env.extCodeHashOf, nonceOf := o.state.env.nonceOf,
    storageOf := o.state.env.storageOf, transientOf := o.state.env.transientOf }

/-- return(p, n) fired (EVMExec.lean:840-843). -/
def Obs.isReturn (o : Obs) : Prop := ∃ d, o.state.halted = some (.ret, d)

/-- The bytes a returning frame exposes. -/
def Obs.returnData (o : Obs) : List UInt8 :=
  match o.state.halted with
  | some (_, d) => d
  | none => []

/-- A non-committing halt: revert, invalid, invalidMemoryAccess, staticViolation.
    Running off the end (halted = none) and stop/selfdestruct are EXCLUDED, so the
    only-two-outcomes conjunct really excludes them (HaltKind.commits,
    EVMExec.lean:250-252). -/
def Obs.isRevertOrHalt (o : Obs) : Prop :=
  ∃ k d, o.state.halted = some (k, d) ∧ k.commits = false

/-- Equality of every world component. This is what ir_refines and worldUnchanged
    talk about; memory and the VEnv are not here on purpose. -/
def WorldEq (a b : EvmState) : Prop :=
  a.storage = b.storage ∧ a.transient = b.transient ∧ a.logs = b.logs ∧
  a.selfdestructs = b.selfdestructs ∧ a.env.selfBalance = b.env.selfBalance ∧
  a.env.balanceOf = b.env.balanceOf ∧ a.env.extCodeOf = b.env.extCodeOf ∧
  a.env.extCodeHashOf = b.env.extCodeHashOf ∧ a.env.nonceOf = b.env.nonceOf ∧
  a.env.storageOf = b.env.storageOf ∧ a.env.transientOf = b.env.transientOf

def Obs.worldUnchanged (st0 : EvmState) (o : Obs) : Prop := WorldEq st0 o.state

/-! #### R-60 S6: the view determines the outcome and the world

`ObsEquiv` is a biconditional over VIEW existence: from a run on one side it gives a
run on the other with the same `Obs.view`. Every headline conclusion is a statement
about the observation, so what transporting it needs is precisely "these properties are
functions of the view" - four three-line lemmas, and NOT `dialect_deterministic`. The
previous repair report claimed the view transport was blocked on that stage-1 hole;
R-60 S6 says so and it is wrong, and the lemmas below are the correction. They are
proved, not stated: a gap list that names a blocker that is not needed is as misleading
as a blocker that is needed and not named. -/

/-- The halt payload is a view component, so view equality carries it. -/
theorem halted_of_view_eq {o₁ o₂ : Obs} (h : o₁.view = o₂.view) :
    o₁.state.halted = o₂.state.halted := congrArg ObsView.halted h

/-- The bytes a returning frame exposes are view-determined. -/
theorem returnData_of_view_eq {o₁ o₂ : Obs} (h : o₁.view = o₂.view) :
    o₁.returnData = o₂.returnData := by
  have hh := halted_of_view_eq h
  unfold Obs.returnData
  rw [hh]

/-- Returning is view-determined, so `obs.isReturn` transports across an `ObsEquiv`. -/
theorem isReturn_of_view_eq {o₁ o₂ : Obs} (h : o₁.view = o₂.view) :
    o₁.isReturn ↔ o₂.isReturn := by
  have hh := halted_of_view_eq h
  constructor <;> intro ⟨d, hd⟩ <;> exact ⟨d, hh ▸ hd⟩

/-- Reverting-or-halting is view-determined, and so is the non-committing half of the
    only-two-outcomes conjunct. -/
theorem isRevertOrHalt_of_view_eq {o₁ o₂ : Obs} (h : o₁.view = o₂.view) :
    o₁.isRevertOrHalt ↔ o₂.isRevertOrHalt := by
  have hh := halted_of_view_eq h
  constructor <;> intro ⟨k, d, hd, hk⟩ <;> exact ⟨k, d, hh ▸ hd, hk⟩

/-- THE POINT OF ADDING selfBalance AND extCodeHashOf TO THE VIEW: with all eleven
    `WorldEq` components carried, "the world is unchanged" is a statement about the
    view, so the third conjunct of `lowering_equivalence` and `only_two_outcomes` is
    transportable across an `ObsEquiv` with no determinism hypothesis at all. Before
    R-60 S6 this was FALSE, and the reason was never named: the view had nine of the
    eleven components, so the two states could agree on the view and disagree on the
    self balance or on an account's code hash. -/
theorem worldEq_of_view_eq {o₁ o₂ : Obs} (h : o₁.view = o₂.view) :
    WorldEq o₁.state o₂.state :=
  ⟨congrArg ObsView.storage h, congrArg ObsView.transient h, congrArg ObsView.logs h,
    congrArg ObsView.selfdestructs h, congrArg ObsView.selfBalance h,
    congrArg ObsView.balanceOf h, congrArg ObsView.extCodeOf h,
    congrArg ObsView.extCodeHashOf h, congrArg ObsView.nonceOf h,
    congrArg ObsView.storageOf h, congrArg ObsView.transientOf h⟩

/-- And the converse direction, so the view is EXACTLY the world plus the halt payload
    plus the outcome: nothing a headline conclusion reads is missing from it, and
    nothing it carries is more than `WorldEq` and the halt carry. -/
theorem view_eq_of_worldEq_and_halt {o₁ o₂ : Obs}
    (hw : WorldEq o₁.state o₂.state) (hh : o₁.state.halted = o₂.state.halted)
    (ho : o₁.outcome = o₂.outcome) : o₁.view = o₂.view := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hw
  simp [Obs.view, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hh, ho]

/-- THE REFUTATION THAT MAKES S6 A FIX AND NOT A CLAIM. Two states that agreed on the
    eleven components the old view carried EXCEPT `selfBalance` had EQUAL views, so an
    `ObsEquiv` could not tell them apart and `worldUnchanged` was not transportable -
    that was the hole, and here it is exhibited as a term: a pair of states that differ
    in the self balance and now have DIFFERENT views. Delete `selfBalance` from
    `ObsView` and the second conjunct stops holding, which is the demonstration (R-41)
    that this can fail. -/
theorem view_sees_selfBalance :
    ∃ a b : EvmState, a.env.selfBalance ≠ b.env.selfBalance ∧
      Obs.view ⟨a, .halt⟩ ≠ Obs.view ⟨b, .halt⟩ :=
  ⟨{ EvmState.init with env.selfBalance := 1 }, { EvmState.init with env.selfBalance := 2 },
    by decide, fun h =>
      have h' : (1 : U256) = 2 := congrArg ObsView.selfBalance h
      absurd h' (by decide)⟩

/-- The same for the code-hash map, the other `WorldEq` component the view used to
    drop: an account whose code hash differs while its code agrees - exactly what a
    pasted codehash constant in a deployment is - is now visible at the view. -/
theorem view_sees_extCodeHashOf :
    ∃ a b : EvmState, a.env.extCodeHashOf ≠ b.env.extCodeHashOf ∧
      Obs.view ⟨a, .halt⟩ ≠ Obs.view ⟨b, .halt⟩ :=
  ⟨{ EvmState.init with env.extCodeHashOf := fun _ => 1 },
    { EvmState.init with env.extCodeHashOf := fun _ => 2 },
    (fun h => by
      have := congrFun h 0
      exact absurd this (by decide)), fun h =>
      have h' : (1 : U256) = 2 := by
        exact congrFun (congrArg ObsView.extCodeHashOf h) 0
      absurd h' (by decide)⟩

/-- The ABI encoding of true: the 32-byte big-endian word 1. TraceReturn.yul:70-72
    does mstore(RETURN_MPTR, 1) then return(RETURN_MPTR, 0x20), and the return
    builtin stores readBytes, so the exposed bytes are exactly this. attack.md
    line 11 records that two designs defined abiTrue separately with the same
    value; line 168 FIX makes Bridge the single home. -/
def abiTrue : List UInt8 := (Midfall.natToBytesBE 1 32).data.toList

/-- The view of a successful run returning abiTrue with world w. -/
def returnView (w : EvmState) : ObsView :=
  Obs.view ⟨{ w with halted := some (.ret, abiTrue) }, .halt⟩

/-- A rolled-back observation leaves the world alone (committedState_rollback,
    Dialect/EVM.lean:37-40 keeps only halted and returndata from the failed frame). -/
theorem worldUnchanged_of_rollback {st0 st' : EvmState} {k d} (h : st'.halted = some (k, d))
    (hk : k.commits = false) : Obs.worldUnchanged st0 ⟨committedState st0 st', .halt⟩ := by
  simp [Obs.worldUnchanged, WorldEq, committedState_rollback h hk]

/-! ### Folding the Externals relations into one ExternalCalls (finding Y-1) -/

/-- Externals CallKind to the vendored one. -/
def toYulKind : YulSemantics.EVM.CallKind -> Midfall.Yul.CallKind
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

/-- EVM request to Externals request: List UInt8 becomes ByteArray; Word256 and
    U256 are the same BitVec 256 type. -/
def toYulReq (req : YulSemantics.EVM.CallRequest) : Midfall.Yul.CallRequest :=
  { kind := toYulKind req.kind, gas := req.gas, target := req.target, value := req.value,
    input := ByteArray.mk req.input.toArray }

/-- A precompile changes no world state, so the honest response carries the
    caller own world projection. -/
def ofOutcome (st : EvmState) (o : Midfall.Yul.CallOutcome) : CallResponse :=
  { success := o.success, returndata := o.returndata.data.toList, world := CallWorld.ofState st }

/-- A rejected request is a failed call that burns the forwarded gas and returns
    nothing (EIP-2537 error semantics, Externals.lean:765-771). -/
def failResp (st : EvmState) : CallResponse :=
  { success := false, returndata := [], world := CallWorld.ofState st }

/-- Target match on the 160-bit account key, the EVM notion of address equality
    (EVMExec.lean:278). Externals.accepts compares the full 256-bit word, which
    would let 2^160 + 0x0f miss the pairing precompile entirely (design2 hazard 3). -/
def hits (r : Midfall.Yul.ExternalCallRelation) (req : YulSemantics.EVM.CallRequest) : Bool :=
  accountKey req.target == accountKey r.address

/-- The honest answer of the first relation whose address the request hits, or a
    failed call when the input is invalid. -/
def honestOf (rels : List Midfall.Yul.ExternalCallRelation) (req : YulSemantics.EVM.CallRequest)
    (st : EvmState) :
    Option CallResponse :=
  (rels.find? (fun r => hits r req)).map fun r =>
    match r.respond (toYulReq req) with
    | some o => ofOutcome st o
    | none => failResp st

/-- The disjunctive fold of finding Y-1: EVM.ExternalCalls bundles ONE ternary
    relation, so the four precompiles plus the quotient-evaluator slot must be
    combined by target. The evaluator slot is a parameter because which address it
    lives at is a deployment fact (Surface.lean, stage 2), not a property of the
    precompiles. -/
def honestCalls (product : Midfall.Yul.PairingProduct)
    (evalAddr : U256) (evalRel : YulSemantics.EVM.CallRequest -> EvmState -> CallResponse -> Prop) :
    ExternalCalls :=
  ⟨fun req st resp =>
    (honestOf (Midfall.Yul.honestRelations product) req st = some resp) ∨
    (accountKey req.target == accountKey evalAddr ∧ evalRel req st resp)⟩

/-- The soundness relation: any FAILURE is permitted (gas is unmodelled, a
    precompile may be missing on a different deployment), a SUCCESS must be the
    honest one, and no world change is ever reported. Stated as a constructor so
    that permissive c is an ExternalCalls and not a Prop - attack.md line 12
    records the two readings and line 36 FIX requires the relation to be
    world-local, which permissive preserves (permissive_worldLocal). -/
def permissive (c : ExternalCalls) : ExternalCalls :=
  ⟨fun req st resp => resp.world = CallWorld.ofState st ∧ (resp.success = true -> c.Call req st resp)⟩

/-- Honest runs are a subset of permissive ones, given the honest relation never
    reports a world change. That side condition is exactly what honestCalls
    satisfies by construction (ofOutcome, failResp). -/
theorem honest_le_permissive (c : ExternalCalls)
    (hw : ∀ req st r, c.Call req st r -> r.world = CallWorld.ofState st) :
    ∀ req st r, c.Call req st r -> (permissive c).Call req st r :=
  fun _ _ _ h => ⟨hw _ _ _ h, fun _ => h⟩

/-- honestOf depends on the caller state only through CallWorld.ofState, which is
    what makes the honest fold world-local. Both branches of its inner match
    (ofOutcome, failResp) store exactly that projection and nothing else. -/
theorem honestOf_eq_of_ofState (rels) (req) (st st')
    (h : CallWorld.ofState st = CallWorld.ofState st') :
    honestOf rels req st = honestOf rels req st' := by
  have h1 : ∀ x : Midfall.Yul.CallOutcome, ofOutcome st x = ofOutcome st' x := by
    intro x
    simp [ofOutcome, h]
  have h2 : failResp st = failResp st' := by simp [failResp, h]
  rcases hmsg : rels.find? (fun r => hits r req) with _|⟨rel⟩
  · simp [honestOf, hmsg]
  · have e1 : honestOf rels req st = some (match rel.respond (toYulReq req) with
        | some o => ofOutcome st o
        | none => failResp st) := by simp [honestOf, hmsg]
    have e2 : honestOf rels req st' = some (match rel.respond (toYulReq req) with
        | some o => ofOutcome st' o
        | none => failResp st') := by simp [honestOf, hmsg]
    rw [e1, e2]
    rcases rel.respond (toYulReq req) with _|⟨o⟩
    · exact congrArg some h2
    · exact congrArg some (h1 o)

/-- The honest fold is world-local (attack.md line 36 FIX: honestCalls and
    permissive satisfy this by construction). The evaluator slot needs the same
    property as a hypothesis, which is what Evaluator.rel provides. -/
theorem honestCalls_worldLocal (product) (evalAddr) (evalRel)
    (hev : ∀ req st st' r, CallWorld.ofState st = CallWorld.ofState st' ->
      (evalRel req st r <-> evalRel req st' r)) :
    (honestCalls product evalAddr evalRel).WorldLocal := by
  intro req st st' r hw
  show (honestOf (Midfall.Yul.honestRelations product) req st = some r ∨
      (accountKey req.target == accountKey evalAddr ∧ evalRel req st r)) ↔
    (honestOf (Midfall.Yul.honestRelations product) req st' = some r ∨
      (accountKey req.target == accountKey evalAddr ∧ evalRel req st' r))
  constructor
  · intro h
    cases h with
    | inl he =>
        rw [← honestOf_eq_of_ofState (Midfall.Yul.honestRelations product) req st st' hw]
        exact Or.inl he
    | inr h2 => exact Or.inr ⟨h2.1, (hev req st st' r hw).mp h2.2⟩
  · intro h
    cases h with
    | inl he =>
        rw [honestOf_eq_of_ofState (Midfall.Yul.honestRelations product) req st st' hw]
        exact Or.inl he
    | inr h2 => exact Or.inr ⟨h2.1, (hev req st' st r hw.symm).mp h2.2⟩

/-- The permissive fold preserves world-locality. -/
theorem permissive_worldLocal (c : ExternalCalls) (hc : c.WorldLocal) : (permissive c).WorldLocal := by
  intro req st st' r hw
  show (r.world = CallWorld.ofState st ∧ (r.success = true -> c.Call req st r)) ↔
    (r.world = CallWorld.ofState st' ∧ (r.success = true -> c.Call req st' r))
  constructor
  · intro h
    exact ⟨h.1.trans hw, fun hs => (hc req st st' r hw).mp (h.2 hs)⟩
  · intro h
    exact ⟨h.1.trans hw.symm, fun hs => (hc req st' st r hw.symm).mp (h.2 hs)⟩

/-- The four precompile addresses are pairwise distinct on the 160-bit key, which
    is what makes honestOf dispatch unambiguous and honestCalls functional. Proved
    by decide on four BitVec literals: Externals relationKats_ok asserts the same
    fact but is a #eval Bool and cannot be cited as a lemma (design2 hazard 5). -/
theorem honestRelations_keys (product : Midfall.Yul.PairingProduct) :
    (Midfall.Yul.honestRelations product).map (fun r => accountKey r.address) =
      [0x0b, 0x0c, 0x0f, 0x05] :=
  rfl

/-- The honest fold is functional provided the evaluator slot is and its address
    does not alias a precompile. PROOF OBLIGATION, registered in SORRY.md: the two
    disjuncts must be shown exclusive, which is where hdisj is used; without it a
    request to 0x0f could be answered by both the pairing relation and the
    evaluator, and the Y-1 agreement obligation reduces to exactly this. -/
theorem honestCalls_functional (product) (evalAddr) (evalRel)
    (hev : ∀ req st r₁ r₂, evalRel req st r₁ -> evalRel req st r₂ -> r₁ = r₂)
    (hdisj : accountKey evalAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat)) :
    ExternalCalls.Functional (honestCalls product evalAddr evalRel) := by
  sorry

/-! ### The quotient-evaluator slot -/

namespace Evaluator

/-- The frame the evaluator fallback runs in: zero memory, the caller world view,
    the raw verifier frame as calldata (not ABI), static := true because the
    production call is a staticcall (QuotientAndLinearization.yul:35), the
    evaluator own code and layout, and the caller keccak oracle. Every remaining
    block-context field is copied from W - the plan sketch left that as a SKETCH
    and it resolves: ExecEnv (EVMExec.lean:114-190) has origin, gasprice,
    selfBalance, createdThisTx, coinbase, timestamp, number, prevrandao, gaslimit,
    chainid, basefee, blobbasefee, blockHashOf and blobHashOf, all of which the
    evaluator may read through the corresponding built-ins. -/
def calleeState (W : ExecEnv) (Lyt : Layout) (addr : U256) (st : EvmState)
    (req : YulSemantics.EVM.CallRequest) : EvmState :=
  { EvmState.init with
    storage := st.env.storageOf addr, transient := st.env.transientOf addr,
    env := { Lyt.env with
      address := addr, caller := st.env.address, callvalue := 0, static := true,
      calldata := req.input, keccakOf := st.env.keccakOf,
      balanceOf := st.env.balanceOf, extCodeOf := st.env.extCodeOf,
      extCodeHashOf := st.env.extCodeHashOf, nonceOf := st.env.nonceOf,
      storageOf := st.env.storageOf, transientOf := st.env.transientOf,
      origin := W.origin, gasprice := W.gasprice, selfBalance := W.selfBalance,
      createdThisTx := W.createdThisTx, coinbase := W.coinbase,
      timestamp := W.timestamp, number := W.number, prevrandao := W.prevrandao,
      gaslimit := W.gaslimit, chainid := W.chainid, basefee := W.basefee,
      blobbasefee := W.blobbasefee, blockHashOf := W.blockHashOf,
      blobHashOf := W.blobHashOf } }

/-- The caller-visible response of a finished callee frame. selfdestruct maps to
    SUCCESS: HaltKind.commits says it commits (EVMExec.lean:250-252), so treating
    it as a failure is wrong as a definition even though the evaluator never
    selfdestructs - attack.md line 102 FIX, binding. A bad frame length reverts
    empty (Halo2QuotientEvaluator.sol:114) and the compact output frame is returned
    at :167. -/
def responseOf (st : EvmState) (stObs : EvmState) : CallResponse :=
  match stObs.halted with
  | some (.ret, d) => { success := true, returndata := d, world := CallWorld.ofState st }
  | some (.stop, _) => { success := true, returndata := [], world := CallWorld.ofState st }
  | some (.selfdestruct, _) => { success := true, returndata := [], world := CallWorld.ofState st }
  | some (_, d) => { success := false, returndata := d, world := CallWorld.ofState st }
  | none => { success := true, returndata := [], world := CallWorld.ofState st }

/-- The evaluator slot of honestCalls: a request to the evaluator address is
    answered by RUNNING the evaluator runtime block in the CLOSED dialect - the
    evaluator calls no precompile and never reads gas(), so no external relation is
    needed and EVM determinism applies. If a future evaluator ever calls a
    precompile this must move to Bridge.Run with honest calls and Run.det. -/
def rel (W : ExecEnv) (Lyt : Layout) (addr : U256) (rt : Block Op) :
    YulSemantics.EVM.CallRequest -> EvmState -> CallResponse -> Prop :=
  fun req st resp => ∃ V' st' o,
    YulSemantics.Run EVM.evm rt (calleeState W Lyt addr st req) V' st' o ∧
    resp = responseOf st (committedState (calleeState W Lyt addr st req) st')

/-- The evaluator relation is functional because the closed dialect is: no
    hypothesis on calls is needed (design2 note), which is why honestCalls_functional
    can take hev as a parameter and discharge it here. -/
theorem rel_functional (W Lyt addr rt) :
    ∀ req st r₁ r₂, rel W Lyt addr rt req st r₁ -> rel W Lyt addr rt req st r₂ -> r₁ = r₂ := by
  rintro req st r₁ r₂ ⟨V₁, t₁, o₁, h₁, rfl⟩ ⟨V₂, t₂, o₂, h₂, rfl⟩
  obtain ⟨_, rfl, _⟩ := EVM.run_det h₁ h₂
  rfl

/-- The evaluator relation is world-local: calleeState reads the caller only
    through storageOf addr, transientOf addr, address and keccakOf, all of which
    are CallWorld projections, and responseOf stores CallWorld.ofState st. The
    proof is the same shape as honestOf_eq_of_ofState. PROOF OBLIGATION, registered
    in SORRY.md. -/
theorem rel_worldLocal (W Lyt addr rt) :
    ∀ req st st' r, CallWorld.ofState st = CallWorld.ofState st' ->
      (rel W Lyt addr rt req st r <-> rel W Lyt addr rt req st' r) := by
  sorry

end Evaluator

/-! ### Syntactic absence of world writers -/

/-- Which EVM built-ins can change the world. isWriter includes the call family
    because a non-static call installs the response world (finishCall,
    EVMExec.lean:612-619); staticcall is excluded because finishCall never installs
    for it. attack.md line 99 FIX: with this list the extra hypothesis that a call
    response never changes the world is decorative, so Run_worldEq_of_noWriters
    below does NOT assume it. -/
def Op.isWriter : Op -> Bool
  | .sstore | .tstore | .log0 | .log1 | .log2 | .log3 | .log4 | .selfdestruct
  | .create | .create2 | .call | .callcode | .delegatecall => true
  | _ => false

/-- Fuel-bounded syntactic scan for world writers (R-37: exhaustion answers false,
    so a program that needs more fuel than it gets is reported as MAY write, never
    as clean). Walks expressions and statements mutually: a builtin call can nest
    (mstore(sload(0), 1)), a function definition body must be scanned, and a for
    loop has three sub-blocks. PROOF OBLIGATION, registered in SORRY.md: this is a
    definition hole, not a theorem hole - the walker is mechanical but long, and
    the plan sketch marks it SKETCH (design2 noWritersFuel). -/
def noWritersFuel : Nat -> Block Op -> Bool := fun _ _ => sorry

/-- A block writes no world state if the scan succeeds with some fuel. -/
def NoWriters (b : Block Op) : Prop := ∃ n, noWritersFuel n b = true

/-- Only staticcalls and no writers means the world is untouched: sstore, tstore,
    the log family, selfdestruct and the create family are the only stepOp world
    writers, and the call family is excluded by NoWriters except staticcall, whose
    response world is never installed (EVMExec.lean:612-616). PROOF OBLIGATION,
    registered in SORRY.md: induction on Step with the isWriter scan. Note the
    decorative hypothesis attack.md line 99 warns about is deliberately absent. -/
theorem Run_worldEq_of_noWriters {c g prog st0 V' st' o}
    (hn : NoWriters prog) (h : Run c g prog st0 V' st' o) : WorldEq st0 st' := by
  sorry


/-! ### Gates -/

/-- The ABI encoding of true is big-endian: 31 zero bytes then 0x01. An
    little-endian encoding would put the 1 first and every TraceReturn comparison
    in the contract would fail - the R-20 byte-order class, pinned here rather than
    assumed (design2 non-vacuity note for abiTrue). -/
def abiTrueKats_ok : Bool :=
  abiTrue.length == 32 && abiTrue.getLast? == some 1 && abiTrue.head? == some 0 &&
    abiTrue.drop 31 == [1] && (Midfall.natToBytesBE 1 32).size == 32

#eval abiTrueKats_ok   -- expect true

/-- The halt classification Obs.isRevertOrHalt reads through: stop and
    selfdestruct commit, revert / invalid / invalidMemoryAccess / staticViolation
    do not. If stop were classified as non-committing the only-two-outcomes
    conjunct would silently count a clean return as a revert (EVMExec.lean:250-252). -/
def haltKindKats_ok : Bool :=
  HaltKind.stop.commits && HaltKind.ret.commits && HaltKind.selfdestruct.commits &&
    ! HaltKind.revert.commits && ! HaltKind.invalid.commits &&
    ! HaltKind.invalidMemoryAccess.commits && ! HaltKind.staticViolation.commits

#eval haltKindKats_ok   -- expect true

/-- The keccak adapter round-trips against the concrete hash: hashing the empty
    byte list is hashing the empty ByteArray. Every keccak-versus-H agreement lemma
    in stage 2 rewrites through this, and a wrong endianness or a dropped byte
    would show up here (P-BR item 4, design2 non-vacuity for hashOfBytes). -/
def hashAdapterKats_ok : Bool :=
  hashOfBytes Midfall.keccak256 (ByteArray.mk #[]).toList == Midfall.keccak256 Midfall.Bytes.empty &&
    hashOfBytes Midfall.keccak256 [1, 2, 3] ==
      Midfall.keccak256 (ByteArray.mk #[1, 2, 3]) &&
    (withKeccak Midfall.keccak256 EvmState.init).env.keccakOf [1, 2] ==
      Midfall.keccak256 (ByteArray.mk #[1, 2])

#eval hashAdapterKats_ok   -- expect true

/-- The honest fold dispatches on the 160-bit account key, not the full word: a
    request to 2^160 + 0x0b still reaches G1ADD (design2 hazard 3 - Externals
    accepts compares full words, which would let the aliased address miss the
    precompile entirely). The last three lines are the failure mapping: a request
    to modexp carrying a G1ADD frame is an invalid input, and an invalid input is a
    FAILED CALL, not no call at all; a request to an address no relation owns
    answers nothing. -/
def honestFoldKats_ok : Bool :=
  let g := Midfall.Yul.bytesOfWords Midfall.Yul.katG1GenWords
  let req : YulSemantics.EVM.CallRequest :=
    { kind := YulSemantics.EVM.CallKind.staticcall, gas := 375,
      target := Midfall.Yul.g1AddAddress, value := 0,
      input := g.data.toList ++ g.data.toList }
  hits Midfall.Yul.g1AddRelation req &&
    hits Midfall.Yul.g1AddRelation { req with target := BitVec.ofNat 256 (2 ^ 160 + 11) } &&
    ! hits Midfall.Yul.g1MsmRelation req &&
    (honestOf (Midfall.Yul.honestRelations (fun _ => true)) req EvmState.init).map (·.success) =
      some true &&
    (honestOf (Midfall.Yul.honestRelations (fun _ => true))
      { req with target := Midfall.Yul.modexpAddress } EvmState.init).map (·.success) =
      some false &&
    honestOf (Midfall.Yul.honestRelations (fun _ => true))
      { req with target := 0x07 } EvmState.init = none

#eval honestFoldKats_ok   -- expect true

/-- The evaluator response classification: a returning frame is a successful call
    carrying its bytes, a revert is a failure carrying them, and selfdestruct is a
    SUCCESS because it commits (attack.md line 102 FIX). A responseOf that mapped
    revert to success would make the completeness proof staticcall-failure arm
    unreachable. -/
def evaluatorResponseKats_ok : Bool :=
  let st := EvmState.init
  (Evaluator.responseOf st { st with halted := some (.ret, [1]) }).success &&
    (Evaluator.responseOf st { st with halted := some (.ret, [1]) }).returndata == [1] &&
    ! (Evaluator.responseOf st { st with halted := some (.revert, [2]) }).success &&
    (Evaluator.responseOf st { st with halted := some (.revert, [2]) }).returndata == [2] &&
    (Evaluator.responseOf st { st with halted := some (.selfdestruct, []) }).success &&
    (Evaluator.responseOf st { st with halted := none }).success &&
    (Evaluator.responseOf st { st with halted := some (.stop, []) }).returndata == []

#eval evaluatorResponseKats_ok   -- expect true

/-- The writer classification NoWriters reads: the sstore/tstore/log family,
    selfdestruct, create and the three value-bearing call kinds write the world;
    staticcall, sload, mstore and the block context do not. This is the list that
    makes Run_worldEq_of_noWriters mean something, so it is pinned rather than
    trusted (attack.md line 99 FIX). -/
def isWriterKats_ok : Bool :=
  Op.isWriter Op.sstore && Op.isWriter Op.tstore && Op.isWriter Op.log0 &&
    Op.isWriter Op.log4 && Op.isWriter Op.selfdestruct && Op.isWriter Op.create &&
    Op.isWriter Op.create2 && Op.isWriter Op.call && Op.isWriter Op.callcode &&
    Op.isWriter Op.delegatecall && ! Op.isWriter Op.staticcall &&
    ! Op.isWriter Op.sload && ! Op.isWriter Op.mstore && ! Op.isWriter Op.keccak256 &&
    ! Op.isWriter Op.stop && ! Op.isWriter Op.ret && ! Op.isWriter Op.revert &&
    ! Op.isWriter Op.gas

#eval isWriterKats_ok   -- expect true

end Midfall.Yul.Bridge