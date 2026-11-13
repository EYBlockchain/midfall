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

/-- A Yul word literal for a machine word: the AST stores a `Nat` and `Dialect.litValue`
    reads it back as `BitVec.ofNat 256 v.toNat`, which is `v` but not definitionally
    (`BitVec.ofNat_toNat`). That one step is why `wlit_eval` needs a cast and no other
    step lemma does. -/
def wlit (v : U256) : Expr Op := .lit (.number v.toNat)

theorem wlit_val {c : ExternalCalls} {g : ExternalGas} (v : U256) :
    (Dialect c g).litValue (.number v.toNat) = v :=
  BitVec.ofNat_toNat 256 v

/-- A word literal evaluates to its word, leaving the state alone, at any frame. -/
theorem wlit_eval {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (Dialect c g)}
    {V : VEnv (Dialect c g)} {st : EvmState} (v : U256) :
    Step (Dialect c g) funs V st (.expr (wlit v)) (.eres (.vals [v] st)) :=
  cast (congrArg (fun w => Step (Dialect c g) funs V st (.expr (wlit v))
            (.eres (EResult.vals [w] st))) (wlit_val v)) Step.lit

/-- A whole list of word literals evaluates to its words. Right-to-left evaluation is a
    property of the semantics (`argsCons` takes the tail first, BigStep.lean:209-212), so
    this is an induction on the list rather than a six-way term. -/
theorem wlits_eval {c : ExternalCalls} {g : ExternalGas} {funs : FunEnv (Dialect c g)}
    {V : VEnv (Dialect c g)} (st : EvmState) (l : List U256) :
    Step (Dialect c g) funs V st (.args (l.map wlit)) (.eres (.vals l st)) := by
  induction l with
  | nil => exact Step.argsNil
  | cons a as ih => exact Step.argsCons ih (wlit_eval a)

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

/-- The block the nondeterminism exhibit runs. -/
def nondetBlock : Block Op :=
  yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }

/-- One run of `nondetBlock` for whatever response the relation offers, with the byte
    that records the answer pinned. The whole exhibit is this lemma twice, once with a
    successful response and once with a failed one. -/
theorem run_staticcall_mstore {c : ExternalCalls} {resp : CallResponse}
    (hcall : c.Call
      { kind := .staticcall, gas := 0, target := 0x0f, value := 0,
        input := readBytes EvmState.init.memory 0 0 } EvmState.init resp) :
    ∃ st',
    Run c (ExternalGas.ofFun fun _ => 0) nondetBlock EvmState.init [] st' .normal ∧
      st'.memory 31 = UInt8.ofNat resp.flag.toNat := by
  let g : ExternalGas := ExternalGas.ofFun fun _ => 0
  let st₁ := finishCall .staticcall EvmState.init resp 0 0 0 0
  have hargs : Step (Dialect c g) [[]] [] EvmState.init
      (.args (([0, 0x0f, 0, 0, 0, 0] : List U256).map wlit))
      (.eres (.vals [0, 0x0f, 0, 0, 0, 0] EvmState.init)) :=
    wlits_eval EvmState.init [0, 0x0f, 0, 0, 0, 0]
  have hbi : (Dialect c g).Builtin Op.staticcall [0, 0x0f, 0, 0, 0, 0] EvmState.init
      (.ok [resp.flag] st₁) := ⟨resp, hcall, rfl⟩
  have hexpr : Step (Dialect c g) [[]] [] EvmState.init
      (.expr (.builtin Op.staticcall (([0, 0x0f, 0, 0, 0, 0] : List U256).map wlit)))
      (.eres (.vals [resp.flag] st₁)) := Step.builtinOk hargs hbi
  have hlet : Step (Dialect c g) [[]] [] EvmState.init
      (.stmt (.letDecl ["s"] (some (.builtin Op.staticcall
        (([0, 0x0f, 0, 0, 0, 0] : List U256).map wlit)))))
      (.sres [("s", resp.flag)] st₁ .normal) := Step.letVal hexpr rfl
  have hnil : Step (Dialect c g) [[]] [("s", resp.flag)] st₁ (.args [])
      (.eres (.vals [] st₁)) := Step.argsNil
  have hvar : Step (Dialect c g) [[]] [("s", resp.flag)] st₁ (.expr (.var "s"))
      (.eres (.vals [resp.flag] st₁)) := Step.var rfl
  have hmsargs : Step (Dialect c g) [[]] [("s", resp.flag)] st₁
      (.args [wlit 0, .var "s"]) (.eres (.vals [0, resp.flag] st₁)) :=
    Step.argsCons (Step.argsCons hnil hvar) (wlit_eval 0)
  have hmsbi : (Dialect c g).Builtin Op.mstore [0, resp.flag] st₁
      (.ok [] { touchMemory st₁ 0 32 with memory := storeWord st₁.memory 0 resp.flag }) := rfl
  have hms : Step (Dialect c g) [[]] [("s", resp.flag)] st₁
      (.stmt (.exprStmt (.builtin Op.mstore [wlit 0, .var "s"])))
      (.sres [("s", resp.flag)]
        { touchMemory st₁ 0 32 with memory := storeWord st₁.memory 0 resp.flag } .normal) :=
    Step.exprStmt (Step.builtinOk hmsargs hmsbi)
  refine ⟨_, Step.block (D := Dialect c g) (body := nondetBlock) (funs := [])
      (Step.seqCons hlet (Step.seqCons hms Step.seqNil)), rfl⟩

/-- hc is not decorative (P-BR acceptance item 4; the R-30/R-32 anti-pattern is a
    lemma whose hypothesis is never used). The relation below answers the pairing
    precompile with BOTH success values; the staticcall then writes 1 or 0 into
    memory, so two runs of the same program from the same state end in different
    memories. PROVED, not registered.

    THE REGISTERED STATEMENT WAS WRONG AND IS CORRECTED HERE. It read
    `st₁.memory 0 ≠ st₂.memory 0`. `mstore(0, s)` stores `s` BIG-ENDIAN across bytes
    0..31, so for s ∈ {0, 1} byte 0 is the most significant byte and is 0 in BOTH runs:
    the old statement is not merely unproved, it is FALSE, and no amount of work on the
    Step rules could have closed it. The plan sketch (P-SE-semantic-equivalence.md
    section B line 601, the statement authority) says `memory 31`, which is the
    least-significant byte and does differ. Reported as a finding: a registered hole whose text is
    unsatisfiable is worse than a missing proof, because it advertises work that cannot
    be done. -/
theorem twoResponses_nondet :
    let c : ExternalCalls :=
      ⟨fun req st r => req.target = 0x0f ∧ r.world = CallWorld.ofState st ∧
        r.returndata = [] ∧ (r.success = true ∨ r.success = false)⟩
    ∃ (V₁ V₂ : VEnv (Dialect c (ExternalGas.ofFun fun _ => 0))) (st₁ st₂ : EvmState),
      Run c (ExternalGas.ofFun fun _ => 0)
        (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₁ st₁ .normal ∧
      Run c (ExternalGas.ofFun fun _ => 0)
        (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₂ st₂ .normal ∧
      st₁.memory 31 ≠ st₂.memory 31 := by
  intro c
  let req0 : YulSemantics.EVM.CallRequest :=
    YulSemantics.EVM.CallRequest.mk .staticcall 0 0x0f 0 (readBytes EvmState.init.memory 0 0)
  let okResp : CallResponse :=
    { success := true, returndata := [], world := CallWorld.ofState EvmState.init }
  let badResp : CallResponse :=
    { success := false, returndata := [], world := CallWorld.ofState EvmState.init }
  have hok : c.Call req0 EvmState.init okResp := ⟨rfl, rfl, rfl, Or.inl rfl⟩
  have hbad : c.Call req0 EvmState.init badResp := ⟨rfl, rfl, rfl, Or.inr rfl⟩
  obtain ⟨st₁, r₁, m₁⟩ := run_staticcall_mstore (c := c) (resp := okResp) hok
  obtain ⟨st₂, r₂, m₂⟩ := run_staticcall_mstore (c := c) (resp := badResp) hbad
  exact ⟨[], [], st₁, st₂, r₁, r₂, by rw [m₁, m₂]; show (1 : UInt8) ≠ 0; decide⟩


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


/-- A `find?` that succeeds found a *member* satisfying the predicate. Stated here
    because the core lemma is about a boolean predicate and this layer needs the
    membership half to route a request to the relation that owns its address. -/
theorem find?_some_mem {α : Type} {l : List α} {p : α -> Bool} {a : α}
    (h : l.find? p = some a) : ∃ x ∈ l, p x ∧ x = a := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      by_cases hx : p x
      · have hthis : (x :: xs).find? p = some x := by simp [hx]
        exact ⟨x, by simp, hx, Option.some.inj (hthis.symm.trans h)⟩
      · have h2 : xs.find? p = some a := by simpa [hx] using h
        obtain ⟨y, hy, hpy, rfl⟩ := ih h2
        exact ⟨y, by simp [hy], hpy, rfl⟩

/-- A request the honest fold answers was claimed by some relation in the list. -/
theorem honestOf_some_target {rels : List Midfall.Yul.ExternalCallRelation}
    {req : YulSemantics.EVM.CallRequest} {st : EvmState} {r : CallResponse}
    (h : honestOf rels req st = some r) : ∃ rel ∈ rels, hits rel req := by
  rcases hmsg : rels.find? (fun rel => hits rel req) with _|⟨rel⟩
  · exact absurd h (by simp [honestOf, hmsg])
  · obtain ⟨x, hx, hp, rfl⟩ := find?_some_mem hmsg
    exact ⟨x, hx, hp⟩

/-- So the target of an answered request is one of the owned addresses. This is the
    half the disjunction-exclusivity argument runs on, and it is why
    `honestRelations_keys` had to be a theorem and not just a `#eval`. -/
theorem honestOf_some_key {rels : List Midfall.Yul.ExternalCallRelation}
    {req : YulSemantics.EVM.CallRequest} {st : EvmState} {r : CallResponse}
    (h : honestOf rels req st = some r) :
    ∃ a ∈ rels.map (fun r' => accountKey r'.address), accountKey req.target = a := by
  obtain ⟨rel, hmem, hhit⟩ := honestOf_some_target h
  exact ⟨accountKey rel.address, List.mem_map.mpr ⟨rel, hmem, rfl⟩,
    by simpa [hits] using hhit⟩

/-- The two disjuncts of `honestCalls` are exclusive when the evaluator address does not
    alias a precompile: a request cannot be answered by the honest fold AND land on the
    evaluator slot. This is the whole content of `hdisj`, factored out so the
    four-case split below reads as one line per case. -/
theorem honestOf_target_not_evalAddr {req : YulSemantics.EVM.CallRequest} {st : EvmState}
    {r : CallResponse} {product : Midfall.Yul.PairingProduct} {evalAddr : U256}
    (e : honestOf (Midfall.Yul.honestRelations product) req st = some r)
    (hb : (accountKey req.target == accountKey evalAddr) = true)
    (hdisj : accountKey evalAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat)) : False := by
  obtain ⟨a, ham, he⟩ := honestOf_some_key e
  rw [honestRelations_keys product] at ham
  have hkey : accountKey req.target = accountKey evalAddr := Nat.beq_eq.mp hb
  exact hdisj ((hkey.symm.trans he) ▸ ham)

/-- The honest fold is functional provided the evaluator slot is and its address
    does not alias a precompile. LANDS P-BRIDGE STEP 3 (mechanical): the two disjuncts
    are exclusive, which is where `hdisj` is used - a request the honest fold answers
    lands on one of the four owned keys (`honestOf_some_key`, which is why
    `honestRelations_keys` had to be a theorem and not the `#eval` it used to shadow),
    and an evaluator request that also lands on the evaluator slot would be answered
    twice. Without `hdisj` a request to 0x0f could be answered by both the pairing
    relation and the evaluator, and the Y-1 agreement obligation reduces to exactly
    this. Both hypotheses are shown load-bearing below. -/theorem honestCalls_functional (product) (evalAddr) (evalRel)
    (hev : ∀ req st r₁ r₂, evalRel req st r₁ -> evalRel req st r₂ -> r₁ = r₂)
    (hdisj : accountKey evalAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat)) :
    ExternalCalls.Functional (honestCalls product evalAddr evalRel) := by
  intro req st r₁ r₂ h₁ h₂
  simp only [honestCalls] at h₁ h₂
  rcases h₁ with e1 | h1
  · rcases h₂ with e2 | h2
    · exact Option.some.inj (e1.symm.trans e2)
    · exact (honestOf_target_not_evalAddr e1 h2.1 hdisj).elim
  · rcases h₂ with e2 | h2
    · exact (honestOf_target_not_evalAddr e2 h1.1 hdisj).elim
    · exact hev req st r₁ r₂ h1.2 h2.2

/-- SATISFIABILITY WITNESS (D-P23, first half) for the functional fold: the two
    hypotheses are jointly inhabited, so the theorem is not an implication with an empty
    antecedent. The evaluator slot at 0x07 (a free address) with the empty relation
    satisfies `hev` trivially and `hdisj` by `decide`. -/
theorem honestCalls_functional_hypotheses_inhabited :
    ∃ (product : Midfall.Yul.PairingProduct) (evalAddr : U256)
      (evalRel : YulSemantics.EVM.CallRequest -> EvmState -> CallResponse -> Prop),
      (∀ req st r₁ r₂, evalRel req st r₁ -> evalRel req st r₂ -> r₁ = r₂) ∧
        accountKey evalAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
        ExternalCalls.Functional (honestCalls product evalAddr evalRel) :=
  ⟨fun _ => true, 0x07, fun _ _ _ => False, fun _ _ _ _ h => h.elim, by decide,
    honestCalls_functional (fun _ => true) 0x07 (fun _ _ _ => False)
      (fun _ _ _ _ h => h.elim) (by decide)⟩

/-- FALSIFICATION (D-P23, second half): `hev` is load-bearing. Drop it and the fold is
    NOT functional - a request to the evaluator address with an always-true relation
    admits every response, and the honest fold cannot answer it (no precompile owns 0x07,
    which is `honestRelations_keys` again), so two different responses both satisfy the
    relation. The address-aliasing hypothesis `hdisj` is what the inl/inr split above
    consumes; this exhibit kills `hev`, and `honestOf_target_not_evalAddr` is the
    statement that `hdisj` cannot be dropped either. -/
theorem honestCalls_not_functional_without_hev :
    ¬ ExternalCalls.Functional
        (honestCalls (fun _ => true) 0x07 (fun _ _ _ => True)) := by
  intro h
  let req : YulSemantics.EVM.CallRequest :=
    { kind := .staticcall, gas := 0, target := 0x07, value := 0, input := [] }
  let ok : CallResponse :=
    { success := true, returndata := [], world := CallWorld.ofState EvmState.init }
  let bad : CallResponse := failResp EvmState.init
  have h1 : (honestCalls (fun _ => true) 0x07 (fun _ _ _ => True)).Call req EvmState.init ok :=
    Or.inr ⟨rfl, trivial⟩
  have h2 : (honestCalls (fun _ => true) 0x07 (fun _ _ _ => True)).Call req EvmState.init bad :=
    Or.inr ⟨rfl, trivial⟩
  have he := h req EvmState.init ok bad h1 h2
  have : ok.success = bad.success := congrArg CallResponse.success he
  exact absurd this (by decide)

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

/-- NOT MECHANICAL, AND NOT TRUE AS STATED - the obstruction, named (P-BRIDGE step 3
    audit finding). The docstring this theorem inherited claimed calleeState reads the
    caller "only through storageOf addr, transientOf addr, address and keccakOf, all of
    which are CallWorld projections". Two of those four are NOT CallWorld components.
    CallWorld (EVMExec.lean:445-468) has exactly eleven fields - selfBalance, balanceOf,
    extCodeOf, extCodeHashOf, nonceOf, storageOf, transientOf, storage, transient, logs,
    selfdestructs - and `env.address` and `env.keccakOf` are not among them. So
    `CallWorld.ofState st = CallWorld.ofState st'` does not pin the caller address or the
    hash oracle, `calleeState` reads both, and a runtime `rt` that calls `caller()` or
    `keccak256` separates two states the hypothesis declares equal. The exhibit below
    proves the separation is real, which is the half a proof of this lemma would need to
    survive. Consequences, both of them load-bearing elsewhere: (i) `honestCalls` cannot
    be discharged world-local with `Evaluator.rel` in the evaluator slot, so
    `honestCalls_worldLocal` cannot be applied to the honest fold as planned; and (ii)
    the attack.md line 36 FIX (responses must depend on the caller only through the world
    projection, or ir_refines is refuted for reasons that are not the optimisation) does
    NOT hold for the evaluator slot as sketched. The repair is a decision, not a proof:
    either widen the projection the relation must respect (add address and keccakOf, which
    changes what WorldLocal claims everywhere), or make calleeState stop reading them
    (which changes the frame the evaluator runs in, and the evaluator DOES read
    keccakOf - the transcript is its whole job). Reported rather than patched. -/
theorem rel_worldLocal (W Lyt addr rt) :
    ∀ req st st' r, CallWorld.ofState st = CallWorld.ofState st' ->
      (rel W Lyt addr rt req st r <-> rel W Lyt addr rt req st' r) := by
  sorry

/-- THE EXHIBIT THAT MAKES THE ABOVE A FINDING AND NOT AN EXCUSE: two states with EQUAL
    CallWorld projections whose caller address and keccak oracle differ. Any `rt` that
    reads `caller()` or `keccak256` separates them, so no hypothesis list that only
    assumes `CallWorld.ofState st = CallWorld.ofState st'` can make the evaluator
    relation world-local. FALSIFICATION (D-P23) of the inherited claim, stated as a
    theorem: delete the two extra fields from the argument and the separation disappears
    with it. -/
theorem world_projection_misses_address_and_keccak :
    ∃ (st st' : EvmState), CallWorld.ofState st = CallWorld.ofState st' ∧
      st.env.address ≠ st'.env.address ∧ st.env.keccakOf ≠ st'.env.keccakOf := by
  refine ⟨{ EvmState.init with env.address := 1, env.keccakOf := fun _ => (0 : U256) },
    { EvmState.init with env.address := 2, env.keccakOf := fun _ => (1 : U256) },
    rfl, ?_, ?_⟩
  · decide
  · intro h
    have : (0 : U256) = 1 := congrFun h ([] : List UInt8)
    exact absurd this (by decide)

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

/-- The syntactic positions the writer scan stands at, as ONE flat index type. The
    AST positions a NO-writers claim has to rule out are an expression, an argument
    list, a statement, a block, and a 'switch' case list; making them constructors of
    one non-recursive type is what lets the scan below be a single function of the
    fuel rather than five mutually recursive ones. Mutual recursion is where this
    walker first went: Lean compiles it through 'WellFounded.fix', which the KERNEL
    cannot reduce, so 'decide' - the only discharge allowed outside Midfall/Instances/
    (D-P20, native_decide confinement) - got stuck and no witness was provable. -/
inductive Scan
  | e  : Expr Op -> Scan
  | es : List (Expr Op) -> Scan
  | s  : Stmt Op -> Scan
  | b  : Block Op -> Scan
  | cs : List (Literal × Block Op) -> Scan

/-- One layer of the writer scan, with the recursive call handed in as an argument
    rather than made. This is the reason the witness theorems below can be closed by
    'decide': 'noWritersStep' is a plain structural function, so the kernel reduces it
    at a variable tail 'rec', and the fuel recursion is the single decreasing 'Nat'
    recursion in 'noWritersScan'. A builtin call nests (mstore(sload(0), 1)); a
    function definition body is scanned (P-13 emits the verifier helpers as 'funDef's
    in the same block as their call sites, so a writer inside a helper is seen); a
    'for' loop has THREE sub-blocks plus its condition; and a 'switch' scans every case
    AND the default, over-approximating the reachable set, which is the sound
    direction for a NO-writers claim. -/
def noWritersStep : Scan -> (Scan -> Bool) -> Bool
  | .e (.lit _), _ => true
  | .e (.var _), _ => true
  | .e (.builtin op args), rec => ! Op.isWriter op && rec (.es args)
  | .e (.call _ args), rec => rec (.es args)
  | .es [], _ => true
  | .es (e :: rest), rec => rec (.e e) && rec (.es rest)
  | .s (.block body), rec => rec (.b body)
  | .s (.funDef _ _ _ body), rec => rec (.b body)
  | .s (.letDecl _ none), _ => true
  | .s (.letDecl _ (some e)), rec => rec (.e e)
  | .s (.assign _ e), rec => rec (.e e)
  | .s (.cond c body), rec => rec (.e c) && rec (.b body)
  | .s (.switch c cases dflt), rec =>
      rec (.e c) && rec (.cs cases) &&
        (match dflt with | none => true | some d => rec (.b d))
  | .s (.forLoop init c post body), rec =>
      rec (.b init) && rec (.e c) && rec (.b post) && rec (.b body)
  | .s (.exprStmt e), rec => rec (.e e)
  | .s .break, _ => true
  | .s .continue, _ => true
  | .s .leave, _ => true
  | .b [], _ => true
  | .b (s :: ss), rec => rec (.s s) && rec (.b ss)
  | .cs [], _ => true
  | .cs ((_, b) :: rest), rec => rec (.b b) && rec (.cs rest)

/-- Fuel-bounded syntactic scan for world writers (R-37: exhaustion answers false,
    so a program that needs more fuel than it gets is reported as MAY write, never
    as clean). LANDS P-BRIDGE STEP 1: this was 'fun _ _ => sorry', and while it was,
    nothing in the tree could satisfy 'NoWriters' at all. -/
def noWritersScan : Nat -> Scan -> Bool
  | 0, _ => false
  | n+1, sc => noWritersStep sc (noWritersScan n)

/-- The block-level face of the scan, the definition 'NoWriters' reads. -/
def noWritersFuel : Nat -> Block Op -> Bool := fun n b => noWritersScan n (.b b)

/-- A block writes no world state if the scan succeeds with some fuel. -/
def NoWriters (b : Block Op) : Prop := ∃ n, noWritersFuel n b = true

/-- Zero fuel never answers clean - R-37 read the other way: the bound is a
    hypothesis the caller pays for, not a free 'True'. -/
theorem noWritersFuel_zero (b : Block Op) : noWritersFuel 0 b = false := rfl

/-- SATISFIABILITY WITNESS (D-P23, first half). The shape every precompile wrapper in
    the generated verifier has - one staticcall bound to a local, then a memory write
    that reads it - is clean, and twelve is not a magic number: the staticcall carries
    six arguments, so the argument-list arm alone walks seven fuel before the second
    statement is reached. -/
theorem NoWriters_staticcall_then_mstore :
    NoWriters (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) :=
  ⟨12, by decide⟩

/-- FALSIFICATION (D-P23, second half), and the reason the walker is not the constant
    'True': a bare sstore is dirty at EVERY fuel, so 'NoWriters' cannot be discharged by
    naming a small bound. The ten-way case split is the shape of that claim - the writer
    sits at depth three, so below three fuel the scan answers false for exhaustion and
    from three up it answers false for the writer; either way there is no clean fuel. -/
theorem not_NoWriters_sstore : ¬ NoWriters (yul% { sstore(0, 1) }) := by
  intro ⟨n, hn⟩
  have key : ∀ m : Nat, noWritersFuel m (yul% { sstore(0, 1) }) = false := by
    intro m
    match m with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl
    | 7 => rfl | 8 => rfl | k+9 => rfl
  rw [key n] at hn
  exact Bool.false_ne_true hn

/-- The writer is seen through a FUNCTION BODY, not just at the top level: P-13 emits
    the verifier helpers as 'funDef's in the same block as their call sites, so a scan
    that only read the top statement list would call this block clean. -/
theorem not_NoWriters_tstore_in_funDef :
    ¬ NoWriters (yul% { function h() { tstore(0, 1) } h() }) := by
  intro ⟨n, hn⟩
  have key : ∀ m : Nat, noWritersFuel m (yul% { function h() { tstore(0, 1) } h() }) = false := by
    intro m
    match m with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl
    | 7 => rfl | 8 => rfl | k+9 => rfl
  rw [key n] at hn
  exact Bool.false_ne_true hn

/-- The writer is seen through a FOR-LOOP BODY (the log family, which is where a
    trace-emitting partial would put it), and a for loop costs four layers of fuel
    before its body is even reached. -/
theorem not_NoWriters_log_in_loop :
    ¬ NoWriters (yul% { for { let i := 0 } lt(i, 4) { i := add(i, 1) } { log1(0, 0, 1) } }) := by
  intro ⟨n, hn⟩
  have key : ∀ m : Nat, noWritersFuel m
      (yul% { for { let i := 0 } lt(i, 4) { i := add(i, 1) } { log1(0, 0, 1) } }) = false := by
    intro m
    match m with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl
    | 7 => rfl | 8 => rfl | k+9 => rfl
  rw [key n] at hn
  exact Bool.false_ne_true hn

/-- The writer is seen NESTED in an argument expression - the mstore(sload(0), 1)
    shape the docstring names - so a scan that only looked at statement heads would
    not do. -/
theorem not_NoWriters_nested_argument :
    ¬ NoWriters (yul% { mstore(add(sstore(0, 1), 1), 2) }) := by
  intro ⟨n, hn⟩
  have key : ∀ m : Nat, noWritersFuel m (yul% { mstore(add(sstore(0, 1), 1), 2) }) = false := by
    intro m
    match m with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl
    | 7 => rfl | 8 => rfl | k+9 => rfl
  rw [key n] at hn
  exact Bool.false_ne_true hn

/-- The 'switch' DEFAULT arm is scanned, not skipped: a writer reachable only through
    the default is still a writer, and the case arm alone ('stop()') is clean. -/
theorem not_NoWriters_switch_default :
    ¬ NoWriters (yul% { switch 2 case 1 { stop() } default { call(0, 1, 2, 3, 4, 5, 6) } }) := by
  intro ⟨n, hn⟩
  have key : ∀ m : Nat, noWritersFuel m
      (yul% { switch 2 case 1 { stop() } default { call(0, 1, 2, 3, 4, 5, 6) } }) = false := by
    intro m
    match m with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl
    | 7 => rfl | 8 => rfl | k+9 => rfl
  rw [key n] at hn
  exact Bool.false_ne_true hn

/-- The two halves fit together: the arm MF-4 below proves reverts is syntactically
    writer-free, so 'Run_worldEq_of_noWriters' says something about it - a failed
    precompile call is allowed to revert and forbidden to touch the world. -/
theorem NoWriters_staticcall_fail_arm :
    NoWriters (yul% {
      let s := staticcall(0, 0x0f, 0, 0, 0, 0)
      if iszero(s) { mstore(0, shl(224, 0x84e81692)) revert(0, 4) }
    }) :=
  ⟨30, by decide⟩

/-- Only staticcalls and no writers means the world is untouched: sstore, tstore,
    the log family, selfdestruct and the create family are the only stepOp world
    writers, and the call family is excluded by NoWriters except staticcall, whose
    response world is never installed (EVMExec.lean:612-616). PROOF OBLIGATION,
    registered in SORRY.md: induction on Step with the isWriter scan. Note the
    decorative hypothesis attack.md line 99 warns about is deliberately absent.

    REACHABILITY, P-BRIDGE step 3: while noWritersFuel was a two-argument hole this
    theorem had NO instances - NoWriters b was unsatisfiable for every b, so the claim
    was vacuously true and uninteresting. That is now false in the useful direction:
    NoWriters_staticcall_then_mstore and NoWriters_staticcall_fail_arm exhibit proved
    instances, so this is a real obligation. What it still needs is (a) subterm closure
    of the scan (a clean block's sub-blocks are clean at reduced fuel) and (b) the
    per-op table 'non-writer op implies WorldEq-preserving' over the 70 local ops plus
    finishCall for staticcall - the same 77-constructor cost class as
    dialect_deterministic, which is why it is reported rather than closed here. -/
theorem Run_worldEq_of_noWriters {c g prog st0 V' st' o}
    (hn : NoWriters prog) (h : Run c g prog st0 V' st' o) : WorldEq st0 st' := by
  sorry


/-! ### MF-4: a failed staticcall reverts with the pinned selector

The cost estimate P-CODEC-C inherited said `finalPairing_spec` is dominated not by the
pairing but by this mapping: FinalPairing.yul:86 and AssemblyHelpers.yul:291-307 turn a
FAILED precompile call into `fail(ERR_PRECOMPILE_FAILED)`, which is
`mstore(0x00, shl(224, sel)); revert(0x00, 0x04)`. Nothing in the vendored semantics does
that for you - a failed staticcall is, at the builtin step, an ordinary `.ok` result
carrying the flag word 0 (`finishCall`, EVMExec.lean:626-633), and the revert is a
separate statement the program executes. So the mapping has to be derived, and it is
derived here: `staticcall_failure_reverts` is the big-step derivation of the whole arm.
MF-4 also records that both failure classes (ERR_PRECOMPILE_FAILED and
ERR_PROOF_REJECTED) map to revert and the spec distinguishes neither (design2 line 160);
the lemma is generic in the selector for exactly that reason. -/


/-- The four bytes a `fail(sel)` arm exposes: `mstore(0x00, shl(224, sel))` writes the
    selector into the TOP four bytes of scratch word 0, and `revert(0x00, 0x04)` reads
    exactly those four back. This is the ABI revert payload, big-endian, and it is what
    makes the two failure classes distinguishable by a caller that decodes revert data.
    Pinned against the keccak-derived selector by `mf4SelectorKats_ok`. -/
def failScratchBytes (sel : U256) : List UInt8 :=
  [byteAt (sel <<< 224) 31, byteAt (sel <<< 224) 30,
    byteAt (sel <<< 224) 29, byteAt (sel <<< 224) 28]

/-- Reading back the four bytes an `mstore` of a left-shifted word wrote: memory is a
    function in this model, so this is the computation the revert payload goes through. -/
theorem readBytes_storeWord_four (mem : Nat -> UInt8) (v : U256) :
    readBytes (storeWord mem 0 v) 0 4 = [byteAt v 31, byteAt v 30, byteAt v 29, byteAt v 28] := rfl

/-- The body of the `fail(sel)` helper, AssemblyHelpers.yul:291-295 verbatim: write the
    selector into scratch word 0 left-aligned, then revert four bytes. -/
def failBody (sel : U256) : Block Op :=
  [ .exprStmt (.builtin Op.mstore [wlit 0, .builtin Op.shl [wlit 224, wlit sel]]),
    .exprStmt (.builtin Op.revert [wlit 0, wlit 4]) ]

/-- The arm: a staticcall bound to `success`, then the fail helper fired on `iszero` of
    it. This is the shape at FinalPairing.yul:86 and at every modexp call site
    (YulGolden.lean:215-216), generic in the six call arguments and the selector so the
    pairing site and the modexp site are instances of the SAME lemma. -/
def staticcallFailArm (gas target inOff inSize outOff outSize sel : U256) : Block Op :=
  [ .letDecl ["success"] (some (.builtin Op.staticcall
      (([gas, target, inOff, inSize, outOff, outSize] : List U256).map wlit))),
    .cond (.builtin Op.iszero [.var "success"]) (failBody sel) ]

/-- `finishCall` never installs for a staticcall, so the caller own halt field is
    whatever it already was - the reason `staticcall` is not a writer op, and the reason
    the success arm below falls through with the halt field untouched. -/
theorem finishCall_staticcall_halted (st : EvmState) (resp : CallResponse)
    (a b c d : Nat) : (finishCall .staticcall st resp a b c d).halted = st.halted := by
  simp [finishCall, touchMemory2, touchMemory]

/-- The `let success := staticcall(...)` statement as one reusable Step term, at any
    enclosing function-scope stack. Both halves of the MF-4 pair share it, and the `funs`
    parameter is what makes that possible: the statement sits inside one `block`, so its
    scope stack is `[[]]` and not `[]`. -/
theorem exec_let_staticcall {c : ExternalCalls} {g : ExternalGas}
    {gas target inOff inSize outOff outSize : U256} {st : EvmState} {resp : CallResponse}
    (funs : FunEnv (Dialect c g))
    (hcall : c.Call { kind := .staticcall, gas := gas, target := target, value := 0,
                      input := readBytes st.memory inOff.toNat inSize.toNat } st resp) :
    Step (Dialect c g) funs [] st
        (.stmt (.letDecl ["success"] (some (.builtin Op.staticcall
          (([gas, target, inOff, inSize, outOff, outSize] : List U256).map wlit)))))
        (.sres (["success"].zip [resp.flag] ++ [])
          (finishCall .staticcall st resp inOff.toNat inSize.toNat outOff.toNat outSize.toNat)
          .normal) := by
  have hargs : Step (Dialect c g) funs [] st
      (.args (([gas, target, inOff, inSize, outOff, outSize] : List U256).map wlit))
      (.eres (.vals [gas, target, inOff, inSize, outOff, outSize] st)) :=
    wlits_eval st [gas, target, inOff, inSize, outOff, outSize]
  have hbi : (Dialect c g).Builtin Op.staticcall
      [gas, target, inOff, inSize, outOff, outSize] st
      (.ok [resp.flag] (finishCall .staticcall st resp inOff.toNat inSize.toNat
        outOff.toNat outSize.toNat)) := ⟨resp, hcall, rfl⟩
  exact Step.letVal (Step.builtinOk hargs hbi) rfl

/-- THE MF-4 STEP LEMMA. Given a staticcall whose external response is a FAILURE, the
    big-step relation yields a halt whose kind is `revert` and whose payload is the four
    pinned selector bytes. Everything the run-related theorems need from Bridge is here:
    the call is answered by the relation parameter (so it works for `honestCalls` and for
    `permissive` alike), the failure is observed by the program own `iszero` test, and the
    revert carries the selector rather than being an empty revert - which is the whole
    point of MF-4. PROVED, not registered: the derivation is about 25 hand-built Step
    terms, and the two environment levels the `Step.block` rule introduces (`hoist`
    prepends a scope, so the arm statements live at `[[]]` and the fail body at
    `[[], []]`) are the part no sketch mentioned. -/
theorem staticcall_failure_reverts {c : ExternalCalls} {g : ExternalGas}
    {gas target inOff inSize outOff outSize sel : U256}
    {st : EvmState} {resp : CallResponse}
    (hcall : c.Call { kind := .staticcall, gas := gas, target := target, value := 0,
                      input := readBytes st.memory inOff.toNat inSize.toNat } st resp)
    (hfail : resp.success = false) :
    ∃ st',
    Run c g (staticcallFailArm gas target inOff inSize outOff outSize sel) st [] st' .halt ∧
      st'.halted = some (.revert, failScratchBytes sel) := by
  have hflag : resp.flag = 0 := by simp [CallResponse.flag, hfail]
  let st₁ := finishCall .staticcall st resp inOff.toNat inSize.toNat outOff.toNat outSize.toNat
  let V₁ : VEnv (Dialect c g) := ["success"].zip [resp.flag] ++ []
  have hlet : Step (Dialect c g) [[]] [] st
      (.stmt (.letDecl ["success"] (some (.builtin Op.staticcall
        (([gas, target, inOff, inSize, outOff, outSize] : List U256).map wlit)))))
      (.sres V₁ st₁ .normal) := exec_let_staticcall [[]] hcall
  have hget : VEnv.get V₁ "success" = some resp.flag := rfl
  have hiszero : (Dialect c g).Builtin Op.iszero [resp.flag] st₁ (.ok [1] st₁) := by
    show builtinWithExternal c ExternalCreates.none g Op.iszero [resp.flag] st₁ (.ok [1] st₁)
    rw [hflag]; rfl
  have hnil : Step (Dialect c g) [[]] V₁ st₁ (.args []) (.eres (.vals [] st₁)) := Step.argsNil
  have hnil2 : Step (Dialect c g) [[], []] V₁ st₁ (.args []) (.eres (.vals [] st₁)) := Step.argsNil
  have hcondexpr : Step (Dialect c g) [[]] V₁ st₁
      (.expr (.builtin Op.iszero [.var "success"])) (.eres (.vals [1] st₁)) :=
    Step.builtinOk (Step.argsCons hnil (Step.var hget)) hiszero
  have hnz : (1 : U256) ≠ (Dialect c g).zero := by show (1 : U256) ≠ 0; decide
  let st₂ := { touchMemory st₁ 0 32 with memory := storeWord st₁.memory 0 (sel <<< 224) }
  have hshlargs : Step (Dialect c g) [[], []] V₁ st₁ (.args [wlit 224, wlit sel])
      (.eres (.vals [224, sel] st₁)) := wlits_eval st₁ [224, sel]
  have hshlbi : (Dialect c g).Builtin Op.shl [224, sel] st₁ (.ok [sel <<< 224] st₁) := rfl
  have hshl : Step (Dialect c g) [[], []] V₁ st₁ (.expr (.builtin Op.shl [wlit 224, wlit sel]))
      (.eres (.vals [sel <<< 224] st₁)) := Step.builtinOk hshlargs hshlbi
  have hMS : Step (Dialect c g) [[], []] V₁ st₁
      (.args [wlit 0, .builtin Op.shl [wlit 224, wlit sel]])
      (.eres (.vals [0, sel <<< 224] st₁)) :=
    Step.argsCons (Step.argsCons hnil2 hshl) (wlit_eval 0)
  have hmsbi : (Dialect c g).Builtin Op.mstore [0, sel <<< 224] st₁ (.ok [] st₂) := rfl
  have hms : Step (Dialect c g) [[], []] V₁ st₁ (.stmt (.exprStmt
      (.builtin Op.mstore [wlit 0, .builtin Op.shl [wlit 224, wlit sel]])))
      (.sres V₁ st₂ .normal) := Step.exprStmt (Step.builtinOk hMS hmsbi)
  let st₃ := { touchMemory st₂ 0 4 with halted := some (.revert, readBytes st₂.memory 0 4) }
  have hRV : Step (Dialect c g) [[], []] V₁ st₂ (.args [wlit 0, wlit 4])
      (.eres (.vals [0, 4] st₂)) := wlits_eval st₂ [0, 4]
  have hrvbi : (Dialect c g).Builtin Op.revert [0, 4] st₂ (.halt st₃) := rfl
  have hrv : Step (Dialect c g) [[], []] V₁ st₂ (.stmt (.exprStmt
      (.builtin Op.revert [wlit 0, wlit 4]))) (.sres V₁ st₃ .halt) :=
    Step.exprStmtHalt (Step.builtinHalt hRV hrvbi)
  have hbody : Step (Dialect c g) [[], []] V₁ st₁ (.stmts (failBody sel))
      (.sres V₁ st₃ .halt) := Step.seqCons hms (Step.seqStop hrv (by simp))
  have hblk : Step (Dialect c g) [[]] V₁ st₁ (.stmt (.block (failBody sel)))
      (.sres V₁ st₃ .halt) :=
    Step.block (D := Dialect c g) (body := failBody sel) (funs := [[]]) hbody
  have hcond : Step (Dialect c g) [[]] V₁ st₁ (.stmt (.cond (.builtin Op.iszero [.var "success"])
      (failBody sel))) (.sres V₁ st₃ .halt) := Step.ifTrue hcondexpr hnz hblk
  have hstmts : Step (Dialect c g) [[]] [] st
      (.stmts (staticcallFailArm gas target inOff inSize outOff outSize sel))
      (.sres V₁ st₃ .halt) := Step.seqCons hlet (Step.seqStop hcond (by simp))
  refine ⟨st₃, Step.block (D := Dialect c g)
      (body := staticcallFailArm gas target inOff inSize outOff outSize sel)
      (funs := []) hstmts, ?_⟩
  have hhalt : st₃.halted = some (.revert, readBytes st₂.memory 0 4) := rfl
  rw [hhalt, readBytes_storeWord_four]
  rfl

/-- FALSIFICATION (D-P23, second half): the failure hypothesis is load-bearing. Hand the
    SAME relation the SAME request a SUCCESS response and the arm does not revert - it
    falls through with `halted = none` and outcome `.normal`. Delete `hfail` from
    `staticcall_failure_reverts` and this refutes its conclusion, so the hypothesis is
    not decoration (the R-30/R-32 pattern). -/
theorem staticcall_success_does_not_revert {c : ExternalCalls} {g : ExternalGas}
    {gas target inOff inSize outOff outSize sel : U256}
    {st : EvmState} {resp : CallResponse}
    (hcall : c.Call { kind := .staticcall, gas := gas, target := target, value := 0,
                      input := readBytes st.memory inOff.toNat inSize.toNat } st resp)
    (hsucc : resp.success = true) (hno : st.halted = none) :
    ∃ st',
    Run c g (staticcallFailArm gas target inOff inSize outOff outSize sel) st [] st' .normal ∧
      st'.halted = none := by
  have hflag : resp.flag = 1 := by simp [CallResponse.flag, hsucc]
  let st₁ := finishCall .staticcall st resp inOff.toNat inSize.toNat outOff.toNat outSize.toNat
  let V₁ : VEnv (Dialect c g) := ["success"].zip [resp.flag] ++ []
  have hlet : Step (Dialect c g) [[]] [] st
      (.stmt (.letDecl ["success"] (some (.builtin Op.staticcall
        (([gas, target, inOff, inSize, outOff, outSize] : List U256).map wlit)))))
      (.sres V₁ st₁ .normal) := exec_let_staticcall [[]] hcall
  have hget : VEnv.get V₁ "success" = some resp.flag := rfl
  have hiszero : (Dialect c g).Builtin Op.iszero [resp.flag] st₁ (.ok [0] st₁) := by
    show builtinWithExternal c ExternalCreates.none g Op.iszero [resp.flag] st₁ (.ok [0] st₁)
    rw [hflag]; rfl
  have hnil : Step (Dialect c g) [[]] V₁ st₁ (.args []) (.eres (.vals [] st₁)) := Step.argsNil
  have hcondexpr : Step (Dialect c g) [[]] V₁ st₁
      (.expr (.builtin Op.iszero [.var "success"])) (.eres (.vals [0] st₁)) :=
    Step.builtinOk (Step.argsCons hnil (Step.var hget)) hiszero
  have hz : (0 : U256) = (Dialect c g).zero := rfl
  have hcond : Step (Dialect c g) [[]] V₁ st₁ (.stmt (.cond (.builtin Op.iszero [.var "success"])
      (failBody sel))) (.sres V₁ st₁ .normal) := Step.ifFalse hcondexpr hz
  have hrest : Step (Dialect c g) [[]] V₁ st₁ (.stmts [.cond (.builtin Op.iszero [.var "success"])
      (failBody sel)]) (.sres V₁ st₁ .normal) := Step.seqCons hcond Step.seqNil
  have hstmts : Step (Dialect c g) [[]] [] st
      (.stmts (staticcallFailArm gas target inOff inSize outOff outSize sel))
      (.sres V₁ st₁ .normal) := Step.seqCons hlet hrest
  refine ⟨st₁, Step.block (D := Dialect c g)
      (body := staticcallFailArm gas target inOff inSize outOff outSize sel)
      (funs := []) hstmts, ?_⟩
  rw [finishCall_staticcall_halted, hno]

/-- The pinned ERR_PRECOMPILE_FAILED selector: bytes4(keccak256("PrecompileFailed()")),
    the constant the generated contract emits (Templates.lean:180) and the keccak-derived
    pin in Common/Keccak.lean:53. Tied to the hash by `mf4SelectorKats_ok`, not assumed:
    the kernel cannot reduce Keccak-f[1600] (Common/Keccak.lean:19-21), so the tie is a
    computed gate while the use is a theorem. -/
def errPrecompileFailed : U256 := 0x84e81692

/-- The pinned selector really does produce the four bytes the contract revert data
    carries: `0x84e81692` big-endian, i.e. exactly the ABI selector. -/
theorem failScratchBytes_precompileFailed :
    failScratchBytes errPrecompileFailed = [0x84, 0xe8, 0x16, 0x92] := rfl

/-- The permissive fold answers every request with the failed response: a failure needs
    no justification (gas is unmodelled, a precompile may be missing on another
    deployment), which is exactly what makes it the witness relation below. -/
theorem permissive_failResp_call (req : YulSemantics.EVM.CallRequest) (st : EvmState) :
    (permissive ExternalCalls.none).Call req st (failResp st) :=
  ⟨rfl, fun h => absurd h (by simp [failResp])⟩

/-- SATISFIABILITY WITNESS (D-P23, first half). The hypotheses of the step lemma are
    inhabited and so is its conclusion, at a relation that is actually part of the layer:
    `permissive ExternalCalls.none` answers every request with `failResp`, which is a
    failure, and the run of the arm from `EvmState.init` really does halt with the four
    pinned bytes. Without this the step lemma could be an implication with an empty
    antecedent. -/
theorem staticcall_failure_reverts_witness :
    ∃ (st stp : EvmState),
      Run (permissive ExternalCalls.none) (ExternalGas.ofFun fun _ => 0)
        (staticcallFailArm 0 0x0f 0 0 0 0 errPrecompileFailed) st [] stp .halt ∧
        stp.halted = some (.revert, [0x84, 0xe8, 0x16, 0x92]) := by
  have hcall : (permissive ExternalCalls.none).Call
      { kind := .staticcall, gas := 0, target := 0x0f, value := 0,
        input := readBytes EvmState.init.memory 0 0 } EvmState.init (failResp EvmState.init) :=
    permissive_failResp_call _ _
  obtain ⟨stp, hr, hh⟩ := staticcall_failure_reverts
    (gas := 0) (target := 0x0f) (inOff := 0) (inSize := 0) (outOff := 0) (outSize := 0)
    (sel := errPrecompileFailed) (st := EvmState.init) (resp := failResp EvmState.init)
    hcall rfl
  exact ⟨EvmState.init, stp, hr, by rw [← failScratchBytes_precompileFailed]; exact hh⟩

/-- The revert payload really is FOUR bytes, not the whole 32-byte scratch word: a
    `revert(0x00, 0x04)` that read 32 bytes would carry the selector plus 28 zero bytes
    and no ABI decoder would accept it. The second conjunct is the falsification - a
    scan that wrote the selector unshifted would expose the wrong four bytes. -/
theorem failScratchBytes_length (sel : U256) : (failScratchBytes sel).length = 4 := rfl

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

/-- MF-4, computed: the selector the step lemma reverts with IS the keccak-derived
    error selector the generated contract emits, not a pasted constant. The kernel cannot
    reduce Keccak-f[1600] (Common/Keccak.lean:19-21), so this tie can only be a computed
    gate - which is why the USE of the selector is a theorem
    (`staticcall_failure_reverts_witness`) and the TIE to the hash is this #eval. The last
    two lines are the falsifications: a selector written unshifted, and a payload read
    32 bytes wide instead of four, both fail this gate.
    -/
def mf4SelectorKats_ok : Bool :=
  errPrecompileFailed.toNat == 0x84e81692 &&
    Midfall.abiSelector "PrecompileFailed()" == (0x84e81692 : BitVec 32) &&
    failScratchBytes errPrecompileFailed == [0x84, 0xe8, 0x16, 0x92] &&
    (failScratchBytes errPrecompileFailed).length == 4 &&
    failScratchBytes 0xc3b0d8cd == [0xc3, 0xb0, 0xd8, 0xcd] &&
    ! (failScratchBytes errPrecompileFailed == [0x92, 0x16, 0xe8, 0x84]) &&
    ! (failScratchBytes errPrecompileFailed).drop 4 == [0]

#eval mf4SelectorKats_ok   -- expect true

/-- The writer scan, computed at a shape the theorems do not name: a value-bearing call
    is a writer (the response world IS installed for it, finishCall EVMExec.lean:626-633),
    a staticcall is not, and a writer buried two levels down in a switch case is seen.
    The falsification half is the last line: an empty block is clean, so the scan is not
    answering false everywhere. -/
def noWritersScanKats_ok : Bool :=
  noWritersFuel 40 (yul% { let a := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, a) }) &&
    ! noWritersFuel 40 (yul% { let a := call(1, 2, 3, 4, 5, 6, 7) pop(a) }) &&
    ! noWritersFuel 40 (yul% { switch 1 case 1 { let z := 3 sstore(0, z) } }) &&
    noWritersFuel 40 (yul% { switch 1 case 1 { let z := 3 mstore(0, z) } }) &&
    noWritersFuel 40 (yul% { }) &&
    ! noWritersFuel 0 (yul% { })

#eval noWritersScanKats_ok   -- expect true

end Midfall.Yul.Bridge