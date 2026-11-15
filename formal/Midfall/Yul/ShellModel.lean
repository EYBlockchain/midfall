-- |
-- Midfall.Yul.ShellModel
--
-- P-M8-SHELL (docs/plans/P-M8-SHELL.md), the first of the two files docs/PLAN.md section 7
-- names as required M8 deliverables and which had never been built - docs/REVIEW.md R-65,
-- human decision docs/design.md D-P38.
--
-- WHAT FABLE ASKED FOR, verbatim (docs/PLAN.md line 224):
--
--   "`ShellModel.lean`: a Yul model of solc's dispatcher for `verifyProof(bytes,uint256[])`,
--    covering selector 0x1e8e1e13, the callvalue check, ABI bounds checks, and binding the
--    locals `vk` and `quotientEvaluator` from immutables."
--
-- and the property the OTHER required file will cite (line 228):
--
--   "`IRCheck.lean` is a verified checker: `irCheck ir L = true -> ObsEquiv ir (ShellModel.wrap L)`."
--
-- So this file has two jobs: the dispatcher model, and `wrap` - the predicate the checker's
-- theorem compares the imported artifact against. `IRCheck.lean` cannot be stated until this
-- exists, which is why this package runs first.
--
-- WHY IT ALSO CLOSES `shell_unfolds`. `Midfall/Lowering/Surface.lean` pins
-- `shell.codeBlock = L.headGuard ++ bindLocals ++ L.main` (R-58 F3). That pin is TRUE of the
-- model it names and FALSE of the artifact, and the field doc says so: "A real solc dispatcher
-- does not satisfy the equality (it decodes ABI heads and tests the selector first), so when M8
-- imports the via-ir object this pin must be restated as design2 had it: the verifyProof ARM of
-- shell runs headGuard ++ bindLocals ++ main from the dispatcher memory." The concrete
-- difference, measured against the pinned `ir` (Midfall/Yul/ImportSolcIR.lean, deployed runtime
-- block, first three of 28 top-level statements):
--
--   * the artifact opens `mstore(64, memoryguard(128))`; the model opens
--     `if gt(mload(0x40), 0x1000) { revert(0,0) }` - a head guard, not a prologue;
--   * the artifact tests `iszero(lt(calldatasize(), 4))`, reads
--     `shift_right_224_unsigned(calldataload(0))` and `switch`es on it; the model tests nothing;
--   * the artifact's `verifyProof` arm rejects a call carrying value, ABI-decodes the two
--     dynamic heads with four bounds tests each, and only then runs the assembly;
--   * the artifact ends the dispatch chain with `revert_error_42b3...()`, i.e. `revert(0,0)`,
--     so an unroutable call reverts; the model runs the verifier body unconditionally.
--
-- The last line is the bug this file exists to fix: **a wrong-selector calldata reverts in the
-- artifact and runs the verifier in the model.** It is not cosmetic - the model described the
-- wrong program at its entry point. `wrong_selector_reverts` below is that fact as a theorem
-- about the new model, and `old_model_runs_the_verifier_on_a_wrong_selector_calldata` is the
-- same fact about the old one, so the difference is written down and not merely asserted.
--
-- D-P30: EVERY STATEMENT HERE IS BUILT FROM THE VENDORED AST. No Yul text is emitted or parsed;
-- the block is a `List (Stmt EVM.Op)` assembled from `Stmt`/`Expr` constructors, which is what
-- the vendored big-step semantics runs. The artifact text beside it
-- (`Midfall/Yul/solc-ir-Halo2Verifier.yul`) is the reference this model is compared against, not
-- the deliverable.
--
-- WHAT THE MODEL DOES NOT CLAIM, stated because a model that hides its gaps is worse than no
-- model:
--
--   1. It is a model of the DISPATCHER, not of the verifier body. The arm runs an opaque
--      `body : YulBlock`; which block that is, is the Surface's business (`armBody`).
--   2. solc routes every abort through a named `revert_error_<digest>()` function and every
--      dispatch arm through a named `external_fun_*()`. The model inlines `revert(0,0)` at the
--      guard sites and the fall-through. That is a structural difference the artifact's own
--      naming hides: Fable's `irCheck` is specified as "alpha-equivalence modulo constant
--      substitution and solc renames", and a call to a one-statement function whose body is
--      `revert(0,0)` is exactly the shape that definition has to identify. Recorded here
--      because it is `IRCheck.lean`'s problem to discharge, not this file's.
--   3. The artifact's switch has a second case, `AUTHORIZED_VK()` at 0x42b72597, which returns
--      32 bytes. It is modelled (`authorizedVkArm`) so that a getter calldata does not
--      silently revert here and return there; the artifact's other getters, and any function a
--      render adds to the ABI, are NOT modelled.
--   4. The immutables are read under the keys `DeploymentW` pins
--      (`AUTHORIZED_VK`, `AUTHORIZED_QUOTIENT`); the artifact reads `loadimmutable("5")`, the
--      linker symbol the constructor's `setimmutable` wrote. The key strings are therefore a
--      deployment fact the model carries as a constant and `IRCheck` has to relate.
--
-- WHY THE FALSIFICATIONS ARE THEOREMS AND NOT GATES. D-P23: a claim needs both halves proved -
-- the statement, and a witness that its hypotheses are satisfiable. Each of the three
-- falsifications below is a `Run` derivation ending in `some (.revert, [])`, each carries its
-- witness calldata as a `def` with the hypotheses discharged by `rfl`, and each carries a
-- load-bearing refutation showing that the hypothesis it names is the one that fires.

import Midfall.Lowering.Surface
import Midfall.Yul.Builtins
import Midfall.Yul.ImportSolcIR
import YulSemantics.BigStep

namespace Midfall.Yul.ShellModel
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Yul Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [AdmissiblePairing G₁ G₂ Gₜ]

/-! ### 1. The constants the dispatcher is built from -/

/-- `verifyProof(bytes,uint256[])`'s 4-byte selector, as the artifact's `case` label has it:
    `shift_right_224_unsigned(calldataload(0))` produces the 4 bytes left-aligned in a word, so
    the value switched on IS the selector. Tied to `Midfall.Generator.fnSigVerifyProof` by
    `shellModelKats_ok` below rather than assumed. -/
def selectorVerifyProof : U256 := 0x1e8e1e13

/-- The second case label the artifact's switch carries: `AUTHORIZED_VK()`, a view getter that
    returns the 32-byte address. Modelled so the wrong-selector falsification is about a
    selector nothing routes, not about a getter. -/
def selectorAuthorizedVk : U256 := 0x42b72597

/-- The free-memory-pointer address. The artifact's prologue stores `memoryguard(128)` here. -/
def fmpAddr : U256 := 0x40

/-- The reservation the pinned `ir` asks for: `memoryguard(128)`. DECISION 1 of
    `Midfall/Yul/ImportSolcIR.lean` records that `irOptimized` says 0x08e0 and that the deployed
    bytes agree with the optimizer, so this constant is the trusted hop showing up in a number. -/
def irMemoryguardReservation : U256 := 128

/-- Where the ABI heads start: after the 4 selector bytes. -/
def headStart : U256 := 4

/-- The head region of `verifyProof(bytes,uint256[])`: two dynamic heads, 32 bytes each. The
    artifact's `abi_decode_tuple` tests `slt(sub(dataEnd, headStart), 64)`. -/
def tupleHeadBytes : U256 := 64

/-- solc's ABI length ceiling: a dynamic length or offset above this reverts before it is used,
    which is what makes `add(offset, 32)` and `add(pos, len)` non-overflowable. -/
def abiLengthCeiling : U256 := 0xffffffffffffffff

/-- The dynamic-head offset the artifact's own head guard expects for the proof:
    `eq(calldataload(0x04), 0x40)` inside `fun_verifyProof_291`. 0x40 = 64 = 4 + 2 heads... no:
    it is the offset measured FROM `headStart`, so the proof data begins at 4 + 0x40 = 68, the
    first byte after the two heads. -/
def proofOffsetFaithful : U256 := 0x40

/-- The immutable key the VK is bound under. `DeploymentW.vkImm` pins
    `shellLayout.immutable (litValue (.string "AUTHORIZED_VK")) = vkAddr`, so the model reads
    the key the deployment already promises. -/
def vkImmutableKey : String := "AUTHORIZED_VK"

/-- The twin of `vkImmutableKey` for a render that externalises the quotient evaluator
    (`DeploymentW.qImm`). The pinned deployed profile is an inline-quotient render and emits
    neither the getter nor this binding; the model carries it because PLAN section 7 names
    `quotientEvaluator` as one of the two locals the dispatcher binds. -/
def quotientImmutableKey : String := "AUTHORIZED_QUOTIENT"

/-- A Yul word literal: `Bridge.wlit`, because the AST stores a `Nat` and the dialect reads a
    `BitVec 256` back, and `wlit_val` is the one cast that discrepancy needs. -/
abbrev w (v : U256) : Expr EVM.Op := wlit v

/-- The single abort the model uses everywhere a guard fires: `revert(0, 0)`, which is what every
    one of the artifact's `revert_error_*()` bodies is. Deviation 2 of the header. -/
def revert00 : Stmt EVM.Op := Stmt.exprStmt (Expr.builtin Op.revert [w 0, w 0])

/-- The state `revert(0,0)` leaves: `stepOp`'s own clause (`EVMExec.lean:881`), named so the
    falsifications can say where they end. -/
def revertState (st : EvmState) : EvmState :=
  { touchMemory st 0 0 with halted := some (.revert, readBytes st.memory 0 0) }

/-- A guard: `if test { revert(0,0) }`. Every check the dispatcher performs is this shape, which
    is what makes the three falsifications instances of one lemma. -/
def guard (test : Expr EVM.Op) : Stmt EVM.Op := Stmt.cond test [revert00]

/-! ### 2. The dispatcher -/

/-- The prologue: `mstore(0x40, memoryguard(128))`, statement 1 of the artifact's runtime block
    and the reason `DeploymentW.memguard` exists. -/
def prologue : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr, Expr.builtin Op.memoryguard
    [w irMemoryguardReservation]])]

/-- `iszero(lt(calldatasize(), 4))`: the artifact's test for "there is at least a selector".
    Note the polarity - the body runs when the size IS at least 4. -/
def calldatasizeTest : Expr EVM.Op :=
  Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.builtin Op.calldatasize [], w 4]]

/-- `shift_right_224_unsigned(calldataload(0))`: the selector read. -/
def selectorExpr : Expr EVM.Op :=
  Expr.builtin Op.shr [w 224, Expr.builtin Op.calldataload [w 0]]

/-- The word the dispatcher routes on, as a function of the frame: what `selectorExpr` evaluates
    to in state `st`. Naming it is what lets the falsifications be stated about a calldata
    instead of about a `Step` derivation. -/
def selectorWord (st : EvmState) : U256 := wordFrom st.env.calldata 0 >>> 224

/-- `let selector := shift_right_224_unsigned(calldataload(0))`. -/
def selectorDecl : Stmt EVM.Op := Stmt.letDecl ["selector"] (some selectorExpr)

/-- The callvalue check: `verifyProof` is `external view`, so solc emits
    `if callvalue() { revert_error_ca66...() }` as the FIRST statement of the arm. -/
def callvalueGuard : Stmt EVM.Op := guard (Expr.builtin Op.callvalue [])

/-- The head-region length test: `if slt(sub(calldatasize(), 4), 64) revert`. -/
def headLengthGuard : Stmt EVM.Op :=
  guard (Expr.builtin Op.slt [Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart],
    w tupleHeadBytes])

/-- `let proofOffset := calldataload(add(headStart, 0))`, the first dynamic head. -/
def proofOffsetDecl : Stmt EVM.Op :=
  Stmt.letDecl ["proofOffset"] (some (Expr.builtin Op.calldataload
    [Expr.builtin Op.add [w headStart, w 0]]))

/-- `let instancesOffset := calldataload(add(headStart, 32))`, the second dynamic head. -/
def instancesOffsetDecl : Stmt EVM.Op :=
  Stmt.letDecl ["instancesOffset"] (some (Expr.builtin Op.calldataload
    [Expr.builtin Op.add [w headStart, w 32]]))

/-- An offset above the ABI ceiling is rejected before it is added to anything. -/
def offsetCeilingGuard (x : String) : Stmt EVM.Op :=
  guard (Expr.builtin Op.gt [Expr.var x, w abiLengthCeiling])

/-- The data position solc computes for a head: `add(headStart, offset)`. -/
def dataPos (offset : String) : Expr EVM.Op :=
  Expr.builtin Op.add [w headStart, Expr.var offset]

/-- `if iszero(slt(add(dataPos, 0x1f), calldatasize())) revert`: there must be room for the
    length word the decoder is about to read. -/
def lengthPresentGuard (offset : String) : Stmt EVM.Op :=
  guard (Expr.builtin Op.iszero [Expr.builtin Op.slt
    [Expr.builtin Op.add [dataPos offset, w 31], Expr.builtin Op.calldatasize []]])

/-- `let proofLength := calldataload(add(headStart, proofOffset))`. -/
def proofLengthDecl : Stmt EVM.Op :=
  Stmt.letDecl ["proofLength"] (some (Expr.builtin Op.calldataload [dataPos "proofOffset"]))

/-- `let instancesLength := calldataload(add(headStart, instancesOffset))`. -/
def instancesLengthDecl : Stmt EVM.Op :=
  Stmt.letDecl ["instancesLength"] (some (Expr.builtin Op.calldataload [dataPos "instancesOffset"]))

/-- The tail test: `if gt(add(add(dataPos, 32), mul(length, stride)), calldatasize()) revert`.
    `stride` is 1 for `bytes` and 32 for `uint256[]`, exactly as the artifact emits it. THIS is
    the check a truncated proof argument trips. -/
def tailGuard (offset length : String) (stride : U256) : Stmt EVM.Op :=
  guard (Expr.builtin Op.gt
    [Expr.builtin Op.add [Expr.builtin Op.add [dataPos offset, w 32],
      Expr.builtin Op.mul [Expr.var length, w stride]],
      Expr.builtin Op.calldatasize []])

/-- The two locals PLAN section 7 names, bound from the immutables. In the artifact the VK
    binding is `let _2 := loadimmutable("5"); let var_vk_286 := _2` inside `fun_verifyProof`,
    i.e. after the ABI decode and before the assembly block - which is where they are here. -/
def bindLocalsFromImmutables : YulBlock :=
  [Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string vkImmutableKey)])),
   Stmt.letDecl ["quotientEvaluator"] (some (Expr.builtin Op.loadimmutable
     [Expr.lit (.string quotientImmutableKey)]))]

/-- The ABI decode of `verifyProof(bytes,uint256[])` as the artifact emits it: one tuple guard,
    then per dynamic argument an offset read, an offset ceiling test, a length-presence test, a
    length read, a length ceiling test and a tail test. -/
def abiDecode : YulBlock :=
  [headLengthGuard, proofOffsetDecl, offsetCeilingGuard "proofOffset",
    lengthPresentGuard "proofOffset", proofLengthDecl,
    offsetCeilingGuard "proofLength", tailGuard "proofOffset" "proofLength" 1,
    instancesOffsetDecl, offsetCeilingGuard "instancesOffset",
    lengthPresentGuard "instancesOffset", instancesLengthDecl,
    offsetCeilingGuard "instancesLength", tailGuard "instancesOffset" "instancesLength" 32]

/-- The `verifyProof` arm: callvalue check, ABI decode, the two immutable bindings, then the
    program the Surface lowered. `body` is opaque here on purpose: which block it is, is
    `armBody`'s business, and no falsification below reaches it. -/
def verifyProofArm (body : YulBlock) : YulBlock :=
  callvalueGuard :: abiDecode ++ bindLocalsFromImmutables ++ body

/-- The `AUTHORIZED_VK()` arm, modelled for shape fidelity: callvalue check, then the getter's
    `loadimmutable` and the 32-byte return the artifact's `abi_encode_tuple_t_address` emits.
    `allocate_unbounded()` is `mload(64)`, which the prologue has just written. -/
def authorizedVkArm : YulBlock :=
  [callvalueGuard,
   Stmt.letDecl ["rval"] (some (Expr.builtin Op.loadimmutable
     [Expr.lit (.string vkImmutableKey)])),
   Stmt.letDecl ["memPos"] (some (Expr.builtin Op.mload [w fmpAddr])),
   Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "memPos", Expr.var "rval"]),
   Stmt.exprStmt (Expr.builtin Op.ret [Expr.var "memPos", w 32])]

/-- The switch's case list, as data: the two labels the artifact's `switch` carries and the
    block each routes to. Named so the lemmas about `selectSwitch` below talk about the same
    list the model runs. -/
def caseList (body : YulBlock) : List (Literal × YulBlock) :=
  [(Literal.number selectorVerifyProof.toNat, verifyProofArm body),
   (Literal.number selectorAuthorizedVk.toNat, authorizedVkArm)]

/-- The switch. `default` is absent, which `selectSwitch` reads as the empty block - the same
    thing the artifact's literal `default {}` is. -/
def selectorSwitch (body : YulBlock) : Stmt EVM.Op :=
  Stmt.switch (Expr.var "selector") (caseList body) none

/-- THE DISPATCHER MODEL. Three top-level statements - prologue, the guarded selector switch,
    and the fall-through abort - which is exactly the shape of the artifact's runtime block:
    everything after those three is a function definition, and a definition is a `Step.funDef`
    no-op on the path to a halt. -/
def dispatcher (body : YulBlock) : YulBlock :=
  prologue ++ [Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body], revert00]

/-- The dispatcher as a `YulObject`, i.e. the thing `Surface.shell` should carry once M8 lands.
    The sub-objects and data segments are the shell's own: the model changes the ENTRY PATH, and
    `shellLayout`'s data and immutable maps are what the entry path reads. (`object` is a Lean
    keyword, hence the name.) -/
def dispatcherObject (shell : YulObject) (body : YulBlock) : YulObject :=
  Object.mk shell.name (dispatcher body) shell.subObjects shell.dataSegs

/-- The block the `verifyProof` arm runs: what `shell_unfolds` names today, and what design2
    wanted the pin to say about the ARM rather than about the whole shell. -/
def armBody (S : Surface p G₁ G₂ Gₜ) : YulBlock := S.L.headGuard ++ S.bindLocals ++ S.L.main

/-- The dispatcher model of a Surface. -/
def dispatcherCode (S : Surface p G₁ G₂ Gₜ) : YulBlock := dispatcher (armBody S)

/-- **`ShellModel.wrap`** - the function PLAN section 7 line 228 cites:
    `irCheck ir L = true -> ObsEquiv ir (ShellModel.wrap L)`.

    SIGNATURE, and why it is not the one-letter function the sketch implies. `ObsEquiv` compares
    two predicates on `Obs` (`Lowering/Surface.lean`), and the left-hand side
    `RunContractIR S W H ir irLyt cd c g` is already a curried `Obs -> Prop` carrying a Surface,
    a world, a hash, a layout, a calldata, a call relation and a gas oracle. For the comparison
    to typecheck at all, `wrap` has to be a predicate on the same observation and the same frame.
    `L` reaches it as `S.L` - the Surface is where `L` lives in this tree - and the remaining
    arguments are `RunShell`'s, so that `wrap` is a replacement for `RunShell` and not a third
    shape nobody can transport between. -/
def wrap (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g (dispatcherCode S) (callState W S.shellLayout H cd)
    V' obs.state obs.outcome

/-- The run relation of the model, in the frame-independent form the falsifications are stated
    in: the dispatcher of `body` from the frame `st0`. `wrap` is this at a Surface's frame. -/
def runOn (body : YulBlock) (st0 : EvmState) (c : ExternalCalls) (g : ExternalGas)
    (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g (dispatcher body) st0 V' obs.state obs.outcome

/-! ### 3. The step engine -/

/-- The open dialect the model runs in, named. The same dialect `RunContractIR` and `RunShell`
    quantify over (`Bridge.Dialect`), so nothing here needs a second semantics. -/
abbrev OD (c : ExternalCalls) (g : ExternalGas) : YulSemantics.Dialect := Bridge.Dialect c g

variable {c : ExternalCalls} {g : ExternalGas}

/-- `calldatasize()` as the dialect sees it: the length of the frame's calldata widened to a
    word. The dispatcher compares words, not naturals, so the falsifications' size hypotheses
    are stated about this. -/
def sizeWord (st : EvmState) : U256 := BitVec.ofNat 256 st.env.calldata.length

/-- The entry frame of a calldata carrying a value: the fields the dispatcher's entry path reads,
    and nothing else. `callState W Lyt H cd` is this at value 0 with the deployment's world and
    layout installed, which is what makes the falsifications transferable. -/
def frame (cd : List UInt8) (v : U256) : EvmState :=
  { EvmState.init with env := { EvmState.init.env with calldata := cd, callvalue := v } }

/-- The prologue's post-state, named once. `Builtins.prologuePostFrom` is P-VEND's definition of
    the same state, so the model does not carry a second one. -/
abbrev stAfterPrologue (st₀ : EvmState) : EvmState := Midfall.Yul.Builtins.prologuePostFrom st₀

/-- A builtin with no arguments. -/
theorem bi0 {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} {op : EVM.Op} {v : U256}
    (hb : (OD c g).Builtin op [] st (.ok [v] st)) :
    Step (OD c g) funs V st (.expr (Expr.builtin op [])) (.eres (.vals [v] st)) :=
  Step.builtinOk Step.argsNil hb

/-- One-argument builtin application. -/
theorem bi1 {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st st' st₂ : EvmState} {op : EVM.Op}
    {e : Expr EVM.Op} {v u : U256}
    (he : Step (OD c g) funs V st (.expr e) (.eres (.vals [v] st')))
    (hb : (OD c g).Builtin op [v] st' (.ok [u] st₂)) :
    Step (OD c g) funs V st (.expr (Expr.builtin op [e])) (.eres (.vals [u] st₂)) :=
  Step.builtinOk (Step.argsCons Step.argsNil he) hb

/-- Two-argument builtin application. Arguments evaluate RIGHT-TO-LEFT (`argsCons` takes the
    tail first) and the values come back in source order, so the first hypothesis below is the
    one about `e₂`. -/
theorem bi2 {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st s₁ s₂ : EvmState} {op : EVM.Op}
    {e₁ e₂ : Expr EVM.Op} {v₁ v₂ u : U256}
    (he₂ : Step (OD c g) funs V st (.expr e₂) (.eres (.vals [v₂] s₁)))
    (he₁ : Step (OD c g) funs V s₁ (.expr e₁) (.eres (.vals [v₁] s₂)))
    (hb : (OD c g).Builtin op [v₁, v₂] s₂ (.ok [u] s₂)) :
    Step (OD c g) funs V st (.expr (Expr.builtin op [e₁, e₂])) (.eres (.vals [u] s₂)) :=
  Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil he₂) he₁) hb

/-- Three-argument builtin application, same right-to-left convention. -/
theorem bi3 {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st s₁ s₂ s₃ : EvmState} {op : EVM.Op}
    {e₁ e₂ e₃ : Expr EVM.Op} {v₁ v₂ v₃ u : U256}
    (he₃ : Step (OD c g) funs V st (.expr e₃) (.eres (.vals [v₃] s₁)))
    (he₂ : Step (OD c g) funs V s₁ (.expr e₂) (.eres (.vals [v₂] s₂)))
    (he₁ : Step (OD c g) funs V s₂ (.expr e₁) (.eres (.vals [v₁] s₃)))
    (hb : (OD c g).Builtin op [v₁, v₂, v₃] s₃ (.ok [u] s₃)) :
    Step (OD c g) funs V st (.expr (Expr.builtin op [e₁, e₂, e₃])) (.eres (.vals [u] s₃)) :=
  Step.builtinOk (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil he₃) he₂) he₁) hb

/-- A variable reference. -/
theorem varS {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} {x : Ident} {v : U256}
    (h : VEnv.get V x = some v) :
    Step (OD c g) funs V st (.expr (Expr.var x)) (.eres (.vals [v] st)) := Step.var h

/-- `revert(0, 0)` halts from any state, with the empty return data. -/
theorem revert00_builtin {st : EvmState} :
    (OD c g).Builtin Op.revert [0, 0] st (.halt (revertState st)) := rfl

/-- `revert(0,0)` as a statement step. -/
theorem revert00_step {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.stmt revert00) (.sres V (revertState st) .halt) :=
  Step.exprStmtHalt (Step.builtinHalt (wlits_eval st [0, 0]) revert00_builtin)

theorem halt_ne_normal : (Outcome.halt : Outcome) ≠ .normal :=
  fun h => Outcome.noConfusion h

/-- `restore V V = V`: a block that introduces no bindings leaves the environment alone.
    `restore outer inner = inner.drop (inner.length - outer.length)`, and `n - n = 0` is not
    reducible for a symbolic `n`, which is why the guard lemma below rewrites through this
    rather than closing by `rfl`. -/
theorem restore_self {V : VEnv (OD c g)} : restore V V = V := by
  show V.drop (V.length - V.length) = V
  rw [Nat.sub_self]
  rfl

/-- **THE GUARD LEMMA EVERY FALSIFICATION USES.** A guard whose test fires aborts the run:
    `if test { revert(0,0) }` where `test` evaluates to a non-zero word. -/
theorem guardReverts {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st st' : EvmState}
    {test : Expr EVM.Op} {v : U256}
    (h : Step (OD c g) funs V st (.expr test) (.eres (.vals [v] st'))) (hv : v ≠ 0) :
    Step (OD c g) funs V st (.stmt (guard test)) (.sres V (revertState st') .halt) := by
  have key : Step (OD c g) funs V st (.stmt (guard test))
      (.sres (restore V V) (revertState st') .halt) :=
    Step.ifTrue h hv (Step.block (D := OD c g) (body := [revert00]) (funs := funs)
        (V := V) (st := st') (Vb := V) (stb := revertState st') (o := .halt)
        (Step.seqStop (D := OD c g) (funs := [] :: funs) (V := V) (st := st') (rest := [])
          (s := revert00) (V1 := V) (st1 := revertState st') (o := .halt)
          revert00_step halt_ne_normal))
  rw [restore_self] at key
  exact key

/-- The dual: a guard whose test does not fire is a no-op that keeps the frame. -/
theorem guardPasses {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st st' : EvmState}
    {test : Expr EVM.Op}
    (h : Step (OD c g) funs V st (.expr test) (.eres (.vals [0] st'))) :
    Step (OD c g) funs V st (.stmt (guard test)) (.sres V st' .normal) :=
  Step.ifFalse h rfl

/-! ### Evaluating the dispatcher's own tests -/

/-- `mstore(0x40, memoryguard(128))`: the prologue, from an arbitrary frame, in the open
    dialect. The same two `stepOp` graphs P-VEND derived for the closed dialect, and the same
    post-state: `stAfterPrologue` IS `Builtins.prologuePostFrom`. -/
theorem prologueExprStep {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st₀ : EvmState} :
    Step (OD c g) funs V st₀
      (.expr (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]]))
      (.eres (.vals [] (stAfterPrologue st₀))) := by
  refine Step.builtinOk (D := OD c g) ?_
    (rfl : (OD c g).Builtin Op.mstore [fmpAddr, irMemoryguardReservation] st₀
      (.ok [] (stAfterPrologue st₀)))
  refine Step.argsCons (D := OD c g) ?_ (wlit_eval fmpAddr)
  refine Step.argsCons (D := OD c g) (Step.argsNil (D := OD c g)) ?_
  exact bi1 (funs := funs) (V := V) (st := st₀) (st' := st₀) (op := Op.memoryguard)
    (e := w irMemoryguardReservation) (v := irMemoryguardReservation)
    (u := irMemoryguardReservation) (wlit_eval irMemoryguardReservation)
    (rfl : (OD c g).Builtin Op.memoryguard [irMemoryguardReservation] st₀
      (.ok [irMemoryguardReservation] st₀))

/-- The prologue as a statement step. -/
theorem prologueStmtStep {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st₀ : EvmState} :
    Step (OD c g) funs V st₀ (.stmt (Stmt.exprStmt (Expr.builtin Op.mstore
        [w fmpAddr, Expr.builtin Op.memoryguard [w irMemoryguardReservation]])))
      (.sres V (stAfterPrologue st₀) .normal) :=
  Step.exprStmt prologueExprStep

/-- `calldatasize()` reads the frame. -/
theorem calldatasizeStep {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.calldatasize []))
      (.eres (.vals [sizeWord st] st)) :=
  bi0 (op := Op.calldatasize) (v := sizeWord st)
    (rfl : (OD c g).Builtin Op.calldatasize [] st (.ok [sizeWord st] st))

/-- The word `iszero(lt(calldatasize(), 4))` computes in a frame, spelled once so the
    falsifications can hypothesise about it instead of re-deriving `b2w` towers. It is 1
    exactly when the calldata is at least selector-long. -/
def sizeTestValue (st : EvmState) : U256 :=
  b2w (b2w ((sizeWord st).ult (4 : U256)) = 0)

/-- `iszero(lt(calldatasize(), 4))` evaluates to `sizeTestValue`, leaving the frame
    alone. No hypothesis: this is the pure `stepOp` graph. -/
theorem calldatasizeTest_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.expr calldatasizeTest) (.eres (.vals [sizeTestValue st] st)) :=
  bi1 (op := Op.iszero) (e := Expr.builtin Op.lt [Expr.builtin Op.calldatasize [], w 4])
    (st' := st) (v := b2w ((sizeWord st).ult (4 : U256))) (u := sizeTestValue st)
    (bi2 (op := Op.lt) (e₁ := Expr.builtin Op.calldatasize []) (e₂ := w 4)
       (s₁ := st) (s₂ := st) (v₁ := sizeWord st) (v₂ := 4)
       (u := b2w ((sizeWord st).ult (4 : U256)))
       (wlit_eval 4) (calldatasizeStep (funs := funs) (V := V) (st := st)) rfl)
    rfl

/-- The head-region test: `slt(sub(calldatasize(), 4), 64)`, the artifact's check that both
    dynamic heads are present. -/
def headLengthValue (st : EvmState) : U256 :=
  b2w (((sizeWord st).sub (headStart : U256)).slt (tupleHeadBytes : U256))

theorem headLengthTest_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.slt
        [Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart], w tupleHeadBytes]))
      (.eres (.vals [headLengthValue st] st)) :=
  bi2 (op := Op.slt)
    (e₁ := Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart])
    (e₂ := w tupleHeadBytes) (s₁ := st) (s₂ := st)
    (v₂ := tupleHeadBytes) (v₁ := sizeWord st - headStart)
    (u := headLengthValue st)
    (wlit_eval tupleHeadBytes)
    (bi2 (op := Op.sub) (e₁ := Expr.builtin Op.calldatasize []) (e₂ := w headStart)
       (s₁ := st) (s₂ := st) (v₁ := sizeWord st) (v₂ := headStart)
       (u := sizeWord st - headStart)
       (wlit_eval headStart) calldatasizeStep rfl)
    rfl

/-- An offset or length above the ABI ceiling: `gt(x, 0xffff…)`. -/
def ceilingValue (x : U256) : U256 := b2w ((abiLengthCeiling : U256).ult x)

theorem ceilingTest_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {y : Ident} {x : U256} (hx : VEnv.get V y = some x) :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.gt [Expr.var y, w abiLengthCeiling]))
      (.eres (.vals [ceilingValue x] st)) :=
  bi2 (op := Op.gt) (e₁ := Expr.var y) (e₂ := w abiLengthCeiling)
    (s₁ := st) (s₂ := st) (v₁ := x) (v₂ := abiLengthCeiling) (u := ceilingValue x)
    (wlit_eval abiLengthCeiling) (varS (funs := funs) (V := V) (st := st) (x := y) (v := x) hx) rfl

/-- `iszero(slt(add(pos, 0x1f), calldatasize()))`: room for the length word at `pos`. -/
def lengthPresentValue (pos : U256) (st : EvmState) : U256 :=
  b2w (b2w (((pos + (31 : U256)).slt (sizeWord st))) = 0)

theorem lengthPresent_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {y : Ident} {pos : U256} (hp : VEnv.get V y = some pos) :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.iszero
        [Expr.builtin Op.slt [Expr.builtin Op.add [dataPos y, w 31],
          Expr.builtin Op.calldatasize []]]))
      (.eres (.vals [lengthPresentValue (headStart + pos) st] st)) :=
  bi1 (op := Op.iszero) (st' := st) (v := b2w (((headStart + pos + 31).slt (sizeWord st))))
    (u := lengthPresentValue (headStart + pos) st)
    (e := Expr.builtin Op.slt [Expr.builtin Op.add [dataPos y, w 31],
        Expr.builtin Op.calldatasize []])
    (bi2 (op := Op.slt) (s₁ := st) (s₂ := st) (v₁ := headStart + pos + 31)
       (v₂ := sizeWord st) (u := b2w (((headStart + pos + 31).slt (sizeWord st))))
       (e₁ := Expr.builtin Op.add [dataPos y, w 31]) (e₂ := Expr.builtin Op.calldatasize [])
       (calldatasizeStep (funs := funs) (V := V) (st := st))
       (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart + pos) (v₂ := (31 : U256))
          (u := headStart + pos + 31) (e₁ := dataPos y) (e₂ := w 31)
          (wlit_eval 31)
          (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart) (v₂ := pos)
             (u := headStart + pos) (e₁ := w headStart) (e₂ := Expr.var y)
             (varS (funs := funs) (V := V) (st := st) (x := y) (v := pos) hp)
             (wlit_eval headStart) rfl)
          rfl)
       rfl)
    rfl

/-- `gt(add(add(pos, 32), bytes), calldatasize())`: the tail test, where `bytes` is
    `length * stride`. THIS is the check a truncated argument trips. -/
def tailValue (pos bytes : U256) (st : EvmState) : U256 :=
  b2w ((sizeWord st).ult (pos + (32 : U256) + bytes))

theorem tail_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {o l : Ident} {pos len : U256} (stride : U256)
    (ho : VEnv.get V o = some pos) (hl : VEnv.get V l = some len) :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.gt
        [Expr.builtin Op.add [Expr.builtin Op.add [dataPos o, w 32],
            Expr.builtin Op.mul [Expr.var l, w stride]],
          Expr.builtin Op.calldatasize []]))
      (.eres (.vals [tailValue (headStart + pos) (len * stride) st] st)) :=
  bi2 (op := Op.gt) (s₁ := st) (s₂ := st) (v₁ := headStart + pos + 32 + len * stride)
    (v₂ := sizeWord st) (u := tailValue (headStart + pos) (len * stride) st)
    (e₁ := Expr.builtin Op.add [Expr.builtin Op.add [dataPos o, w 32],
              Expr.builtin Op.mul [Expr.var l, w stride]])
    (e₂ := Expr.builtin Op.calldatasize [])
    (calldatasizeStep (funs := funs) (V := V) (st := st))
    (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart + pos + 32)
       (v₂ := len * stride) (u := headStart + pos + 32 + len * stride)
       (e₁ := Expr.builtin Op.add [dataPos o, w 32]) (e₂ := Expr.builtin Op.mul [Expr.var l, w stride])
       (bi2 (op := Op.mul) (s₁ := st) (s₂ := st) (v₁ := len) (v₂ := stride)
          (u := len * stride) (e₁ := Expr.var l) (e₂ := w stride)
          (wlit_eval stride) (varS (funs := funs) (V := V) (st := st) (x := l) (v := len) hl) rfl)
       (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart + pos) (v₂ := (32 : U256))
          (u := headStart + pos + 32) (e₁ := dataPos o) (e₂ := w 32)
          (wlit_eval 32)
          (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart) (v₂ := pos)
             (u := headStart + pos) (e₁ := w headStart) (e₂ := Expr.var o)
             (varS (funs := funs) (V := V) (st := st) (x := o) (v := pos) ho)
             (wlit_eval headStart) rfl)
          rfl) rfl)
    rfl

/-- `calldataload(p)` for a position already bound in the environment. -/
theorem calldataload_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {y : Ident} {p : U256} (hp : VEnv.get V y = some p) :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.calldataload [Expr.var y]))
      (.eres (.vals [wordFrom st.env.calldata p.toNat] st)) :=
  bi1 (op := Op.calldataload) (st' := st) (v := p) (u := wordFrom st.env.calldata p.toNat)
    (e := Expr.var y)
    (varS (funs := funs) (V := V) (st := st) (x := y) (v := p) hp)
    (rfl : (OD c g).Builtin Op.calldataload [p] st
      (.ok [wordFrom st.env.calldata p.toNat] st))

/-- `calldataload(add(headStart, 0))`: the first head, read at a literal position. -/
theorem headLoad_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} (q : U256) :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.calldataload
        [Expr.builtin Op.add [w headStart, w q]]))
      (.eres (.vals [wordFrom st.env.calldata (headStart + q).toNat] st)) :=
  bi1 (op := Op.calldataload) (st' := st) (v := headStart + q)
    (u := wordFrom st.env.calldata (headStart + q).toNat)
    (e := Expr.builtin Op.add [w headStart, w q])
    (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart) (v₂ := q)
       (u := headStart + q) (e₁ := w headStart) (e₂ := w q)
       (wlit_eval q) (wlit_eval headStart) rfl)
    (rfl : (OD c g).Builtin Op.calldataload [headStart + q] st
      (.ok [wordFrom st.env.calldata (headStart + q).toNat] st))

/-- `shift_right_224_unsigned(calldataload(0))` evaluates to `selectorWord`, leaving
    the frame alone: the selector read is a pure calldata read. -/
theorem selectorStep {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.expr selectorExpr) (.eres (.vals [selectorWord st] st)) :=
  bi2 (op := Op.shr) (e₁ := w 224) (e₂ := Expr.builtin Op.calldataload [w 0])
    (s₁ := st) (s₂ := st) (v₁ := 224) (v₂ := wordFrom st.env.calldata 0)
    (u := selectorWord st)
    (bi1 (op := Op.calldataload) (e := w 0) (st' := st) (v := 0)
       (u := wordFrom st.env.calldata 0)
       (wlit_eval 0)
       (rfl : (OD c g).Builtin Op.calldataload [0] st
         (.ok [wordFrom st.env.calldata 0] st)))
    (wlit_eval 224)
    (rfl : (OD c g).Builtin Op.shr [224, wordFrom st.env.calldata 0] st
      (.ok [wordFrom st.env.calldata 0 >>> 224] st))

/-- `callvalue()` reads the frame. -/
theorem callvalueStep {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.callvalue []))
      (.eres (.vals [st.env.callvalue] st)) :=
  bi0 (op := Op.callvalue) (v := st.env.callvalue)
    (rfl : (OD c g).Builtin Op.callvalue [] st (.ok [st.env.callvalue] st))

/-- **The selector matches nothing.** The general form of "wrong selector": neither case label
    equals the scrutinee, so `selectSwitch` answers the empty block - which is what the
    artifact's literal `default {}` is too. -/
theorem switch_miss {cv : U256} {body : YulBlock}
    (h1 : cv ≠ selectorVerifyProof) (h2 : cv ≠ selectorAuthorizedVk) :
    selectSwitch (OD c g) cv (caseList body) none = [] := by
  have e1 : (OD c g).litValue (Literal.number selectorVerifyProof.toNat) = selectorVerifyProof :=
    BitVec.ofNat_toNat 256 selectorVerifyProof
  have e2 : (OD c g).litValue (Literal.number selectorAuthorizedVk.toNat) = selectorAuthorizedVk :=
    BitVec.ofNat_toNat 256 selectorAuthorizedVk
  have d1 : decide (cv = (OD c g).litValue (Literal.number selectorVerifyProof.toNat)) = false :=
    decide_eq_false (fun h => h1 (h.trans e1))
  have d2 : decide (cv = (OD c g).litValue (Literal.number selectorAuthorizedVk.toNat)) = false :=
    decide_eq_false (fun h => h2 (h.trans e2))
  show selectSwitch (OD c g) cv
      [(Literal.number selectorVerifyProof.toNat, verifyProofArm body),
       (Literal.number selectorAuthorizedVk.toNat, authorizedVkArm)] none = []
  simp only [selectSwitch, List.find?, d1, d2]
  rfl

/-- The switch hits the `verifyProof` arm. -/
theorem switch_verifyProof {cv : U256} {body : YulBlock} (h : cv = selectorVerifyProof) :
    selectSwitch (OD c g) cv (caseList body) none = verifyProofArm body := by
  have e1 : (OD c g).litValue (Literal.number selectorVerifyProof.toNat) = selectorVerifyProof :=
    BitVec.ofNat_toNat 256 selectorVerifyProof
  have d1 : decide (cv = (OD c g).litValue (Literal.number selectorVerifyProof.toNat)) = true :=
    decide_eq_true (h.trans e1.symm)
  show selectSwitch (OD c g) cv
      [(Literal.number selectorVerifyProof.toNat, verifyProofArm body),
       (Literal.number selectorAuthorizedVk.toNat, authorizedVkArm)] none = verifyProofArm body
  simp only [selectSwitch, List.find?, d1]

/-! ### 4. The three falsifications -/

/-- One step of the sequence, with the dialect pinned so the `DecidableEq` index does not have
    to be guessed. -/
private theorem seqC {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {s₁ : Stmt EVM.Op} {rest : YulBlock} {V₁ st₁ V₂ st₂ o}
    (h₁ : Step (OD c g) funs V st (.stmt s₁) (.sres V₁ st₁ .normal))
    (h₂ : Step (OD c g) funs V₁ st₁ (.stmts rest) (.sres V₂ st₂ o)) :
    Step (OD c g) funs V st (.stmts (s₁ :: rest)) (.sres V₂ st₂ o) :=
  Step.seqCons (D := OD c g) h₁ h₂

/-- A halt stops the sequence. -/
private theorem seqStopH {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {s₁ : Stmt EVM.Op} {rest : YulBlock} {V₁ st₁}
    (h₁ : Step (OD c g) funs V st (.stmt s₁) (.sres V₁ st₁ .halt)) :
    Step (OD c g) funs V st (.stmts (s₁ :: rest)) (.sres V₁ st₁ .halt) :=
  Step.seqStop (D := OD c g) h₁ halt_ne_normal

/-- The empty sequence. -/
private theorem seqN {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} :
    Step (OD c g) funs V st (.stmts []) (.sres V st .normal) := Step.seqNil (D := OD c g)

/-- A block, with the dialect pinned. -/
private theorem blk {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState} {body : YulBlock}
    {V₁ st₁ o} (h : Step (OD c g) (hoist (OD c g) body :: funs) V st (.stmts body)
      (.sres V₁ st₁ o)) :
    Step (OD c g) funs V st (.stmt (.block body)) (.sres (restore V V₁) st₁ o) :=
  Step.block (D := OD c g) h

/-- `1 ≠ 0` in the dialect's value type, once. -/
theorem one_ne_zero : (1 : U256) ≠ (OD c g).zero := by show (1 : U256) ≠ 0; decide

/-- `0 = 0` in the dialect's value type, once. -/
theorem zero_eq_zero : (0 : U256) = (OD c g).zero := rfl

/-- **FALSIFICATION 1 - THE ONE THE OLD MODEL GOT WRONG.** A calldata that carries a selector
    nothing routes reverts.

    This is precisely the behaviour `Surface.shell` does not have: the old model's entry is the
    head guard, so a wrong-selector calldata falls straight into `headGuard ++ bindLocals ++ main`
    and RUNS THE VERIFIER. `old_shell_runs_the_verifier_on_the_same_frame` below is that
    difference as a theorem, not as a sentence.

    Hypotheses, each about what the dispatcher itself reads: `sizeTestValue st₀ = 1` says the
    calldata is at least 4 bytes long (the `ImportedIR` empty-calldata witness is the dual case,
    `cdWellFormed_is_accepted.1`); the two `≠`s say the selector matches neither case label,
    which `switch_miss` turns into the empty `selectSwitch` block. -/
theorem wrong_selector_reverts {body : YulBlock} {st₀ : EvmState}
    (hsize : sizeTestValue st₀ = 1)
    (hsel : selectorWord st₀ ≠ selectorVerifyProof)
    (hsel2 : selectorWord st₀ ≠ selectorAuthorizedVk) :
    ∃ st', Run c g (dispatcher body) st₀ [] st' .halt ∧
      st'.halted = some (.revert, []) := by
  let st₁ := stAfterPrologue st₀
  let sel := selectorWord st₀
  let V₁ : VEnv (OD c g) := [("selector", sel)]
  let FI : FunEnv (OD c g) := hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]]
  have hprol : Step (OD c g) [[]] [] st₀
      (.stmt (Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]])))
      (.sres [] st₁ .normal) := prologueStmtStep (c := c) (g := g)
  have htest : Step (OD c g) [[]] [] st₁ (.expr calldatasizeTest) (.eres (.vals [1] st₁)) := by
    have e := calldatasizeTest_val (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
    rw [show sizeTestValue st₁ = sizeTestValue st₀ from rfl, hsize] at e
    exact e
  have hdecl : Step (OD c g) FI [] st₁ (.stmt selectorDecl) (.sres V₁ st₁ .normal) := by
    refine Step.letVal (D := OD c g) (vars := ["selector"]) (vals := [sel]) (e := selectorExpr)
      (st1 := st₁) ?_ rfl
    exact selectorStep (c := c) (g := g) (funs := FI) (V := []) (st := st₁)
  have hvar : Step (OD c g) FI V₁ st₁ (.expr (Expr.var "selector"))
      (.eres (.vals [sel] st₁)) :=
    Step.var (D := OD c g) (funs := FI) (V := V₁) (st := st₁) (x := "selector") (v := sel) rfl
  have hinner : Step (OD c g) FI V₁ st₁
      (.stmt (.block (selectSwitch (OD c g) sel (caseList body) none)))
      (.sres (restore V₁ V₁) st₁ .normal) := by
    rw [switch_miss (c := c) (g := g) (cv := sel) (body := body) hsel hsel2]
    exact blk (c := c) (g := g) (body := []) (funs := FI) (V := V₁) (st := st₁)
      (V₁ := V₁) (st₁ := st₁) (o := .normal) (seqN (c := c) (g := g)
        (funs := hoist (OD c g) [] :: FI) (V := V₁) (st := st₁))
  have hsw : Step (OD c g) FI V₁ st₁ (.stmt (selectorSwitch body))
      (.sres V₁ st₁ .normal) := by
    have key : Step (OD c g) FI V₁ st₁ (.stmt (selectorSwitch body))
        (.sres (restore V₁ V₁) st₁ .normal) :=
      Step.switchExec (D := OD c g) (funs := FI) (V := V₁) (st := st₁)
        (cases := caseList body) (dflt := none) (cv := sel) hvar hinner
    rw [restore_self (V := V₁)] at key
    exact key
  have hblk : Step (OD c g) [[]] [] st₁ (.stmt (.block [selectorDecl, selectorSwitch body]))
      (.sres (restore ([] : VEnv (OD c g)) V₁) st₁ .normal) :=
    blk (c := c) (g := g) (body := [selectorDecl, selectorSwitch body]) (funs := [[]]) (V := [])
      (st := st₁) (seqC (c := c) (g := g) (funs := FI) (V := []) (st := st₁)
        (s₁ := selectorDecl) (rest := [selectorSwitch body]) (V₁ := V₁) (st₁ := st₁)
        (V₂ := V₁) (st₂ := st₁) (o := .normal) hdecl
        (seqC (c := c) (g := g) (funs := FI) (V := V₁) (st := st₁)
          (s₁ := selectorSwitch body) (rest := []) (V₁ := V₁) (st₁ := st₁)
          (V₂ := V₁) (st₂ := st₁) (o := .normal) hsw
          (seqN (c := c) (g := g) (funs := FI) (V := V₁) (st := st₁))))
  have hcond : Step (OD c g) [[]] [] st₁
      (.stmt (Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body]))
      (.sres ([] : VEnv (OD c g)) st₁ .normal) := by
    have key : Step (OD c g) [[]] [] st₁
        (.stmt (Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body]))
        (.sres (restore ([] : VEnv (OD c g)) V₁) st₁ .normal) :=
      Step.ifTrue (D := OD c g) (funs := [[]]) (V := []) (st := st₁)
        (body := [selectorDecl, selectorSwitch body]) htest one_ne_zero hblk
    rw [show (restore ([] : VEnv (OD c g)) V₁) = ([] : VEnv (OD c g)) from rfl] at key
    exact key
  have hrv : Step (OD c g) [[]] [] st₁ (.stmt revert00)
      (.sres [] (revertState st₁) .halt) := revert00_step (c := c) (g := g)
  have hstmts : Step (OD c g) [[]] [] st₀ (.stmts (dispatcher body))
      (.sres [] (revertState st₁) .halt) := by
    show Step (OD c g) [[]] [] st₀
      (.stmts [Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
          Expr.builtin Op.memoryguard [w irMemoryguardReservation]]),
        Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body], revert00])
      (.sres [] (revertState st₁) .halt)
    exact seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := st₀)
      (rest := [Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body], revert00])
      (V₁ := []) (st₁ := st₁) (V₂ := []) (st₂ := revertState st₁) (o := .halt)
      hprol (seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
        (s₁ := Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body])
        (rest := [revert00]) (V₁ := []) (st₁ := st₁) (V₂ := [])
        (st₂ := revertState st₁) (o := .halt) hcond
        (seqStopH (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁) (s₁ := revert00)
          (rest := []) (V₁ := []) (st₁ := revertState st₁) hrv))
  exact ⟨revertState st₁, blk (c := c) (g := g) (funs := []) (V := []) (st := st₀)
      (body := dispatcher body) (V₁ := []) (st₁ := revertState st₁) (o := .halt) hstmts,
    rfl⟩

/-! ### The dispatch prefix, proved once -/

/-- `restore [] V = []`: a top-level block keeps no bindings of an inner scope. Needed because
    `restore outer inner = inner.drop (inner.length - outer.length)` and `[].length = 0`
    leaves `V.drop V.length`, which is not `rfl` for a symbolic `V`. -/
theorem restore_nil {V : VEnv (OD c g)} : restore ([] : VEnv (OD c g)) V = [] := by
  show V.drop (V.length - ([] : VEnv (OD c g)).length) = []
  simp

/-- **The dispatch prefix.** Prologue, size test, selector binding, switch: everything the
    dispatcher does before an arm's own first statement, parameterised by what the selected arm
    block does. Both routed falsifications are this with a different arm derivation, so the entry
    path is proved once and each falsification is about its own guard. -/
theorem dispatch_prefix {body : YulBlock} {st₀ : EvmState} (hsize : sizeTestValue st₀ = 1)
    {st' : EvmState}
    (harm : Step (OD c g)
        (hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]])
        [("selector", selectorWord st₀)] (stAfterPrologue st₀)
        (.stmt (.block (selectSwitch (OD c g) (selectorWord st₀) (caseList body) none)))
        (.sres [("selector", selectorWord st₀)] st' .halt)) :
    Step (OD c g) [[]] [] st₀ (.stmts (dispatcher body)) (.sres [] st' .halt) := by
  let st₁ := stAfterPrologue st₀
  let sel := selectorWord st₀
  let V₁ : VEnv (OD c g) := [("selector", sel)]
  let FI : FunEnv (OD c g) := hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]]
  have hprol : Step (OD c g) [[]] [] st₀
      (.stmt (Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]])))
      (.sres [] st₁ .normal) := prologueStmtStep (c := c) (g := g)
  have htest : Step (OD c g) [[]] [] st₁ (.expr calldatasizeTest) (.eres (.vals [1] st₁)) := by
    have e := calldatasizeTest_val (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
    rw [show sizeTestValue st₁ = sizeTestValue st₀ from rfl, hsize] at e
    exact e
  have hdecl : Step (OD c g) FI [] st₁ (.stmt selectorDecl) (.sres V₁ st₁ .normal) := by
    refine Step.letVal (D := OD c g) (vars := ["selector"]) (vals := [sel]) (e := selectorExpr)
      (st1 := st₁) ?_ rfl
    exact selectorStep (c := c) (g := g) (funs := FI) (V := []) (st := st₁)
  have hsw : Step (OD c g) FI V₁ st₁ (.stmt (selectorSwitch body)) (.sres V₁ st' .halt) :=
    Step.switchExec (D := OD c g) (funs := FI) (V := V₁) (st := st₁)
      (cases := caseList body) (dflt := none) (cv := sel)
      (Step.var (D := OD c g) (funs := FI) (V := V₁) (st := st₁) (x := "selector")
        (v := sel) rfl) harm
  have hblk : Step (OD c g) [[]] [] st₁ (.stmt (.block [selectorDecl, selectorSwitch body]))
      (.sres (restore ([] : VEnv (OD c g)) V₁) st' .halt) :=
    blk (c := c) (g := g) (body := [selectorDecl, selectorSwitch body]) (funs := [[]]) (V := [])
      (st := st₁) (seqC (c := c) (g := g) (funs := FI) (V := []) (st := st₁)
        (s₁ := selectorDecl) (rest := [selectorSwitch body]) (V₁ := V₁) (st₁ := st₁)
        (V₂ := V₁) (st₂ := st') (o := .halt) hdecl
        (seqStopH (c := c) (g := g) (funs := FI) (V := V₁) (st := st₁)
          (s₁ := selectorSwitch body) (rest := []) (V₁ := V₁) (st₁ := st') hsw))
  have hcond : Step (OD c g) [[]] [] st₁
      (.stmt (Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body]))
      (.sres ([] : VEnv (OD c g)) st' .halt) := by
    have key : Step (OD c g) [[]] [] st₁
        (.stmt (Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body]))
        (.sres (restore ([] : VEnv (OD c g)) V₁) st' .halt) :=
      Step.ifTrue (D := OD c g) (funs := [[]]) (V := []) (st := st₁)
        (body := [selectorDecl, selectorSwitch body]) htest one_ne_zero hblk
    rw [restore_nil (V := V₁)] at key
    exact key
  show Step (OD c g) [[]] [] st₀
    (.stmts [Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]]),
      Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body], revert00])
    (.sres [] st' .halt)
  exact seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := st₀)
    (s₁ := Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]]))
    (rest := [Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body], revert00])
    (V₁ := []) (st₁ := st₁) (V₂ := []) (st₂ := st') (o := .halt) hprol
    (seqStopH (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
      (s₁ := Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body])
      (rest := [revert00]) (V₁ := []) (st₁ := st') hcond)

/-- **FALSIFICATION 2 - THE CALLVALUE CHECK.** A `verifyProof` calldata carrying value
    reverts: `verifyProof` is `external view`, so solc's arm opens with
    `if callvalue() revert`. The hypothesis is load-bearing:
    `cdWellFormed_is_accepted.2.2.1` is the same fact at value 0 and does not take this
    abort. -/
theorem nonzero_callvalue_reverts {body : YulBlock} {st₀ : EvmState}
    (hsize : sizeTestValue st₀ = 1) (hsel : selectorWord st₀ = selectorVerifyProof)
    (hcv : st₀.env.callvalue ≠ 0) :
    ∃ st', Run c g (dispatcher body) st₀ [] st' .halt ∧
      st'.halted = some (.revert, []) := by
  let st₁ := stAfterPrologue st₀
  let sel := selectorWord st₀
  let V₁ : VEnv (OD c g) := [("selector", sel)]
  let FA : FunEnv (OD c g) :=
    hoist (OD c g) (verifyProofArm body) :: hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]]
  have hguard : Step (OD c g) FA V₁ st₁ (.stmt callvalueGuard)
      (.sres V₁ (revertState st₁) .halt) :=
    guardReverts (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁)
      (test := Expr.builtin Op.callvalue []) (v := st₁.env.callvalue)
      (callvalueStep (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁)) hcv
  have harm : Step (OD c g)
      (hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]])
      V₁ st₁
      (.stmt (.block (selectSwitch (OD c g) sel (caseList body) none)))
      (.sres V₁ (revertState st₁) .halt) := by
    rw [switch_verifyProof (c := c) (g := g) (body := body) (cv := sel) hsel]
    have key : Step (OD c g) (hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]])
        V₁ st₁ (.stmt (.block (verifyProofArm body)))
        (.sres (restore V₁ V₁) (revertState st₁) .halt) :=
      blk (c := c) (g := g) (body := verifyProofArm body)
        (funs := hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]]) (V := V₁)
        (st := st₁) (V₁ := V₁) (st₁ := revertState st₁) (o := .halt)
        (seqStopH (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁)
          (s₁ := callvalueGuard) (rest := abiDecode ++ bindLocalsFromImmutables ++ body)
          (V₁ := V₁) (st₁ := revertState st₁) hguard)
    rw [restore_self (V := V₁)] at key
    exact key
  have hstmts : Step (OD c g) [[]] [] st₀ (.stmts (dispatcher body))
      (.sres [] (revertState st₁) .halt) :=
    dispatch_prefix (c := c) (g := g) (body := body) (st₀ := st₀) hsize harm
  exact ⟨revertState st₁, blk (c := c) (g := g) (funs := []) (V := []) (st := st₀)
      (body := dispatcher body) (V₁ := []) (st₁ := revertState st₁) (o := .halt) hstmts,
    rfl⟩

/-- `calldataload(dataPos o)`: the length word of a dynamic argument whose head is bound
    in `o`. -/
theorem dataPosLoad_val {funs : FunEnv (OD c g)} {V : VEnv (OD c g)} {st : EvmState}
    {o : Ident} {pos : U256} (ho : VEnv.get V o = some pos) :
    Step (OD c g) funs V st (.expr (Expr.builtin Op.calldataload [dataPos o]))
      (.eres (.vals [wordFrom st.env.calldata (headStart + pos).toNat] st)) :=
  bi1 (op := Op.calldataload) (st' := st) (v := headStart + pos)
    (u := wordFrom st.env.calldata (headStart + pos).toNat) (e := dataPos o)
    (bi2 (op := Op.add) (s₁ := st) (s₂ := st) (v₁ := headStart) (v₂ := pos)
       (u := headStart + pos) (e₁ := w headStart) (e₂ := Expr.var o)
       (varS (funs := funs) (V := V) (st := st) (x := o) (v := pos) ho)
       (wlit_eval headStart) rfl)
    (rfl : (OD c g).Builtin Op.calldataload [headStart + pos] st
      (.ok [wordFrom st.env.calldata (headStart + pos).toNat] st))

/-- **FALSIFICATION 3 - THE ABI BOUNDS CHECK.** A `verifyProof` calldata whose `bytes`
    argument declares more data than the calldata carries reverts, at the tail test
    `gt(add(add(headStart, offset, 32), length), calldatasize())` - the check the artifact's
    `abi_decode_t_bytes_calldata_ptr` emits and the one a truncated proof trips.

    Every hypothesis before `htrunc` is a check that PASSES (the arm gets as far as the tail
    test); `htrunc` is the check that fails. `armPrefix_passes` (P-LOWEQ) is the lemma that
    discharges them all at a well-formed calldata and shows the arm proceeds, so the truncation
    hypothesis is the one doing the work. -/
theorem truncated_bytes_reverts {body : YulBlock} {st₀ : EvmState}
    (hsize : sizeTestValue st₀ = 1) (hsel : selectorWord st₀ = selectorVerifyProof)
    (hcv : st₀.env.callvalue = 0) (hheads : headLengthValue st₀ = 0)
    {po : U256} (hpo : wordFrom st₀.env.calldata headStart.toNat = po)
    (hpoBound : ceilingValue po = 0)
    (hlenPresent : lengthPresentValue (headStart + po) st₀ = 0)
    {pl : U256} (hpl : wordFrom st₀.env.calldata (headStart + po).toNat = pl)
    (hplBound : ceilingValue pl = 0) (htrunc : tailValue (headStart + po) (pl * 1) st₀ = 1) :
    ∃ st', Run c g (dispatcher body) st₀ [] st' .halt ∧
      st'.halted = some (.revert, []) := by
  let st₁ := stAfterPrologue st₀
  let sel := selectorWord st₀
  let V₁ : VEnv (OD c g) := [("selector", sel)]
  let V₂ : VEnv (OD c g) := [("proofOffset", po)] ++ V₁
  let V₃ : VEnv (OD c g) := [("proofLength", pl)] ++ V₂
  let FI : FunEnv (OD c g) := hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]]
  let FA : FunEnv (OD c g) := hoist (OD c g) (verifyProofArm body) :: FI
  -- the entry prefix
  have hprol : Step (OD c g) [[]] [] st₀
      (.stmt (Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]])))
      (.sres [] st₁ .normal) := prologueStmtStep (c := c) (g := g)
  have htest : Step (OD c g) [[]] [] st₁ (.expr calldatasizeTest) (.eres (.vals [1] st₁)) := by
    have e := calldatasizeTest_val (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
    rw [show sizeTestValue st₁ = sizeTestValue st₀ from rfl, hsize] at e
    exact e
  have hdecl : Step (OD c g) FI [] st₁ (.stmt selectorDecl) (.sres V₁ st₁ .normal) := by
    refine Step.letVal (D := OD c g) (vars := ["selector"]) (vals := [sel]) (e := selectorExpr)
      (st1 := st₁) ?_ rfl
    exact selectorStep (c := c) (g := g) (funs := FI) (V := []) (st := st₁)
  -- arm step 1: the callvalue guard passes
  have hcvs : Step (OD c g) FA V₁ st₁ (.expr (Expr.builtin Op.callvalue []))
      (.eres (.vals [0] st₁)) := by
    have e := callvalueStep (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁)
    rw [show st₁.env.callvalue = st₀.env.callvalue from rfl, hcv] at e
    exact e
  have h1 : Step (OD c g) FA V₁ st₁ (.stmt callvalueGuard) (.sres V₁ st₁ .normal) :=
    guardPasses (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.callvalue []) hcvs
  -- arm step 2: the head-region length guard passes
  have hheads' : Step (OD c g) FA V₁ st₁ (.expr (Expr.builtin Op.slt
        [Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart], w tupleHeadBytes]))
      (.eres (.vals [0] st₁)) := by
    have e := headLengthTest_val (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁)
    rw [show headLengthValue st₁ = headLengthValue st₀ from rfl, hheads] at e
    exact e
  have h2 : Step (OD c g) FA V₁ st₁ (.stmt headLengthGuard) (.sres V₁ st₁ .normal) :=
    guardPasses (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.slt
        [Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart], w tupleHeadBytes])
      hheads'
  -- arm step 3: let proofOffset := calldataload(add(headStart, 0))
  have hpo' : Step (OD c g) FA V₁ st₁ (.expr (Expr.builtin Op.calldataload
        [Expr.builtin Op.add [w headStart, w 0]]))
      (.eres (.vals [po] st₁)) := by
    have e := headLoad_val (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁) 0
    rw [show wordFrom st₁.env.calldata (headStart + 0).toNat =
          wordFrom st₀.env.calldata headStart.toNat from rfl, hpo] at e
    exact e
  have h3 : Step (OD c g) FA V₁ st₁ (.stmt proofOffsetDecl) (.sres V₂ st₁ .normal) := by
    refine Step.letVal (D := OD c g) (vars := ["proofOffset"]) (vals := [po])
      (e := Expr.builtin Op.calldataload [Expr.builtin Op.add [w headStart, w 0]])
      (st1 := st₁) (V := V₁) (funs := FA) (st := st₁) hpo' rfl
  -- arm step 4: the offset ceiling guard passes
  have h4e : Step (OD c g) FA V₂ st₁ (.expr (Expr.builtin Op.gt
        [Expr.var "proofOffset", w abiLengthCeiling])) (.eres (.vals [0] st₁)) := by
    have e := ceilingTest_val (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁)
      (y := "proofOffset") (x := po) (rfl : VEnv.get V₂ "proofOffset" = some po)
    rw [hpoBound] at e
    exact e
  have h4 : Step (OD c g) FA V₂ st₁ (.stmt (offsetCeilingGuard "proofOffset"))
      (.sres V₂ st₁ .normal) :=
    guardPasses (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.var "proofOffset", w abiLengthCeiling]) h4e
  -- arm step 5: the length word is inside the calldata
  have h5e : Step (OD c g) FA V₂ st₁ (.expr (Expr.builtin Op.iszero
        [Expr.builtin Op.slt [Expr.builtin Op.add [dataPos "proofOffset", w 31],
          Expr.builtin Op.calldatasize []]])) (.eres (.vals [0] st₁)) := by
    have e := lengthPresent_val (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁)
      (y := "proofOffset") (pos := po) (rfl : VEnv.get V₂ "proofOffset" = some po)
    rw [show lengthPresentValue (headStart + po) st₁ =
          lengthPresentValue (headStart + po) st₀ from rfl, hlenPresent] at e
    exact e
  have h5 : Step (OD c g) FA V₂ st₁ (.stmt (lengthPresentGuard "proofOffset"))
      (.sres V₂ st₁ .normal) :=
    guardPasses (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.iszero [Expr.builtin Op.slt
        [Expr.builtin Op.add [dataPos "proofOffset", w 31], Expr.builtin Op.calldatasize []]]) h5e
  -- arm step 6: let proofLength := calldataload(add(headStart, proofOffset))
  have hpl' : Step (OD c g) FA V₂ st₁ (.expr (Expr.builtin Op.calldataload
        [dataPos "proofOffset"])) (.eres (.vals [pl] st₁)) := by
    have e := dataPosLoad_val (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁)
      (o := "proofOffset") (pos := po) (rfl : VEnv.get V₂ "proofOffset" = some po)
    rw [show wordFrom st₁.env.calldata (headStart + po).toNat =
          wordFrom st₀.env.calldata (headStart + po).toNat from rfl, hpl] at e
    exact e
  have h6 : Step (OD c g) FA V₂ st₁ (.stmt proofLengthDecl) (.sres V₃ st₁ .normal) := by
    refine Step.letVal (D := OD c g) (vars := ["proofLength"]) (vals := [pl])
      (e := Expr.builtin Op.calldataload [dataPos "proofOffset"])
      (st1 := st₁) (V := V₂) (funs := FA) (st := st₁) hpl' rfl
  -- arm step 7: the length ceiling guard passes
  have h7e : Step (OD c g) FA V₃ st₁ (.expr (Expr.builtin Op.gt
        [Expr.var "proofLength", w abiLengthCeiling])) (.eres (.vals [0] st₁)) := by
    have e := ceilingTest_val (c := c) (g := g) (funs := FA) (V := V₃) (st := st₁)
      (y := "proofLength") (x := pl) (rfl : VEnv.get V₃ "proofLength" = some pl)
    rw [hplBound] at e
    exact e
  have h7 : Step (OD c g) FA V₃ st₁ (.stmt (offsetCeilingGuard "proofLength"))
      (.sres V₃ st₁ .normal) :=
    guardPasses (c := c) (g := g) (funs := FA) (V := V₃) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.var "proofLength", w abiLengthCeiling]) h7e
  -- arm step 8: THE TAIL TEST FIRES
  have h8e : Step (OD c g) FA V₃ st₁ (.expr (Expr.builtin Op.gt
        [Expr.builtin Op.add [Expr.builtin Op.add [dataPos "proofOffset", w 32],
            Expr.builtin Op.mul [Expr.var "proofLength", w 1]],
          Expr.builtin Op.calldatasize []])) (.eres (.vals [1] st₁)) := by
    have e := tail_val (c := c) (g := g) (funs := FA) (V := V₃) (st := st₁)
      (o := "proofOffset") (l := "proofLength") (pos := po) (len := pl) (stride := 1)
      (rfl : VEnv.get V₃ "proofOffset" = some po)
      (rfl : VEnv.get V₃ "proofLength" = some pl)
    rw [show tailValue (headStart + po) (pl * 1) st₁ =
          tailValue (headStart + po) (pl * 1) st₀ from rfl, htrunc] at e
    exact e
  have h8 : Step (OD c g) FA V₃ st₁ (.stmt (tailGuard "proofOffset" "proofLength" 1))
      (.sres V₃ (revertState st₁) .halt) :=
    guardReverts (c := c) (g := g) (funs := FA) (V := V₃) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.builtin Op.add
          [Expr.builtin Op.add [dataPos "proofOffset", w 32],
            Expr.builtin Op.mul [Expr.var "proofLength", w 1]],
          Expr.builtin Op.calldatasize []])
      (v := 1) h8e (one_ne_zero (c := c) (g := g))
  -- assemble the arm: seven passing steps, then the tail test halts
  have hseq : Step (OD c g) FA V₁ st₁ (.stmts (verifyProofArm body))
      (.sres V₃ (revertState st₁) .halt) := by
    show Step (OD c g) FA V₁ st₁
      (.stmts ([callvalueGuard, headLengthGuard, proofOffsetDecl,
          offsetCeilingGuard "proofOffset", lengthPresentGuard "proofOffset", proofLengthDecl,
          offsetCeilingGuard "proofLength", tailGuard "proofOffset" "proofLength" 1,
          instancesOffsetDecl, offsetCeilingGuard "instancesOffset",
          lengthPresentGuard "instancesOffset", instancesLengthDecl,
          offsetCeilingGuard "instancesLength",
          tailGuard "instancesOffset" "instancesLength" 32]
          ++ bindLocalsFromImmutables ++ body))
        (.sres V₃ (revertState st₁) .halt)
    refine seqC (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁) (V₁ := V₁)
      (st₁ := st₁) h1 ?_
    refine seqC (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁) (V₁ := V₁)
      (st₁ := st₁) h2 ?_
    refine seqC (c := c) (g := g) (funs := FA) (V := V₁) (st := st₁) (V₁ := V₂)
      (st₁ := st₁) h3 ?_
    refine seqC (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁) (V₁ := V₂)
      (st₁ := st₁) h4 ?_
    refine seqC (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁) (V₁ := V₂)
      (st₁ := st₁) h5 ?_
    refine seqC (c := c) (g := g) (funs := FA) (V := V₂) (st := st₁) (V₁ := V₃)
      (st₁ := st₁) h6 ?_
    refine seqC (c := c) (g := g) (funs := FA) (V := V₃) (st := st₁) (V₁ := V₃)
      (st₁ := st₁) h7 ?_
    exact seqStopH (c := c) (g := g) (funs := FA) (V := V₃) (st := st₁)
      (V₁ := V₃) (st₁ := revertState st₁) h8
  have harm : Step (OD c g) FI V₁ st₁
      (.stmt (.block (selectSwitch (OD c g) sel (caseList body) none)))
      (.sres V₁ (revertState st₁) .halt) := by
    rw [switch_verifyProof (c := c) (g := g) (body := body) (cv := sel) hsel]
    have key : Step (OD c g) FI V₁ st₁ (.stmt (.block (verifyProofArm body)))
        (.sres (restore V₁ V₃) (revertState st₁) .halt) :=
      blk (c := c) (g := g) (body := verifyProofArm body) (funs := FI) (V := V₁) (st := st₁)
        (V₁ := V₃) (st₁ := revertState st₁) (o := .halt) hseq
    have hres : restore V₁ V₃ = V₁ := rfl
    rw [hres] at key
    exact key
  have hstmts : Step (OD c g) [[]] [] st₀ (.stmts (dispatcher body))
      (.sres [] (revertState st₁) .halt) :=
    dispatch_prefix (c := c) (g := g) (body := body) (st₀ := st₀) hsize harm
  exact ⟨revertState st₁, blk (c := c) (g := g) (funs := []) (V := []) (st := st₀)
      (body := dispatcher body) (V₁ := []) (st₁ := revertState st₁) (o := .halt) hstmts,
    rfl⟩

/-! ### 5. The witnesses, and the hypotheses seen to be load-bearing -/

-- The witness facts below are kernel reductions over a 100-230 byte calldata: `wordFrom` reads
-- 32 bytes at a position and each byte walks the appended list, so the default recursion budget is
-- not enough - the same reason the 2,900-line import raises it.
set_option maxRecDepth 100000

/-- The 4 big-endian bytes of a selector. -/
def be4 (v : Nat) : List UInt8 :=
  (List.range 4).map fun i => Nat.toUInt8 ((((BitVec.ofNat 32 v) >>> (8 * (3 - i))) &&& 0xff).toNat)

/-- The 32 big-endian bytes of a word. -/
def be32 (v : Nat) : List UInt8 :=
  (List.range 32).map fun i => Nat.toUInt8 ((((BitVec.ofNat 256 v) >>> (8 * (31 - i))) &&& 0xff).toNat)

/-- `n` zero bytes. -/
def zbytes (n : Nat) : List UInt8 := List.replicate n 0

/-- A calldata carrying a selector nothing routes. -/
def cdWrongSelector : List UInt8 := be4 0xdeadbeef ++ zbytes 100

/-- A `verifyProof` calldata whose `bytes` argument declares 100 bytes and carries 16.
    The head region is intact and the offset is 0x40 - exactly what the artifact's own head guard
    `eq(calldataload(0x04), 0x40)` expects - the length word is inside the calldata, and the
    tail runs 84 bytes past the end. -/
def cdTruncatedProof : List UInt8 :=
  be4 0x1e8e1e13 ++ be32 64 ++ be32 0 ++ be32 100 ++ zbytes 16

/-- The same calldata made well-formed: the proof carries its declared 64 bytes and the
    `uint256[]` head points at a one-element array that also fits. Every dispatcher check
    passes here, which is what makes the truncation hypothesis load-bearing rather than decorative. -/
def cdWellFormed : List UInt8 :=
  be4 0x1e8e1e13 ++ be32 64 ++ be32 160 ++ be32 64 ++ zbytes 64 ++ be32 1 ++ be32 0

/-- A stand-in for the lowered program: it returns, which is what the real `traceReturn`
    partial does (`traceReturn_spec`) and what makes the halt kind observable. Used only
    where a hypothesis has to be seen to MATTER; the body is opaque in the theorems themselves. -/
def retBody : YulBlock := [Stmt.exprStmt (Expr.builtin Op.ret [w 0, w 0])]

/-- **D-P23, FIRST HALF FOR FALSIFICATION 1.** The wrong-selector hypotheses are satisfiable at a
    frame a real call produces: `callState W Lyt H cd` has exactly this calldata and value 0,
    so the theorem applies at a deployment frame and not only at `frame`. -/
theorem wrong_selector_reverts_at_witness {body : YulBlock} :
    ∃ st', Run c g (dispatcher body) (frame cdWrongSelector 0) [] st' .halt ∧
      st'.halted = some (.revert, []) :=
  wrong_selector_reverts (body := body) (st₀ := frame cdWrongSelector 0) rfl (by decide) (by decide)

/-- **D-P23, FIRST HALF FOR FALSIFICATION 2.** -/
theorem nonzero_callvalue_reverts_at_witness {body : YulBlock} :
    ∃ st', Run c g (dispatcher body) (frame cdWellFormed 7) [] st' .halt ∧
      st'.halted = some (.revert, []) :=
  nonzero_callvalue_reverts (body := body) (st₀ := frame cdWellFormed 7) rfl rfl (by decide)

/-- **D-P23, FIRST HALF FOR FALSIFICATION 3.** -/
theorem truncated_bytes_reverts_at_witness {body : YulBlock} :
    ∃ st', Run c g (dispatcher body) (frame cdTruncatedProof 0) [] st' .halt ∧
      st'.halted = some (.revert, []) :=
  truncated_bytes_reverts (body := body) (st₀ := frame cdTruncatedProof 0)
    (po := 64) (pl := 100) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl


/-- **THE BINDINGS DO WHAT THE DEPLOYMENT PINS.** Running the two binding statements in a frame
    whose immutable map answers the two keys puts exactly those words in `vk` and
    `quotientEvaluator`. This is the half of PLAN section 7's "binding the locals `vk` and
    `quotientEvaluator` from immutables" that a gate cannot fake: the `loadimmutable`
    steps are derivations, and the keys they read are the ones `DeploymentW.vkImm` and
    `qImm` pin. Perturbing either key or either name reddens this theorem, and did before it
    was written - the control is in the package report. -/
theorem bindLocals_read_the_pinned_immutables {c : ExternalCalls} {g : ExternalGas}
    (a₁ a₂ : U256) (st : EvmState)
    (h₁ : st.env.immutable (litValue (.string vkImmutableKey)) = a₁)
    (h₂ : st.env.immutable (litValue (.string quotientImmutableKey)) = a₂) :
    Step (OD c g) [[]] [] st (.stmts bindLocalsFromImmutables)
      (.sres [("quotientEvaluator", a₂), ("vk", a₁)] st .normal) := by
  have hvk : Step (OD c g) [[]] [] st (.expr (Expr.builtin Op.loadimmutable
      [Expr.lit (.string vkImmutableKey)]))
      (.eres (.vals [a₁] st)) :=
    bi1 (c := c) (g := g) (op := Op.loadimmutable) (st' := st) (e := Expr.lit (.string vkImmutableKey))
      (v := litValue (.string vkImmutableKey)) (u := a₁) (funs := [[]]) (V := []) (st := st)
      (Step.lit (D := OD c g) (l := Literal.string vkImmutableKey) (funs := [[]]) (V := [])
        (st := st))
      (by rw [← h₁]; rfl : (OD c g).Builtin Op.loadimmutable
        [litValue (.string vkImmutableKey)] st (.ok [a₁] st))
  have hq : Step (OD c g) [[]] [("vk", a₁)] st (.expr (Expr.builtin Op.loadimmutable
      [Expr.lit (.string quotientImmutableKey)]))
      (.eres (.vals [a₂] st)) :=
    bi1 (c := c) (g := g) (op := Op.loadimmutable) (st' := st)
      (e := Expr.lit (.string quotientImmutableKey)) (v := litValue (.string quotientImmutableKey))
      (u := a₂) (funs := [[]]) (V := [("vk", a₁)]) (st := st)
      (Step.lit (D := OD c g) (l := Literal.string quotientImmutableKey) (funs := [[]])
        (V := [("vk", a₁)]) (st := st))
      (by rw [← h₂]; rfl : (OD c g).Builtin Op.loadimmutable
        [litValue (.string quotientImmutableKey)] st (.ok [a₂] st))
  have h1 : Step (OD c g) [[]] [] st (.stmt (Stmt.letDecl ["vk"]
        (some (Expr.builtin Op.loadimmutable [Expr.lit (.string vkImmutableKey)]))))
      (.sres [("vk", a₁)] st .normal) :=
    Step.letVal (D := OD c g) (vars := ["vk"]) (vals := [a₁])
      (e := Expr.builtin Op.loadimmutable [Expr.lit (.string vkImmutableKey)])
      (st1 := st) (funs := [[]]) (V := []) (st := st) hvk rfl
  have h2 : Step (OD c g) [[]] [("vk", a₁)] st
      (.stmt (Stmt.letDecl ["quotientEvaluator"]
        (some (Expr.builtin Op.loadimmutable [Expr.lit (.string quotientImmutableKey)]))))
      (.sres [("quotientEvaluator", a₂), ("vk", a₁)] st .normal) :=
    Step.letVal (D := OD c g) (vars := ["quotientEvaluator"]) (vals := [a₂])
      (e := Expr.builtin Op.loadimmutable [Expr.lit (.string quotientImmutableKey)])
      (st1 := st) (funs := [[]]) (V := [("vk", a₁)]) (st := st) hq rfl
  show Step (OD c g) [[]] [] st (.stmts bindLocalsFromImmutables)
    (.sres [("quotientEvaluator", a₂), ("vk", a₁)] st .normal)
  exact seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := st) (V₁ := [("vk", a₁)])
    (st₁ := st) (V₂ := [("quotientEvaluator", a₂), ("vk", a₁)]) (st₂ := st)
    (o := .normal) h1 (seqC (c := c) (g := g) (funs := [[]]) (V := [("vk", a₁)]) (st := st)
      (V₁ := [("quotientEvaluator", a₂), ("vk", a₁)]) (st₁ := st) h2
      (seqN (c := c) (g := g) (funs := [[]]) (V := [("quotientEvaluator", a₂), ("vk", a₁)])
        (st := st)))

/-- The two bindings read the two keys the deployment pins, spelled as a gate so a swap of the
    KEYS (not just of a name) reddens the KAT even where the theorem above is not applied. -/
def bindLocals_keys_are_the_pinned_ones : Bool :=
  match bindLocalsFromImmutables with
  | [Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string k₁)])),
     Stmt.letDecl ["quotientEvaluator"] (some (Expr.builtin Op.loadimmutable
       [Expr.lit (.string k₂)]))] => k₁ == vkImmutableKey && k₂ == quotientImmutableKey
  | _ => false

/-- The getter arm really returns 32 bytes - the shape `abi_encode_tuple_t_address` emits -
    rather than falling off the end. Ungated before this line was added, and a control that changed
    `return` to `stop` proved it was invisible. -/
def getter_arm_returns_one_word : Bool :=
  authorizedVkArm.any fun s => match s with
    | Stmt.exprStmt (Expr.builtin Op.ret [_, Expr.lit (.number 32)]) => true
    | _ => false

/-- **THE HYPOTHESES ARE THE ONES DOING THE WORK (D-P23, second half).** At the well-formed
    calldata every dispatcher test the falsifications name answers the OTHER way: the size test
    enters the switch, the selector routes, the head region is present, the offset and length
    ceilings are respected, the length word is inside the calldata, and - the one falsification 3
    needs - the tail test does NOT fire. The truncated calldata differs in that last answer and
    in nothing else the model looks at. -/
theorem falsification_hypotheses_are_load_bearing :
    sizeTestValue (frame cdWellFormed 0) = 1 ∧
      selectorWord (frame cdWellFormed 0) = selectorVerifyProof ∧
      headLengthValue (frame cdWellFormed 0) = 0 ∧
      wordFrom (frame cdWellFormed 0).env.calldata headStart.toNat = 64 ∧
      ceilingValue (64 : U256) = 0 ∧
      lengthPresentValue (headStart + 64) (frame cdWellFormed 0) = 0 ∧
      wordFrom (frame cdWellFormed 0).env.calldata (headStart + 64).toNat = 64 ∧
      tailValue (headStart + 64) (64 * 1) (frame cdWellFormed 0) = 0 ∧
      tailValue (headStart + 64) (100 * 1) (frame cdTruncatedProof 0) = 1 ∧
      selectorWord (frame cdWrongSelector 0) ≠ selectorVerifyProof ∧
      selectorWord (frame cdWrongSelector 0) ≠ selectorAuthorizedVk ∧
      (frame cdWellFormed 0).env.callvalue = 0 ∧ (frame cdWellFormed 1).env.callvalue ≠ 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, by decide⟩

/-! ### 6. The difference between the old shell model and this one, as theorems -/

/-- The OLD model's entry path, spelled as a block: the head guard `if gt(mload(0x40), 0x1000)
    revert(0,0)` and then straight into the program. This is what `shell_unfolds` pins
    (`shell.codeBlock = L.headGuard ++ bindLocals ++ L.main`) and what the fixture's
    `fxHeadGuard` installs. -/
def oldShell (body : YulBlock) : YulBlock :=
  [Stmt.cond (Expr.builtin Op.gt [Expr.builtin Op.mload [w fmpAddr], w 0x1000]) [revert00]] ++ body

/-- The state a `return(0,0)` leaves, as a definition: the structure-update notation needs a
    variable head, and the old-model proof below has a compound term to update. -/
def retState (st : EvmState) : EvmState :=
  { touchMemory st 0 0 with halted := some (.ret, readBytes st.memory 0 0) }

/-- **THE OLD MODEL RUNS THE VERIFIER ON A WRONG-SELECTOR CALLDATA.** Same frame as
    `wrong_selector_reverts_at_witness`, same body: the old model does not revert, it
    returns. -/
theorem old_shell_runs_the_verifier_on_the_same_frame :
    ∃ st', Run c g (oldShell retBody) (frame cdWrongSelector 0) [] st' .halt ∧
      st'.halted = some (.ret, []) := by
  have hmload : Step (OD c g) [[]] [] (frame cdWrongSelector 0)
      (.expr (Expr.builtin Op.mload [w fmpAddr]))
      (.eres (.vals [0] (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))) :=
    bi1 (c := c) (g := g) (op := Op.mload) (e := w fmpAddr)
      (st := frame cdWrongSelector 0) (st' := frame cdWrongSelector 0)
      (st₂ := touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)
      (v := fmpAddr) (u := 0) (wlit_eval fmpAddr)
      (rfl : (OD c g).Builtin Op.mload [fmpAddr] (frame cdWrongSelector 0)
        (.ok [0] (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)))
  have hgt : Step (OD c g) [[]] [] (frame cdWrongSelector 0)
      (.expr (Expr.builtin Op.gt [Expr.builtin Op.mload [w fmpAddr], w 0x1000]))
      (.eres (.vals [0] (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))) :=
    bi2 (c := c) (g := g) (op := Op.gt) (e₁ := Expr.builtin Op.mload [w fmpAddr]) (e₂ := w 0x1000)
      (st := frame cdWrongSelector 0) (s₁ := frame cdWrongSelector 0)
      (s₂ := touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)
      (v₁ := 0) (v₂ := 0x1000) (u := 0)
      (wlit_eval 0x1000) hmload
      (rfl : (OD c g).Builtin Op.gt [0, 0x1000]
        (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32) (.ok [0]
          (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)))
  have hcond : Step (OD c g) [[]] [] (frame cdWrongSelector 0)
      (.stmt (Stmt.cond (Expr.builtin Op.gt [Expr.builtin Op.mload [w fmpAddr], w 0x1000])
        [revert00])) (.sres ([] : VEnv (OD c g))
        (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32) .normal) :=
    Step.ifFalse (D := OD c g) (funs := [[]]) (V := []) (st := frame cdWrongSelector 0)
      (body := [revert00]) hgt (zero_eq_zero (c := c) (g := g))
  have hret : Step (OD c g) [[]] [] (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)
      (.stmt (Stmt.exprStmt (Expr.builtin Op.ret [w 0, w 0])))
      (.sres ([] : VEnv (OD c g)) (retState (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)) .halt) :=
    Step.exprStmtHalt (D := OD c g) (funs := [[]]) (V := []) (st := (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))
      (e := Expr.builtin Op.ret [w 0, w 0]) (st1 := retState (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))
      (Step.builtinHalt (D := OD c g) (funs := [[]]) (V := []) (st := (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))
        (op := Op.ret) (args := [w 0, w 0]) (argvals := [0, 0]) (st1 := (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))
        (st2 := retState (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))
        (wlits_eval (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32) [0, 0])
        (rfl : (OD c g).Builtin Op.ret [0, 0] (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32) (.halt (retState (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)))))
  have hstmts : Step (OD c g) [[]] [] (frame cdWrongSelector 0) (.stmts (oldShell retBody))
      (.sres [] { touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32 with
                  halted := some (.ret, []) } .halt) :=
    seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := frame cdWrongSelector 0)
      (rest := [Stmt.exprStmt (Expr.builtin Op.ret [w 0, w 0])]) (V₁ := [])
      (st₁ := touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32) (V₂ := [])
      (st₂ := retState (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)) (o := .halt) hcond
      (seqStopH (c := c) (g := g) (funs := [[]]) (V := [])
        (st := touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32)
        (s₁ := Stmt.exprStmt (Expr.builtin Op.ret [w 0, w 0])) (rest := []) (V₁ := [])
        (st₁ := { touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32 with
                     halted := some (.ret, []) }) hret)
  exact ⟨_, blk (c := c) (g := g) (funs := []) (V := []) (st := frame cdWrongSelector 0)
      (body := oldShell retBody) (V₁ := [])
      (st₁ := retState (touchMemory (frame cdWrongSelector 0) fmpAddr.toNat 32))
      (o := .halt) hstmts, rfl⟩

/-- **AND THE NEW MODEL REVERTS ON THAT EXACT FRAME AND BODY.** -/
theorem new_shell_reverts_on_the_same_frame_and_body :
    ∃ st', Run c g (dispatcher retBody) (frame cdWrongSelector 0) [] st' .halt ∧
      st'.halted = some (.revert, []) :=
  wrong_selector_reverts_at_witness (body := retBody)

/-- The two halt kinds differ, spelled as the `ObsView` field `ObsEquiv` reads:
    `halted : Option (HaltKind × List UInt8)`. So `RunShell` and
    `ShellModel.wrap` are NOT equivalent on a wrong-selector calldata, and no proof of
    `ir_refines` can transport through the old shell - which is the required finding's
    first half. -/
theorem old_and_new_differ_in_the_observable_halt :
    (some (.ret, []) : Option (HaltKind × List UInt8)) ≠ some (.revert, []) := by
  intro h
  exact HaltKind.noConfusion (congrArg Prod.fst (Option.some.inj h))


/-- **THE UNROUTABLE INPUT.** A calldata shorter than a selector: the size test does not fire, the
    switch is skipped, and the dispatcher falls through to `revert(0,0)` - the same thing the
    artifact's `revert_error_42b3…()` is. This is the input `Instances/ImportedIR.lean`
    runs the REAL artifact on, so it is the one input where model and artifact can be compared
    today, and `ImportedIR.model_and_artifact_agree_on_the_unroutable_input` does compare them. -/
theorem unroutable_calldata_reverts {body : YulBlock} {st₀ : EvmState}
    (hsize : sizeTestValue st₀ = 0) :
    exists st', Run c g (dispatcher body) st₀ [] st' .halt ∧
      st'.halted = some (.revert, []) := by
  let st₁ := stAfterPrologue st₀
  have hprol : Step (OD c g) [[]] [] st₀
      (.stmt (Stmt.exprStmt (Expr.builtin Op.mstore [w fmpAddr,
        Expr.builtin Op.memoryguard [w irMemoryguardReservation]])))
      (.sres [] st₁ .normal) := prologueStmtStep (c := c) (g := g)
  have htest : Step (OD c g) [[]] [] st₁ (.expr calldatasizeTest) (.eres (.vals [0] st₁)) := by
    have e := calldatasizeTest_val (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
    rw [show sizeTestValue st₁ = sizeTestValue st₀ from rfl, hsize] at e
    exact e
  have hcond : Step (OD c g) [[]] [] st₁
      (.stmt (Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body]))
      (.sres ([] : VEnv (OD c g)) st₁ .normal) :=
    Step.ifFalse (D := OD c g) (funs := [[]]) (V := []) (st := st₁)
      (body := [selectorDecl, selectorSwitch body]) htest (zero_eq_zero (c := c) (g := g))
  have hrv : Step (OD c g) [[]] [] st₁ (.stmt revert00) (.sres [] (revertState st₁) .halt) :=
    revert00_step (c := c) (g := g)
  have hstmts : Step (OD c g) [[]] [] st₀ (.stmts (dispatcher body))
      (.sres [] (revertState st₁) .halt) :=
    seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := st₀)
      (rest := [Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body], revert00])
      (V₁ := []) (st₁ := st₁) (V₂ := []) (st₂ := revertState st₁) (o := .halt) hprol
      (seqC (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁)
        (s₁ := Stmt.cond calldatasizeTest [selectorDecl, selectorSwitch body]) (rest := [revert00])
        (V₁ := []) (st₁ := st₁) (V₂ := []) (st₂ := revertState st₁) (o := .halt) hcond
        (seqStopH (c := c) (g := g) (funs := [[]]) (V := []) (st := st₁) (s₁ := revert00)
          (rest := []) (V₁ := []) (st₁ := revertState st₁) hrv))
  exact ⟨revertState st₁, blk (c := c) (g := g) (funs := []) (V := []) (st := st₀)
      (body := dispatcher body) (V₁ := []) (st₁ := revertState st₁) (o := .halt) hstmts,
    rfl⟩

/-- The empty calldata is the model's own `sizeTestValue = 0` case, computed: the same answer
    the artifact gives on `ImportedIR`'s witness input. -/
theorem size_test_skips_the_switch_on_empty_calldata :
    sizeTestValue (frame [] 0) = 0 := rfl

/-! ### 7. The falsifications at `wrap`, and the statement IRCheck will cite -/

/-- **FALSIFICATION 1 AT `wrap`** - the level `IRCheck`'s theorem cites. On a
    wrong-selector calldata the dispatcher model has a revert observation, and it leaves the world
    unchanged: the abort happens before anything writes. -/
theorem wrong_selector_reverts_wrap {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Hash)
    (cd : Bytes)
    (hsize : sizeTestValue (callState W S.shellLayout H cd) = 1)
    (hsel : selectorWord (callState W S.shellLayout H cd) ≠ selectorVerifyProof)
    (hsel2 : selectorWord (callState W S.shellLayout H cd) ≠ selectorAuthorizedVk) :
    exists obs, wrap S W H cd c (ExternalGas.ofFun fun _ => 0) obs ∧ obs.isRevertOrHalt ∧
      obs.worldUnchanged (callState W S.shellLayout H cd) := by
  obtain ⟨st', hrun, hhalt⟩ := wrong_selector_reverts (body := armBody S) hsize hsel hsel2
  set st₀ := callState W S.shellLayout H cd
  refine ⟨⟨committedState st₀ st', .halt⟩, ⟨[], ⟨st', hrun, rfl⟩⟩,
    ⟨.revert, [], by rw [committedState_rollback hhalt rfl, hhalt], rfl⟩, worldUnchanged_of_rollback hhalt rfl⟩

/-- **FALSIFICATION 2 AT `wrap`.** -/
theorem nonzero_callvalue_reverts_wrap {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Hash)
    (cd : Bytes)
    (hsize : sizeTestValue (callState W S.shellLayout H cd) = 1)
    (hsel : selectorWord (callState W S.shellLayout H cd) = selectorVerifyProof)
    (hcv : (callState W S.shellLayout H cd).env.callvalue ≠ 0) :
    exists obs, wrap S W H cd c (ExternalGas.ofFun fun _ => 0) obs ∧ obs.isRevertOrHalt ∧
      obs.worldUnchanged (callState W S.shellLayout H cd) := by
  obtain ⟨st', hrun, hhalt⟩ := nonzero_callvalue_reverts (body := armBody S) hsize hsel hcv
  set st₀ := callState W S.shellLayout H cd
  refine ⟨⟨committedState st₀ st', .halt⟩, ⟨[], ⟨st', hrun, rfl⟩⟩,
    ⟨.revert, [], by rw [committedState_rollback hhalt rfl, hhalt], rfl⟩, worldUnchanged_of_rollback hhalt rfl⟩

/-- **FALSIFICATION 3 AT `wrap`.** -/
theorem truncated_bytes_reverts_wrap {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Hash)
    (cd : Bytes)
    (hsize : sizeTestValue (callState W S.shellLayout H cd) = 1)
    (hsel : selectorWord (callState W S.shellLayout H cd) = selectorVerifyProof)
    (hcv : (callState W S.shellLayout H cd).env.callvalue = 0)
    (hheads : headLengthValue (callState W S.shellLayout H cd) = 0)
    {po : U256} (hpo : wordFrom (callState W S.shellLayout H cd).env.calldata headStart.toNat = po)
    (hpoBound : ceilingValue po = 0)
    (hlenPresent : lengthPresentValue (headStart + po) (callState W S.shellLayout H cd) = 0)
    {pl : U256}
    (hpl : wordFrom (callState W S.shellLayout H cd).env.calldata (headStart + po).toNat = pl)
    (hplBound : ceilingValue pl = 0)
    (htrunc : tailValue (headStart + po) (pl * 1) (callState W S.shellLayout H cd) = 1) :
    exists obs, wrap S W H cd c (ExternalGas.ofFun fun _ => 0) obs ∧ obs.isRevertOrHalt ∧
      obs.worldUnchanged (callState W S.shellLayout H cd) := by
  obtain ⟨st', hrun, hhalt⟩ :=
    truncated_bytes_reverts (body := armBody S) hsize hsel hcv hheads hpo hpoBound hlenPresent
      hpl hplBound htrunc
  set st₀ := callState W S.shellLayout H cd
  refine ⟨⟨committedState st₀ st', .halt⟩, ⟨[], ⟨st', hrun, rfl⟩⟩,
    ⟨.revert, [], by rw [committedState_rollback hhalt rfl, hhalt], rfl⟩, worldUnchanged_of_rollback hhalt rfl⟩

/-- **THE REQUIRED FINDING, AS A TYPE.** PLAN section 7 line 228's
    `irCheck ir L = true -> ObsEquiv ir (ShellModel.wrap L)` becomes statable: both sides are
    predicates on the same `Obs`, over the same Surface, world, hash, calldata, call relation
    and gas oracle. Compare `LoweringCorrect.ir_refines`, whose right-hand side is
    `RunShell`: `wrap` has `RunShell`'s exact arity, so `ir_refines` can be
    restated with the dispatcher model in place of the head-guard model without touching anything
    else. Whether it is TRUE for the pinned `ir` is `IRCheck.lean`'s question; that it
    STATES is this file's answer. -/
example : Prop :=
  ∀ {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Hash) (ir : YulObject)
      (irLyt : EVM.Layout) (cd : Bytes) (c : ExternalCalls) (g₀ : U256),
    ObsEquiv (RunContractIR S W H ir irLyt cd c (ExternalGas.ofFun fun _ => g₀))
      (wrap S W H cd c (ExternalGas.ofFun fun _ => g₀))

/-! ### 8. Cross-check against the pinned artifact's dispatcher -/

/-- The artifact's own first three deployed-runtime statements: prologue, guarded switch,
    fall-through. `ImportedIR.irRuntime_shape` already pins these propositionally; this is
    the same fact read as a comparison against the MODEL. -/
def artifactHead3 : List (Stmt EVM.Op) := Midfall.Yul.Ir.verifierRuntime.take 3

/-- **THE MODEL'S PROLOGUE IS THE ARTIFACT'S PROLOGUE.** `mstore(64, memoryguard(128))`,
    statement for statement, under the vendored structural comparator - and DECISION 1's
    `memoryguard(128)` rather than the optimizer's `0x08e0`, which is the trusted hop
    appearing in the model as a number. -/
def model_prologue_is_the_artifacts : Bool := SyntaxEq.stmtsBeq (artifactHead3.take 1) prologue

/-- **THE MODEL'S SIZE TEST IS THE ARTIFACT'S SIZE TEST**: `iszero(lt(calldatasize(), 4))`,
    the second statement of the deployed block, compared structurally. -/
def model_size_test_is_the_artifacts : Bool :=
  match artifactHead3 with
  | _ :: Stmt.cond c _ :: _ => SyntaxEq.exprBeq c calldatasizeTest
  | _ => false

/-- **THE ARTIFACT ROUTES ON `verifyProof(bytes,uint256[])` at 0x1e8e1e13**, read out of the
    imported AST rather than typed by hand: the case labels of the deployed block's switch. This is
    the tie between `selectorVerifyProof` here and the artifact there. -/
def artifact_case_labels : Bool :=
  match artifactHead3 with
  | _ :: Stmt.cond _ (Stmt.letDecl _ _ :: Stmt.switch _ cases _ :: _) :: _ =>
      (cases.any fun p => p.1 == Literal.number 0x1e8e1e13) && cases.length == 2
  | _ => false

/-- The selector constant is the generator's own `fnSigVerifyProof`, not a re-typed number. -/
theorem model_selector_is_the_generators :
    bytesToNatBE Midfall.Generator.fnSigVerifyProof = selectorVerifyProof.toNat := rfl

/-- **THE SHAPE DIFFERENCE `IRCheck` HAS TO DISCHARGE**, recorded rather than hidden: the
    artifact routes the selector shift through a declared helper
    `shift_right_224_unsigned(calldataload(0))` and every abort through a named
    `revert_error_<digest>()`, while the model inlines `shr` and `revert(0,0)`.
    Under Fable's definition ($α$-equivalence modulo constant substitution and solc renames) a
    one-call helper whose body is the operation is the same program - but that is a check
    `IRCheck.lean` has to implement and prove, not something this file may assume. -/
def artifact_uses_named_helpers_where_the_model_inlines : Bool :=
  (match artifactHead3 with
   | _ :: Stmt.cond _ (Stmt.letDecl _ (some (Expr.call "shift_right_224_unsigned" _)) :: _) :: _ =>
       true
   | _ => false) &&
  (match Midfall.Yul.Ir.verifierRuntime.drop 2 with
   | Stmt.exprStmt (Expr.call fn []) :: _ => fn.take 13 == "revert_error_"
   | _ => false)

/-! ### 9. Gate -/

/-- **THE GATE.** Every line is a fact the theorems above depend on, recomputed by
    `kat_gate.py`: the selector tie to the generator, the prologue and size-test agreement
    with the pinned artifact, the arm's shape, and the three witness frames' own test values -
    including the pair that makes falsification 3 load-bearing (the tail test answers 1 on the
    truncated calldata and 0 on the well-formed one). -/
def shellModelKats_ok : Bool :=
  model_prologue_is_the_artifacts &&
    model_size_test_is_the_artifacts &&
    artifact_case_labels &&
    artifact_uses_named_helpers_where_the_model_inlines &&
    selectorVerifyProof.toNat == 0x1e8e1e13 &&
    selectorAuthorizedVk.toNat == 0x42b72597 &&
    SyntaxEq.stmtsBeq (artifactHead3.take 1) prologue &&
    (match artifactHead3 with
      | _ :: Stmt.cond c _ :: _ => SyntaxEq.exprBeq c calldatasizeTest
      | _ => false) &&
    (dispatcher retBody).length == 3 &&
    (verifyProofArm retBody).length == 17 &&
    bindLocalsFromImmutables.length == 2 &&
    bindLocals_keys_are_the_pinned_ones &&
    getter_arm_returns_one_word &&
    abiDecode.length == 13 &&
    (caseList retBody).length == 2 &&
    sizeTestValue (frame cdWrongSelector 0) == 1 &&
    selectorWord (frame cdWrongSelector 0) == 0xdeadbeef &&
    sizeTestValue (frame cdWellFormed 0) == 1 &&
    selectorWord (frame cdWellFormed 0) == selectorVerifyProof &&
    (frame cdWellFormed 7).env.callvalue != 0 &&
    tailValue (headStart + 64) (100 * 1) (frame cdTruncatedProof 0) == 1 &&
    tailValue (headStart + 64) (64 * 1) (frame cdWellFormed 0) == 0 &&
    headLengthValue (frame cdWellFormed 0) == 0 &&
    lengthPresentValue (headStart + 64) (frame cdWellFormed 0) == 0 &&
    ceilingValue 64 == 0 && ceilingValue 100 == 0 &&
    -- the empty-calldata case the ImportedIR witness runs: the switch is skipped
    sizeTestValue (frame [] 0) == 0 &&
    -- and the old model has no dispatch at all: that is the gap this file closes
    (oldShell retBody).any (fun s => match s with
      | Stmt.cond c _ => SyntaxEq.exprBeq c calldatasizeTest
      | _ => false) == false &&
    (dispatcher retBody).any (fun s => match s with
      | Stmt.cond c _ => SyntaxEq.exprBeq c calldatasizeTest
      | _ => false) == true

#print axioms Midfall.Yul.ShellModel.shellModelKats_ok
#eval shellModelKats_ok                       -- expect true

/-! ### Axiom audit -/

-- The three falsifications must be derivations, not assumptions. Expected: no sorryAx, and no
-- axiom beyond what the vendored semantics' own quotation machinery uses.
#print axioms Midfall.Yul.ShellModel.wrong_selector_reverts
#print axioms Midfall.Yul.ShellModel.nonzero_callvalue_reverts
#print axioms Midfall.Yul.ShellModel.truncated_bytes_reverts
#print axioms Midfall.Yul.ShellModel.old_shell_runs_the_verifier_on_the_same_frame

/-! ### 10. P-LOWEQ: the transport from 'wrap' to the lowered program -/

/-- Everything the 'verifyProof' arm runs before the lowered program: the callvalue guard, the
thirteen ABI-decode statements and the two immutable bindings. -/
def armPrefix : YulBlock := callvalueGuard :: abiDecode ++ bindLocalsFromImmutables

/-- The arm is the prefix and the program and nothing else, definitionally. -/
theorem verifyProofArm_eq_armPrefix (body : YulBlock) :
    verifyProofArm body = armPrefix ++ body := rfl

/-- **THE PROGRAM HALF OF THE KEY LEMMA.** The 'verifyProof' arm runs
'S.L.headGuard ++ S.bindLocals ++ S.L.main', which is LITERALLY the program 'RunVerifier' runs
(Surface.lean:799), and under the surface pin 'shell_unfolds' it is also 'S.shell.codeBlock'. The
dispatcher puts an entry path in front of the verifier program; it does not replace it. This is a
'rfl', and that is the point: there is no second copy of the program anywhere in the transport. -/
theorem armBody_is_the_verifier_program (S : Surface p G₁ G₂ Gₜ) :
    armBody S = S.L.headGuard ++ S.bindLocals ++ S.L.main := rfl

/-- The same identification through the pin that makes 'RunShell' and 'RunVerifier' one program
(R-58 F3). -/
theorem armBody_eq_shell_codeBlock (S : Surface p G₁ G₂ Gₜ) :
    S.shell.codeBlock = armBody S := S.shell_unfolds

/-- The four tests one dynamic ABI argument must pass: offset ceiling, length presence, length
ceiling, tail bound. 'stride' is 1 for 'bytes' and 32 for 'uint256[]'. -/
def argAccepted (st₀ : EvmState) (head stride : U256) : Prop :=
  let off := wordFrom st₀.env.calldata head.toNat
  ceilingValue off = 0 ∧ lengthPresentValue (headStart + off) st₀ = 0 ∧
    (let len := wordFrom st₀.env.calldata (headStart + off).toNat
     ceilingValue len = 0 ∧ tailValue (headStart + off) (len * stride) st₀ = 0)

/-- **THE DISPATCHER ACCEPTS THE CALLDATA.** Every test the entry path performs answers PASS at
the frame 'st₀': the size test enters the switch, the selector routes to 'verifyProof', the
callvalue is zero, the head region is present, and both dynamic arguments clear their four
bounds. This is a condition on the FRAME, not on a Surface or a deployment, which is what makes it
usable as the hypothesis of a transport that has to work at every Surface. -/
def dispatcherAccepts (st₀ : EvmState) : Prop :=
  sizeTestValue st₀ = 1 ∧ selectorWord st₀ = selectorVerifyProof ∧
    st₀.env.callvalue = 0 ∧ headLengthValue st₀ = 0 ∧
    argAccepted st₀ headStart 1 ∧ argAccepted st₀ (headStart + 32) 32

/-- The environment the selector declaration leaves. -/
def selEnv (st₀ : EvmState) : VEnv (OD c g) := [("selector", selectorWord st₀)]

/-- The word the arm's 'vk' binding reads at this frame. -/
def immVk (st₀ : EvmState) : U256 := st₀.env.immutable (litValue (.string vkImmutableKey))

/-- Its twin for the quotient evaluator. -/
def immQuotient (st₀ : EvmState) : U256 :=
  st₀.env.immutable (litValue (.string quotientImmutableKey))

/-- The first dynamic head, read off the frame. -/
def proofOffsetAt (st₀ : EvmState) : U256 := wordFrom st₀.env.calldata headStart.toNat

/-- The 'bytes' length word, at 'headStart + proofOffsetAt'. -/
def proofLengthAt (st₀ : EvmState) : U256 :=
  wordFrom st₀.env.calldata (headStart + proofOffsetAt st₀).toNat

/-- The second dynamic head. -/
def instancesOffsetAt (st₀ : EvmState) : U256 :=
  wordFrom st₀.env.calldata (headStart + 32).toNat

/-- The 'uint256[]' length word. -/
def instancesLengthAt (st₀ : EvmState) : U256 :=
  wordFrom st₀.env.calldata (headStart + instancesOffsetAt st₀).toNat

/-- The environment the thirteen decode statements leave, innermost binding first. Written flat;
it is definitionally the cons chain the 'letVal' steps build, which is what makes the transport's
environment close by 'rfl'. -/
def decodeEnv (st₀ : EvmState) : VEnv (OD c g) :=
  [("instancesLength", instancesLengthAt st₀), ("instancesOffset", instancesOffsetAt st₀),
    ("proofLength", proofLengthAt st₀), ("proofOffset", proofOffsetAt st₀),
    ("selector", selectorWord st₀)]

/-- The decode environment plus the 'vk' binding: what the second immutable let starts from. -/
def vkEnv (st₀ : EvmState) : VEnv (OD c g) :=
  [("vk", immVk st₀), ("instancesLength", instancesLengthAt st₀),
    ("instancesOffset", instancesOffsetAt st₀), ("proofLength", proofLengthAt st₀),
    ("proofOffset", proofOffsetAt st₀), ("selector", selectorWord st₀)]

/-- The environment the whole arm prefix leaves: the two immutable bindings on top of the decode
values. -/
def armEnv (st₀ : EvmState) : VEnv (OD c g) :=
  [("quotientEvaluator", immQuotient st₀), ("vk", immVk st₀),
    ("instancesLength", instancesLengthAt st₀), ("instancesOffset", instancesOffsetAt st₀),
    ("proofLength", proofLengthAt st₀), ("proofOffset", proofOffsetAt st₀),
    ("selector", selectorWord st₀)]

/-- **THE FRAME THE ARM EXECUTES IN**: the deployment frame after the dispatcher's prologue. -/
def armFrame (st₀ : EvmState) : EvmState := stAfterPrologue st₀

/-- The function scopes the 'verifyProof' arm block sees inside the dispatcher. -/
def armFuns (body : YulBlock) : FunEnv (OD c g) :=
  hoist (OD c g) (verifyProofArm body) ::
    hoist (OD c g) [selectorDecl, selectorSwitch body] :: [[]]

/-- **THE ENTRY PATH CONTRIBUTES NO HALT.** On a calldata the dispatcher accepts, the whole
'verifyProof' arm prefix - callvalue guard, thirteen decode statements, two immutable bindings -
runs to '.normal' in the frame the prologue leaves, and the environment it leaves is 'armEnv'.

This is the lemma the three falsifications' own docstrings promise and which was NOT in the file:
'calldatasizeTest_passes' (cited at line 708), 'zero_callvalue_reaches_the_body' (cited at line
869) and 'wellformed_calldata_reaches_the_body' (cited at line 931) are three names that appear
nowhere in the tree but in those three comments. The falsifications showed the guards FIRE;
nothing showed them PASS. Recorded as a finding in the package report rather than fixed silently. -/
theorem armPrefix_passes {st₀ : EvmState} (hacc : dispatcherAccepts st₀)
    {F : FunEnv (OD c g)} {P : YulBlock} {V' : VEnv (OD c g)} {st' : EvmState} {o : Outcome}
    (hP : Step (OD c g) F (armEnv st₀) (armFrame st₀) (.stmts P) (.sres V' st' o)) :
    Step (OD c g) F (selEnv st₀) (armFrame st₀) (.stmts (armPrefix ++ P))
      (.sres V' st' o) := by
  obtain ⟨hsz, hselv, hcv, hheads, hproof, hinst⟩ := hacc
  obtain ⟨hpoBound, hpoPresent, hplBound, hplTail⟩ := hproof
  obtain ⟨hioBound, hioPresent, hilBound, hilTail⟩ := hinst
  -- 'argAccepted' spells its two values with a 'let', so the four facts above arrive in the
  -- unfolded form. Re-state them at the named definitions the proof uses; each is 'rfl'.
  have hpoBound' : ceilingValue (proofOffsetAt st₀) = 0 := hpoBound
  have hpoPresent' : lengthPresentValue (headStart + proofOffsetAt st₀) st₀ = 0 := hpoPresent
  have hplBound' : ceilingValue (proofLengthAt st₀) = 0 := hplBound
  have hplTail' : tailValue (headStart + proofOffsetAt st₀) (proofLengthAt st₀ * 1) st₀ = 0 :=
    hplTail
  have hioBound' : ceilingValue (instancesOffsetAt st₀) = 0 := hioBound
  have hioPresent' : lengthPresentValue (headStart + instancesOffsetAt st₀) st₀ = 0 := hioPresent
  have hilBound' : ceilingValue (instancesLengthAt st₀) = 0 := hilBound
  have hilTail' : tailValue (headStart + instancesOffsetAt st₀) (instancesLengthAt st₀ * 32) st₀
      = 0 := hilTail
  let st₁ := armFrame st₀
  let V₂ : VEnv (OD c g) :=
    [("proofOffset", proofOffsetAt st₀), ("selector", selectorWord st₀)]
  let V₃ : VEnv (OD c g) :=
    [("proofLength", proofLengthAt st₀), ("proofOffset", proofOffsetAt st₀),
      ("selector", selectorWord st₀)]
  let V₄ : VEnv (OD c g) :=
    [("instancesOffset", instancesOffsetAt st₀), ("proofLength", proofLengthAt st₀),
      ("proofOffset", proofOffsetAt st₀), ("selector", selectorWord st₀)]
  -- 1. the callvalue guard passes
  have hcvs : Step (OD c g) F (selEnv st₀) st₁ (.expr (Expr.builtin Op.callvalue []))
      (.eres (.vals [0] st₁)) := by
    have e := callvalueStep (funs := F) (V := selEnv st₀) (st := st₁)
    rw [show st₁.env.callvalue = st₀.env.callvalue from rfl, hcv] at e
    exact e
  have h1 : Step (OD c g) F (selEnv st₀) st₁ (.stmt callvalueGuard)
      (.sres (selEnv st₀) st₁ .normal) :=
    guardPasses (funs := F) (V := selEnv st₀) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.callvalue []) hcvs
  -- 2. the head-region guard passes
  have hheads' : Step (OD c g) F (selEnv st₀) st₁ (.expr (Expr.builtin Op.slt
        [Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart], w tupleHeadBytes]))
      (.eres (.vals [0] st₁)) := by
    have e := headLengthTest_val (funs := F) (V := selEnv st₀) (st := st₁)
    rw [show headLengthValue st₁ = headLengthValue st₀ from rfl, hheads] at e
    exact e
  have h2 : Step (OD c g) F (selEnv st₀) st₁ (.stmt headLengthGuard)
      (.sres (selEnv st₀) st₁ .normal) :=
    guardPasses (funs := F) (V := selEnv st₀) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.slt
        [Expr.builtin Op.sub [Expr.builtin Op.calldatasize [], w headStart], w tupleHeadBytes])
      hheads'
  -- 3. let proofOffset := calldataload(add(headStart, 0))
  have hpo' : Step (OD c g) F (selEnv st₀) st₁ (.expr (Expr.builtin Op.calldataload
        [Expr.builtin Op.add [w headStart, w 0]])) (.eres (.vals [proofOffsetAt st₀] st₁)) := by
    have e := headLoad_val (funs := F) (V := selEnv st₀) (st := st₁) 0
    rw [show wordFrom st₁.env.calldata (headStart + 0).toNat = proofOffsetAt st₀ from rfl] at e
    exact e
  have h3 : Step (OD c g) F (selEnv st₀) st₁ (.stmt proofOffsetDecl) (.sres V₂ st₁ .normal) :=
    Step.letVal (vars := ["proofOffset"]) (vals := [proofOffsetAt st₀])
      (e := Expr.builtin Op.calldataload [Expr.builtin Op.add [w headStart, w 0]])
      (st1 := st₁) (funs := F) (V := selEnv st₀) (st := st₁) hpo' rfl
  -- 4. the proof offset ceiling passes
  have h4e : Step (OD c g) F V₂ st₁
      (.expr (Expr.builtin Op.gt [Expr.var "proofOffset", w abiLengthCeiling]))
      (.eres (.vals [0] st₁)) := by
    have e := ceilingTest_val (funs := F) (V := V₂) (st := st₁) (y := "proofOffset")
      (x := proofOffsetAt st₀) (rfl : VEnv.get V₂ "proofOffset" = some (proofOffsetAt st₀))
    rw [hpoBound'] at e
    exact e
  have h4 : Step (OD c g) F V₂ st₁ (.stmt (offsetCeilingGuard "proofOffset"))
      (.sres V₂ st₁ .normal) :=
    guardPasses (funs := F) (V := V₂) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.var "proofOffset", w abiLengthCeiling]) h4e
  -- 5. the proof length word is inside the calldata
  have h5e : Step (OD c g) F V₂ st₁ (.expr (Expr.builtin Op.iszero
        [Expr.builtin Op.slt [Expr.builtin Op.add [dataPos "proofOffset", w 31],
          Expr.builtin Op.calldatasize []]])) (.eres (.vals [0] st₁)) := by
    have e := lengthPresent_val (funs := F) (V := V₂) (st := st₁) (y := "proofOffset")
      (pos := proofOffsetAt st₀) (rfl : VEnv.get V₂ "proofOffset" = some (proofOffsetAt st₀))
    rw [show lengthPresentValue (headStart + proofOffsetAt st₀) st₁ =
          lengthPresentValue (headStart + proofOffsetAt st₀) st₀ from rfl, hpoPresent'] at e
    exact e
  have h5 : Step (OD c g) F V₂ st₁ (.stmt (lengthPresentGuard "proofOffset"))
      (.sres V₂ st₁ .normal) :=
    guardPasses (funs := F) (V := V₂) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.iszero [Expr.builtin Op.slt
        [Expr.builtin Op.add [dataPos "proofOffset", w 31], Expr.builtin Op.calldatasize []]]) h5e
  -- 6. let proofLength := calldataload(add(headStart, proofOffset))
  have hpl' : Step (OD c g) F V₂ st₁
      (.expr (Expr.builtin Op.calldataload [dataPos "proofOffset"]))
      (.eres (.vals [proofLengthAt st₀] st₁)) := by
    have e := dataPosLoad_val (funs := F) (V := V₂) (st := st₁) (o := "proofOffset")
      (pos := proofOffsetAt st₀) (rfl : VEnv.get V₂ "proofOffset" = some (proofOffsetAt st₀))
    rw [show wordFrom st₁.env.calldata (headStart + proofOffsetAt st₀).toNat =
          proofLengthAt st₀ from rfl] at e
    exact e
  have h6 : Step (OD c g) F V₂ st₁ (.stmt proofLengthDecl) (.sres V₃ st₁ .normal) :=
    Step.letVal (vars := ["proofLength"]) (vals := [proofLengthAt st₀])
      (e := Expr.builtin Op.calldataload [dataPos "proofOffset"])
      (st1 := st₁) (funs := F) (V := V₂) (st := st₁) hpl' rfl
  -- 7. the proof length ceiling passes
  have h7e : Step (OD c g) F V₃ st₁
      (.expr (Expr.builtin Op.gt [Expr.var "proofLength", w abiLengthCeiling]))
      (.eres (.vals [0] st₁)) := by
    have e := ceilingTest_val (funs := F) (V := V₃) (st := st₁) (y := "proofLength")
      (x := proofLengthAt st₀) (rfl : VEnv.get V₃ "proofLength" = some (proofLengthAt st₀))
    rw [hplBound'] at e
    exact e
  have h7 : Step (OD c g) F V₃ st₁ (.stmt (offsetCeilingGuard "proofLength"))
      (.sres V₃ st₁ .normal) :=
    guardPasses (funs := F) (V := V₃) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.var "proofLength", w abiLengthCeiling]) h7e
  -- 8. the proof tail bound passes - the check truncated_bytes_reverts shows firing
  have h8e : Step (OD c g) F V₃ st₁ (.expr (Expr.builtin Op.gt
        [Expr.builtin Op.add [Expr.builtin Op.add [dataPos "proofOffset", w 32],
            Expr.builtin Op.mul [Expr.var "proofLength", w 1]],
          Expr.builtin Op.calldatasize []])) (.eres (.vals [0] st₁)) := by
    have e := tail_val (funs := F) (V := V₃) (st := st₁) (o := "proofOffset")
      (l := "proofLength") (pos := proofOffsetAt st₀) (len := proofLengthAt st₀) (stride := 1)
      (rfl : VEnv.get V₃ "proofOffset" = some (proofOffsetAt st₀))
      (rfl : VEnv.get V₃ "proofLength" = some (proofLengthAt st₀))
    rw [show tailValue (headStart + proofOffsetAt st₀) (proofLengthAt st₀ * 1) st₁ =
          tailValue (headStart + proofOffsetAt st₀) (proofLengthAt st₀ * 1) st₀ from rfl,
        hplTail'] at e
    exact e
  have h8 : Step (OD c g) F V₃ st₁ (.stmt (tailGuard "proofOffset" "proofLength" 1))
      (.sres V₃ st₁ .normal) :=
    guardPasses (funs := F) (V := V₃) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.builtin Op.add
          [Expr.builtin Op.add [dataPos "proofOffset", w 32],
            Expr.builtin Op.mul [Expr.var "proofLength", w 1]],
          Expr.builtin Op.calldatasize []]) h8e
  -- 9. let instancesOffset := calldataload(add(headStart, 32))
  have hio' : Step (OD c g) F V₃ st₁ (.expr (Expr.builtin Op.calldataload
        [Expr.builtin Op.add [w headStart, w 32]]))
      (.eres (.vals [instancesOffsetAt st₀] st₁)) := by
    have e := headLoad_val (funs := F) (V := V₃) (st := st₁) 32
    rw [show wordFrom st₁.env.calldata (headStart + 32).toNat = instancesOffsetAt st₀ from rfl] at e
    exact e
  have h9 : Step (OD c g) F V₃ st₁ (.stmt instancesOffsetDecl) (.sres V₄ st₁ .normal) :=
    Step.letVal (vars := ["instancesOffset"]) (vals := [instancesOffsetAt st₀])
      (e := Expr.builtin Op.calldataload [Expr.builtin Op.add [w headStart, w 32]])
      (st1 := st₁) (funs := F) (V := V₃) (st := st₁) hio' rfl
  -- 10. the instances offset ceiling passes
  have h10e : Step (OD c g) F V₄ st₁
      (.expr (Expr.builtin Op.gt [Expr.var "instancesOffset", w abiLengthCeiling]))
      (.eres (.vals [0] st₁)) := by
    have e := ceilingTest_val (funs := F) (V := V₄) (st := st₁) (y := "instancesOffset")
      (x := instancesOffsetAt st₀)
      (rfl : VEnv.get V₄ "instancesOffset" = some (instancesOffsetAt st₀))
    rw [hioBound'] at e
    exact e
  have h10 : Step (OD c g) F V₄ st₁ (.stmt (offsetCeilingGuard "instancesOffset"))
      (.sres V₄ st₁ .normal) :=
    guardPasses (funs := F) (V := V₄) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.var "instancesOffset", w abiLengthCeiling]) h10e
  -- 11. the instances length word is inside the calldata
  have h11e : Step (OD c g) F V₄ st₁ (.expr (Expr.builtin Op.iszero
        [Expr.builtin Op.slt [Expr.builtin Op.add [dataPos "instancesOffset", w 31],
          Expr.builtin Op.calldatasize []]])) (.eres (.vals [0] st₁)) := by
    have e := lengthPresent_val (funs := F) (V := V₄) (st := st₁) (y := "instancesOffset")
      (pos := instancesOffsetAt st₀)
      (rfl : VEnv.get V₄ "instancesOffset" = some (instancesOffsetAt st₀))
    rw [show lengthPresentValue (headStart + instancesOffsetAt st₀) st₁ =
          lengthPresentValue (headStart + instancesOffsetAt st₀) st₀ from rfl, hioPresent'] at e
    exact e
  have h11 : Step (OD c g) F V₄ st₁ (.stmt (lengthPresentGuard "instancesOffset"))
      (.sres V₄ st₁ .normal) :=
    guardPasses (funs := F) (V := V₄) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.iszero [Expr.builtin Op.slt
        [Expr.builtin Op.add [dataPos "instancesOffset", w 31],
          Expr.builtin Op.calldatasize []]]) h11e
  -- 12. let instancesLength := calldataload(add(headStart, instancesOffset))
  have hil' : Step (OD c g) F V₄ st₁
      (.expr (Expr.builtin Op.calldataload [dataPos "instancesOffset"]))
      (.eres (.vals [instancesLengthAt st₀] st₁)) := by
    have e := dataPosLoad_val (funs := F) (V := V₄) (st := st₁) (o := "instancesOffset")
      (pos := instancesOffsetAt st₀)
      (rfl : VEnv.get V₄ "instancesOffset" = some (instancesOffsetAt st₀))
    rw [show wordFrom st₁.env.calldata (headStart + instancesOffsetAt st₀).toNat =
          instancesLengthAt st₀ from rfl] at e
    exact e
  have h12 : Step (OD c g) F V₄ st₁ (.stmt instancesLengthDecl)
      (.sres (decodeEnv st₀) st₁ .normal) :=
    Step.letVal (vars := ["instancesLength"]) (vals := [instancesLengthAt st₀])
      (e := Expr.builtin Op.calldataload [dataPos "instancesOffset"])
      (st1 := st₁) (funs := F) (V := V₄) (st := st₁) hil' rfl
  -- 13. the instances length ceiling passes
  have h13e : Step (OD c g) F (decodeEnv st₀) st₁
      (.expr (Expr.builtin Op.gt [Expr.var "instancesLength", w abiLengthCeiling]))
      (.eres (.vals [0] st₁)) := by
    have e := ceilingTest_val (funs := F) (V := decodeEnv st₀) (st := st₁)
      (y := "instancesLength") (x := instancesLengthAt st₀)
      (rfl : VEnv.get (decodeEnv st₀) "instancesLength" = some (instancesLengthAt st₀))
    rw [hilBound'] at e
    exact e
  have h13 : Step (OD c g) F (decodeEnv st₀) st₁
      (.stmt (offsetCeilingGuard "instancesLength")) (.sres (decodeEnv st₀) st₁ .normal) :=
    guardPasses (funs := F) (V := decodeEnv st₀) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.var "instancesLength", w abiLengthCeiling]) h13e
  -- 14. the instances tail bound passes
  have h14e : Step (OD c g) F (decodeEnv st₀) st₁ (.expr (Expr.builtin Op.gt
        [Expr.builtin Op.add [Expr.builtin Op.add [dataPos "instancesOffset", w 32],
            Expr.builtin Op.mul [Expr.var "instancesLength", w 32]],
          Expr.builtin Op.calldatasize []])) (.eres (.vals [0] st₁)) := by
    have e := tail_val (funs := F) (V := decodeEnv st₀) (st := st₁) (o := "instancesOffset")
      (l := "instancesLength") (pos := instancesOffsetAt st₀) (len := instancesLengthAt st₀)
      (stride := 32)
      (rfl : VEnv.get (decodeEnv st₀) "instancesOffset" = some (instancesOffsetAt st₀))
      (rfl : VEnv.get (decodeEnv st₀) "instancesLength" = some (instancesLengthAt st₀))
    rw [show tailValue (headStart + instancesOffsetAt st₀) (instancesLengthAt st₀ * 32) st₁ =
          tailValue (headStart + instancesOffsetAt st₀) (instancesLengthAt st₀ * 32) st₀ from rfl,
        hilTail'] at e
    exact e
  have h14 : Step (OD c g) F (decodeEnv st₀) st₁
      (.stmt (tailGuard "instancesOffset" "instancesLength" 32))
      (.sres (decodeEnv st₀) st₁ .normal) :=
    guardPasses (funs := F) (V := decodeEnv st₀) (st := st₁) (st' := st₁)
      (test := Expr.builtin Op.gt [Expr.builtin Op.add
          [Expr.builtin Op.add [dataPos "instancesOffset", w 32],
            Expr.builtin Op.mul [Expr.var "instancesLength", w 32]],
          Expr.builtin Op.calldatasize []]) h14e

  -- 15-16. the two immutable bindings
  have hvkE : Step (OD c g) F (decodeEnv st₀) st₁ (.expr (Expr.builtin Op.loadimmutable
        [Expr.lit (.string vkImmutableKey)])) (.eres (.vals [immVk st₀] st₁)) :=
    bi1 (op := Op.loadimmutable) (st' := st₁) (e := Expr.lit (.string vkImmutableKey))
      (v := litValue (.string vkImmutableKey)) (u := immVk st₀) (funs := F) (V := decodeEnv st₀)
      (st := st₁)
      (Step.lit (D := OD c g) (l := Literal.string vkImmutableKey) (funs := F)
        (V := decodeEnv st₀) (st := st₁))
      (rfl : (OD c g).Builtin Op.loadimmutable [litValue (.string vkImmutableKey)] st₁
        (.ok [immVk st₀] st₁))
  have h15 : Step (OD c g) F (decodeEnv st₀) st₁
      (.stmt (Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable
        [Expr.lit (.string vkImmutableKey)]))))
      (.sres (vkEnv st₀) st₁ .normal) :=
    Step.letVal (vars := ["vk"]) (vals := [immVk st₀])
      (e := Expr.builtin Op.loadimmutable [Expr.lit (.string vkImmutableKey)])
      (st1 := st₁) (funs := F) (V := decodeEnv st₀) (st := st₁) hvkE rfl
  have hqE : Step (OD c g) F (vkEnv st₀) st₁
      (.expr (Expr.builtin Op.loadimmutable [Expr.lit (.string quotientImmutableKey)]))
      (.eres (.vals [immQuotient st₀] st₁)) :=
    bi1 (op := Op.loadimmutable) (st' := st₁) (e := Expr.lit (.string quotientImmutableKey))
      (v := litValue (.string quotientImmutableKey)) (u := immQuotient st₀) (funs := F)
      (V := vkEnv st₀) (st := st₁)
      (Step.lit (D := OD c g) (l := Literal.string quotientImmutableKey) (funs := F)
        (V := vkEnv st₀) (st := st₁))
      (rfl : (OD c g).Builtin Op.loadimmutable [litValue (.string quotientImmutableKey)] st₁
        (.ok [immQuotient st₀] st₁))
  have h16 : Step (OD c g) F (vkEnv st₀) st₁
      (.stmt (Stmt.letDecl ["quotientEvaluator"] (some (Expr.builtin Op.loadimmutable
        [Expr.lit (.string quotientImmutableKey)])))) (.sres (armEnv st₀) st₁ .normal) :=
    Step.letVal (vars := ["quotientEvaluator"]) (vals := [immQuotient st₀])
      (e := Expr.builtin Op.loadimmutable [Expr.lit (.string quotientImmutableKey)])
      (st1 := st₁) (funs := F) (V := vkEnv st₀) (st := st₁) hqE rfl
  -- assemble: armPrefix is exactly the sixteen statements above, in this order
  show Step (OD c g) F (selEnv st₀) st₁
    (.stmts ([callvalueGuard, headLengthGuard, proofOffsetDecl,
        offsetCeilingGuard "proofOffset", lengthPresentGuard "proofOffset", proofLengthDecl,
        offsetCeilingGuard "proofLength", tailGuard "proofOffset" "proofLength" 1,
        instancesOffsetDecl, offsetCeilingGuard "instancesOffset",
        lengthPresentGuard "instancesOffset", instancesLengthDecl,
        offsetCeilingGuard "instancesLength", tailGuard "instancesOffset" "instancesLength" 32]
        ++ bindLocalsFromImmutables ++ P))
      (.sres V' st' o)
  refine seqC (c := c) (g := g) (funs := F) (V := selEnv st₀) (st := st₁) (V₁ := selEnv st₀)
    (st₁ := st₁) h1 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := selEnv st₀) (st := st₁) (V₁ := selEnv st₀)
    (st₁ := st₁) h2 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := selEnv st₀) (st := st₁) (V₁ := V₂)
    (st₁ := st₁) h3 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₂) (st := st₁) (V₁ := V₂) (st₁ := st₁) h4 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₂) (st := st₁) (V₁ := V₂) (st₁ := st₁) h5 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₂) (st := st₁) (V₁ := V₃) (st₁ := st₁) h6 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₃) (st := st₁) (V₁ := V₃) (st₁ := st₁) h7 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₃) (st := st₁) (V₁ := V₃) (st₁ := st₁) h8 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₃) (st := st₁) (V₁ := V₄)
    (st₁ := st₁) h9 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₄) (st := st₁) (V₁ := V₄) (st₁ := st₁) h10 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₄) (st := st₁) (V₁ := V₄) (st₁ := st₁) h11 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := V₄) (st := st₁) (V₁ := decodeEnv st₀)
    (st₁ := st₁) h12 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := decodeEnv st₀) (st := st₁)
    (V₁ := decodeEnv st₀) (st₁ := st₁) h13 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := decodeEnv st₀) (st := st₁)
    (V₁ := decodeEnv st₀) (st₁ := st₁) h14 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := decodeEnv st₀) (st := st₁)
    (V₁ := vkEnv st₀) (st₁ := st₁) h15 ?_
  refine seqC (c := c) (g := g) (funs := F) (V := vkEnv st₀)
    (st := st₁) (V₁ := armEnv st₀) (st₁ := st₁) h16 ?_
  exact hP

/-- The prefix alone, with nothing after it: the '.normal' termination of the entry path. -/
theorem armPrefix_normal {st₀ : EvmState} (hacc : dispatcherAccepts st₀)
    {F : FunEnv (OD c g)} :
    Step (OD c g) F (selEnv st₀) (armFrame st₀) (.stmts armPrefix)
      (.sres (armEnv st₀) (armFrame st₀) .normal) :=
  armPrefix_passes (hacc := hacc) (P := []) (seqN (c := c) (g := g) (funs := F)
    (V := armEnv st₀) (st := armFrame st₀))

/-- **THE KEY TRANSPORT.** Suppose the routed 'verifyProof' arm - the switch block the dispatcher
selects, which on an accepting calldata IS 'armPrefix ++ armBody S' - runs the lowered program and
halts. Then the Surface has a 'wrap' run, observed at the deployment frame. Together with
'armPrefix_passes' this says the entry path contributes the prologue's frame change and nothing
else: no halt, no world effect, no external call.

The hypothesis is the switch block's own step rather than a 'Run' of 'armBody S', and that is
deliberate: inside the dispatcher the arm sees the function scopes 'armFuns' and the variable
environment 'armEnv', and a 'Step' derivation does not move between environments - 'VEnv.get'
answers the innermost binding, so a body that names 'vk' means a different word in a different
environment. Stating the transport where the arm actually runs is the honest form; stating it as
'Run (armBody S)' would be a claim about a different program. -/
theorem wrap_of_arm_run {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Hash) (cd : Bytes)
    (hacc : dispatcherAccepts (callState W S.shellLayout H cd)) {st' : EvmState}
    (harm : Step (OD c g)
        (hoist (OD c g) [selectorDecl, selectorSwitch (armBody S)] :: [[]])
        (selEnv (callState W S.shellLayout H cd)) (armFrame (callState W S.shellLayout H cd))
        (.stmt (.block (selectSwitch (OD c g) (selectorWord (callState W S.shellLayout H cd))
            (caseList (armBody S)) none)))
        (.sres (selEnv (callState W S.shellLayout H cd)) st' .halt)) :
    wrap S W H cd c g ⟨committedState (callState W S.shellLayout H cd) st', .halt⟩ := by
  set st₀ := callState W S.shellLayout H cd
  have hstmts : Step (OD c g) [[]] [] st₀ (.stmts (dispatcher (armBody S))) (.sres [] st' .halt) :=
    dispatch_prefix (body := armBody S) (st₀ := st₀) hacc.1 harm
  exact ⟨[], st', blk (c := c) (g := g) (funs := []) (V := []) (st := st₀)
      (body := dispatcher (armBody S)) (V₁ := []) (st₁ := st') (o := .halt) hstmts, rfl⟩

/-- **THE ARM BLOCK, DECOMPOSED.** On an accepting calldata the routed switch block IS the arm
prefix followed by the lowered program: the prefix runs to '.normal' in the prologue's frame
('armPrefix_passes') and the program's own step finishes the job. This is the form the headline
transport cites, and it is the lemma the file's own docstrings promised. -/
theorem switch_block_of_body_run {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Hash) (cd : Bytes)
    (hacc : dispatcherAccepts (callState W S.shellLayout H cd))
    {V' : VEnv (OD c g)} {st' : EvmState}
    (hbody : Step (OD c g) (armFuns (armBody S)) (armEnv (callState W S.shellLayout H cd))
        (armFrame (callState W S.shellLayout H cd)) (.stmts (armBody S)) (.sres V' st' .halt))
    (hres : restore (selEnv (callState W S.shellLayout H cd)) V' =
      selEnv (callState W S.shellLayout H cd)) :
    Step (OD c g)
        (hoist (OD c g) [selectorDecl, selectorSwitch (armBody S)] :: [[]])
        (selEnv (callState W S.shellLayout H cd)) (armFrame (callState W S.shellLayout H cd))
        (.stmt (.block (selectSwitch (OD c g) (selectorWord (callState W S.shellLayout H cd))
            (caseList (armBody S)) none)))
        (.sres (selEnv (callState W S.shellLayout H cd)) st' .halt) := by
  set st₀ := callState W S.shellLayout H cd
  have hseq : Step (OD c g) (armFuns (armBody S)) (selEnv st₀) (armFrame st₀)
      (.stmts (verifyProofArm (armBody S))) (.sres V' st' .halt) := by
    show Step (OD c g) (armFuns (armBody S)) (selEnv st₀) (armFrame st₀)
      (.stmts (armPrefix ++ armBody S)) (.sres V' st' .halt)
    exact armPrefix_passes (hacc := hacc) (F := armFuns (armBody S)) (P := armBody S) hbody
  have key : Step (OD c g) (hoist (OD c g) [selectorDecl, selectorSwitch (armBody S)] :: [[]])
      (selEnv st₀) (armFrame st₀)
      (.stmt (.block (selectSwitch (OD c g) (selectorWord st₀) (caseList (armBody S)) none)))
      (.sres (restore (selEnv st₀) V') st' .halt) := by
    rw [switch_verifyProof (cv := selectorWord st₀) (body := armBody S) hacc.2.1]
    exact blk (c := c) (g := g) (body := verifyProofArm (armBody S))
      (funs := hoist (OD c g) [selectorDecl, selectorSwitch (armBody S)] :: [[]]) (V := selEnv st₀)
      (st := armFrame st₀) (V₁ := V') (st₁ := st') (o := .halt) hseq
  rw [hres] at key
  exact key

/-! ### 11. The frame tie, and why it does not tie -/

/-- The prologue's mark bump, on its own: whatever the incoming frame's mark is, the arm frame's
is at least three words, because 'mstore(0x40, memoryguard(128))' touches the byte range
[64, 96). -/
theorem arm_frame_active_words_nonzero (st₀ : EvmState) : (armFrame st₀).activeWords ≠ 0 := by
  show (stAfterPrologue st₀).activeWords ≠ 0
  have h : (stAfterPrologue st₀).activeWords =
      BitVec.ofNat 256 (Nat.max st₀.activeWords.toNat 3) := by
    show BitVec.ofNat 256 (activeWordsAfter st₀.activeWords.toNat 64 32) = _
    rw [activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  intro hh
  have hto : (BitVec.ofNat 256 (Nat.max st₀.activeWords.toNat 3)).toNat =
      (0 : BitVec 256).toNat := congrArg BitVec.toNat (h ▸ hh)
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.max_lt.mpr ⟨st₀.activeWords.isLt, by decide⟩)] at hto
  have hz : (0 : BitVec 256).toNat = 0 := rfl
  rw [hz] at hto
  have h3 : 3 ≤ Nat.max st₀.activeWords.toNat 3 := Nat.le_max_right _ _
  omega

/-- **NO MEMORY CHOICE MAKES THE 'RunVerifier' FRAME THE ARM FRAME.** 'RunVerifier' builds its
frame with 'initState', which takes the memory as a parameter and nothing else, so its
active-words mark is always 'EvmState.init.activeWords = 0'. The dispatcher's prologue
'mstore(0x40, memoryguard(128))' bumps the mark to three words, and 'armFrame' is the prologue's
post-state. So the two frames are never the same state, for ANY 'mem₀' - including the one that
copies the prologue's write into the memory.

This is the exact obstruction between the 'wrap' model and the three run fields of
'LoweringCorrect', and it is a fact about the model rather than a missing proof: 'activeWords' is
what 'msize' answers ('EVMExec.lean:375' defines 'memorySize' and ':765' is its only reader in
the vendored dialect), so a program that reads 'msize' can tell the two frames apart, and no
hypothesis of 'LoweringCorrect' says the lowered program does not. -/
theorem no_mem₀_reaches_the_arm_frame (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash)
    (cd : Bytes) (mem₀ : Nat → UInt8) :
    initState W S.shellLayout H cd mem₀ ≠ armFrame (callState W S.shellLayout H cd) := by
  intro h
  have h₁ : (initState W S.shellLayout H cd mem₀).activeWords = 0 := rfl
  have h₂ : (armFrame (callState W S.shellLayout H cd)).activeWords ≠ 0 :=
    arm_frame_active_words_nonzero (callState W S.shellLayout H cd)
  exact h₂ (by rw [← h, h₁])

/-- The prologue's write is visible in the frame the arm runs in: the free-memory-pointer word is
the reservation, not zero. Stated as the two words the arm's FIRST statement reads, because
'headGuard' is 'if gt(mload(0x40), 0x1000) revert' - the arm's own first act is to read the word
the dispatcher wrote. So the difference is not in a corner of the state the program never looks
at: it is in the first word the program looks at. -/
theorem arm_frame_reads_a_different_head_word (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash)
    (cd : Bytes) :
    (callState W S.shellLayout H cd).memory 95 = 0 ∧
      (armFrame (callState W S.shellLayout H cd)).memory 95 = 0x80 :=
  ⟨rfl, rfl⟩

/-- **THE TRANSPORT IS NOT A VIEW EQUIVALENCE, AND HERE IS THE PROGRAM THAT SHOWS IT.** The
two-statement program 'return(mload(0x40), 32)' run from the deployment frame and from the arm
frame halts with two DIFFERENT return payloads, so the bridge 'LoweringCorrect' would need - an
'ObsEquiv' between the dispatcher model and the body-only model - is FALSE rather than merely
unstated. This is the same class of finding as the 'ir_refines' refutation: the candidate
hypothesis is shown unable to hold, not just unproved. -/
theorem prologue_write_is_observable :
    ∃ (P : YulBlock) (st₀ : EvmState) (s₁ s₂ : EvmState),
      Run c g P st₀ [] s₁ .halt ∧ Run c g P (stAfterPrologue st₀) [] s₂ .halt ∧
        s₁.halted ≠ s₂.halted := by
  let st₀ : EvmState := frame (be4 0xdeadbeef) 0
  let st₂ : EvmState := stAfterPrologue st₀
  -- 'return(0x5f, 1)': the last byte of the word the prologue writes. Zero in the deployment
  -- frame, 0x80 in the arm frame.
  let P : YulBlock := [Stmt.exprStmt (Expr.builtin Op.ret [w 0x5f, w 1])]
  let s₁ : EvmState :=
    { touchMemory st₀ 0x5f 1 with halted := some (HaltKind.ret, readBytes st₀.memory 0x5f 1) }
  let s₂ : EvmState :=
    { touchMemory st₂ 0x5f 1 with halted := some (HaltKind.ret, readBytes st₂.memory 0x5f 1) }
  have h₁ : Run c g P st₀ [] s₁ .halt :=
    blk (c := c) (g := g) (funs := []) (V := []) (st := st₀) (body := P) (V₁ := []) (st₁ := s₁)
      (o := .halt)
      (seqStopH (c := c) (g := g) (funs := hoist (OD c g) P :: []) (V := []) (st := st₀)
        (s₁ := Stmt.exprStmt (Expr.builtin Op.ret [w 0x5f, w 1])) (rest := []) (V₁ := [])
        (st₁ := s₁)
        (Step.exprStmtHalt (D := OD c g) (funs := hoist (OD c g) P :: []) (V := [])
          (st := st₀) (e := Expr.builtin Op.ret [w 0x5f, w 1]) (st1 := s₁)
          (Step.builtinHalt (D := OD c g) (funs := hoist (OD c g) P :: []) (V := [])
            (st := st₀) (op := Op.ret) (args := [w 0x5f, w 1]) (argvals := [0x5f, 1])
            (st1 := st₀) (st2 := s₁) (wlits_eval st₀ [0x5f, 1])
            (rfl : (OD c g).Builtin Op.ret [0x5f, 1] st₀ (.halt s₁)))))
  have h₂ : Run c g P st₂ [] s₂ .halt :=
    blk (c := c) (g := g) (funs := []) (V := []) (st := st₂) (body := P) (V₁ := []) (st₁ := s₂)
      (o := .halt)
      (seqStopH (c := c) (g := g) (funs := hoist (OD c g) P :: []) (V := []) (st := st₂)
        (s₁ := Stmt.exprStmt (Expr.builtin Op.ret [w 0x5f, w 1])) (rest := []) (V₁ := [])
        (st₁ := s₂)
        (Step.exprStmtHalt (D := OD c g) (funs := hoist (OD c g) P :: []) (V := [])
          (st := st₂) (e := Expr.builtin Op.ret [w 0x5f, w 1]) (st1 := s₂)
          (Step.builtinHalt (D := OD c g) (funs := hoist (OD c g) P :: []) (V := [])
            (st := st₂) (op := Op.ret) (args := [w 0x5f, w 1]) (argvals := [0x5f, 1])
            (st1 := st₂) (st2 := s₂) (wlits_eval st₂ [0x5f, 1])
            (rfl : (OD c g).Builtin Op.ret [0x5f, 1] st₂ (.halt s₂)))))
  have hne : s₁.halted ≠ s₂.halted := by
    show some (HaltKind.ret, readBytes st₀.memory 0x5f 1) ≠
      some (HaltKind.ret, readBytes st₂.memory 0x5f 1)
    intro hh
    have hd := congrArg Prod.snd (Option.some.inj hh)
    have hz : readBytes st₀.memory 0x5f 1 = [0] := rfl
    have ho : readBytes st₂.memory 0x5f 1 = [0x80] := rfl
    rw [hz, ho] at hd
    exact absurd hd (by decide)
  exact ⟨P, st₀, s₁, s₂, h₁, h₂, hne⟩

-- **AXIOM AUDIT FOR THE TRANSPORT.** The key lemma, the transport and the frame refutation are
-- derivations, not assumptions: no proof hole, and nothing beyond the vendored semantics' own
-- quotation machinery.
#print axioms Midfall.Yul.ShellModel.armPrefix_passes
#print axioms Midfall.Yul.ShellModel.wrap_of_arm_run
#print axioms Midfall.Yul.ShellModel.prologue_write_is_observable

/-! ### 12. The in-tree object the headline bridge is read at -/

/-- **THE DISPATCHER MODEL AS A YUL OBJECT.** One runtime sub-object, named the way the Surface
names runtimes, whose code block IS 'dispatcherCode S'. No solc artifact is involved: the object
is assembled from the model. This is the object 'LoweringCorrect.ir_refines' is read at when the
headline theorem speaks about 'wrap' rather than about an imported via-ir object. -/
def modelIr (S : Surface p G₁ G₂ Gₜ) : YulObject :=
  Object.mk S.shell.name ([] : YulBlock)
    [Object.mk (S.runtimeName S.shell.name) (dispatcherCode S) [] []] []

/-- The Surface's own runtime lookup finds the model, by 'rfl' - which is the point: the naming
field and the object are built from the same 'S.runtimeName', so there is no second convention to
disagree with (R-60 S1 was exactly this failure mode). -/
theorem modelIr_irRuntime (S : Surface p G₁ G₂ Gₜ) :
    S.irRuntime (modelIr S) = some (dispatcherCode S) := by
  have hsub : (modelIr S).subObject (S.runtimeName (modelIr S).name)
      = some (Object.mk (S.runtimeName S.shell.name) (dispatcherCode S) [] []) := by
    show List.find? (fun x => decide (x.name = S.runtimeName (modelIr S).name))
        [Object.mk (S.runtimeName S.shell.name) (dispatcherCode S) [] []] = _
    refine List.find?_cons_of_pos (decide_eq_true rfl)
  rw [Surface.irRuntime, hsub]
  rfl

/-- **THE MODEL PASSES THE IMPORT CHECK.** 'Surface.irCheck' is the decidable fragment: the
runtime sub-object exists and has no unresolved top-level call. The dispatcher's three top-level
statements are an 'mstore', a 'cond' and a 'revert', all builtins, so nothing is unresolved - the
model is inside the fragment by construction rather than by assumption. -/
theorem modelIr_irCheck (S : Surface p G₁ G₂ Gₜ) : S.irCheck (modelIr S) = true := by
  have h : S.irCheck (modelIr S) = ! unresolvedTop (dispatcherCode S) := by
    rw [Surface.irCheck, modelIr_irRuntime]
  rw [h]
  rfl

/-- **THE BRIDGE IS A DEFINITIONAL IDENTIFICATION, NOT A SIMULATION.** At the model object,
'RunContractIR' IS 'wrap': same program, same frame, same commit base. This is the step that lets
the headline be restated over 'wrap' without losing the only transport 'LoweringCorrect' carries. -/
theorem wrap_iff_modelRunContractIR (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) (obs : Obs) :
    RunContractIR S W H (modelIr S) S.shellLayout cd c g obs ↔ wrap S W H cd c g obs := by
  constructor
  · rintro ⟨rt, V', hrt, hrun⟩
    rw [modelIr_irRuntime] at hrt
    cases Option.some.inj hrt
    exact ⟨V', hrun⟩
  · rintro ⟨V', hrun⟩
    exact ⟨dispatcherCode S, V', modelIr_irRuntime S, hrun⟩

/-- **AND THE SHELL RUN IS THE VERIFIER RUN AT ZERO MEMORY.** 'RunShell' and 'RunVerifier' differ
in the statement by which block and which frame: 'shell.codeBlock' versus
'S.L.headGuard ++ S.bindLocals ++ S.L.main', and 'callState' versus 'initState ... mem₀'. Under
the surface pin 'shell_unfolds' the two programs are one, and 'callState' IS 'initState' at the
everywhere-zero memory - so the two run predicates are the same predicate, by 'rfl'. This is the
one frame identification the model DOES give for free, and it is what the headline's soundness
conjunct runs on. -/
theorem runShell_eq_runVerifier_zero (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) (obs : Obs) :
    RunShell S W H cd c g obs → RunVerifier S W H cd (fun _ => 0) c g obs :=
  fun ⟨V', hrun⟩ => ⟨V', by rw [← S.shell_unfolds]; exact hrun⟩

/-! ### 13. D-P23 for the transport: the accepting calldata, and two more falsifications -/

/-- **THE WITNESS THAT 'dispatcherAccepts' IS SATISFIABLE.** At the file's own well-formed
calldata every entry-path test answers PASS: the size test enters the switch, the selector routes,
the callvalue is zero, the head region is present, and both dynamic arguments clear offset ceiling,
length presence, length ceiling and tail bound - thirteen 'rfl's, i.e. a computation on the model's
own decoder rather than a claim about it. Without this line 'armPrefix_passes' would be a theorem
about a condition nothing satisfies, which is exactly the D-P23 half the three falsifications had
and the positive direction did not. -/
theorem cdWellFormed_is_accepted : dispatcherAccepts (frame cdWellFormed 0) :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, ⟨rfl, rfl⟩⟩, ⟨rfl, rfl, ⟨rfl, rfl⟩⟩⟩

/-- **AND THE ACCEPTING CONDITION IS NOT VACUOUS IN THE OTHER DIRECTION EITHER**: the two calldata
the falsifications use both FAIL it, the wrong-selector one on the routing conjunct and the
truncated one on the proof tail bound. So 'dispatcherAccepts' discriminates, and 'armPrefix_passes'
is not an implication over an empty set. -/
theorem dispatcherAccepts_refuted_by_the_falsification_witnesses :
    ¬ dispatcherAccepts (frame cdWrongSelector 0) ∧
      ¬ dispatcherAccepts (frame cdTruncatedProof 0) ∧
      ¬ dispatcherAccepts (frame [] 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨_, hsel, _, _, _, _⟩ := h
    exact absurd hsel (by decide)
  · intro h
    obtain ⟨_, _, _, _, hproof, _⟩ := h
    obtain ⟨_, _, _, htail⟩ := hproof
    exact absurd htail (by decide)
  · intro h
    obtain ⟨hsize, _, _, _, _, _⟩ := h
    exact absurd hsize (by decide)

/-- A body that runs off its last statement: 'stop()' halts with a COMMITTING kind, which is
neither a return nor a revert. -/
def stopBody : YulBlock := [Stmt.exprStmt (Expr.builtin Op.stop [])]

/-- The state 'stop()' leaves: 'stepOp's own clause (EVMExec.lean:875). -/
def stopState (st : EvmState) : EvmState := { st with halted := some (.stop, []) }

/-- **FALSIFICATION 4 - A RUN THAT IS NEITHER RETURN NOR REVERT.** The two-outcome conjunct of the
headline is not a theorem about programs. A dispatcher run on a calldata the dispatcher ACCEPTS -
so the entry path contributes nothing - reaches 'stop', and the observation is neither
'Obs.isReturn' nor 'Obs.isRevertOrHalt' ('HaltKind.commits stop = true', so the read-only half of
the disjunct fails too). This is precisely what 'LoweringCorrect.only_two_outcomes' rules out by
hypothesis, and it is exhibited here as a run of the model rather than asserted in prose: delete
the hypothesis and the conjunct is false of a program this model runs. -/
theorem stop_run_is_neither_return_nor_revert :
    ∃ obs, runOn stopBody (frame cdWellFormed 0) c g obs ∧
      ¬ obs.isReturn ∧ ¬ obs.isRevertOrHalt := by
  let st₀ : EvmState := frame cdWellFormed 0
  let FI : FunEnv (OD c g) := hoist (OD c g) [selectorDecl, selectorSwitch stopBody] :: [[]]
  let FA : FunEnv (OD c g) := hoist (OD c g) (verifyProofArm stopBody) :: FI
  have hstop : Step (OD c g) FA (armEnv st₀) (armFrame st₀) (.stmts stopBody)
      (.sres (armEnv st₀) (stopState (armFrame st₀)) .halt) := by
    show Step (OD c g) FA (armEnv st₀) (armFrame st₀)
      (.stmts [Stmt.exprStmt (Expr.builtin Op.stop [])])
      (.sres (armEnv st₀) (stopState (armFrame st₀)) .halt)
    exact seqStopH (c := c) (g := g) (funs := FA) (V := armEnv st₀) (st := armFrame st₀)
      (s₁ := Stmt.exprStmt (Expr.builtin Op.stop [])) (rest := []) (V₁ := armEnv st₀)
      (st₁ := stopState (armFrame st₀))
      (Step.exprStmtHalt (D := OD c g) (funs := FA) (V := armEnv st₀) (st := armFrame st₀)
        (e := Expr.builtin Op.stop []) (st1 := stopState (armFrame st₀))
        (Step.builtinHalt (D := OD c g) (funs := FA) (V := armEnv st₀) (st := armFrame st₀)
          (op := Op.stop) (args := ([] : List (Expr EVM.Op))) (argvals := ([] : List U256))
          (st1 := armFrame st₀) (st2 := stopState (armFrame st₀))
          (Step.argsNil (D := OD c g) (st := armFrame st₀))
          (rfl : (OD c g).Builtin Op.stop [] (armFrame st₀)
            (.halt (stopState (armFrame st₀))))))
  have hseq : Step (OD c g) FA (selEnv st₀) (armFrame st₀)
      (.stmts (verifyProofArm stopBody)) (.sres (armEnv st₀) (stopState (armFrame st₀)) .halt) := by
    show Step (OD c g) FA (selEnv st₀) (armFrame st₀)
      (.stmts (armPrefix ++ stopBody)) (.sres (armEnv st₀) (stopState (armFrame st₀)) .halt)
    exact armPrefix_passes (hacc := cdWellFormed_is_accepted) (F := FA) (P := stopBody) hstop
  have hres : (restore (selEnv st₀) (armEnv st₀) : VEnv (OD c g)) = selEnv st₀ := rfl
  have harm : Step (OD c g) FI (selEnv st₀) (armFrame st₀)
      (.stmt (.block (selectSwitch (OD c g) (selectorWord st₀) (caseList stopBody) none)))
      (.sres (selEnv st₀) (stopState (armFrame st₀)) .halt) := by
    rw [switch_verifyProof (cv := selectorWord st₀) (body := stopBody)
      cdWellFormed_is_accepted.2.1]
    have key : Step (OD c g) FI (selEnv st₀) (armFrame st₀)
        (.stmt (.block (verifyProofArm stopBody)))
        (.sres (restore (selEnv st₀) (armEnv st₀)) (stopState (armFrame st₀)) .halt) :=
      blk (c := c) (g := g) (body := verifyProofArm stopBody) (funs := FI) (V := selEnv st₀)
        (st := armFrame st₀) (V₁ := armEnv st₀) (st₁ := stopState (armFrame st₀)) (o := .halt)
        hseq
    rw [hres] at key
    exact key
  have hsize : sizeTestValue st₀ = 1 := cdWellFormed_is_accepted.1
  have hstmts : Step (OD c g) [[]] [] st₀ (.stmts (dispatcher stopBody))
      (.sres [] (stopState (armFrame st₀)) .halt) :=
    dispatch_prefix (body := stopBody) (st₀ := st₀) hsize harm
  refine ⟨⟨stopState (armFrame st₀), .halt⟩, ⟨[], ⟨_, blk (c := c) (g := g) (funs := [])
      (V := []) (st := st₀) (body := dispatcher stopBody) (V₁ := [])
      (st₁ := stopState (armFrame st₀)) (o := .halt) hstmts, rfl⟩⟩, ?_, ?_⟩
  · intro ⟨d, hd⟩
    exact HaltKind.noConfusion (congrArg Prod.fst (Option.some.inj hd))
  · intro ⟨k, d, hd, hk⟩
    have hk2 : k = HaltKind.stop :=
      congrArg Prod.fst (Option.some.inj hd).symm
    rw [hk2] at hk
    exact absurd hk (by decide)

/-- **FALSIFICATION 5 - A CALLDATA THAT FAILS THE SELECTOR HYPOTHESIS.** The headline keeps
'hsel : bytesTake cd 0 4 = some fnSigVerifyProof', and this is the witness that it can fail:
'cdWrongSelector' carries 0xdeadbeef, so its first four bytes are not the selector and
'dispatcherAccepts' is false of its frame ('dispatcherAccepts_refuted_by_the_falsification_witnesss'
is the second half) - and yet it HAS a dispatcher run, namely 'wrong_selector_reverts_at_witness',
whose halt is 'revert(0,0)'. So the selector hypothesis is not implied by the existence of a run,
which is the reason it stays in the statement, and the run an unroutable calldata does have lands on
the second disjunct of the third conjunct rather than the first. -/
theorem wrong_selector_calldata_fails_hsel :
    cdWrongSelector.take 4 ≠ Midfall.Generator.fnSigVerifyProof.data.toList := by
  intro h
  exact absurd h (by decide)

#print axioms Midfall.Yul.ShellModel.cdWellFormed_is_accepted
#print axioms Midfall.Yul.ShellModel.stop_run_is_neither_return_nor_revert
#print axioms Midfall.Yul.ShellModel.dispatcherAccepts_refuted_by_the_falsification_witnesses

end Midfall.Yul.ShellModel

