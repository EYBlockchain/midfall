-- |
-- Midfall.Yul.Builtins
--
-- P-VEND (docs/plans/P-VEND-dialect.md): the gates for the two builtins the vendored
-- EVM dialect was missing - `memoryguard` and `setimmutable` - and the evidence that a
-- run of the imported via-IR is now constructible at all.
--
-- WHY THESE TWO NAMES. The artifact of record is solc's textual via-IR, imported verbatim
-- as generated `yul%` quotations (docs/design.md D-P15). `parse`
-- (vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean) answers `none` for a name it does
-- not know, `mkCall` then elaborates the call as a USER-FUNCTION call, and no `Step` rule
-- derives from a user call whose definition is absent - so every run of the imported
-- program was stuck at its FIRST statement, `mstore(64, memoryguard(128))`. That is why
-- `RunContractIR` (Midfall/Lowering/Surface.lean:483) was uninhabited and why stage 4
-- declined to state `lowering_equivalence` rather than ship it vacuous.
--
-- MEASURED, NOT ASSUMED. `scripts/extract_ir_builtins.py` compiles the tracked deployed
-- sources with the pinned compiler and the pinned triple (solc 0.8.30, sha256
-- 738dcdc6...dd683, viaIR true, optimizer enabled runs 200, evmVersion cancun, metadata
-- bytecodeHash none) and classifies every called name in the `ir` artifact. The result is
-- the tracked manifest `Midfall/Yul/ir-builtins.tsv`, which `irManifest_ok` below reads at
-- #eval time (D-P19: a gate reads the artifact, it does not paste a string). Three
-- artifacts, 249 rows, 43 distinct builtins, ZERO unresolved names after the fork edit.
-- Before it, exactly two names were unresolved: `memoryguard` (2 sites in Halo2Verifier -
-- creation object, and the FIRST statement of the runtime object - plus 1 in
-- Halo2VerifyingKey) and `setimmutable` (1 site, creation object only). `loadimmutable`
-- was already modelled and needed no change.
--
-- WHAT THE MEASUREMENT ALSO FOUND, which the plan did not expect: `memoryguard` is NOT
-- folded out of the artifact for the contract that matters. In the deployed verifier it
-- survives BOTH `ir` and `irOptimized`; what the optimizer changes is its ARGUMENT. The
-- pre-optimisation `ir` runtime object says `memoryguard(128)`; `irOptimized` says
-- `memoryguard(0x08e0)`, and the deployed bytes begin PUSH2 0x08e0 PUSH1 0x40 MSTORE -
-- which is what `Midfall.Generator.runtimeFreeMemoryPointerInit` (Generator/Evm.lean:129)
-- reads back. In the VK contract the optimizer does fold it away entirely: its
-- `irOptimized` has zero occurrences. So "memoryguard is a compile-time construct that
-- disappears" is true of some artifacts and false of the one being imported, which is
-- exactly why this was measured rather than assumed. The identity rule below is therefore
-- exact for `irOptimized` and for the bytes, and for `ir` it yields the minimum reservation
-- solc documents. Whoever lands the import must decide which artifact to pin: `ir` (what
-- D-P15 says) puts the free pointer at 0x80, the deployed bytes put it at 0x8e0. That is a
-- layout difference, not an observable one - `Bridge.ObsView` deliberately excludes memory -
-- but it is a decision, and it is recorded here rather than discovered later.
--
-- THE OTHER TWO OBSTACLES TO THE IMPORT, found by actually elaborating it so that stage 6
-- does not rediscover them. Taking the deployed runtime object out of the `ir` artifact
-- (2,610 lines) and quoting it as `yulObject% ...` SUCCEEDS against this forked dialect -
-- `#print axioms` on the resulting `Object EVM.Op` reports `[propext, Classical.choice,
-- Quot.sound]`, no `sorryAx` - after exactly three mechanical edits, none of them dialect
-- semantics: (1) strip `//` comments and the `/// @src` / `/// @use-src` annotations, for
-- which the DSL has no production; (2) rename the identifier character `$`, which Lean's
-- `ident` lexeme rejects - the runtime object has 4,547 of them (the generator's `usr$`
-- prefix and solc's `abi_decode_t_array$...` mangling); (3) rename the bare identifier
-- `end`, which solc uses as a parameter name and Lean reserves (6 sites in the runtime
-- object). There are ZERO `: u256` and `-> u256` annotations in the deployed runtime object,
-- and the single `hex"..."` literal is a `data` segment, which the DSL does support. So the
-- import is a script, not a research task.
--
-- WHAT IS NOT HERE. The import itself (`ImportSolcIR.lean`, D-P15, M8) and `irCheck` (PLAN
-- section 7): this package unblocks them, it does not write them. And no second semantics:
-- `Bridge.Run` / `Bridge.RunCommitted` (stage 1) are the run layer these gates use for the
-- open dialect, and `YulSemantics.Run` for the closed one.

import YulSemantics
import YulSemantics.Dialect.EVM
import Midfall.Yul.Bridge

namespace Midfall.Yul.Builtins
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge

/-! ### Small observation helpers -/

/-- The single word a built-in step returned on a normal return, if it did. `EvmState`
holds functions, so it has no `BEq`: gates observe WORDS and `isSome`/`isNone` rather
than comparing whole states. -/
def ret1 (r : Option (BuiltinResult U256 EvmState)) : Option U256 :=
  match r with
  | some (.ok [v] _) => some v
  | _ => none

/-- The word an `EvmState` reports for an immutable name, keyed the way the dialect keys
it: the string-literal encoding of the name (`ExecEnv.immutable`). -/
def immutableAt (st : EvmState) (name : String) : U256 :=
  st.env.immutable (litValue (.string name))

/-- The free-memory-pointer word the state carries at byte 64: what solc's prologue
writes, and what `runtimeFreeMemoryPointerInit` reads out of the bytes. -/
def freePtr (st : EvmState) : U256 := loadWord st.memory 64

/-! ### 1. Name resolution -/

/-- GATE 1: the two new names resolve, in both directions, and the fall-through case is
still `none`. Red if `parse` loses an arm, if `opName` and `parse` disagree, or if the
catch-all `| _ => none` is dropped - the last line is what makes that visible. -/
def parseNewBuiltins_ok : Bool :=
  parse "memoryguard" == some Op.memoryguard &&
    parse "setimmutable" == some Op.setimmutable &&
    opName Op.memoryguard == "memoryguard" &&
    opName Op.setimmutable == "setimmutable" &&
    parse (opName Op.memoryguard) == some Op.memoryguard &&
    parse (opName Op.setimmutable) == some Op.setimmutable &&
    (parse "not_a_builtin").isNone &&
    -- and the pre-existing object-data names are untouched by the fork
    parse "loadimmutable" == some Op.loadimmutable

#eval parseNewBuiltins_ok                     -- expect true

/-- GATE 2: `mkCall`, which is what the `yul%` elaborator actually calls, now builds a
BUILT-IN for the two names instead of a user call - and still builds a user call for a
name nothing defines. The third conjunct is the pre-fork shape: before the vendor edit
`memoryguard(128)` elaborated to exactly `Expr.call "memoryguard" [...]`, the term with
no `Step` derivation. Red if the fork is reverted, and red if `mkCall` is made to resolve
everything (the user-call path has to survive). -/
def mkCallSplits_ok : Bool :=
  SyntaxEq.exprBeq (mkCall "memoryguard" [Expr.lit (.number 128)])
    (Expr.builtin Op.memoryguard [Expr.lit (.number 128)]) &&
    SyntaxEq.exprBeq (mkCall "setimmutable"
      [Expr.var "_2", Expr.lit (.string "5"), Expr.builtin Op.mload [Expr.lit (.number 128)]])
      (Expr.builtin Op.setimmutable
        [Expr.var "_2", Expr.lit (.string "5"), Expr.builtin Op.mload [Expr.lit (.number 128)]]) &&
    ! SyntaxEq.exprBeq (mkCall "memoryguard" [Expr.lit (.number 128)])
      (Expr.call "memoryguard" [Expr.lit (.number 128)]) &&
    SyntaxEq.exprBeq (mkCall "usr$helper_1" []) (Expr.call "usr$helper_1" [])

#eval mkCallSplits_ok                         -- expect true

/-! ### 2. The artifact quotations elaborate -/

/-- The first statement of the deployed runtime object, verbatim: line 288 of the `ir`
artifact of `Halo2Verifier.sol`, inside `object "Halo2Verifier_292_deployed"`. -/
def irRuntimePrologue : Block Op := yul% { mstore(64, memoryguard(128)) }

/-- The creation-object statement that patches the immutable, verbatim in shape (line 15
of the same artifact, with the code-copy offset written as a literal instead of the
variable `_2` the artifact binds). -/
def irCreationSetImmutable : Block Op := yul% { setimmutable(128, "5", 7) }

/-- GATE 3: the prologue quotation elaborates to the AST the artifact means - a builtin
`mstore` of a builtin `memoryguard` - and NOT to a user call. The second conjunct is
the negative control: the same quotation with `memoryguard` written as a user call is a
different AST, so a reverted `parse` turns this red. The fourth is the same for the
immutable name: it is a STRING literal in the artifact, not a number. -/
def prologueElab_ok : Bool :=
  SyntaxEq.stmtsBeq irRuntimePrologue
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])] &&
    ! SyntaxEq.stmtsBeq irRuntimePrologue
      [Stmt.exprStmt (Expr.builtin Op.mstore
          [Expr.lit (.number 64), Expr.call "memoryguard" [Expr.lit (.number 128)]])] &&
    SyntaxEq.stmtsBeq irCreationSetImmutable
      [Stmt.exprStmt (Expr.builtin Op.setimmutable
          [Expr.lit (.number 128), Expr.lit (.string "5"), Expr.lit (.number 7)])] &&
    ! SyntaxEq.stmtsBeq irCreationSetImmutable
      [Stmt.exprStmt (Expr.builtin Op.setimmutable
          [Expr.lit (.number 128), Expr.lit (.number 5), Expr.lit (.number 7)])]

#eval prologueElab_ok                         -- expect true

/-- PROPOSITIONAL, not merely `beq`: the quotation *is* the expected AST. This is D-P15's
"the elaborator is the checker" in Lean - if `parse` ever stops resolving the name, the
term on the right stops being what `yul%` produces and the `rfl` below stops checking,
which is a build failure rather than a red gate. -/
example : irRuntimePrologue =
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])] := rfl

/-- The same for the creation-object statement, including the STRING-literal name key. -/
example : irCreationSetImmutable =
    [Stmt.exprStmt (Expr.builtin Op.setimmutable
        [Expr.lit (.number 128), Expr.lit (.string "5"), Expr.lit (.number 7)])] := rfl

/-! ### 3. The step rules -/

/-- GATE 4: `memoryguard` is the identity and touches nothing. In order: it returns its
argument; it returns it for the value the deployed artifact carries after optimization
(0x08e0) as well as for the pre-optimisation 128 and for 0; a wrong arity is stuck; the
state is unchanged (stated as "the free pointer is still what it was", since `EvmState`
has no `BEq`); and the composition the artifact actually performs leaves the pointer at
128. Red if the arm becomes `a + 1`, if the arity guard is dropped, or if it starts
writing memory. -/
def memoryguardStep_ok : Bool :=
  ret1 (stepOp Op.memoryguard [128] EvmState.init) == some 128 &&
    ret1 (stepOp Op.memoryguard [0x08e0] EvmState.init) == some 0x08e0 &&
    ret1 (stepOp Op.memoryguard [0] EvmState.init) == some 0 &&
    (stepOp Op.memoryguard [] EvmState.init).isNone &&
    (stepOp Op.memoryguard [1, 2] EvmState.init).isNone &&
    freePtr (match stepOp Op.memoryguard [128] EvmState.init with
      | some (.ok _ st) => st | _ => EvmState.init) == 0 &&
    freePtr (match stepOp Op.mstore [64, 128] EvmState.init with
      | some (.ok _ st) => st | _ => EvmState.init) == 128

#eval memoryguardStep_ok                      -- expect true

/-- GATE 5: `setimmutable` writes the immutable map and nothing else - not memory, not
storage, not the free pointer, not the active-word mark - returns no values, is stuck at
the wrong arity, and is keyed by the name's string-literal encoding exactly like
`loadimmutable`. The last two conjuncts are the pair law D-P15 asks for: after the
write, the read of the SAME name returns the written word and the read of a DIFFERENT
name is still zero. Red if `base` is ever read as a memory offset (the fourth conjunct
would then see a memory write), if the key is dropped, or if the value is swapped with
the name. -/
def setimmutableStep_ok : Bool :=
  let st := match stepOp Op.setimmutable [128, litValue (.string "5"), 7] EvmState.init with
    | some (.ok rets st) => if rets.isEmpty then st else EvmState.init
    | _ => EvmState.init
  immutableAt st "5" == 7 &&
    immutableAt st "29" == 0 &&
    freePtr st == 0 &&
    st.memory 128 == 0 &&
    st.storage 0 == 0 &&
    st.activeWords == 0 &&
    (stepOp Op.setimmutable [128, litValue (.string "5")] EvmState.init).isNone &&
    (stepOp Op.setimmutable [128, litValue (.string "5"), 7, 8] EvmState.init).isNone &&
    (stepOp Op.setimmutable [] EvmState.init).isNone &&
    ret1 (stepOp Op.loadimmutable [litValue (.string "5")] st) == some 7 &&
    ret1 (stepOp Op.loadimmutable [litValue (.string "29")] st) == some 0

#eval setimmutableStep_ok                     -- expect true

/-- GATE 6: the effect classification the fork advertises. `memoryguard` is pure, so a
pass may CSE or delete it; `setimmutable` is a blind writer that never halts, so it may
be reordered past a memory reader but not past another immutable write. `effects_sound`
(vendor `Dialect/EVM.lean`) is proved over the whole enum, so these flags are checked
against `stepOp` for every op rather than trusted. -/
def newEffects_ok : Bool :=
  effects Op.memoryguard ==
    { deterministic := true, reads := false, writes := false, halts := false } &&
    effects Op.setimmutable ==
      { deterministic := true, reads := false, writes := true, halts := false } &&
    Effects.pure (effects Op.memoryguard) &&
    ! Effects.pure (effects Op.setimmutable) &&
    (effects Op.loadimmutable).writes == false

#eval newEffects_ok                           -- expect true

/-! ### 4. Runs: the inhabitation evidence -/

/-- The state the deployed runtime prologue leaves behind from a fresh frame: the free
memory pointer set to the artifact's reservation (128 = 0x80), three active words (the
write touches [64, 96)), nothing halted. -/
def prologuePost : EvmState :=
  { EvmState.init with
    memory := storeWord EvmState.init.memory 64 128
    activeWords := 3 }

/-- The prologue's two steps, as the `Step` derivation needs them. `evm.Builtin` is
definitionally the `stepOp` equation (`EVMExec`'s `evm` instance), so each of these is `rfl`:
the derivation assumes nothing the semantics does not compute. -/
theorem stepPrologueGuard :
    stepOp Op.memoryguard [128] EvmState.init = some (.ok [128] EvmState.init) := rfl
theorem stepPrologueMstore :
    stepOp Op.mstore [64, 128] EvmState.init = some (.ok [] prologuePost) := rfl

theorem guardBuiltin :
    evm.Builtin Op.memoryguard [128] EvmState.init (.ok [128] EvmState.init) := rfl
theorem mstoreBuiltin :
    evm.Builtin Op.mstore [64, 128] EvmState.init (.ok [] prologuePost) := rfl

/-- The same two through the OPEN dialect stage 1 built. Both new built-ins fall through the
`| _ => stepOp op args st = some result` arm of `builtinWithExternal`, so they compose with
any call relation and any gas oracle with no further work - which is what makes
`RunContractIR`'s `∀ c g` quantification harmless for them. -/
theorem guardBuiltinOpen (c : ExternalCalls) (g : ExternalGas) :
    (Bridge.Dialect c g).Builtin Op.memoryguard [128] EvmState.init (.ok [128] EvmState.init) := by
  simp only [Bridge.Dialect, evmWithExternal, builtinWithExternal]
  exact stepPrologueGuard
theorem mstoreBuiltinOpen (c : ExternalCalls) (g : ExternalGas) :
    (Bridge.Dialect c g).Builtin Op.mstore [64, 128] EvmState.init (.ok [] prologuePost) := by
  simp only [Bridge.Dialect, evmWithExternal, builtinWithExternal]
  exact stepPrologueMstore

/-- The prologue's argument list, evaluated right-to-left: the inner `memoryguard` first
(state unchanged, one word back), then the literal `64`. Stated with its full type so every
implicit of `Step.builtinOk` is pinned by the goal rather than guessed. -/
theorem prologueArgsStep {funs : FunEnv (D := evm)} :
    Step evm funs [] EvmState.init
      (Code.args [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])
      (.eres (.vals [64, 128] EvmState.init)) :=
  Step.argsCons
    (Step.argsCons (Step.argsNil (D := evm) (st := EvmState.init))
      (Step.builtinOk (D := evm) (argvals := [128]) (st1 := EvmState.init)
        (rets := [128]) (st2 := EvmState.init)
        (Step.argsCons (D := evm) (rest := []) (restvals := []) (st := EvmState.init)
          (Step.argsNil (D := evm) (st := EvmState.init))
          (Step.lit (D := evm) (st := EvmState.init) (l := Literal.number 128)))
        guardBuiltin))
    (Step.lit (D := evm) (st := EvmState.init) (l := Literal.number 64))

/-- The prologue's `mstore(64, memoryguard(128))` expression step. -/
theorem prologueExprStep {funs : FunEnv (D := evm)} :
    Step evm funs [] EvmState.init
      (Code.expr (Expr.builtin Op.mstore
          [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]]))
      (.eres (.vals [] prologuePost)) :=
  Step.builtinOk (D := evm) prologueArgsStep mstoreBuiltin

/-- RUNCONTRACTIR IS NO LONGER BLOCKED AT ITS FIRST STATEMENT. A big-step `Run` derivation
of the deployed runtime prologue, assembled from the `Step` constructors above: `Step.block`,
`Step.seqCons`, `Step.exprStmt`, `Step.builtinOk` for the mstore, whose argument list is
evaluated right-to-left through `Step.argsCons` into `Step.builtinOk` for the memoryguard.
Before the fork the innermost premise was a `Builtin` of a *user* call and there was nothing
to apply - this is the derivation that did not exist. -/
theorem irPrologue_runs :
    YulSemantics.Run evm irRuntimePrologue EvmState.init [] prologuePost .normal := by
  show YulSemantics.Run evm
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])]
    EvmState.init [] prologuePost .normal
  exact Step.block (D := evm) (Step.seqCons (Step.exprStmt prologueExprStep) Step.seqNil)

/-- The same two steps through the open dialect, with every implicit pinned the same way. -/
theorem prologueArgsStepOpen (c : ExternalCalls) (g : ExternalGas)
    {funs : FunEnv (D := Bridge.Dialect c g)} :
    Step (Bridge.Dialect c g) funs [] EvmState.init
      (Code.args [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])
      (.eres (.vals [64, 128] EvmState.init)) :=
  Step.argsCons
    (Step.argsCons (Step.argsNil (D := Bridge.Dialect c g) (st := EvmState.init))
      (Step.builtinOk (D := Bridge.Dialect c g) (argvals := [128]) (st1 := EvmState.init)
        (rets := [128]) (st2 := EvmState.init)
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
          (st := EvmState.init)
          (Step.argsNil (D := Bridge.Dialect c g) (st := EvmState.init))
          (Step.lit (D := Bridge.Dialect c g) (st := EvmState.init) (l := Literal.number 128)))
        (guardBuiltinOpen c g)))
    (Step.lit (D := Bridge.Dialect c g) (st := EvmState.init) (l := Literal.number 64))

theorem prologueExprStepOpen (c : ExternalCalls) (g : ExternalGas)
    {funs : FunEnv (D := Bridge.Dialect c g)} :
    Step (Bridge.Dialect c g) funs [] EvmState.init
      (Code.expr (Expr.builtin Op.mstore
          [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]]))
      (.eres (.vals [] prologuePost)) :=
  Step.builtinOk (D := Bridge.Dialect c g) (prologueArgsStepOpen c g) (mstoreBuiltinOpen c g)

/-- The prologue's post-state for an ARBITRARY frame. `RunContractIR` runs the runtime block
from `callState W irLyt H cd`, whose memory and active-words mark are the deployment's, not
`EvmState.init`, so the inhabitation statement has to be generic over the incoming state or
it does not apply where it is needed. -/
def prologuePostFrom (st0 : EvmState) : EvmState :=
  { st0 with
    memory := storeWord st0.memory 64 128
    activeWords := BitVec.ofNat 256 (activeWordsAfter st0.activeWords.toNat 64 32) }

theorem guardBuiltinFrom {st0 : EvmState} :
    evm.Builtin Op.memoryguard [128] st0 (.ok [128] st0) := rfl
theorem mstoreBuiltinFrom {st0 : EvmState} :
    evm.Builtin Op.mstore [64, 128] st0 (.ok [] (prologuePostFrom st0)) := rfl

/-- The argument list of the prologue's mstore, from an arbitrary frame. Every implicit is
pinned by the stated type, which is what makes the `Step` constructors elaborate. -/
theorem prologueArgsStepFrom {st0 : EvmState} {funs : FunEnv (D := evm)} :
    Step evm funs [] st0
      (Code.args [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])
      (.eres (.vals [64, 128] st0)) :=
  Step.argsCons
    (Step.argsCons (Step.argsNil (D := evm) (st := st0))
      (Step.builtinOk (D := evm) (argvals := [128]) (st1 := st0) (rets := [128]) (st2 := st0)
        (Step.argsCons (D := evm) (rest := []) (restvals := []) (st := st0)
          (Step.argsNil (D := evm) (st := st0))
          (Step.lit (D := evm) (st := st0) (l := Literal.number 128)))
        guardBuiltinFrom))
    (Step.lit (D := evm) (st := st0) (l := Literal.number 64))

theorem prologueExprStepFrom {st0 : EvmState} {funs : FunEnv (D := evm)} :
    Step evm funs [] st0
      (Code.expr (Expr.builtin Op.mstore
          [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]]))
      (.eres (.vals [] (prologuePostFrom st0))) :=
  Step.builtinOk (D := evm) prologueArgsStepFrom mstoreBuiltinFrom

/-- THE PROLOGUE STEPS FROM ANY FRAME. This is the inhabitation statement stage 6 needs:
whatever `EvmState` `callState` builds, the imported runtime's first statement has a `Step`
derivation and the frame's free-memory pointer becomes the artifact's reservation. -/
theorem irPrologue_runs_from (st0 : EvmState) :
    YulSemantics.Run evm irRuntimePrologue st0 [] (prologuePostFrom st0) .normal := by
  show YulSemantics.Run evm
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])]
    st0 [] (prologuePostFrom st0) .normal
  exact Step.block (D := evm)
    (Step.seqCons (Step.exprStmt prologueExprStepFrom) Step.seqNil)

/-- The same two runs through the executable interpreter, as an independent cross-check of
the hand-built derivations: fuel 20 suffices and the answer is `.ok`. Against the PRISTINE
upstream dialect the identical statements were proved the other way - the probe

    example : Interp.run exec 20 (yul% { mstore(64, memoryguard(128)) }) EvmState.init
        = .stuck := rfl
    example : Interp.run exec 20 (yul% { setimmutable(128, "5", 7) }) EvmState.init
        = .stuck := rfl

checks against `c9914c1`, together with `parse "memoryguard" = none` and
`(yulE% memoryguard(128)) = Expr.call "memoryguard" [...]`. Same program, same fuel, same
interpreter: the verdict flipped because the dialect grew two rules. That is the R-41
evidence for these Step rules, produced on a copy of the vendor tree outside the working
tree (R-54). -/
example : exists r, Interp.run exec 20 irRuntimePrologue EvmState.init = .ok r := ⟨_, rfl⟩
example : exists r, Interp.run exec 20 irCreationSetImmutable EvmState.init = .ok r := ⟨_, rfl⟩

/-- The same run in the open dialect (`Bridge.Run`, i.e.
`evmWithExternal calls ExternalCreates.none gas`), the dialect `RunContractIR` quantifies
over. -/
theorem irPrologue_runs_open (c : ExternalCalls) (g : ExternalGas) :
    Bridge.Run c g irRuntimePrologue EvmState.init [] prologuePost .normal := by
  show YulSemantics.Run (Bridge.Dialect c g)
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])]
    EvmState.init [] prologuePost .normal
  exact Step.block (D := Bridge.Dialect c g)
    (Step.seqCons (Step.exprStmt (prologueExprStepOpen c g)) Step.seqNil)

/-- And at the frame boundary: `RunCommitted`, the shape `RunContractIR` is defined with
(Surface.lean:483). The prologue does not halt, so the commit map is the identity. -/
theorem irPrologue_runCommitted (c : ExternalCalls) (g : ExternalGas) :
    Bridge.RunCommitted c g irRuntimePrologue EvmState.init [] prologuePost .normal :=
  ⟨prologuePost, irPrologue_runs_open c g, (committedState_none rfl).symm⟩

/-- The immutable pair: the creation-code write and the deployed-code read of the same name
in one program, with the read result stored where the state can show it. This is PLAN
section 7's irCheck property - "immutables come from `loadimmutable`, which equals
constructor-set values" - as an executable run rather than as a wish. -/
def immutablePair : Block Op := yul% {
  setimmutable(128, "5", 7)
  mstore(0, loadimmutable("5"))
}

/-- The state after the write and before the read: the immutable map, and nothing else. -/
def pairMid : EvmState :=
  { EvmState.init with
    env := { EvmState.init.env with
      immutable := upd EvmState.init.env.immutable (litValue (.string "5")) 7 } }

/-- The state `immutablePair` leaves, written the way `stepOp` produces it so the
derivation below is `rfl`; `immutablePair_ok` is where the human-readable claims (one active
word, the 7 in the LAST byte of word 0) are checked. -/
def pairPost : EvmState :=
  { touchMemory pairMid 0 32 with memory := storeWord pairMid.memory 0 7 }

theorem setimmBuiltin :
    evm.Builtin Op.setimmutable [128, litValue (.string "5"), 7] EvmState.init (.ok [] pairMid) :=
  rfl
theorem loadimmBuiltin :
    evm.Builtin Op.loadimmutable [litValue (.string "5")] pairMid (.ok [7] pairMid) := by
  show stepOp Op.loadimmutable [litValue (.string "5")] pairMid = some (.ok [7] pairMid)
  simp [pairMid, stepOp, rd1, upd]
theorem mstorePairBuiltin : evm.Builtin Op.mstore [0, 7] pairMid (.ok [] pairPost) := rfl

/-- THE SET/LOAD PAIR RUNS: `setimmutable` followed by `loadimmutable` of the same name, in
the closed dialect, ending with the written word in memory. -/
theorem immutablePair_runs :
    YulSemantics.Run evm immutablePair EvmState.init [] pairPost .normal :=
  Step.block (D := evm)
    (Step.seqCons
      (Step.exprStmt (Step.builtinOk (D := evm)
        (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) Step.lit)
        setimmBuiltin))
      (Step.seqCons
        (Step.exprStmt
          (Step.builtinOk (D := evm)
            (Step.argsCons
              (Step.argsCons Step.argsNil
                (Step.builtinOk (D := evm) (Step.argsCons Step.argsNil Step.lit) loadimmBuiltin))
              Step.lit)
            mstorePairBuiltin))
        Step.seqNil))

/-- GATE 7: the pair law as a computation, independent of the derivation above: the word
the run leaves in memory is the word the constructor wrote, and a name nobody set is
still zero. Red if `setimmutable` and `loadimmutable` stop sharing a key - the drift
the fork note in `EVMExec` promises against. -/
def immutablePair_ok : Bool :=
  immutableAt pairPost "5" == 7 && pairPost.memory 31 == 7 && pairPost.memory 0 == 0 &&
    immutableAt pairPost "29" == 0 && pairPost.activeWords == 1 &&
    -- the write itself touched no memory: only the following mstore did
    pairPost.memory 128 == 0 && pairPost.storage 0 == 0

#eval immutablePair_ok                        -- expect true

/-! ### 4b. Composition with stage 1 -/

/-- GATE 10: the fork composes with stage 1's classification instead of disturbing it.
`Op.isWriter` (Bridge.lean:563) decides which built-ins can change the WORLD, and
`WorldEq` (Bridge.lean:303) has no immutable component - it lists storage, transient,
logs, selfdestructs and the world projections, not `env.immutable`. So neither new op is a
writer, `Run_worldEq_of_noWriters` still applies to programs that touch immutables, and
the `| _ => false` catch-all in stage 1's file is doing the right thing for names it was
written before. Red if `setimmutable` is ever reinterpreted as a memory or world write, or
if `WorldEq` grows an immutable component (in which case the writer list must grow too -
in stage 1's file, not here). -/
def isWriterComposition_ok : Bool :=
  ! Op.isWriter Op.memoryguard && ! Op.isWriter Op.setimmutable &&
    Op.isWriter Op.sstore && ! Op.isWriter Op.loadimmutable &&
    -- and the open dialect's catch-all really is what runs the new ops: a static frame
    -- does not gate them, because neither writes the world
    (match stepOp Op.setimmutable [0, litValue (.string "5"), 7]
        { EvmState.init with env := { EvmState.init.env with static := true } } with
      | some (.ok _ st) => st.env.static && immutableAt st "5" == 7
      | _ => false)

#eval isWriterComposition_ok                  -- expect true

/-! ### 5. The artifact manifest -/

/-- A missing manifest is a RED, never a silent true (the `EvmKats.readFirst` precedent,
re-declared rather than imported so the Yul layer does not acquire the generator).
Relative paths resolve from `formal/`, where checks.sh and lake run. -/
def readIrManifest : IO String :=
  ["Midfall/Yul/ir-builtins.tsv", "formal/Midfall/Yul/ir-builtins.tsv"].foldl
    (fun (acc : IO String) (path : String) =>
      acc >>= fun got =>
        if got != "" then pure got
        else (try IO.FS.readFile path catch _ => pure ""))
    (pure "")

/-- One manifest row: artifact, classification, name, call sites. -/
structure IrRow where
  artifact : String
  kind : String
  name : String
  sites : Nat

/-- `digitsToNat s`: the natural the decimal digits of `s` spell, ignoring everything else.
Written out because this file imports neither a string-number parser nor Mathlib. -/
def digitsToNat (s : String) : Nat :=
  s.toList.foldl (fun acc c =>
    if '0' <= c && c <= '9' then acc * 10 + (c.toNat - '0'.toNat) else acc) 0

/-- The manifest, parsed. Lines starting with `#` are the header the script writes, and a
row needs exactly four tab-separated fields. -/
def parseIrManifest (text : String) : List IrRow :=
  text.splitOn "\n" |>.filterMap fun line =>
    if line.startsWith "#" || line.startsWith "\t" then none
    else
      let parts := line.splitOn "\t"
      if parts.length == 4 then
        some { artifact := parts[0]!, kind := parts[1]!, name := parts[2]!,
               sites := digitsToNat parts[3]! }
      else none

/-- `hasSubstr t needle`: needle occurs in t. Stated through `splitOn` because this file
does not import the string-search helpers. -/
def hasSubstr (t needle : String) : Bool := (t.splitOn needle).length > 1

/-- GATE 8 (reachability first, per the standing D-P19 note): the manifest exists and is
non-empty, so a moved file is a named red rather than a vacuous pass. -/
def irManifestReachable_ok : IO Bool :=
  readIrManifest >>= fun t =>
    pure (!(parseIrManifest t).isEmpty && hasSubstr t "memoryguard" &&
      hasSubstr t "unresolved")  -- the header documents the classification; a truncated
                                  -- or hand-edited file would not carry it

#eval irManifestReachable_ok                  -- expect true

/-- GATE 9: THE MEASUREMENT GATE. Every name the deployed via-IR calls is either resolved
by `parse` or is a user function defined in the artifact; nothing is unresolved; and the
three names this package is about appear with the counts the pinned compiler produced.
Red if a future solc or a future template emits a builtin the dialect cannot parse -
exactly the failure that would silently re-empty `RunContractIR`. Re-run
`python3 scripts/extract_ir_builtins.py` after any change to the artifact or to `parse`.
The last conjunct pins the distinct-builtin count, so a manifest that stopped covering
the deployed artifact shows up here too. -/
def irManifest_ok : IO Bool := do
  let rows := parseIrManifest (← readIrManifest)
  let sites (art name : String) : Nat :=
    (rows.filter fun r => r.artifact == art && r.name == name).foldl (fun acc r => acc + r.sites) 0
  let present (art name kind : String) : Bool :=
    ! (rows.filter fun r => r.artifact == art && r.name == name && r.kind == kind).isEmpty
  let distinctBuiltins :=
    ((rows.filter fun r => r.kind == "builtin").map (fun r => r.name)).eraseDups.length
  pure
    (rows.length > 40 &&
      -- nothing is unresolved: the whole point of the package
      (rows.filter fun r => r.kind == "unresolved").length == 0 &&
      -- the classification is a partition of `parse`, not a label someone kept current
      (rows.filter fun r =>
        (r.kind == "builtin") != ((parse r.name).isSome && r.kind != "user")).length == 0 &&
      sites "Halo2Verifier" "memoryguard" == 2 &&
      sites "Halo2VerifyingKey" "memoryguard" == 1 &&
      sites "Halo2Verifier" "setimmutable" == 1 &&
      sites "Halo2Verifier" "loadimmutable" == 2 &&
      present "Halo2Verifier" "memoryguard" "builtin" &&
      present "Halo2Verifier" "setimmutable" "builtin" &&
      -- the artifact of record is the deployed verifier, and it is not empty
      present "Halo2Verifier" "mstore" "builtin" &&
      distinctBuiltins == 43)

#eval irManifest_ok                           -- expect true

end Midfall.Yul.Builtins
