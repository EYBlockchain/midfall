

# AREA: Yul semantics layer: vendored powdr-labs/yul-semantics (formal/vendor/yul-semantics/YulSemantics/**), Midfall/Yul/Externals.lean (EIP-2537/EIP-198 byte relations), and what the unwritten Midfall/Yul/Bridge.lean (P-BR, D-

## constraints
- Y-3, confirmed: YulSemantics.RunCommitted (Observation.lean:39; namespace YulSemantics, NOT EVM.RunCommitted) is fixed to the closed EVM.evm dialect. There stepOp returns none for gas/call/staticcall/delegatecall/callcode/create/create2 (EVMExec.lean:832-833). Every precompile call in the verifier is a staticcall, so RunCommitted over the verifier has NO derivation and any '∀ obs, RunCommitted … → …' soundness statement is VACUOUSLY true. RunVerifier and RunContractIR must be built on the generic YulSemantics.Run (BigStep.lean:366) at EVM.evmWithExternal calls ExternalCreates.none gasOracle, composed with EVM.committedState.
- PLAN's `(keccak := H)` named argument does not exist (Y-2). The hash is the state field st0.env.keccakOf : List UInt8 → U256 (EVMExec.lean:160, read at :731-733). So hash-agnosticism IS achievable at this layer by quantifying over st0.env.keccakOf, which answers P-BR item 4 positively. No step changes env.keccakOf: CallWorld.install (:571), finishSelfdestruct, sstore/tstore and finishCreate touch other env fields. An invariance lemma is therefore provable. A Midfall Hash (Bytes → H256) needs the List UInt8 ↔ ByteArray conversion.
- Y-2 trap, made precise: extcodehash returns projectedCodeHash st.env st.env.balanceOf a (EVMExec.lean:822, :295-298). That is env.keccakOf (env.extCodeOf a) unless the account is empty, and it is NOT ExecEnv.extCodeHashOf, which stepOp never reads. So Deployment.vkHash and qHash become hypotheses on H (H vkRuntime = vkCodehash, given W.extCodeOf vkAddr = vkRuntime and a nonzero code length). They are not facts about the world W. The verifier checks extcodesize plus extcodehash (VkLoading.yul:68-70, QuotientAndLinearization.yul:21-24).
- There is no Obs type, and none of .return / .isReturn / obs.data / isRevertOrHalt / worldUnchanged exists. The observation is (stObs : EvmState, o : Outcome). Outcome (Ast.lean:353) has no payload: return/revert kind and data are in stObs.halted : Option (HaltKind × List UInt8), and the data is a List UInt8, not Bytes. Running off the end gives o = .normal with halted = none. Top-level .break/.continue/.leave are derivable, because block and seqStop propagate them and no rule makes them stuck, so obsOf must handle them.
- worldUnchanged must be defined over the world components (storage, transient, logs, selfdestructs and the env world maps), not as stObs = st0. Memory, activeWords, returndata and halted always differ. On revert/invalid, committedState rolls back to st0 except halted and returndata (committedState_rollback, EVM.lean:37), so a revert is world-unchanged by construction. On return it needs every call to be a staticcall (finishCall_static_storage, EVM.lean:76) plus no sstore/tstore/log. Trace mode uses call(gas(),…) and log1(…gas()), which is excluded by Supported.production.
- Determinism: YulSemantics.Run.det (Determinism.lean:411; :410 is the docstring) is dialect-generic with hypothesis `∀ op, D.Deterministic op`. For evmWithExternal calls ExternalCreates.none gasOracle this holds when (i) calls is functional, (ii) gasOracle is functional (e.g. ExternalGas.ofFun f), and (iii) create/create2 hold vacuously or trivially, since the static branch is deterministic. ExternalGas.any makes .gas nondeterministic, which blocks Run.det. ExternalGas.none makes gas() stuck. The production external-quotient path executes staticcall(gas(), quotientEvaluator, …) (QuotientAndLinearization.yul:35), so .none would make that path underivable. Y-3's remark that option (a) 'silently loses determinism' is overstated: only RunCommitted.det's 3-line proof, which goes through EVM.run_det, has to be redone.
- RunContract, StmtContract and StmtsContract (Contract.lean:21,85,94) are EXISTENTIAL: some run satisfies post. With a non-functional external relation (the adversarial `calls` of verifier_sound) they say nothing about ALL runs. verifier_sound and the per-partial '…∨ Inv' specs need a ∀-runs partial-correctness contract, which is missing.
- Per-partial specs cannot be RunContract. RunContract is a whole-program Run with funs = [] and V = [], while the partial blocks call helpers defined elsewhere (AssemblyHelpers functions, fail(…)) and read local variables. Use StmtsContract with an explicit funs (the hoisted scope of the enclosing program) and a VEnv-aware pre. post has type VEnv D → D.State → VEnv D → D.State → Outcome → Prop, not `fun s => …`. StmtsContract.cons (:143) requires the head outcome = .normal. There is no halting-head cons, append, cond/switch/function-call contract or halting loop rule, and all of these are needed for 's.reverted ∨ Inv'.
- D is not inferable from `program : Block D.Op`, because Dialect.Op is a structure field. Every RunContract or StmtsContract use at the open dialect must write (D := EVM.evmWithExternal c ExternalCreates.none g) explicitly. DecidableEq D.Value resolves because evmWithExternal is @[reducible] with Value := U256, although nothing in the tree yet runs Run at evmWithExternal.
- PLAN's `bindLocals L` (locals := immutables, let-bound) CANNOT work for Solidity constants. Free identifiers such as FR_MODULUS, MODEXP_GAS and ERR_* (91 internal constants, ecosystem 12.4) appear INSIDE Yul function bodies (AssemblyHelpers.yul:22,31-33 in scalar_inv). Yul calls (BigStep callOk :185-193) run the body with VEnv = params ++ rets only, so Expr.var "FR_MODULUS" is stuck. Constants must be substituted as literals, which is what solc does, or bound some other way.
- memoryguard and setimmutable are absent from EVM.Op (EVMExec.lean:47-51, deliberate; D-P15 needs them). D-P15's 'the elaborator is the checker' is FALSE for unknown names: yul% resolves calls through EVM.mkCall (Syntax.lean:107,174; EVMOp.lean:216-219), so memoryguard(x) elaborates silently to Expr.call "memoryguard" [x] and is stuck at run time. A gate must check for unresolved callee names. loadimmutable IS present (EVMOp.lean:42) and reads env.immutable (EVMExec.lean:793).
- RunObject and runObject (ObjectRun.lean:64,68) run the closed dialect from Layout.initState, whose env.calldata = []. They execute o.codeBlock, the constructor code, not the runtime sub-object. So qvm_yul_refines' precondition 'calldata = f.bytes' and RunContractIR's ir.runtime cannot be expressed with them. Object has no .runtime field; use Object.subObject (Object.lean:80).
- Externals.lean types are not EVM types. Midfall.Yul.CallKind (Externals:743) is a separate inductive from EVM.CallKind (EVMExec:408). Midfall.Yul.CallRequest.input is a ByteArray, against List UInt8 in EVM. CallOutcome has no world field. Bridge must convert all three and supply world := CallWorld.ofState st. respond (:799) ignores kind and gas, and returns none both for a wrong target and for invalid input. accepts compares the full 256-bit target, whereas EVM account equality is accountKey mod 2^160 (EVMExec:278).
- Y-1: assemble ONE `EVM.ExternalCalls.mk (fun req st resp => …)` as a disjunction split by target. The four precompile addresses are distinct (0x0b, 0x0c, 0x0f, 0x05), so the sub-relations' agreement obligation reduces to address disjointness, plus a Deployment hypothesis that the quotient evaluator address is none of these. Soundness needs a PERMISSIVE relation (success → honest output; failure always allowed, since gas is unmodelled). Completeness and determinism need the FUNCTIONAL honest relation (honestCalls).
- PAIRING_CHECK's result is the oracle `PairingProduct := Bytes -> Bool` (Externals:941). Eip2537.Holds must be a named hypothesis relating `product (pairingFrame [(g1Bytes P1, g2Bytes Q1), …])` to the Lean AdmissiblePairing equation through the G1/G2 codecs. Pairing orientation is swapped at the call site (R-11, FinalPairing.yul:88).
- Externals.lean contains ZERO theorems. All its gates are #eval Bool (:1309-1318) and are not kernel-checked, so nothing there can be cited as a proved lemma.
- Gas is not modelled: EvmState has no gas field. 'Enough gas' can only be expressed as the honest external relation ignoring req.gas, or through ExternalGas.ofFun (Y-5).
- Adequacy (Interp.run_adequacy, Adequacy.lean:772) exists only for an ExecDialect. There is no interpreter or adequacy for evmWithExternal. Executable differential gates need a new ExecDialect whose builtinFn answers precompile staticcalls via respond and gas() via a fixed function, together with a Lawful proof against evmWithExternal(honestCalls, .none, .ofFun f). Y-4: state the theorems over the fuel-free Run, not Interp.run.
- render_eq_print as a text equality is false (R-39). Restate it structurally with YulSemantics.SyntaxEq.stmtsBeq (Ast.lean:147; D-P13 misnames it Ast.stmtsBeq). Only stmtsBeq_eq (soundness, :288) exists: no reflexivity lemma, and equality is on name strings with no alpha-equivalence (ecosystem 12.2). No runtime Yul parser exists, so an `astOf (g.render o)` cannot be defined.
- R-37: Lean 4.35 cannot do structural recursion through Stmt.switch's List (Literal × Block). Any recursive pass over Block (constant substitution, irCheck, partial extraction) needs fuel with a loud failure marker, or well-founded recursion.
- Other plan statements already reported unstatable or false: decodeAcc_injective is FALSE (R-25). qvm_compile_correct, qvm_validated_noOOB, qvm_yul_refines and direct_correct are not statable as written (D-P20 items 1-4). Supported.layout over-claims (D-P18). Lowering/Types.lean's Deployment is an all-True placeholder (:71-76).
- Citation corrections: P-BR cites evmWithExternal at Dialect/EVM.lean:135-164, but it is at Dialect/EVMExec.lean:953 (EVM.lean:135 is effects_sound_withExternal). Ecosystem Y-1 cites ExternalCalls none/any at :532/:535, but those lines are ExternalCreates.none/any; ExternalCalls.none/any are at :480/:484. Determinism.lean:410 is a docstring; Run.det is at :411.

## missing
- formal/Midfall/Yul/Bridge.lean (P-BR, D-P10) does not exist. Its contents are model-level, with no Rust source: Bridge.Run := YulSemantics.Run (EVM.evmWithExternal calls EVM.ExternalCreates.none gasOracle); Bridge.RunCommitted := ∃ st', Bridge.Run … st' o ∧ stObs = EVM.committedState st0 st'; Bridge.Functional (calls) := ∀ req st r₁ r₂, calls.Call req st r₁ → calls.Call req st r₂ → r₁ = r₂; a lemma that every op of evmWithExternal is Deterministic given Functional calls and a functional gas oracle; Bridge.RunCommitted.det via YulSemantics.Run.det; and a counterexample gate with a two-response `calls`.
- A keccak hook: withKeccak (st : EvmState) (H : Midfall.Halo2.Hash) setting env.keccakOf := fun l => H (ByteArray.mk l.toArray), plus a lemma that keccakOf is invariant along any Run.
- An Obs type, obsOf (stObs : EvmState) (o : Outcome), isReturn / data / isRevertOrHalt, and worldUnchanged over the world components. None of these exist.
- calls L W, Eip2537.rel, Modexp.rel and Evaluator.rel. Today there are only decidable records (Externals.lean honestRelations :1006). Still missing: the conversion to EVM.CallRequest/CallResponse (Bytes ↔ List UInt8, Midfall.Yul.CallKind ↔ EVM.CallKind, world := CallWorld.ofState st), a permissive soundness relation, a functional honestCalls, and Eip2537.Holds / Modexp.Holds (the PairingProduct ↔ AdmissiblePairing link).
- Evaluator.rel L W: an ExternalCalls answering the quotient evaluator address by running the evaluator's RUNTIME sub-object with env.calldata := req.input and env.static := true, mapping committed halted (.ret, d) to success with d. It needs a calldata-carrying RunObject variant and a runtime-sub-object accessor. Port source: the generator's quotient evaluator object (proofs/solidity-verifier/src/lowering, the quotient VM emitter) and vm/reference.rs semantics (D-P20).
- A World / Deployment model over EVM.ExecEnv. Lowering/Types.lean:71 is an all-True placeholder. Required fields: extCodeOf vkAddr = vkRuntime, H vkRuntime = vkCodehash (via projectedCodeHash), the matching quotient fields, and address disjointness from 0x05/0x0b/0x0c/0x0f.
- initState W cd mem₀ and callState W cd (EvmState builders: env := W with calldata := cd.data.toList, keccakOf := H, memory := mem₀). They are absent. Rust reference: the revm harness in proofs/solidity-verifier/src/evm.rs.
- bindLocals L. It must be a constant-substitution pass (Ident → literal) over Block, using fuel per R-37, not let-binding, because constants appear inside Yul functions. Port source: the TemplateConstants and Constants.sol rendering in proofs/solidity-verifier/src/lowering/render and layout/mod.rs.
- A ∀-runs partial-correctness contract layer (e.g. StmtsContractAll / RunContractAll) plus composition lemmas the vendor lacks: halting-head cons, append, cond, switch, user-function call, and a halting loop countdown.
- The phase invariants Inv k (layout/memory.rs) and the partial-block extraction `blk .vkLoading L`, … for the vkLoading/transcriptParser/lagrange/quotientLin/pcs/finalPairing/traceReturn specs. Port source: proofs/solidity-verifier/src/lowering/layout/memory.rs and the templates/partials/verifier/*.yul partials.
- RunShell, SolShell, ObsEquiv, irCheck and ImportSolcIR (D-P15 generated yul% quotes), plus an ir.runtime accessor. Prerequisites: memoryguard and setimmutable must be added to EVM.Op or eliminated before import, and a gate must reject unresolved .call names, since mkCall silently produces them.
- A lawful executable ExecDialect for the honest open world, so the Lean contract model can be run differentially against revm. The vendored adequacy covers only EVM.exec.
- QVM.Program / Frame / Output and L.plan.qprog (D-P20; LoweringPlan is P-11). Rust source: vm/reference.rs eval_quotient_identity plus the segment walker.

## declarations
- `YulSemantics.Dialect` (formal/vendor/yul-semantics/YulSemantics/Dialect.lean:108)
    sig: structure Dialect where Op : Type Value : Type State : Type litValue : Literal → Value litWF : Literal → Prop Builtin : Op → List Value → State → BuiltinResult Value State → Prop effects : Op → Effects
    notes: The step relation is Builtin, a Prop-valued relation, so it can be nondeterministic. Dialect.Op is a field, so Block D.Op does not determine D. Whenever D is implicit (RunContract, StmtsContract, ...), pass (D := ...) explicitly.
- `YulSemantics.BuiltinResult` (formal/vendor/yul-semantics/YulSemantics/Dialect.lean:28)
    sig: inductive BuiltinResult (Value State : Type) | ok (rets : List Value) (st : State) | halt (st : State)
    notes: halt carries no payload. The return/revert kind and data live in the state (EvmState.halted).
- `YulSemantics.Dialect.Deterministic` (formal/vendor/yul-semantics/YulSemantics/Dialect.lean:135)
    sig: def Deterministic (op : D.Op) : Prop := ∀ args st r₁ r₂, D.Builtin op args st r₁ → D.Builtin op args st r₂ → r₁ = r₂
    notes: Declared under `variable (D : Dialect)`. Run.det needs this for EVERY op. NonWriting is at :139, NonHalting at :143, NonReading at :152, EffectsSound at :160.
- `YulSemantics.ExecDialect / ExecDialect.Lawful` (formal/vendor/yul-semantics/YulSemantics/Dialect.lean:176)
    sig: structure ExecDialect extends Dialect where builtinFn : Op → List Value → State → Option (BuiltinResult Value State) def ExecDialect.Lawful (E : ExecDialect) : Prop := ∀ op args st r, E.Builtin op args st r ↔ E.builtinFn op args st = some r
    notes: Lawful is at :184. The interpreter and adequacy exist only for ExecDialect. The tree has no ExecDialect for evmWithExternal.
- `YulSemantics.Expr / Stmt / Block / Literal / Outcome` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:52)
    sig: inductive Expr (Op : Type) | lit (l : Literal) | var (x : Ident) | builtin (op : Op) (args : List (Expr Op)) | call (fn : Ident) (args : List (Expr Op)) deriving Repr, Inhabited inductive Stmt (Op : Type) -- :64 | block (body : List (Stmt Op)) | funDef (name : Ident) (params rets : List Ident) (body : List (Stmt Op)) | letDecl (vars : List Ident) (val : Option (Expr Op)) | assign (vars : List Ident) (val : Expr Op) | cond (c : Expr Op) (body : List (Stmt Op)) | switch (c : Expr Op) (cases : List (Literal × List (Stmt Op))) (dflt : Option (List (Stmt Op))) | forLoop (init : List (Stmt Op)) (c : Expr Op) (post : List (Stmt Op)) (body : List (Stmt Op)) | exprStmt (e : Expr Op) | «break» | «continue» | leave deriving Repr, Inhabited abbrev Block (Op : Type) := List (Stmt Op) -- :90 inductive Literal | number (n : Nat) | bool (b : Bool) | string (s : String) -- :38, DecidableEq inductive Outcome | normal | «break» | «continue» | leave | halt -- :353, DecidableEq abbrev Ident := String -- :30
    notes: Expr and Stmt derive no DecidableEq or BEq. Use SyntaxEq. Outcome is dialect-agnostic and has no payload. The yul% quotation syntax exists (Syntax.lean:240 yul% { … } : Block EVM.Op, :242 yulE%, :244 yulObject%). It is a macro, not a runtime parser.
- `YulSemantics.Object / Data` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:327)
    sig: inductive Object (Op : Type) | mk (name : String) (code : Block Op) (subObjects : List (Object Op)) (data : List (String × Data)) deriving Repr, Inhabited
    notes: The accessors are name :335, codeBlock :337, subObjects :339 and dataSegs :342. Data is `hex (bytes : List UInt8) | string (s : String)` at :320. There is no `.runtime` field. Use Object.subObject (Object.lean:80) or lookupRef (:106) to get at the _deployed sub-object.
- `YulSemantics.SyntaxEq.stmtsBeq / stmtsBeq_eq` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:147)
    sig: variable {Op : Type} [BEq Op] def stmtsBeq : List (Stmt Op) → List (Stmt Op) → Bool -- :288, under [LawfulBEq Op] theorem stmtsBeq_eq : ∀ (left right : List (Stmt Op)), stmtsBeq left right = true → left = right
    notes: The namespace is YulSemantics.SyntaxEq, not 'Ast' as D-P13 writes. exprBeq is at :106, stmtBeq :131, casesBeq :154, exprBeq_eq :174, stmtBeq_eq :214. Only soundness is proved: there is no reflexivity or completeness lemma. Names are compared as strings, so there is no alpha-equivalence (ecosystem 12.2).
- `YulSemantics.VEnv / FDecl / FunEnv / hoist / restore` (formal/vendor/yul-semantics/YulSemantics/BigStep.lean:66)
    sig: abbrev VEnv (D : Dialect) := List (Ident × D.Value) structure FDecl (D : Dialect) where params : List Ident; rets : List Ident; body : Block D.Op -- :69 abbrev FScope (D : Dialect) := List (Ident × FDecl D) -- :78 abbrev FunEnv (D : Dialect) := List (FScope D) -- :81 def restore {D : Dialect} (outer inner : VEnv D) : VEnv D -- :111 def hoist (D : Dialect) (body : Block D.Op) : FScope D -- :115
    notes: callOk (:185-193) runs a function body with VEnv `(decl.params.zip argvals) ++ bindZeros D decl.rets`. Callees cannot see caller or outer variables.
- `YulSemantics.Step` (formal/vendor/yul-semantics/YulSemantics/BigStep.lean:164)
    sig: inductive Step (D : Dialect) [DecidableEq D.Value] : FunEnv D → VEnv D → D.State → Code D.Op → Res D → Prop where
    notes: A single indexed judgment over Code (:141, cases expr/args/stmt/stmts/loop) and Res (:155, `eres (r : EResult D) | sres (V : VEnv D) (st : D.State) (o : Outcome)`). Arguments are evaluated right to left. Ill-formed code is stuck (no derivation). Note that break/continue/leave at top level are NOT stuck: they propagate through seqStop and block.
- `YulSemantics.Run` (formal/vendor/yul-semantics/YulSemantics/BigStep.lean:366)
    sig: def Run (D : Dialect) [DecidableEq D.Value] (prog : Block D.Op) (st0 : D.State) (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop := ExecStmt D [] [] st0 (.block prog) V' st' o
    notes: Fully dialect-generic and fuel-free. This is the right base for Bridge.Run over EVM.evmWithExternal. ExecStmt is at :350, ExecStmts :355, ExecLoop :360, EvalExpr :340.
- `YulSemantics.RunContract` (formal/vendor/yul-semantics/YulSemantics/Contract.lean:21)
    sig: variable {D : Dialect} [DecidableEq D.Value] def RunContract (program : Block D.Op) (pre : D.State → Prop) (post : D.State → VEnv D → D.State → Outcome → Prop) : Prop := ∀ initial, pre initial → ∃ finalEnv final outcome, Run D program initial finalEnv final outcome ∧ post initial finalEnv final outcome
    notes: EXISTENTIAL (total correctness: some run satisfies post). It is not 'every run'. post takes 4 arguments. The combinators are intro :31, consequence :41, and_post :55, map_program :71 (∀ initial finalEnv final outcome, Run D program … → Run D program' … ) and of_stmts :205.
- `YulSemantics.StmtContract / StmtsContract` (formal/vendor/yul-semantics/YulSemantics/Contract.lean:85)
    sig: def StmtContract (funs : FunEnv D) (stmt : Stmt D.Op) (pre : VEnv D → D.State → Prop) (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop -- :94 def StmtsContract (funs : FunEnv D) (stmts : Block D.Op) (pre : VEnv D → D.State → Prop) (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop
    notes: Both are existential like RunContract. These are what per-partial specs need: a fixed funs, meaning the hoisted helper functions, plus VEnv-aware pre and post.
- `YulSemantics.StmtsContract.cons` (formal/vendor/yul-semantics/YulSemantics/Contract.lean:143)
    sig: theorem cons {funs : FunEnv D} {stmt : Stmt D.Op} {stmts : Block D.Op} {pre mid : VEnv D → D.State → Prop} {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop} (head : StmtContract funs stmt pre (fun _ _ V' st' outcome => outcome = .normal ∧ mid V' st')) (tail : ∀ V st, pre V st → StmtsContract funs stmts mid (fun _ _ V' st' outcome => post V st V' st' outcome)) : StmtsContract funs (stmt :: stmts) pre post
    notes: The head must end .normal. The tree has no variant for a halting head (seqStop), no append, and no cond/switch/call contract. Also present: StmtsContract.nil :122, StmtsContract.consequence :129, StmtContract.consequence :105.
- `YulSemantics.StmtsContract.block` (formal/vendor/yul-semantics/YulSemantics/Contract.lean:158)
    sig: theorem block {funs : FunEnv D} {body : Block D.Op} {pre : VEnv D → D.State → Prop} {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop} (h : StmtsContract (hoist D body :: funs) body pre (fun V st V' st' outcome => post V st (restore V V') st' outcome)) : StmtContract funs (.block body) pre post
    notes: Lifts a contract through a block scope.
- `YulSemantics.ExecLoop.countdown` (formal/vendor/yul-semantics/YulSemantics/Contract.lean:176)
    sig: theorem ExecLoop.countdown {funs : FunEnv D} {cond : Expr D.Op} {post body : Block D.Op} {Inv : Nat → VEnv D → D.State → Prop} (done : ∀ V st, Inv 0 V st → ∃ cv st', EvalExpr D funs V st cond (.vals [cv] st') ∧ cv = D.zero ∧ Inv 0 V st') (step : ∀ n V st, Inv (n + 1) V st → ∃ cv stc Vb stb ob Vp stp, EvalExpr D funs V st cond (.vals [cv] stc) ∧ cv ≠ D.zero ∧ ExecStmt D funs V stc (.block body) Vb stb ob ∧ (ob = .normal ∨ ob = .continue) ∧ ExecStmt D funs Vb stb (.block post) Vp stp .normal ∧ Inv n Vp stp) : ∀ n V st, Inv n V st → ∃ V' st', ExecLoop D funs V st cond post body V' st' .normal ∧ Inv 0 V' st'
    notes: Only covers loops that terminate normally. There is no halting-loop variant, so a revert inside a loop body needs a new lemma.
- `YulSemantics.RunContract.of_stmts` (formal/vendor/yul-semantics/YulSemantics/Contract.lean:205)
    sig: theorem RunContract.of_stmts {program : Block D.Op} {pre : D.State → Prop} {post : D.State → VEnv D → D.State → Outcome → Prop} (h : StmtsContract [hoist D program] program (fun V st => V = [] ∧ pre st) (fun _ st V' st' outcome => post st (restore [] V') st' outcome)) : RunContract program pre post
    notes: The final composition step from a sequence contract to a whole-program contract.
- `YulSemantics.Step.det / Run.det` (formal/vendor/yul-semantics/YulSemantics/Determinism.lean:411)
    sig: theorem Step.det (hdet : ∀ op, D.Deterministic op) {funs V st code r₁} (h₁ : Step D funs V st code r₁) : ∀ {r₂}, Step D funs V st code r₂ → r₁ = r₂ -- :22 theorem Run.det (hdet : ∀ op, D.Deterministic op) {prog st0 V₁ st₁ o₁ V₂ st₂ o₂} (h₁ : Run D prog st0 V₁ st₁ o₁) (h₂ : Run D prog st0 V₂ st₂ o₂) : V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ -- :411 (docstring :410)
    notes: Dialect-GENERIC: it applies directly to evmWithExternal once every op is shown Deterministic. Corollaries: EvalExpr.det :389, EvalArgs.det :394, ExecStmt.det :399, ExecStmts.det :405.
- `YulSemantics.EVM.evm_deterministic / EVM.run_det` (formal/vendor/yul-semantics/YulSemantics/Determinism.lean:419)
    sig: theorem EVM.evm_deterministic (op : EVM.Op) : EVM.evm.Deterministic op -- :427 theorem EVM.run_det {prog st0 V₁ st₁ o₁ V₂ st₂ o₂} (h₁ : Run EVM.evm prog st0 V₁ st₁ o₁) (h₂ : Run EVM.evm prog st0 V₂ st₂ o₂) : V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂
    notes: Closed dialect only.
- `YulSemantics.Interp.run / Interp.run_adequacy / EVM.run_adequacy` (formal/vendor/yul-semantics/YulSemantics/Adequacy.lean:772)
    sig: def run (fuel : Nat) (prog : Block E.toDialect.Op) (st0 : E.toDialect.State) : Result (SResult E) -- Interp.lean:212, variable (E : ExecDialect) [DecidableEq E.toDialect.Value] theorem run_adequacy (hE : E.Lawful) {prog st0 V' st' o} : Run E.toDialect prog st0 V' st' o ↔ ∃ n, Interp.run E n prog st0 = .ok (V', st', o) -- :772 theorem EVM.run_adequacy {prog st0 V' st' o} : Run EVM.evm prog st0 V' st' o ↔ ∃ n, Interp.run EVM.exec n prog st0 = .ok (V', st', o) -- :786
    notes: Result (Interp.lean:24) has cases ok, stuck and outOfFuel. run_sound is at :452. Adequacy holds only for an ExecDialect. There is none for the open world, so executing with precompiles needs a new lawful ExecDialect.
- `YulSemantics.RunCommitted` (formal/vendor/yul-semantics/YulSemantics/Observation.lean:39)
    sig: def RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm) (stObs : EvmState) (o : Outcome) : Prop := ∃ st', Run EVM.evm prog st0 V' st' o ∧ stObs = committedState st0 st'
    notes: Namespace is YulSemantics, NOT EVM. It is HARD-WIRED to the closed EVM.evm dialect, with no dialect or keccak argument (Y-3). The 'observation' is the pair (stObs : EvmState, o : Outcome). No Obs type exists.
- `YulSemantics.RunCommitted.det` (formal/vendor/yul-semantics/YulSemantics/Observation.lean:45)
    sig: theorem RunCommitted.det {prog st0 V₁ s₁ o₁ V₂ s₂ o₂} (h₁ : RunCommitted prog st0 V₁ s₁ o₁) (h₂ : RunCommitted prog st0 V₂ s₂ o₂) : V₁ = V₂ ∧ s₁ = s₂ ∧ o₁ = o₂
    notes: Proved through EVM.run_det, so it is closed-dialect only. The open-dialect version is a 3-line proof from Run.det plus a determinism hypothesis.
- `YulSemantics.EVM.Op` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean:27)
    sig: inductive Op | add | sub | mul | div | sdiv | mod | smod | addmod | mulmod | exp | signextend | clz | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar | keccak256 | pop | mload | mstore | mstore8 | mcopy | msize | sload | sstore | tload | tstore | calldataload | calldatasize | calldatacopy | codesize | codecopy | returndatasize | returndatacopy | datasize | dataoffset | datacopy | loadimmutable | address | origin | caller | callvalue | gasprice | selfbalance | coinbase | timestamp | number | prevrandao | gaslimit | chainid | basefee | blobbasefee | balance | extcodesize | extcodecopy | extcodehash | blockhash | blobhash | log0 | log1 | log2 | log3 | log4 | gas | call | callcode | delegatecall | staticcall | create | create2 | selfdestruct | stop | ret | revert | invalid deriving Repr, DecidableEq, Inhabited
    notes: Present: keccak256, staticcall, extcodehash, extcodecopy, loadimmutable. ABSENT: memoryguard, setimmutable, verbatim, linkersymbol (EVMExec.lean:47-51, deliberate). `ret` is the return opcode. U256 is :23 (abbrev U256 := BitVec 256). litValue is :71, effects :88, opName :142, parse :173, mkCall :216.
- `YulSemantics.EVM.HaltKind` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean:62)
    sig: inductive HaltKind | stop | ret | revert | invalid | invalidMemoryAccess | selfdestruct | staticViolation deriving Repr, DecidableEq, Inhabited
    notes: Stored in EvmState.halted together with the data.
- `YulSemantics.EVM.mkCall` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean:216)
    sig: def mkCall (name : Ident) (args : List (Expr Op)) : Expr Op := match parse name with | some op => .builtin op args | none => .call name args
    notes: The yul% elaborator calls this (Syntax.lean:107,174), so memoryguard(...) silently becomes the user-function call .call "memoryguard" args. It does not fail to elaborate.
- `YulSemantics.EVM.ExecEnv` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:114)
    sig: structure ExecEnv where address : U256 := 0; origin : U256 := 0; caller : U256 := 0; callvalue : U256 := 0 gasprice : U256 := 0; selfBalance : U256 := 0; createdThisTx : Bool := false; static : Bool := false coinbase timestamp number prevrandao gaslimit chainid basefee blobbasefee : U256 := 0 calldata : List UInt8 := [] code : List UInt8 := [] keccakOf : List UInt8 → U256 := keccakBytes balanceOf : U256 → U256 := fun _ => 0 extCodeOf : U256 → List UInt8 := fun _ => [] extCodeHashOf : U256 → U256 := fun _ => 0 nonceOf : U256 → U256 := fun _ => 0 storageOf : U256 → U256 → U256 := fun _ _ => 0 transientOf : U256 → U256 → U256 := fun _ _ => 0 blockHashOf blobHashOf : U256 → U256 := fun _ => 0 dataOffset dataSize immutable : U256 → U256 := fun _ => 0 deriving Inhabited
    notes: Field list condensed from :114-189. This is the world: there is no separate World type. keccakOf (:160) is the hash oracle (Y-2). extCodeHashOf is NEVER read by stepOp, because extcodehash uses projectedCodeHash (:295, :822). keccakBytes is `opaque keccakBytes : List UInt8 → U256` at :88.
- `YulSemantics.EVM.EvmState / EvmState.init` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:205)
    sig: structure EvmState where memory : Nat → UInt8 activeWords : U256 storage : U256 → U256 transient : U256 → U256 env : ExecEnv returndata : List UInt8 logs : List LogEntry selfdestructs : List (U256 × Bool) halted : Option (HaltKind × List UInt8) -- :230 def EvmState.init : EvmState := { memory := fun _ => 0, activeWords := 0, storage := fun _ => 0, transient := fun _ => 0, env := default, returndata := [], logs := [], selfdestructs := [], halted := none }
    notes: There is NO gas field. Calldata lives in env.calldata. Return and revert data are in halted. EvmState has no deriving clause.
- `YulSemantics.EVM.committedState / HaltKind.commits` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:262)
    sig: def committedState (st0 st' : EvmState) : EvmState def HaltKind.commits : HaltKind → Bool -- :250
    notes: STATE-typed, not op-typed, so it can be reused unchanged at evmWithExternal (answers P-BR item 2). The lemmas are committedState_none (EVM.lean:27, simp), committedState_commit (:33) and committedState_rollback (:37).
- `YulSemantics.EVM.CallKind / CallRequest` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:416)
    sig: inductive CallKind | call | callcode | delegatecall | staticcall -- :408 structure CallRequest where kind : CallKind gas : U256 target : U256 value : U256 input : List UInt8
    notes: input is the already-copied memory slice. The pre-call EvmState is passed separately to ExternalCalls.Call.
- `YulSemantics.EVM.CallWorld / CallWorld.install / CallWorld.ofState` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:433)
    sig: structure CallWorld where selfBalance : U256; balanceOf : U256 → U256; extCodeOf : U256 → List UInt8 extCodeHashOf : U256 → U256; nonceOf : U256 → U256; storageOf : U256 → U256 → U256 transientOf : U256 → U256 → U256; storage : U256 → U256; transient : U256 → U256 logs : List LogEntry; selfdestructs : List (U256 × Bool) def CallWorld.install (world : CallWorld) (st : EvmState) : EvmState -- :571 def CallWorld.ofState (st : EvmState) : CallWorld -- :587
    notes: Fields condensed from :433-456. install never touches env.keccakOf, calldata or code, so keccakOf is invariant across calls. ofState is the 'world unchanged' response world a precompile should return.
- `YulSemantics.EVM.CallResponse / ExternalCalls` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:472)
    sig: structure CallResponse where success : Bool returndata : List UInt8 world : CallWorld -- :461 structure ExternalCalls where Call : CallRequest → EvmState → CallResponse → Prop -- :472 def none : ExternalCalls where Call := fun _ _ _ => False -- :480 def any : ExternalCalls where Call := fun _ _ _ => True -- :484
    notes: ExternalCalls is a single-field structure, so there is no union operator (Y-1). Note that ecosystem.md's Y-1 cites :532/:535 for none/any, but those lines are ExternalCreates.none/any.
- `YulSemantics.EVM.ExternalCreates / ExternalGas` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:549)
    sig: structure ExternalCreates where Create : CreateRequest → EvmState → CreateResponse → Prop -- :525; none :532, any :535 structure ExternalGas where Gas : EvmState → U256 → Prop -- :549 def any : ExternalGas where Gas := fun _ _ => True -- :557 def none : ExternalGas where Gas := fun _ _ => False -- :561 def ofFun (f : EvmState → U256) : ExternalGas where Gas := fun st g => g = f st -- :564
    notes: PLAN's 'noCreates' is ExternalCreates.none. gas() under ExternalGas.any is NOT Deterministic. ofFun is deterministic.
- `YulSemantics.EVM.finishCall / CallResponse.flag` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:612)
    sig: def finishCall (kind : CallKind) (st : EvmState) (response : CallResponse) (inputOffset inputSize outputOffset outputSize : Nat) : EvmState def CallResponse.flag (response : CallResponse) : U256 := if response.success then 1 else 0 -- :622
    notes: staticcall never installs response.world, even on success (finishCall_static_storage, EVM.lean:76). It copies min(outputSize, |returndata|) bytes and sets returndata.
- `YulSemantics.EVM.stepOp` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:699)
    sig: def stepOp (op : Op) (args : List U256) (st : EvmState) : Option (BuiltinResult U256 EvmState)
    notes: keccak256 (:731-733) is `[p, n] => some (.ok [st.env.keccakOf (readBytes st.memory p.toNat n.toNat)] (touchMemory st p.toNat n.toNat))`. return (:840-843) sets halted := some (.ret, readBytes st.memory p s). gas/call/callcode/delegatecall/staticcall/create/create2 return none (:832-833).
- `YulSemantics.EVM.externalCall / builtinWithExternal` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:878)
    sig: def externalCall (external : ExternalCalls) (kind : CallKind) (gas target value : U256) (inputOffset inputSize outputOffset outputSize : U256) (st : EvmState) (result : BuiltinResult U256 EvmState) : Prop -- :852 def builtinWithExternal (calls : ExternalCalls) (creates : ExternalCreates) (gasOracle : ExternalGas) (op : Op) (args : List U256) (st : EvmState) (result : BuiltinResult U256 EvmState) : Prop -- :878
    notes: staticcall (:906-910) takes [gas, target, inputOffset, inputSize, outputOffset, outputSize] with value 0. gas (:926-928) is `∃ g : U256, gasOracle.Gas st g ∧ result = .ok [g] st`. All other ops are `stepOp op args st = some result`.
- `YulSemantics.EVM.evm / evmWithExternal / evmWithCalls / exec` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:953)
    sig: @[reducible] def evm : Dialect -- :942 @[reducible] def evmWithExternal (calls : ExternalCalls) (creates : ExternalCreates) (gasOracle : ExternalGas) : Dialect -- :953 @[reducible] def evmWithCalls (external : ExternalCalls) : Dialect := evmWithExternal external ExternalCreates.none ExternalGas.any -- :964 @[reducible] def exec : ExecDialect := { toDialect := evm, builtinFn := stepOp } -- :969
    notes: In every variant Op := Op, Value := U256 and State := EvmState, all reducible. So VEnv (evmWithExternal …) = VEnv evm definitionally and DecidableEq resolves. P-BR wrongly cites Dialect/EVM.lean:135-164 for this definition. That range is effects_sound_withExternal.
- `YulSemantics.EVM.effects_sound_withExternal` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVM.lean:135)
    sig: theorem effects_sound_withExternal (calls : ExternalCalls) (creates : ExternalCreates) (gasOracle : ExternalGas) : (evmWithExternal calls creates gasOracle).EffectsSound
    notes: The only open-world metatheorem in the tree. exec_lawful : exec.Lawful is at :92 and effects_sound : evm.EffectsSound at :98.
- `YulSemantics.EVM.Layout / RunObject / runObject` (formal/vendor/yul-semantics/YulSemantics/ObjectRun.lean:68)
    sig: structure Layout where code : List UInt8 dataOffset : U256 → U256 dataSize : U256 → U256 immutable : U256 → U256 := fun _ => 0 -- :33 def Layout.initState (L : Layout) : EvmState := { EvmState.init with env := L.env } -- :53 def Layout.Consistent (L : Layout) (o : Object EVM.Op) : Prop -- :58 def runObject (fuel : Nat) (o : Object EVM.Op) (L : Layout) : Result (Interp.SResult exec) -- :64 def RunObject (o : Object EVM.Op) (L : Layout) (V : VEnv evm) (st : EvmState) (out : Outcome) : Prop := Run evm o.codeBlock L.initState V st out -- :68
    notes: These are closed-dialect, the calldata is always [] (L.env sets no calldata), and they run codeBlock (deploy code), not the runtime sub-object. That makes them unusable as-is for qvm_yul_refines or RunContractIR. Also present: datacopy_copies_data :89 and constructorCode_returns :138.
- `YulSemantics.EVM.print / printObject` (formal/vendor/yul-semantics/YulSemantics/PrettyPrint.lean:141)
    sig: def print (b : Block EVM.Op) : String := ppProgram EVM.opName b def printObject (o : Object EVM.Op) : String := ppObject EVM.opName 0 o -- :144
    notes: A semantic pretty-printer. Its output differs from Rust's bytes (R-39).
- `Midfall.Yul.CallKind / CallRequest / CallOutcome` (formal/Midfall/Yul/Externals.lean:752)
    sig: inductive CallKind | call | callcode | delegatecall | staticcall deriving Repr, BEq, DecidableEq, Inhabited -- :743 structure CallRequest where kind : CallKind gas : Word256 target : Word256 value : Word256 input : Bytes -- :752 structure CallOutcome where success : Bool returndata : Bytes -- :772
    notes: These are DISTINCT types from EVM.CallKind and EVM.CallRequest. input is a ByteArray, not a List UInt8, and CallOutcome has no world field. Bridge must convert between them. Word256 = BitVec 256 = U256 (Common/Bytes.lean:21).
- `Midfall.Yul.ExternalCallRelation` (formal/Midfall/Yul/Externals.lean:779)
    sig: structure ExternalCallRelation where address : Word256 validInput : Bytes -> Bool outputLen : Bytes -> Option Nat gas : Bytes -> Nat output : Bytes -> Option Bytes
    notes: A plain decidable record, not a Prop relation.
- `Midfall.Yul.ExternalCallRelation.accepts / respond` (formal/Midfall/Yul/Externals.lean:799)
    sig: def ExternalCallRelation.accepts (r : ExternalCallRelation) (req : CallRequest) : Bool -- :792 def ExternalCallRelation.respond (r : ExternalCallRelation) (req : CallRequest) : Option CallOutcome -- :799
    notes: none means a wrong target OR invalid input, so the two cases are conflated. respond ignores req.kind and req.gas. It never yields success := false. The target comparison is on the full 256-bit word (EVM accountKey uses 160 bits).
- `Midfall.Yul.g1AddRelation / g1AddValidInput / g1AddOutput` (formal/Midfall/Yul/Externals.lean:834)
    sig: def g1AddValidInput (input : Bytes) : Bool -- :812 def g1AddOutputLen (input : Bytes) : Option Nat -- :820 def g1AddOutput (input : Bytes) : Option Bytes -- :824 def g1AddGas (_ : Bytes) : Nat := g1AddGasScheduled -- :831 def g1AddRelation : ExternalCallRelation -- :834
    notes: 0x0b. The input is 0x100 bytes, with no subgroup check. The output is the computed affine sum (affineAdd fpOps, :376).
- `Midfall.Yul.g1MsmRelation / g1MsmPairs? / g1MsmValidInput / g1MsmOutput` (formal/Midfall/Yul/Externals.lean:893)
    sig: def g1MsmPairs? (input : Bytes) : Option (List ((Nat × Nat) × Nat)) -- :846 def g1MsmValidInput (input : Bytes) : Bool -- :865 def g1MsmOutputLen (input : Bytes) : Option Nat -- :872 def g1MsmOutput (input : Bytes) : Option Bytes -- :879 def g1MsmGas (input : Bytes) : Nat -- :890 def g1MsmRelation : ExternalCallRelation -- :893
    notes: 0x0c. Pairs are interleaved as 0xa0-byte (point, scalar) records. The subgroup check is explicit r*P=O. Scalars are unconstrained. The output is computed.
- `Midfall.Yul.PairingProduct / pairingRelation / pairingOutput` (formal/Midfall/Yul/Externals.lean:941)
    sig: abbrev PairingProduct := Bytes -> Bool -- :941 def pairingPairs? (input : Bytes) : Option (List ((Nat × Nat) × ((Nat × Nat) × (Nat × Nat)))) -- :905 def pairingValidInput (input : Bytes) : Bool -- :924 def pairingOutputWord (b : Bool) : Bytes -- :948 def pairingOutput (product : PairingProduct) (input : Bytes) : Option Bytes -- :951 def pairingRelation (product : PairingProduct) : ExternalCallRelation -- :958
    notes: 0x0f. THE arithmetic hole: the Fp12 product check is an oracle over the whole input frame. Eip2537.Holds must tie it to AdmissiblePairing through the codecs. pairingFrame (:544) is caller-ordered (R-11: the swap is at FinalPairing.yul:88).
- `Midfall.Yul.modexpRelation / modexpOutput / modexpInvFrame` (formal/Midfall/Yul/Externals.lean:996)
    sig: def modexpValidInput (input : Bytes) : Bool := modexpWithinLimits input -- :970 def modexpOutputLen (input : Bytes) : Option Nat -- :979 def modexpOutput (input : Bytes) : Option Bytes -- :984 def modexpRelation : ExternalCallRelation -- :996 def modexpInvFrame (x : Nat) : Bytes -- :560 def modPow (base exp m : Nat) : Nat -- :310
    notes: 0x05. Modulus 0 returns zero bytes. The output is modsize bytes. modexpGas (:711) is the max of the EIP-2565 and EIP-7883 prices.
- `Midfall.Yul.honestRelations` (formal/Midfall/Yul/Externals.lean:1006)
    sig: def honestRelations (product : PairingProduct) : List ExternalCallRelation := [g1AddRelation, g1MsmRelation, pairingRelation product, modexpRelation]
    notes: The addresses are pairwise distinct ([0x0b,0x0c,0x0f,0x05], checked in relationKats_ok :1286, a Bool #eval at :1318). This discharges Y-1's agreement obligation by target disjointness. The file has ZERO theorems: all gates are #eval Bool (:1309-1318).
- `Midfall.Lowering.Lowered / Deployment` (formal/Midfall/Lowering/Types.lean:71)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject -- :34 structure Deployment (vkRuntime : Bytes) (evaluator : Option YulObject) (vkCodehash quotientCodehash : H256) : Prop where vkCode : True vkHash : True qObj : True qHash : True
    notes: YulBlock = YulSemantics.Block YulSemantics.EVM.Op (:25). Deployment is an all-True placeholder, so any theorem hypothesis on it is vacuous.
- `Midfall.Halo2.Hash / Midfall.keccak256` (formal/Midfall/Halo2/Exec/Native.lean:50)
    sig: abbrev Hash := Bytes → H256 -- formal/Midfall/Common/Keccak.lean:15 def keccak256 (bs : Bytes) : H256
    notes: H256 = BitVec 256 = U256 and Bytes = ByteArray. The oracle for the Yul side is `fun l : List UInt8 => H (ByteArray.mk l.toArray)`, installed as st0.env.keccakOf.

## verbatim excerpts

### formal/vendor/yul-semantics/YulSemantics/Dialect.lean:108
```lean
structure Dialect where
  /-- The dialect's built-in operation type (a finite enum for the EVM dialect). The AST is
  parameterized over this type (see `YulSemantics.Expr`). -/
  Op : Type
  /-- The value type (for the EVM dialect: `BitVec 256`). -/
  Value : Type
  /-- The machine / world state (memory, storage, …). -/
  State : Type
  /-- Interpret a literal as a value. Total; on ill-formed literals (see `litWF`) its behavior is
  unspecified-but-defined (e.g. the EVM dialect wraps mod `2^256`), and such literals never occur in
  well-formed programs. -/
  litValue : Literal → Value
  /-- Which literals are well-formed for this dialect (e.g. EVM: numbers `< 2^256`, string literals
  `≤ 32` bytes). The semantics and compiler are stated over well-formed programs. -/
  litWF : Literal → Prop
  /-- Interpretation of a built-in call: `Builtin op args st r` holds when invoking `op` on `args`
  in state `st` may produce result `r`. A relation (not a function) so that non-deterministic
  built-ins (`gas()`, external calls) can be modeled. -/
  Builtin : Op → List Value → State → BuiltinResult Value State → Prop
  /-- Effect classification of each built-in. -/
  effects : Op → Effects
```

### formal/vendor/yul-semantics/YulSemantics/BigStep.lean:349
```lean
/-- Single-statement execution. -/
abbrev ExecStmt (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (s : Stmt D.Op) (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  Step D funs V st (.stmt s) (.sres V' st' o)

/-- Statement-sequence execution. -/
abbrev ExecStmts (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (ss : List (Stmt D.Op)) (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  Step D funs V st (.stmts ss) (.sres V' st' o)

/-- `for`-loop iteration (after `init`). -/
abbrev ExecLoop (D : Dialect) [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D)
    (st : D.State) (c : Expr D.Op) (post body : Block D.Op)
    (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  Step D funs V st (.loop c post body) (.sres V' st' o)

/-- Run a whole program (a top-level block) from an initial state with empty environments. -/
def Run (D : Dialect) [DecidableEq D.Value] (prog : Block D.Op) (st0 : D.State)
    (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop :=
  ExecStmt D [] [] st0 (.block prog) V' st' o
```

### formal/vendor/yul-semantics/YulSemantics/Observation.lean:34
```lean
/-- A top-level **observed** run of an EVM program: it runs the program (`Run`) and then applies the
frame-boundary commit/rollback (`committedState`) to obtain the caller/transaction-observable state.

With whole-program determinism (`EVM.run_det`) this relation is functional — see
`RunCommitted.det`. -/
def RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm)
    (stObs : EvmState) (o : Outcome) : Prop :=
  ∃ st', Run EVM.evm prog st0 V' st' o ∧ stObs = committedState st0 st'

/-- `RunCommitted` is functional: `committedState` is a function of the (unique, by `EVM.run_det`)
raw run result. -/
theorem RunCommitted.det {prog st0 V₁ s₁ o₁ V₂ s₂ o₂}
    (h₁ : RunCommitted prog st0 V₁ s₁ o₁) (h₂ : RunCommitted prog st0 V₂ s₂ o₂) :
    V₁ = V₂ ∧ s₁ = s₂ ∧ o₁ = o₂ := by
  obtain ⟨st₁', hrun₁, rfl⟩ := h₁
  obtain ⟨st₂', hrun₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl, rfl⟩ := EVM.run_det hrun₁ hrun₂
  exact ⟨rfl, rfl, rfl⟩
```

### formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:248
```lean
/-- Whether a halt *commits* the frame's accumulated world changes (`stop`/`return`/`selfdestruct`),
as opposed to discarding them (`revert`/`invalid`/`invalidMemoryAccess`). -/
def HaltKind.commits : HaltKind → Bool
  | .stop | .ret | .selfdestruct => true
  | .revert | .invalid | .invalidMemoryAccess | .staticViolation => false

/-- The frame's *observable* state at its boundary, given its initial state `st0` and its final
`Step` state `st'`.

* Not halted, or halted with a committing kind (`stop`/`return`/`selfdestruct`): the frame commits,
  so the observation is `st'` unchanged.
* Halted with a non-committing kind (`revert`/`invalid`/`invalidMemoryAccess`): every accumulated
  effect is rolled back to `st0`, carrying over only the outcome marker (`halted`) and the exposed
  return data (`returndata`) — exactly what real EVM leaves visible to the caller/transaction. -/
def committedState (st0 st' : EvmState) : EvmState :=
  match st'.halted with
  | none => st'
  | some (k, _) =>
      if k.commits then st'
      else { st0 with halted := st'.halted, returndata := st'.returndata }
```

### formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:461
```lean
structure CallResponse where
  /-- Whether the call completed successfully. -/
  success    : Bool
  /-- The complete return-data buffer exposed to the caller. -/
  returndata : List UInt8
  /-- The tentative post-world, committed only by successful non-static calls. -/
  world      : CallWorld

/-- Open-world interpretation of external calls. The relation may depend on the entire pre-call
state and may admit multiple responses. In particular, a response's post-world may include effects
of arbitrary nested calls and re-entrant executions of the caller. -/
structure ExternalCalls where
  /-- Relates a request and pre-call state to any permitted completed response. -/
  Call : CallRequest → EvmState → CallResponse → Prop

namespace ExternalCalls

/-- No external execution is available. This recovers the current local EVM reference dialect,
where call-family built-ins are stuck. -/
def none : ExternalCalls where Call := fun _ _ _ => False

/-- The maximally open environment: every response is possible. Useful for may-semantics; compiler
forward simulation uses a narrower relation coupled to the target EVM execution. -/
def any : ExternalCalls where Call := fun _ _ _ => True
```

### formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:850
```lean
/-- Relational execution of one external call after its arguments have been checked. The external
environment chooses a response; `finishCall` fixes all caller-local consequences. -/
def externalCall (external : ExternalCalls) (kind : CallKind) (gas target value : U256)
    (inputOffset inputSize outputOffset outputSize : U256) (st : EvmState)
    (result : BuiltinResult U256 EvmState) : Prop :=
  ∃ response,
    external.Call
      { kind, gas, target, value,
        input := readBytes st.memory inputOffset.toNat inputSize.toNat }
      st response ∧
    result = .ok [response.flag]
      (finishCall kind st response inputOffset.toNat inputSize.toNat
        outputOffset.toNat outputSize.toNat)
```

### formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:951
```lean
/-- The gas-free EVM reference dialect with open-world call and creation behavior. Unlike `evm`,
this dialect may be nondeterministic and therefore has no canonical executable interpreter. -/
@[reducible] def evmWithExternal (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) : Dialect where
  Op       := Op
  Value    := U256
  State    := EvmState
  litValue := litValue
  litWF    := litWF
  Builtin  := builtinWithExternal calls creates gasOracle
  effects  := effects

/-- Backwards-compatible call-only open-world dialect, with the unconstrained gas oracle. -/
@[reducible] def evmWithCalls (external : ExternalCalls) : Dialect :=
  evmWithExternal external ExternalCreates.none ExternalGas.any
```

### formal/Midfall/Yul/Externals.lean:791
```lean
/-- A request addresses this precompile and carries an input it accepts. -/
def ExternalCallRelation.accepts (r : ExternalCallRelation) (req : CallRequest) : Bool :=
  req.target == r.address && r.validInput req.input

/-- The honest response to an accepted request: success with the computed return
    data, or - for PAIRING_CHECK, whose arithmetic is a parameter - success with
    the length the EIP fixes. A rejected request is a failed call that burns the
    forwarded gas. -/
def ExternalCallRelation.respond (r : ExternalCallRelation) (req : CallRequest) : Option CallOutcome :=
  if req.target != r.address || ! (r.validInput req.input) then none
  else match r.output req.input with
    | some out => some { success := true, returndata := out }
    | none => if let some n := r.outputLen req.input then
                some { success := true, returndata := bytesZero n }
              else none
```


# AREA: L0 Exec verifier surface (Midfall.Halo2.Exec.{Native,Verifier,Types,Features,Error,VerifyingKey,Transcript,Pcs,Query,Linearization,Domain,Arith}, Exec/Kzg/{Msm,Params,Utils,MultiOpen}, Common/{Curve,Bytes,Codec,Keccak,Wo

## constraints
- Statements.lean is SHA-256 frozen (Statements.sha256). The new theorem file must not redeclare verifyNative_iff_msgs, verifyMsgs_iff_spec or contractRef_noAcc in Midfall.Statements. Use another namespace, for example Midfall.Lowering.Equiv.
- Phantom parameters: DualMSM (F G₁ G₂ Gₜ) has phantom G₂ and Gₜ (Msm.lean:164-173, D-P7). ParamsVerifierKZG (G₁ G₂) has phantom G₁ (Params.lean:15-17). KzgAcc has phantom G₂ and Gₜ. verifyNative and verifyNativeWith rebind `{Gₜ : Type}` locally, so callers write `(Gₜ := Gₜ)`. Passing `E : VerifierEnv p G₁ G₂ Gₜ` already pins Gₜ for prepare, decodeRust, prepareMsgs and verifyMsgs. AdmissiblePairing has `p` and `Gₜ` as outParams.
- Actual argument shapes versus PLAN 9.5 pseudo-Lean (D-P9, R-27). The real calls are `prepareMsgs E H F vk inst ms`, `decodeRust E F vk inst π`, `verifyNative (Gₜ := Gₜ) E F params vk inst π`, `verifyMsgs E H F params vk inst ms` and `Lowering.ContractRefAccepts E H params vk inst ms : Bool`. The plan's forms omit E and/or inst, and use g.vk or g.params.
- verifyNative hard-codes committed = [[1]] (multiplicative identity of G₁; PLAN 9.2 writes [[0]]) and inst = [[inst.toList]]: one proof, one committed column holding the identity point, one public column. parseTrace then requires numInstanceColumns = 1 + 1 = 2. That matches Supported.instShape (numInstanceColumns = 2, 1 committed) and D-P11 (flat inst).
- verifyNative_iff_msgs as frozen has NO codec hypothesis. This is my own analysis, not a REVIEW id. prepareMsgs re-serialises G1 messages with E.g1.toCompressed, while decodeRust decodes with ofCompressed?. With a degenerate codec (for example toCompressed := fun _ => Bytes.empty), the re-serialised stream is short: verifyMsgs faults while verifyNative can succeed. Any provable restatement needs at least `E.g1.compressedRoundtrip` (Codec.lean:113), which gives width 48 and re-decodability. It also needs the provable Fr lemma `frOfRepr? b = some x → frToRepr x = b`, the fact that `Transcript.initWithHash keccak256 b = Transcript.initFromBytes b` (expected rfl because hash defaults to keccak256), and the fact that the read log concatenates exactly to the consumed prefix.
- verifyMsgs_iff_spec is unprovable today: Spec.accepts is `sorry` (Spec/Piop.lean:56). It also takes no `E`, while verifyMsgs depends on E.delta, E.field.numBits (truncation), E.g1 (toEip absorbs) and E.fewerPointSetsRuntime. A predicate that ignores E cannot be equivalent for every E. Restate with E (or its components) as arguments of the spec, together with the side conditions below.
- There is no root-of-unity, order or delta hypothesis anywhere (R-3, R-3 extended, R-47). FieldConsts (Arith.lean:64) is four bare data fields. The planned `FieldConsts.IsWellFormed` in `Assumptions/TwoAdicity.lean` does not exist, and `orderOf` has zero hits. vk.domain is an imported record (not produced by EvaluationDomain.new), and VerifyingKey.WellFormed.domainConsistent only gives n = 2^k and quotientPolyDegree = csDegree - 1. So lagrange_spec and quotientLin_spec must assume on vk.domain: orderOf omega = n (or omega^n = 1 plus primitivity), omegaInv * omega = 1, barycentricWeight = (n : Fr)⁻¹, and (n : Fr) ≠ 0. Spec/Lemmas.rotate_omega_eq defers the reduced-index form for this reason.
- R-2: lIRange silently returns 0 entries when x is a domain point, and MultiPrepare.fEval panics (kzg/mod.rs:479) when x3 hits a point-set element. Correctness statements need explicit `x ∉ domain` and `x3 ∉ pointSets` side conditions. Equivalence statements (Lean vs Yul) do not, provided both sides are compared at the faulting outcome: Fault.panic maps to revert.
- R-22 / D-P14: under Features.solidity (truncatedChallenges = true), x3 is `truncate E.field.numBits x3raw` and the x1/x4 batching coefficients are truncatedPowers. theta, beta, gamma, trash, y and x are full `digest mod r` values. Challenge derivation: `Transcript.squeezeChallenge` returns `frOfDigest (bytesToWordBE (wordToBytesBE (t.hash t.state)))`, i.e. `((t.hash t.state).toNat : ZMod p)` after a BE round-trip lemma. The state is replaced by the 32-byte BE digest, NOT the reduced challenge. Absorbs use toInput of the decoded value: toEip (128 bytes) for G1, frToInputBE (32 bytes BE) for Fr. Wire formats are 48-byte compressed G1 and 32-byte LE Fr.
- R-8: Verifier.verifyAlgebraicConstraints collapses every `Fault.error` from pcs.multiPrepare to `Error.opening` and lets `Fault.panic` through. Observational equivalence only distinguishes accept from reject/revert, so per-partial specs should treat all Fault values alike.
- R-11: DualMSM.check computes e(left, params.sG2Prepared) · e(right, params.nG2Prepared) = 1 (it does not use params.sG2). The contract evaluates e(RHS, G2) · e(LHS, -sG2) because of the swap at FinalPairing.yul:88. pcs_spec / finalPairing_spec should relate PAIRING_LHS to `(d.left).eval` and PAIRING_RHS to `(d.right).eval` and invoke Spec/Lemmas.pairing_reorder. R-4: nG2Prepared = g2⁻¹ or g2Gen⁻¹ depending on the constructor, so assume `params.nG2Prepared = P.g₂⁻¹` explicitly.
- The per-partial Inv k cannot name most intermediate values directly: x, xn, splittingFactor, quotient limb commitments, instanceEvals, adviceEvals, lIS, l0/lLast/lBlind, x1..x4, fCom, qEvalsOnX3, fEval, v, pi, piMsm, scaledPi and the pre-addMsm DualMSM are all `let` locals in do-blocks (Verifier.lean:796-949, MultiOpen.lean:201-252, Verifier.lean:267-275). Named carriers are: parseTrace returning VerifierTrace (theta/beta/gamma/trashChallenge/y/challenges), readFixedEvals, Permutation.VerifyingKey.evaluate, Permutation/Logup/Trash Committed.evaluate, partiallyEvaluateIdentities, computeLinearizationCommitment, collectQueries, constructIntermediateSets, MultiPrepare.buildQ/fEval/finalCom/vCalc, and vk.domain.lIRange. The theorem file must either define a snapshot record abstractly, with a hypothesis relating it to `StateT.run` of a pipeline prefix (for example `(parseTrace E.g1 F vk #[#[1]] #[#[inst]]).run t0`), or wait for an Exec refactor that splits verifyAlgebraicConstraints and multiPrepare into named phases.
- multiPrepare never calls DualMSM.scale. The 'before/after' pair is `{left := piMsm, right := finalCom}` and `{acc with right := acc.right.addMsm scaledPi}`, with scaledPi bases `#[pi, P.g₁⁻¹]` and scalars `#[x3, v]`. DualMSM/MSMKZG scaling appears only in batchedCheck (by alpha), msmInnerProduct and MultiPrepare. Spec/Lemmas.dualMsm_scale_check needs `c ≠ 0`, and alphaOf maps 0 to 1 for that reason.
- MSMKZG.Wf (lockstep lengths) is not carried in the type. MSMKZG.eval has a `scalars.toList = [1]` shortcut and a `getD 0 1` fallback. msmSpecific and msmInnerProduct truncate on zip (rule R3). An Inv relating memory to an MSM value should go through `eval`, not through the arrays.
- R-7: grouping in constructIntermediateSets uses kzgCommitBeq (value equality), while the Rust uses pointer equality. The Lean-vs-Yul theorems are relative to the Lean verifier, so this matters only for Rust conformance claims, which should carry an explicit no-aliased-equal-commitments hypothesis.
- Codec soundness is not assumed anywhere. G1Codec.ofEip? is on-curve only, with no subgroup check (Codec.lean:69-80); the plan-9.1 `G1.ofEip? := (E1.ofEip? b).bind toSubgroup?` does not exist. The BLS conformance codec g1AffineCodec (Instances/Bls12_381.lean:147) has no torsion check, and G1Affine has no Group instance. points_subgroup_checked and any decodeAcc-based theorem need codec hypotheses as binders. AdmissiblePairing assumes everything (bilinear by type, generators non-identity, non-degenerate on the generators, decEq) and proves nothing. There is no BLS12-381 instance, and D-P17 forbids proof imports of Instances/.
- R-25: decodeAcc_injective is FALSE as written. Identity-flagged points discard their coordinate words, so accWords must project them to (0,0,1). R-39: render_eq_print is false as a text equation; restate it structurally (D-P13). D-P20: qvm_compile_correct is statable only per identity (no QVM.Program/Frame/Output, and the fold is unmodelled). qvm_validated_noOOB's `.oob` cannot arise, because memory is a PRNG over u32 and the only out-of-range faults are past the end of the program or the constant table. D-P18 (open): Supported.layout claims more than the predicate delivers.
- Lowering/Types.lean Supported takes Nat/Prop/Bool parameters (numAdvice numInstances numChallenges numQuotientLimbs csDegree qvmValidated trace gasCheckpoints) and has only advice/instShape/singlePhase/hLimbs/qvm/production. It lacks noRotInst, acc, vkPoints and layout. Deployment's four fields are all `True` placeholders. Lowered has only headGuard/main/vkRuntime/evaluator.
- No `sorry` in Midfall/Halo2/Exec, Common or Assumptions. The tree-wide sorries are Statements.lean:46, 59, 75 and Spec/Piop.lean:56 (Spec.accepts). No `partial def` anywhere under Midfall/ (rule R10). Recursion is structural or uses termination_by (Transcript.readN.go, powers.go, extLoop fuel). keccak256 is kernel-irreducible, so known-answer tests are #eval Bools, and native_decide is confined to Instances/.
- Msg has no DecidableEq or BEq instance (Types.lean:14). Hash is `Midfall.Halo2.Hash`; Fr, H256, Word256, Bytes and keccak256 are in namespace `Midfall`. Transcript has defaulted fields (hash := keccak256, log := #[]), so the anonymous-constructor form has 5 fields.

## missing
- FieldConsts.IsWellFormed / Assumptions/TwoAdicity.lean (R-47; plans/P-4a-roots.md): primitive 2^s-th root, zeta of order 3, delta order hypothesis. Rust source: ff PrimeField::ROOT_OF_UNITY/S, WithSmallOrderMulGroup<3>::ZETA, F::DELTA constants in curves/src/bls12_381/scalar.rs (used at proofs/src/poly/domain.rs:55-99 and plonk/permutation.rs).
- BLS12_381Data hypothesis structure promised by the Assumptions/Pairing.lean header, plus a BLS12-381 AdmissiblePairing instance. Rust source: midnight_curves bls12_381 (G1/G2/GT, pairing, final_exponentiation) used by poly/kzg/msm.rs:284-308.
- Subgroup-checked G1.ofEip? / E1.ofEip? / toSubgroup? (plan 9.1), and the torsion-free half of G1Codec.ofCompressed? for the real curve. Rust source: curves/src/bls12_381/g1.rs:369-371 (from_bytes torsion check) and the contract-side G1 checks.
- Named per-phase L0 snapshots that Inv k (vkLoading/transcript/lagrange/quotient/pcs/pairing) can reference: x, xn, splittingFactor, quotient limb coms, instance/advice evals, Lagrange l0/lLast/lBlind, x1..x4, fCom, qEvalsOnX3, fEval, v, pi, and the pre/post-scaledPi DualMSM. Today these are do-block locals. Rust source: proofs/src/plonk/verifier.rs:238-652, poly/kzg/mod.rs:321-574, and the memory slots in proofs/solidity-verifier/src/layout/memory.rs.
- Spec.accepts body (Spec/Piop.lean:56, sorry); it also needs an E-dependent signature. Rust source: none (mathematical spec, plan Section 6).
- ContractRefAccepts accumulator arm: Lowering/Types.lean:83 has the no-acc arm only, although decodeAcc/alphaOf/batchedCheck exist in Exec/Accumulator.lean:955/1014/1036. Rust/contract source: FinalPairing.yul:14-60, AccumulatorHelpers.yul, circuits/src/verifier/accumulator.rs.
- accWords (for decodeAcc_injective, R-25 projected form) and calldataOf / decodeCalldata / encodeCalldata / repackProof / encodeContractProof: zero hits in Midfall/. Rust source: proofs/solidity-verifier generator calldata and repack code (lowering/artifacts.rs and the calldata layout in layout/*.rs). encodeAccInstances exists in Exec/Accumulator.lean.
- VerifyingKey.allCommitments and isValidG1 (Supported.vkPoints): zero hits. Rust source: generator VK export (proofs/solidity-verifier vk rendering) over plonk/mod.rs:61-70 fields.
- A g.vk.digest accessor on the Exec VerifyingKey: alphaOf takes `vkDigest : Word256` as a bare argument. vkDigest appears in Generator/Vk.lean and Generator/Models.lean, not in Exec. Rust source: proofs/solidity-verifier layout/mod.rs:332-337.
- honestCalls, Eip2537.Holds, Modexp.Holds, irCheck and LoweringPlan: no Lean definitions (Eip2537 appears only as text in Generator/Models.lean). Rust source: revm precompiles and the generator's LoweringPlan in proofs/solidity-verifier/src/lowering.

## declarations
- `Midfall.Halo2.VerifierEnv` (Midfall/Halo2/Exec/Native.lean:38)
    sig: structure VerifierEnv (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type) [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where g1 : G1Codec G₁ field : FieldConsts (Fr p) delta : Fr p fewerPointSetsRuntime : Bool
    notes: D-P9 bundle. It holds data only, with NO hypotheses: nothing says the codec is canonical, nothing says omega/zeta/delta have the right order. The field is named `field`; the stale doc block at Native.lean:140 calls it `fc`. Gₜ appears only through the instance binders, but passing E still pins Gₜ for prepare/decodeRust/prepareMsgs/verifyMsgs.
- `Midfall.Halo2.Hash` (Midfall/Halo2/Exec/Native.lean:50)
    sig: abbrev Hash := Bytes → H256
    notes: Lives in namespace Midfall.Halo2, not Midfall. It has the same type as the Transcript.hash field.
- `Midfall.Halo2.msgWire` (Midfall/Halo2/Exec/Native.lean:150)
    sig: def msgWire {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) : Msg (Fr p) G₁ → Bytes
    notes: | Msg.g1 P => E.g1.toCompressed P | Msg.fr s => frToRepr (p := p) s. prepareMsgs uses it to re-serialise messages into wire bytes, so it is the hinge of verifyNative_iff_msgs.
- `Midfall.Halo2.prepareWith` (Midfall/Halo2/Exec/Native.lean:164)
    sig: def prepareWith (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁) (committed : List (List G₁)) (inst : List (List (List (Fr p)))) : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: Uses the file-level variables. Body: Verifier.prepare (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.delta F (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime) vk (committed as Array) (inst as Array).
- `Midfall.Halo2.verifyNativeWith` (Midfall/Halo2/Exec/Native.lean:177)
    sig: def verifyNativeWith {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) : Except Fault Unit
    notes: Same body as verifyNative, but calls prepareWith.
- `Midfall.Halo2.prepare` (Midfall/Halo2/Exec/Native.lean:199)
    sig: def prepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁) (committed : List (List G₁)) (inst : List (List (List (Fr p)))) : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: The plan-9.2 entry point. Definitionally prepareWith (Gₜ := Gₜ) E F vk committed inst. Do not confuse it with Midfall.Halo2.Verifier.prepare (Verifier.lean:957), the faithful Rust port that takes g1/delta/feat/pcs explicitly.
- `Midfall.Halo2.verifyNative` (Midfall/Halo2/Exec/Native.lean:207)
    sig: def verifyNative {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) : Except Fault Unit
    notes: Rebinds Gₜ locally, shadowing the file variable. Call it as verifyNative (Gₜ := Gₜ) E F params vk inst π. It hard-codes the Solidity shape: committed = [[1]] (the multiplicative identity of G₁; PLAN 9.2 writes [[0]]) and inst = [[inst.toList]] (one proof, one non-committed column). Order: run prepare on Transcript.initFromBytes, then t.assertEmpty, then DualMSM.check, which throws Fault.error Error.opening when false.
- `Midfall.Halo2.decodeRust` (Midfall/Halo2/Exec/Native.lean:228)
    sig: def decodeRust (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) : Option (List (Msg (Fr p) G₁))
    notes: Derived from the transcript log rather than a second schedule. It runs prepare on π, returns none on any Fault or on trailing bytes, then maps each log record (width, raw): width 48 decodes with E.g1.ofCompressed?, width 32 with frOfRepr?. The plan's 3-argument form `decodeRust .solidity g.vk π` is wrong: E and inst are required (R-27, D-P9).
- `Midfall.Halo2.prepareMsgs` (Midfall/Halo2/Exec/Native.lean:255)
    sig: def prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: Re-serialises ms with msgWire, runs the same prepare from Transcript.initWithHash H bytes, then assertEmpty. It is hash-polymorphic through the Transcript.hash field. The plan's `prepareMsgs H .solidity g.vk inst ms` lacks E.
- `Midfall.Halo2.verifyMsgs` (Midfall/Halo2/Exec/Native.lean:273)
    sig: def verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Except Fault Unit
    notes: prepareMsgs followed by DualMSM.check, which throws Fault.error Error.opening when false. H has no default value here; the plan wrote `(H : Hash := keccak256)`.
- `Midfall.Halo2.Msg` (Midfall/Halo2/Exec/Types.lean:14)
    sig: inductive Msg (Fr G₁ : Type) where | g1 (P : G₁) | fr (s : Fr)
    notes: No deriving clauses, so there is no DecidableEq or BEq. A theorem that compares message lists needs an explicit instance. Fr here is a type parameter that shadows Midfall.Fr.
- `Midfall.Halo2.Fault` (Midfall/Halo2/Exec/Error.lean:56)
    sig: inductive Fault where | error (e : Error) | panic (site : String)
    notes: Every Fault maps to revert at the contract boundary (PLAN 9.5). R-8 suggests adding a poly constructor (not done). Panic sites are strings citing a Rust file:line.
- `Midfall.Halo2.Error` (Midfall/Halo2/Exec/Error.lean:41)
    sig: inductive Error where | synthesis (msg : String) | invalidInstances | constraintSystemFailure | boundsFailure | opening | transcript (k : IoErrorKind) | notEnoughRowsAvailable (current_k : Nat) | instanceTooLarge | notEnoughColumnsForConstants | columnNotInPermutation (col : ColumnAny) | tableError (e : TableError) | srsError (srs_k circuit_k : Nat)
    notes: IoErrorKind (line 21) has three cases: unexpectedEof | notFound | other. A short read gives unexpectedEof, a bad repr gives other, trailing bytes give notFound.
- `Midfall.Halo2.Features` (Midfall/Halo2/Exec/Features.lean:10)
    sig: structure Features where committedInstances : Bool truncatedChallenges : Bool outerFewerPointSets : Bool outerSingleHCommitment : Bool
    notes: Field doc comments are elided here; the four Bool fields appear in this order.
- `Midfall.Halo2.Features.solidity` (Midfall/Halo2/Exec/Features.lean:30)
    sig: def Features.solidity : Features where committedInstances := true truncatedChallenges := true outerFewerPointSets := false outerSingleHCommitment := false
    notes: Comes with a TODO(BASELINE) saying it is not yet confirmed against the deploy command line. Because outerFewerPointSets = false, E.fewerPointSetsRuntime is irrelevant under solidity. truncatedChallenges = true makes R-22/D-P14 apply.
- `Midfall.Halo2.DualMSM` (Midfall/Halo2/Exec/Kzg/Msm.lean:171)
    sig: structure DualMSM (F G₁ G₂ Gₜ : Type) where left : MSMKZG F G₁ right : MSMKZG F G₁
    notes: G₂ and Gₜ are PHANTOM parameters (D-P7): the Rust DualMSM<E> has only G1 data. Every user has to name Gₜ, through (Gₜ := Gₜ) or via E's type. Helper ops: DualMSM.init (178), DualMSM.new (182), DualMSM.scale (187), DualMSM.addMsm (192) and DualMSM.split (199), each with binders `{G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] {G₂ Gₜ : Type}`.
- `Midfall.Halo2.DualMSM.check` (Midfall/Halo2/Exec/Kzg/Msm.lean:222)
    sig: def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) : Bool
    notes: Checks e(left, sG2Prepared) + e(right, nG2Prepared) = 0 additively, using decideBool on P.decEqGₜ. It reads params.sG2Prepared and params.nG2Prepared, NOT params.sG2. The contract orientation is swapped at the FinalPairing.yul:88 call site (R-11). The exponent-level lemmas pairing_reorder and dualMsm_scale_check are in Spec/Lemmas.lean:31 and :100.
- `Midfall.Halo2.DualMSM.verify` (Midfall/Halo2/Exec/Kzg/Msm.lean:238)
    sig: def verify {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) : Except Fault Unit
    notes: Returns .ok () when check succeeds, otherwise .error (Fault.error Error.opening). Implements the Guard trait (Pcs.kzgGuard, Pcs.lean:86).
- `Midfall.Halo2.MSMKZG` (Midfall/Halo2/Exec/Kzg/Msm.lean:60)
    sig: structure MSMKZG (F G : Type) where scalars : Array F bases : Array G labels : Array CommitmentLabel
    notes: The invariant MSMKZG.Wf (line 68) is `m.scalars.size = m.bases.size ∧ m.bases.size = m.labels.size`; the type does not carry it. MSMKZG.eval (113) is `if m.scalars.toList = [1] then m.bases.getD 0 1 else msmSpecific m.scalars m.bases`. msmSpecific (52) zips with truncation and drops zero coefficients. gsmul (35) is `Additive.toMul (s • Additive.ofMul Q)`. Other ops: addMsm 74, init 80, fromMany 85, fromBase 89, appendTerm 93, scale 103 (multiplies scalars by the factor on the right), MSMKZG.check 120, collapse 132. msmInnerProduct is at 147.
- `Midfall.Halo2.ParamsVerifierKZG` (Midfall/Halo2/Exec/Kzg/Params.lean:18)
    sig: structure ParamsVerifierKZG (G₁ G₂ : Type) where sG2 : G₂ nG2Prepared : G₂ sG2Prepared : G₂
    notes: G₁ is a PHANTOM parameter. Two constructors exist: ParamsVerifierKZG.ofParams (30) with nG2Prepared := g2⁻¹, and ParamsVerifierKZG.read (45) with nG2Prepared := g2Gen⁻¹ (the R-4 divergence). No hypothesis links sG2 to sG2Prepared or nG2Prepared to a generator. Correctness lemmas must assume nG2Prepared = P.g₂⁻¹ and sG2Prepared = s • g₂.
- `Midfall.Halo2.VerifyingKey` (Midfall/Halo2/Exec/VerifyingKey.lean:41)
    sig: structure VerifyingKey (Fr G₁ : Type) where domain : EvaluationDomain Fr fixedCommitments : Array G₁ permutation : Permutation.VerifyingKey G₁ cs : ConstraintSystem Fr csDegree : Nat transcriptRepr : Fr
    notes: Field doc comments are elided. transcriptRepr is imported, not computed (R-1). domain is an imported raw EvaluationDomain record; nothing ties omega to FieldConsts. VerifyingKey.n (60) = vk.domain.n. VerifyingKey.fromParts is at 65. VerifyingKey.hashInto (79) is `def VerifyingKey.hashInto (vk : VerifyingKey (Fr p) G₁) : TranscriptM Unit := tmCommon hashableFr vk.transcriptRepr`.
- `Midfall.Halo2.VerifyingKey.WellFormed` (Midfall/Halo2/Exec/VerifyingKey.lean:109)
    sig: structure VerifyingKey.WellFormed (vk : VerifyingKey (Fr p) G₁) (F : Features) : Prop where csDegreeMatches : vk.cs.degree = .ok vk.csDegree chunkLenPositive : 3 ≤ vk.csDegree domainConsistent : vk.domain.n = 2 ^ vk.domain.k ∧ vk.domain.quotientPolyDegree = vk.csDegree - 1 permutationCommitmentsMatch : vk.permutation.commitments.size = divCeil vk.cs.permutation.columns.size (vk.csDegree - 2) fixedCommitmentsMatch : vk.fixedCommitments.size = vk.cs.numFixedColumns singlePhase : vk.cs.numChallenges = 0 committedInstancesOn : F.committedInstances = true
    notes: Uses the file variables {p} [Fact] {G₁} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (lines 71-72). It says NOTHING about omega's order, omegaInv, barycentricWeight, gCoset or delta (R-47). ConstraintSystem.degree and blindingFactors return Except Fault Nat (Circuit.lean:1548, 1593).
- `Midfall.Halo2.Transcript` (Midfall/Halo2/Exec/Transcript.lean:86)
    sig: structure Transcript where state : Bytes buffer : Bytes pos : Nat hash : Bytes → H256 := keccak256 log : Array (Nat × Bytes) := #[]
    notes: Doc comments are elided; the fields appear in this order. state is the raw concatenation of absorbed toInput bytes, re-seeded after each squeeze by the 32-byte BE digest. hash and log have defaults. initFromBytes (110) = { state := Bytes.empty, buffer := bytes, pos := 0 }. initWithHash (115) is `def Transcript.initWithHash (H : Bytes -> H256) (bytes : Bytes) : Transcript` = { state := Bytes.empty, buffer := bytes, pos := 0, hash := H }, so initWithHash keccak256 b should be rfl-equal to initFromBytes b.
- `Midfall.Halo2.TranscriptM` (Midfall/Halo2/Exec/Transcript.lean:106)
    sig: abbrev TranscriptM := StateT Transcript (Except Fault)
    notes: Monad helpers: tmSqueezeChallenge (178) `def tmSqueezeChallenge {p : ℕ} [Fact (Nat.Prime p)] : TranscriptM (Fr p)`; tmRead (185) `def tmRead {T : Type} (h : Hashable T) : TranscriptM T`; tmCommon (192) `def tmCommon {T : Type} (h : Hashable T) (input : T) : TranscriptM Unit`; tmReadN (197) `def tmReadN {T : Type} (h : Hashable T) (n : Nat) : TranscriptM (Array T)`.
- `Midfall.Halo2.Transcript.common / squeeze / squeezeChallenge / read / assertEmpty / readN` (Midfall/Halo2/Exec/Transcript.lean:120)
    sig: def Transcript.common {T : Type} (h : Hashable T) (t : Transcript) (input : T) : Transcript def Transcript.squeeze (t : Transcript) : Bytes × Transcript def Transcript.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)] (t : Transcript) : Fr p × Transcript def Transcript.read {T : Type} (h : Hashable T) (t : Transcript) : Except Fault (T × Transcript) def Transcript.assertEmpty (t : Transcript) : Except Fault Unit def Transcript.readN {T : Type} (h : Hashable T) (t : Transcript) (n : Nat) : Except Fault (Array T × Transcript)
    notes: Lines: common 120, squeeze 127, squeezeChallenge 136, read 145, assertEmpty 159, readN 166 (go, termination_by). Absorb is append. The challenge is frOfDigest (bytesToWordBE (wordToBytesBE (t.hash t.state))), i.e. digest.toNat mod p after a BE round trip, and the state is REPLACED by the raw digest bytes, not by the reduced challenge. read decodes, advances pos by width, logs (width, repr), then absorbs toInput of the DECODED value.
- `Midfall.Halo2.Hashable / hashableFr / hashableG1 / hashableU32` (Midfall/Halo2/Exec/Transcript.lean:38)
    sig: structure Hashable (T : Type) where toInput : T → Bytes toBytes : T → Bytes width : Nat readRepr? : Bytes → Option T def hashableFr {p : ℕ} [Fact (Nat.Prime p)] : Hashable (Fr p) def hashableG1 {G₁ : Type} (c : G1Codec G₁) : Hashable G₁ def hashableU32 : Hashable Nat
    notes: Lines: hashableFr 55, hashableG1 65, hashableU32 75. hashableFr has toInput frToInputBE (32 bytes BE), toBytes frToRepr (32 bytes LE), width 32, readRepr? frOfRepr?. hashableG1 has toInput c.toEip (128 bytes), toBytes c.toCompressed, width g1CompressedWidth = 48, readRepr? c.ofCompressed?. hashableU32 is not on the verifier path.
- `Midfall.G1Codec` (Midfall/Common/Codec.lean:81)
    sig: structure G1Codec (G₁ : Type) where ofCompressed? : Bytes → Option G₁ toCompressed : G₁ → Bytes toEip : G₁ → Bytes ofEip? : Bytes → Option G₁
    notes: A structure, not a class (D-P6). Properties, as Props, not fields: G1Codec.eipRoundtrip (106) `∀ b : Bytes, ∀ P : G₁, c.ofEip? b = some P → c.toEip P = b` and G1Codec.compressedRoundtrip (113) `∀ b : Bytes, ∀ P : G₁, c.ofCompressed? b = some P → c.toCompressed P = b`. ofEip? is on-curve only, with NO subgroup check (Codec.lean:69-80). The plan-9.1 subgroup-checked G1.ofEip? and toSubgroup? do not exist. Widths are g1CompressedWidth := 48 (89) and g1EipWidth := 128 (90).
- `Midfall.frOfDigest / frToRepr / frOfRepr? / frToInputBE` (Midfall/Common/Codec.lean:27)
    sig: def frOfDigest {p : ℕ} [Fact (Nat.Prime p)] (d : H256) : Fr p := Nat.cast d.toNat def frToRepr {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) : Bytes := natToBytesLE x.val 32 def frOfRepr? {p : ℕ} [Fact (Nat.Prime p)] (b : Bytes) : Option (Fr p) := if b.size == 32 && bytesToNatLE b < p then some (Nat.cast (bytesToNatLE b)) else none def frToInputBE {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) : Bytes := natToBytesBE x.val 32
    notes: Lines 27, 32, 38, 44. A challenge is `digest mod r` via Nat.cast. frOfRepr? enforces canonicity (rule R7).
- `Midfall.Halo2.FieldConsts` (Midfall/Halo2/Exec/Arith.lean:64)
    sig: structure FieldConsts (F : Type) where numBits : Nat s : Nat rootOfUnity : F zeta : F
    notes: Doc comments are elided. There is NO hypothesis that rootOfUnity is a primitive 2^s-th root, that zeta has order 3, or anything about delta, which is not a field (R-3, R-3 extended, R-47). `orderOf` has zero hits in Midfall/. Related: truncate (283) `def truncate {p : ℕ} [Fact (Nat.Prime p)] (numBits : Nat) (scalar : Fr p) : Fr p`, the low divCeil(divCeil numBits 8) 2 bytes of the LE repr; powers (295) `def powers (base : F) (n : Nat) : List F`; truncatedPowers (305) `def truncatedPowers {p : ℕ} [Fact (Nat.Prime p)] (numBits : Nat) (base : Fr p) (n : Nat) : List (Fr p)`.
- `Midfall.Fr / H256 / Word256 / Bytes / Midfall.Word / keccak256` (Midfall/Common/Curve.lean:30)
    sig: abbrev Fr (p : ℕ) := ZMod p abbrev Word256 := BitVec 256 abbrev H256 := BitVec 256 abbrev Bytes := ByteArray abbrev Midfall.Word := BitVec 256 def keccak256 (bs : Bytes) : H256 := bytesToWordBE (VCVio.Algorithms.Keccak.keccak256 bs)
    notes: Fr is at Curve.lean:30. Word256, H256 and Bytes are at Common/Bytes.lean:21, 24, 27; Bytes.empty (30) is `ByteArray.mk #[]`. Midfall.Word is a duplicate 256-bit abbrev at Common/Word.lean:3. keccak256 is at Common/Keccak.lean:15. It is kernel-irreducible (decide hits the recursion limit), so known-answer tests are #eval Bools. bytesToWordBE is at Bytes.lean:33 and wordToBytesBE at 64.
- `Midfall.AdmissiblePairing` (Midfall/Common/Curve.lean:35)
    sig: class AdmissiblePairing {p : outParam ℕ} [Fact (Nat.Prime p)] (G₁ G₂ : Type*) (Gₜ : outParam Type*) [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] where e : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ) g₁ : G₁ g₂ : G₂ hG₁ : g₁ ≠ 1 hG₂ : g₂ ≠ 1 hNonDeg : e (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0 decEqG₁ : DecidableEq G₁ decEqGₜ : DecidableEq Gₜ
    notes: Doc comments are elided. Everything here is ASSUMED, nothing proved: bilinearity holds by type, non-degeneracy only on the generators, decEq is for computability. p and Gₜ are outParams (D-P7). No BLS12-381 instance exists. The only instance is the exponent model expAdmissible (Instances/ExponentModel.lean:247), and D-P17 forbids importing Instances/ for proofs. Assumptions/Pairing.lean defines only r (35), fr_eq_compPoly (43, rfl), pBase (52) and pBaseKats_ok (68). Its header promises a `BLS12_381Data` hypothesis structure that does NOT exist.
- `PrimeOrderWith (ArkLib)` (.lake/packages/ArkLib/ArkLib/Data/GroupTheory/PrimeOrder.lean:40)
    sig: class PrimeOrderWith (G : Type*) [Group G] (p : outParam ℕ) [Fact (Nat.Prime p)] where hCard : Nat.card G = p
    notes: From ArkLib, not in the Midfall tree. It induces a PrimeOrder G instance.
- `Midfall.Halo2.EvaluationDomain / rotateOmega / lIRange` (Midfall/Halo2/Exec/Domain.lean:55)
    sig: structure EvaluationDomain (F : Type) where n : Nat k : Nat extendedK : Nat omega : F omegaInv : F extendedOmega : F extendedOmegaInv : F gCoset : F gCosetInv : F quotientPolyDegree : Nat ifftDivisor : F extendedIfftDivisor : F tEvaluations : Array F barycentricWeight : F def EvaluationDomain.rotateOmega (d : EvaluationDomain F) (value : F) (rotation : Rotation) : F def EvaluationDomain.lIRange (d : EvaluationDomain F) (x xn : F) (rotations : List Int) : Array F
    notes: File variables: {F : Type} [Field F] [DecidableEq F]. rotateOmega is at 232 and lIRange at 251. lIRange returns zeros when x is a domain point (R-2), so lagrange_spec needs x ∉ domain. EvaluationDomain.new (125) `(fc : FieldConsts F) (j k : Nat) : Except Fault (EvaluationDomain F)` computes barycentricWeight = (n)⁻¹ by batch inversion, but the VK's domain is imported, so new's output cannot be assumed.
- `Midfall.Halo2.VerifierTrace` (Midfall/Halo2/Exec/Verifier.lean:53)
    sig: structure VerifierTrace (Fr G₁ : Type) where adviceCommitments : Array (Array G₁) lookups : Array (Array (Logup.Committed G₁)) trashcans : Array (Array (Trash.Committed G₁)) permutations : Array (Permutation.Committed G₁) challenges : Array Fr beta : Fr gamma : Fr theta : Fr trashChallenge : Fr y : Fr
    notes: The ONLY named carrier of theta, beta, gamma, trashChallenge, y and the user challenges (empty under singlePhase). The squeeze order is theta, beta, gamma, trashChallenge, y, even though the fields list beta and gamma first.
- `Midfall.Halo2.parseTrace` (Midfall/Halo2/Exec/Verifier.lean:94)
    sig: def parseTrace (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁) (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p)))) : TranscriptM (VerifierTrace (Fr p) G₁)
    notes: Uses the file variables. Schedule: three InvalidInstances checks; hashInto; absorb committed points (toEip); for each instance column absorb Nat.cast len then the values; per phase read advice and squeeze user challenges; theta; lookup multiplicities; beta; gamma; permutation products; lookup commitments; trashChallenge; trashcan commitments; y. The transcriptParser_spec invariant should name `(parseTrace ...).run t`.
- `Midfall.Halo2.partiallyEvaluateIdentities` (Midfall/Halo2/Exec/Verifier.lean:253)
    sig: def partiallyEvaluateIdentities {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (fixedEvals : Array (Fr p)) (instanceEvals : Array (Array (Fr p))) (adviceEvals : Array (Array (Fr p))) (permutationEvals : Array (Array (Permutation.SetEvaluated (Fr p)))) (lookupEvals : Array (Array (Logup.Evals (Fr p)))) (trashcanEvals : Array (Array (Trash.Eval (Fr p)))) (permutationsCommon : Permutation.CommonEvaluated (Fr p)) (x xn beta gamma theta trashChallenge : Fr p) (challenges : Array (Fr p)) : Except Fault (Array (Option Nat × Fr p))
    notes: Pure. Its output feeds the quotientLin_spec invariant. The Lagrange values are LOCALS here: rotations -(bf+1)..0 through vk.domain.lIRange x xn; lLast = lEvals[0]!, lBlind = sum of lEvals[1..bf], l0 = lEvals[bf+1]!. Entry tags: (some selectorCol) for gate terms, none for perm/logUp/trash.
- `Midfall.Halo2.computeLinearizationCommitment` (Midfall/Halo2/Exec/Linearization.lean:68)
    sig: def computeLinearizationCommitment {F G₁ : Type} [Field F] [BEq F] (expressions : Array (Option Nat × F)) (vk : VerifyingKey F G₁) (x : F) (y : F) (xn : F) (splittingFactor : F) (quotientLimbCommitments : Array G₁) : Except Fault (VerifierQuery F G₁)
    notes: Result: point x, label custom "linearization_poly", commitment .linear (limb commitments ++ fixed selector commitments, in BTreeMap key order). The limb scalars are (1-xn)·sf^i. The eval is the linearization_expected_eval: minus the y-weighted sum of the none bucket, with y powers assigned in REVERSE expression order. groupedAdd is at 42 and optionNatLt at 34.
- `Midfall.Halo2.Verifier.readFixedEvals` (Midfall/Halo2/Exec/Verifier.lean:678)
    sig: def readFixedEvals {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p)) : TranscriptM (Array (Fr p))
    notes: Ports the R-14 insert-shift as written.
- `Midfall.Halo2.Verifier.collectQueries` (Midfall/Halo2/Exec/Verifier.lean:715)
    sig: def collectQueries {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p) (committedInstances adviceCommitments : Array (Array G₁)) (instanceEvals adviceEvals : Array (Array (Fr p))) (permutationsEvaluated : Array (Permutation.Evaluated (Fr p) G₁)) (lookupsEvaluated : Array (Array (Logup.Evaluated (Fr p) G₁))) (trashcansEvaluated : Array (Array (Trash.Evaluated (Fr p) G₁))) (fixedEvals : Array (Fr p)) (permutationsCommon : Permutation.CommonEvaluated (Fr p)) (linCom : VerifierQuery (Fr p) G₁) : Except Fault (Array (VerifierQuery (Fr p) G₁))
    notes: Pure. The query order is load-bearing for x1..x4.
- `Midfall.Halo2.Verifier.verifyAlgebraicConstraints` (Midfall/Halo2/Exec/Verifier.lean:796)
    sig: def verifyAlgebraicConstraints {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁) (committedInstances : Array (Array G₁)) (instances : Array (Array (Array (Fr p)))) : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: These are do-block LOCALS, not named defs: quotientLimbComs (837), x (839), splittingFactor = powVartime x (n-1) (842), xn (843), lIS (872), instanceEvals (900-902), adviceEvals (904-906), fixedEvals (908), permutationsCommon (910), the per-proof evaluated vectors (912-920), expressions (922), linCom (932), queries (935). The multiPrepare result is collapsed: Fault.error becomes Error.opening and panics pass through (R-8).
- `Midfall.Halo2.Verifier.prepare` (Midfall/Halo2/Exec/Verifier.lean:957)
    sig: def prepare {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (g1 : G1Codec G₁) (delta : Fr p) (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) (committedInstances : Array (Array G₁)) (instances : Array (Array (Array (Fr p)))) : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: Equals parseTrace followed by verifyAlgebraicConstraints. This is the natural cut point between the transcript and the algebra.
- `Midfall.Halo2.Pcs / Pcs.kzg / Pcs.kzgGuard / Guard` (Midfall/Halo2/Exec/Pcs.lean:57)
    sig: structure Pcs (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type) [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] where multiPrepare : Array (VerifierQuery (Fr p) G₁) → TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: Pcs.kzg (72) takes `(g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features) (fewerPointSetsRuntime : Bool) : Pcs p G₁ G₂ Gₜ`. Pcs.kzgGuard is at 86. Guard (36) is `structure Guard (G P : Type) where verify : G → P → Except Fault Unit`. Guard.batchVerify is at 45.
- `Midfall.Halo2.multiPrepare` (Midfall/Halo2/Exec/Kzg/MultiOpen.lean:201)
    sig: def multiPrepare (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features) (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁)) : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)
    notes: Uses the file variables, including [P : AdmissiblePairing]. These are LOCALS: x1 (215), x2 (216), commitmentMap/pointSets (218), qComs/qEvalSets (222), fCom (225), x3raw (227), x3 = truncate when the truncated feature is on (228), qEvalsOnX3 (230), fEval (232), x4 (234), finalCom (236), v (238), pi (240), piMsm (241), scaledPi (244, bases [pi, P.g₁⁻¹], scalars [x3, v]), acc before (251) = {left := piMsm, right := finalCom}, and the result = right.addMsm scaledPi (252). Named sub-steps: MultiPrepare.addDummies 62, MultiPrepare.buildQ 95, MultiPrepare.fEval 150 `(pointSets : Array (Array (Fr p))) (qEvalSets : Array (Array (Fr p))) (qEvalsOnX3 : List (Fr p)) (x2 x3 : Fr p) : Except Fault (Fr p)`, MultiPrepare.finalCom 172 `(feat : Features) (fc : FieldConsts (Fr p)) (qComs : Array (MSMKZG (Fr p) G₁)) (fCom : G₁) (x4 : Fr p) : Except Fault (MSMKZG (Fr p) G₁)`, MultiPrepare.vCalc 187 `(feat : Features) (fc : FieldConsts (Fr p)) (qEvalsOnX3 : List (Fr p)) (fEval : Fr p) (x4 : Fr p) : Except Fault (Fr p)`, kzgCommitBeq 42 (value equality, R-7), and constructIntermediateSets (Kzg/Utils.lean:123) `{F C : Type} [Field F] [BEq F] (eqC : CommitmentReference F C → CommitmentReference F C → Bool) (queries : Array (VerifierQuery F C)) : Except Fault (IntermediateSets F C)`. There is NO DualMSM scaling inside multiPrepare.
- `Midfall.Halo2.VerifierQuery / CommitmentReference / CommitmentLabel` (Midfall/Halo2/Exec/Query.lean:94)
    sig: structure VerifierQuery (F C : Type) where point : F commitmentLabel : CommitmentLabel commitment : CommitmentReference F C eval : F
    notes: CommitmentReference (53) has cases `onePiece (com : C) | linear (points : Array C) (scalars : Array F) (labels : Array CommitmentLabel)`. CommitmentLabel (21) has cases advice | instance_ | fixed | permutation (Nat each) | custom (s : String) | noLabel, deriving BEq. VerifierQuery.new is at 106 and newLinear at 113 (Except, panics).
- `Per-argument evaluators (named, transcript-reading)` (Midfall/Halo2/Exec/Permutation.lean:207)
    sig: def VerifyingKey.evaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (vk : VerifyingKey G₁) : TranscriptM (CommonEvaluated (Fr p)) def Committed.evaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (coms : Committed G₁) : TranscriptM (Evaluated (Fr p) G₁)
    notes: Permutation.VerifyingKey.evaluate is at Permutation.lean:207 and Permutation.Committed.evaluate at :224 (3k-2 reads). Logup.Committed.evaluate is at Logup.lean:172 and Trash.Committed.evaluate at Trash.lean:126, both `{p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (coms : Committed G₁) : TranscriptM (Evaluated (Fr p) G₁)`. Per-argument query builders: Permutation.Evaluated.queries 265 (Except), CommonEvaluated.queries 300, Logup.Evaluated.queries 196, Trash.Evaluated.queries 135. Expression evaluators: Permutation.expressions 367, Logup.expressions 247, Trash.expressions 168.
- `Midfall.Lowering.ContractRefAccepts` (Midfall/Lowering/Types.lean:83)
    sig: def ContractRefAccepts {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool
    notes: The no-accumulator arm only. A proved theorem already exists: contractRefAccepts_iff_verifyMsgs (Lowering/SemanticEquivalence.lean:29), stating `ContractRefAccepts E H params vk inst ms = true ↔ verifyMsgs E H Features.solidity params vk inst ms = .ok ()`. The argument order is inst then ms, the reverse of the plan's `ContractRef.accepts H g ms inst`.
- `Midfall.Statements (frozen theorems)` (Midfall/Statements.lean:43)
    sig: theorem verifyNative_iff_msgs : verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔ ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧ verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by sorry theorem verifyMsgs_iff_spec (hwf : vk.WellFormed F) : (verifyMsgs (Gₜ := Gₜ) E H F params vk inst ms).isOk ↔ Spec.accepts H F params vk inst ms := by sorry theorem contractRef_noAcc : Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms ↔ verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () := by sorry
    notes: SHA-256 pinned (Statements.sha256), so they cannot be edited. Sorries are at lines 46, 59 and 75. contractRef_noAcc follows directly from contractRefAccepts_iff_verifyMsgs. Spec.accepts (Spec/Piop.lean:54) is `def accepts (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Prop := sorry`.
- `Midfall.Halo2.decodeAcc / alphaOf / batchedCheck` (Midfall/Halo2/Exec/Accumulator.lean:955)
    sig: def decodeAcc {G₁ G₂ Gₜ : Type} (enc : AccumulatorEncoding) (codec : G1Codec G₁) (fixedBases : Array (AccFixedBase G₁)) (inst : Array Word256) : Option (KzgAcc (Fr p) G₁ G₂ Gₜ) def alphaOf {G₁ : Type} (H : Bytes → H256) (vkDigest : Word256) (codec : G1Codec G₁) (kzgLhs kzgRhs accLhs accRhs : G₁) : Fr p def batchedCheck {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (params : ParamsVerifierKZG G₁ G₂) (alpha : Fr p) (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (fixedBases : Array (String × G₁)) : Bool
    notes: Outside the core L0 area but needed by contractRef_acc_complete. Lines: decodeAcc 955, alphaOf 1014, batchedCheck 1036. KzgAcc (662) carries phantom G₂ and Gₜ. decodeAcc takes 4 arguments versus the plan's 2, and reads Word256 instance words rather than Fr. The only DualMSM-level scaling in the tree is here: the accumulator MSMs are scaled by alpha.

## verbatim excerpts

### Midfall/Halo2/Exec/Native.lean:37
```lean
/-- Runtime data required by the §9.2 verifier path. -/
structure VerifierEnv (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where
  g1 : G1Codec G₁
  field : FieldConsts (Fr p)
  delta : Fr p
  fewerPointSetsRuntime : Bool

/-- A hash: the concrete Keccak for execution, or a random oracle in the proofs
    (plan 9.1 `abbrev Hash`). -/
abbrev Hash := Bytes → H256
```

### Midfall/Halo2/Exec/Native.lean:207
```lean
def verifyNative {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) :
    Except Fault Unit := do
  -- Gₜ is a phantom of DualMSM, so it has to be named: nothing in the
  -- arguments pins it.
  let m := prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]
  let (g, t) ← StateT.run m (Transcript.initFromBytes proof)
  t.assertEmpty
  unless DualMSM.check g params do throw (Fault.error Error.opening)
```

### Midfall/Halo2/Exec/Native.lean:228
```lean
def decodeRust (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) :
    Option (List (Msg (Fr p) G₁)) := do
  -- The messages are whatever the pipeline actually consumed, recorded by
  -- Transcript.read. Deriving them this way is deliberate: a hand-written second
  -- copy of the schedule is exactly what R-30 and R-32 got wrong, and it would
  -- drift the moment the Rust changed. If the run faults, there is no message
  -- stream; if it leaves trailing bytes, the proof is not exactly the schedule
  -- either ("schedule-driven, exact length" in plan 9.2).
  let t0 := Transcript.initFromBytes π
  let (_, t) ← (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run t0 |>.toOption
  if t.buffer.size ≠ t.pos then none
  else
    let wG1 := (hashableG1 E.g1).width
    let wFr := (hashableFr (p := p)).width
    t.log.toList.mapM fun rec =>
      if rec.1 == wG1 then (E.g1.ofCompressed? rec.2).map Msg.g1
      else if rec.1 == wFr then (frOfRepr? (p := p) rec.2).map Msg.fr
      else none
```

### Midfall/Halo2/Exec/Native.lean:255
```lean
def prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ) := do
  -- Re-serialise the messages to the wire bytes the transcript would have read,
  -- then run the SAME pipeline with the caller's hash. Going through the byte
  -- level rather than a parallel message-driven interpreter is what keeps
  -- verifyNative_iff_msgs close to a definitional unfolding: both sides execute
  -- one schedule, not two that must be proved to agree.
  let bytes := ms.foldl (init := Bytes.empty)
    (fun acc m => ByteArray.append acc (msgWire E m))
  let (g, t) ← (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]).run
    (Transcript.initWithHash H bytes)
  t.assertEmpty
  pure g

/-- `verifyNative` at the message level: the same pipeline, with the messages
    re-serialised to the wire bytes and the caller's hash honoured. -/
def verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features)
    (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    Except Fault Unit := do
  let g ← prepareMsgs (Gₜ := Gₜ) E H F vk inst ms
  unless DualMSM.check g params do throw (Fault.error Error.opening)
```

### Midfall/Halo2/Exec/Transcript.lean:127
```lean
def Transcript.squeeze (t : Transcript) : Bytes × Transcript :=
  let d := wordToBytesBE (t.hash t.state)
  (d, { t with state := d })

/-- rust: proofs/src/transcript/mod.rs:126 squeeze_challenge::<Fq> composed
    with Sampleable<Keccak256> for Fq (implementors.rs:347-351), i.e.
    sample_keccak_digest_be_mod_r (implementors.rs:20-39). The Rust asserts
    the digest is 32 bytes; squeeze builds it from a BitVec 256, so that
    assertion is discharged by construction and is not a panic site. -/
def Transcript.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)] (t : Transcript) :
    Fr p × Transcript :=
  let (d, t2) := t.squeeze
  (frOfDigest (bytesToWordBE d), t2)
```

### Midfall/Halo2/Exec/Transcript.lean:145
```lean
def Transcript.read {T : Type} (h : Hashable T) (t : Transcript) :
    Except Fault (T × Transcript) :=
  match bytesTake t.buffer t.pos h.width with
  | none => .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof))
  | some repr =>
      match h.readRepr? repr with
      | none => .error (Fault.error (Error.transcript IoErrorKind.other))
      | some val =>
          let t2 := { t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }
          .ok (val, t2.common h val)
```

### Midfall/Halo2/Exec/Kzg/Msm.lean:222
```lean
def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) : Bool :=
  let left := g.left.eval
  let right := g.right.eval
  decideBool (P.decEqGₜ
    (Additive.toMul
      (P.e (Additive.ofMul left) (Additive.ofMul params.sG2Prepared) +
       P.e (Additive.ofMul right) (Additive.ofMul params.nG2Prepared))) 1)
```

### Midfall/Halo2/Exec/Kzg/MultiOpen.lean:234
```lean
  let x4 ← tmSqueezeChallenge
  -- kzg/mod.rs:488-508
  let finalCom ← StateT.lift (MultiPrepare.finalCom feat fc qComs fCom x4)
  -- kzg/mod.rs:510-516
  let v ← StateT.lift (MultiPrepare.vCalc feat fc qEvalsOnX3 fEval x4)
  -- kzg/mod.rs:527-533
  let pi ← tmRead (hashableG1 g1)
  let piMsm := MSMKZG.appendTerm MSMKZG.init 1 pi (.custom "π")
  -- kzg/mod.rs:544-551: scalars [x3, v] over bases [pi, -generator]. The
  -- generator is AdmissiblePairing.g₁ (D-P1); the Rust writes -E::G1::generator().
  let scaledPi : MSMKZG (Fr p) G₁ :=
    { scalars := #[x3, v], bases := #[pi, P.g₁⁻¹],
      labels := #[.custom "π", .custom "-G"] }
  -- kzg/mod.rs:553-558: (π, C − vG + zπ). The Rust calls add_msm on
  -- msm_accumulator.right, which mutates in place and returns nothing; a port
  -- that computed addMsm and discarded the result would silently drop the whole
  -- scaled_pi term and accept every proof. The value is threaded here.
  let acc : DualMSM (Fr p) G₁ G₂ Gₜ := { left := piMsm, right := finalCom }
  pure { acc with right := acc.right.addMsm scaledPi }
```


# AREA: Generator port, render/template/layout side: formal/Midfall/Generator/{Templates,Render,YulGolden,Models,Filters,Layout,LayoutMemory,Protocol}.lean, mapped to proofs/solidity-verifier/templates/{contracts,partials}

## constraints
- NO Lean function returns a Yul AST for any of the 13 verifier or 2 evaluator partials. The only template rendered to a vendored AST is the VK constructor (Halo2VerifyingKey.constructorStmts : Block EVM.Op, Templates.lean:319). Constants.sol is represented only by literals (errorSelectors, frModulusConstant, BLS_P words). P-13 (docs/plans/P-13-templates.md) is DRAFT and blocked on P-05..P-12. So every per-partial theorem (vkLoading/transcriptParser/lagrange/quotientLin/pcs/finalPairing/traceReturn _spec) must take the partial's Block EVM.Op as an abstract parameter, e.g. a structure field `blk : VerifierPartial → Block EVM.Op`. It cannot be stated over a concrete Lean renderer.
- The Pcs.yul body is produced today as TEXT: Midfall.Generator.computations (Kzg.lean:1320) returns Except Fault (List (List String)), and the quotient bodies are List (List String) fields of Halo2Verifier. No runtime Yul parser exists (D-P2 amendment; R-42 decided option A: yul% quotations generated from text). So pcs_spec / quotientLin_spec need an abstract AST plus an assumed or decided link to that text.
- render_eq_print is FALSE as written (REVIEW R-39). Comments inside statements and the 91 free `internal constant` identifiers are not representable in Stmt. Restate it structurally (R-39 resolution 1, matching D-P13): stmtsBeq (astOf (render g o)) (lower g o).main = true, lifted to `=` via YulSemantics.SyntaxEq.stmtsBeq_eq (needs LawfulBEq EVM.Op, which holds because EVM.Op derives DecidableEq). The token relation yulTokens is strictly weaker than stmtsBeq (builtin vs call, R-38 F2), so do not state anything over it.
- Supported.layout as written (`g.plan.memory.WellFormed`) is ill-typed against the ported code. WellFormed is defined on MemoryMap (Layout.lean:1127), and the Rust LoweringPlan.memory is a VerifierMemoryLayout, so write `g.plan.memory.map.WellFormed`. D-P18 (design.md:395, OPEN, needs sign-off) shows WellFormed does not deliver 'aligned' (no len%32 arm) or 'above solc spill window' (it bounds at 0x80, not 0x1000). Recommended option 1: `memory.map.WellFormed ∧ memory.validate = .ok ()`. D-P18 forbids picking a reading silently, so flag the choice or parameterise over it.
- Disjointness is lifetime-relative: the poseidon layout has 54 same-byte, different-phase region pairs, and naive global byte-disjointness is FALSE (LayoutMemory.lean:909). transcript_buffer, constructor_smoke_scratch, pcs_pairing_static_working, verifier_return, quotient_return and accumulator_pairing_batch all start at 0x1000, and final_pairing_scratch is at 0x1240. Inv k must therefore NOT assert that a phase-scoped region's contents survive into a later phase, e.g. the transcript buffer is dead by .pcs/.pairing. Only Permanent regions (vk_payload, challenge_slots, theta slots, q_eval_cptr_slot, g1_identity, decoded_evals, decompressed_commitments, trace_u256_log_word) may carry cross-phase facts.
- PLAN's Inv indices (.start,.vk,.transcript,.lagrange,.quotient,.pcs,.pairing) do not exist. MemoryPhase (Layout.lean:407) is a different, 16-constructor scratch-lifetime enum, so a new checkpoint inductive must be introduced. MemoryPhase derives only BEq and Ord, and MemoryLifetime only BEq. Reasoning about memoryLifetimeIntersects's `lhs == rhs` needs a LawfulBEq instance or case splits.
- Memory pointers are Ptr {loc : Location, value : Value}, with Value = integer Int | identifier String Int, not Nat. Ptr arithmetic is WORD-wise (Ptr.add/Value.add multiply by wordBytes, Encoding.lean:249/276). Template constants like VK_DIGEST_MPTR = {{ memory.vk_mptr + vk_header.vk_digest }} are Ptr.add with word offsets. Convert to byte addresses via Value.asUsizeNat (ptrValue p) (Layout.lean:1010). VerifierMemoryLayout.new only ever builds ptrMemory (valueFromNat _), which is worth a lemma.
- There is no Lean def or field named RETURN_MPTR or returnMptr. RETURN_MPTR renders `memory.verifier_return_mptr|hex()` (Constants.sol:42), i.e. VerifierMemoryLayout.verifierReturnMptr : Nat = verifierReturnBufferStart = lowMemoryScratchStart = 0x1000, the same address as TRANSCRIPT_MPTR (transcriptMptr). The template comment 'TRANSCRIPT_MPTR (0x80)' at Halo2Verifier.sol:194-197 is stale.
- traceReturn_spec holds only for production renders. TraceReturn.yul:55-72 returns `iszero(iszero(success))` (possibly false) when trace=true, and otherwise does `if iszero(success) { fail(ERR_PROOF_REJECTED) } mstore(RETURN_MPTR, 1) return(RETURN_MPTR, 0x20)`. It needs Supported.production (Api.lean RenderDiagnostics.trace/gasCheckpoints).
- FinalPairing.yul:88 calls `ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)` with the arguments SWAPPED (pairing input [RHS|G2|LHS|NEG_S_G2], P-13 hazard 4). In accumulator mode it first overwrites PAIRING_RHS/LHS in place with + alpha*ACC_RHS/LHS (FinalPairing.yul:33-58). So pcs_spec's 'PAIRING_LHS/RHS = DualMSM left/right' holds at the end of Pcs, not after FinalPairing.
- Structure of Halo2Verifier.sol: a separate ABI-shape guard assembly block (Halo2Verifier.sol:147-154), Solidity locals (`address vk = AUTHORIZED_VK`, `address quotientEvaluator`), then the main assembly block opening with the spill guard `if gt(mload(0x40), TRANSCRIPT_MPTR) { mstore(0x00, shl(224, ERR_MEMORY_LAYOUT_VIOLATED)) revert(0x00, 0x04) }`, then the three helper partials, then `let r := FR_MODULUS let success := true`, then VkLoading..TraceReturn. Free identifiers (FR_MODULUS, *_MPTR, *_GAS, ERR_*) are unbound in the AST (Render.lean loss class 4), so `bindLocals L` must supply them from the Halo2Verifier model.
- Halo2Verifier (Memory Proof : Type) and Halo2QuotientEvaluator (Memory : Type) take real (non-phantom) type parameters, since `memory : Memory` and `codegenLayout : VerifierCodegenLayout Proof` are fields, but they are never instantiated and nothing builds them (artifacts.rs unported). Instantiate as Halo2Verifier VerifierMemoryLayout ProofCalldataLayout (Abi.lean:209), or abstract over them.
- The golden gates are all `def … : Bool` plus `#eval -- expect true`, not theorems. `<base>_ast` vs `<base>_direct` are both hand-transcribed; provenance is enforced by scripts/check_golden_provenance.py, not Lean (R-38 F1). D-P19 asks future gates to IO.FS.readFile the artifact. native_decide is banned outside Midfall/Instances/ (PLAN.md:118,136), so any theorem version of a gate needs kernel `decide` through stmtsBeq_eq, which is untested at fixture size.
- Fuel: any Lean function that recurses over generated Yul (irCheck, a per-partial block extractor, the renderer) hits R-37: no structural recursion through Stmt.switch in Lean 4.35. The renderer uses renderFuel := 512 with a '<fuel-exhausted>' marker. Plan for fuel or well-founded recursion in any definition used in theorem statements.
- Name clashes to avoid when opening namespaces: Midfall.Generator.Word (Encoding.lean:289, a structure over Ptr) vs YulSemantics.Word := BitVec 256 (vendor Basic.lean:26); Midfall.Generator.GeneratorError (Api.lean:309) vs Midfall.Lowering.GeneratorError (Lowering/Types.lean:41); Midfall.Lowering.{Lowered,Supported,Deployment,ContractRefAccepts,Op,YulBlock,YulObject} already exist; Midfall.Generator.wordBytes/g1Bytes defs vs TemplateConstants.wordBytes/g1Bytes fields; Midfall.Generator.Value vs YulSemantics Dialect D.Value.
- The vendored YulSemantics.RunContract (Contract.lean:21) has signature `(program : Block D.Op) (pre : D.State → Prop) (post : D.State → VEnv D → D.State → Outcome → Prop) : Prop` and EXISTENTIAL run semantics (∀ initial, pre → ∃ run ∧ post). PLAN's `RunContract (blk .vkLoading L) (Inv .start) (fun s => s.reverted ∨ Inv .vk s)` has the wrong post arity, and ∃-semantics alone does not give the ∀-runs soundness that verifier_sound needs under relational externals. YulSemantics.RunCommitted (Observation.lean:39) is over EVM.evm only and has no `(keccak := H)` parameter; keccak goes through ExecEnv.keccakOf.
- Midfall.Generator.TemplateConstants exists (Models.lean:230), so PLAN's `Lowered.consts : TemplateConstants` can be typed today with templateConstantsDefault, which has been checked against the golden fixtures (TemplateKats templateConstants_matchSmokeFixture_ok etc.).

## missing
- Lean template functions returning Block EVM.Op for all 13 verifier partials: proofs/solidity-verifier/templates/partials/verifier/{AssemblyHelpers.yul (310 lines), AccumulatorHelpers.yul (372), TraceAndGasHelpers.yul (23), VkLoading.yul (141), TranscriptProofParser.yul (424), Lagrange.yul (99), QuotientAndLinearization.yul (165), Pcs.yul (39), FinalPairing.yul (92), TraceReturn.yul (73)} plus the Solidity partials {Constants.sol (255), PrecompileSmoke.sol (216), Constructors.sol (92)}. None exists. P-13 (DRAFT) recommends AssemblyHelpers.yul and FinalPairing.yul first, for finalPairing_spec.
- Lean template functions for the 2 evaluator partials: templates/partials/quotient_numerator/{QuotientHelpers.yul (81), QuotientNumeratorBlock.yul (1442)}. None exists. QuotientNumeratorBlock is only parsed at #eval for opcode-table gates (P-09a), and P-13 hazard 3 says it is blocked on P-09d yul_emit.
- Contract shells for Halo2Verifier.sol (232 lines) and Halo2QuotientEvaluator.sol (170), and the Askama render wrappers models.rs M:955-960 (Halo2Verifier::render) and M:1008-1013 (Halo2QuotientEvaluator::render). Only the VK one (M:820-825) is ported, as constructorStmts/constructorLines. PLAN's SolShell type does not exist.
- Halo2Verifier::validate_layout (src/lowering/render/models.rs:830-952) and Halo2QuotientEvaluator::validate_layout (models.rs:965-1005), deferred per the Models.lean header.
- Model builders: generate_verifier (src/lowering/artifacts.rs:~79-260, builds `Halo2Verifier {..}` at :247) and generate_quotient_evaluator_from_plan (artifacts.rs:22-60). Nothing in Lean constructs a Halo2Verifier/Halo2QuotientEvaluator value.
- LoweringPlan (src/lowering/plan.rs:28-44: vk, vk_mptr, meta, data, proof_layout, lowering, sorted_simple, quotient, direct, pcs_memory_requirements, memory : VerifierMemoryLayout), needed for PLAN's `L.plan` / `g.plan.memory`. Not ported.
- SolidityGenerator.render: src/builder/render.rs:35 `pub fn render(&self, options: RenderOptions) -> Result<RenderedArtifacts, GeneratorError>` (also render_quotient_evaluator :119, render_quotient_probe :185). The Lean side has RenderOptions/RenderedArtifacts/RenderDiagnostics (Api.lean:923-1010) but no render function. SolidityGenerator.lower and Lowered.print do not exist anywhere.
- The per-partial apparatus `blk : _ → Lowered → Block`, the Inv checkpoint index (.start/.vk/.transcript/.lagrange/.quotient/.pcs/.pairing) and Inv itself, bindLocals, irCheck and RunShell. None is in the Lean tree. Inv would be derived from layout/memory.rs region and phase semantics plus the L0 state.
- An AST form of the PCS block: Kzg.lean:1320 `computations` emits text (port of src/lowering/kzg/mod.rs emitter KZ:934+). pcs_spec needs either an AST-emitting variant or a parse step; no runtime Yul parser exists (R-42 option A).

## declarations
- `Midfall.Generator.Halo2VerifyingKey.constructorStmts` (formal/Midfall/Generator/Templates.lean:319)
    sig: def Halo2VerifyingKey.constructorStmts (self : Halo2VerifyingKey) : Block EVM.Op :=
    notes: This is the only Lean function in the tree that returns a vendored Yul AST for a template. It renders the body of the assembly block in T:contracts/Halo2VerifyingKey.sol:54-96 (braces excluded): vkSetupStmts ++ vkConstantStmts ++ vkCommStmts(fixed) ++ vkCommStmts(perm) ++ [constructorReturnStmt]. It is gated against provenance-pinned artifact ASTs by stmtsBeq: vkConstructor_matchesGolden_ok (Templates.lean:627, take 8 vs Golden.vkHead_ast, DVK:62-72) and vkConstructor_fixedComms_matchesArtifact_ok (:832, vs Golden.vkComms_ast, DVK:103-132). The permutation loop is checked only against a hand-written AST (:737).
- `Midfall.Generator.vkSetupStmts / vkConstantStmts / vkCommStmts / vkPayloadWordStmt` (formal/Midfall/Generator/Templates.lean:238)
    sig: def vkPayloadWordStmt (wordIdx : Nat) (val : Word256) : Stmt EVM.Op := | def vkSetupStmts (self : Halo2VerifyingKey) : Block EVM.Op := (256) | def vkConstantStmts (self : Halo2VerifyingKey) : Block EVM.Op := (273) | def vkCommStmts (base : Nat) (comms : List G1Words) : Block EVM.Op := (285)
    notes: These are the pieces of constructorStmts. The payload word is `mstore(add(payload, 32*wordIdx), val.toNat)` as .builtin EVM.Op.mstore / EVM.Op.add. The setup is `let runtime := constructorPayloadMptr; let payload := add(runtime, vkRuntimePrefixLen); mstore8(runtime, vkRuntimePrefix)`.
- `Midfall.Generator.Halo2VerifyingKey.constructorReturnStmt` (formal/Midfall/Generator/Templates.lean:309)
    sig: def Halo2VerifyingKey.constructorReturnStmt (self : Halo2VerifyingKey) : Stmt EVM.Op :=
    notes: This is `return(runtime, 1 + 32*(constants.len + 4*fixed + 4*perm))`, recomputed the way the template does it rather than taken from runtimeLen. vkConstructor_returnFormula_ok (:896) shows on a test VK that the two formulas give the same number.
- `Midfall.Generator.Halo2VerifyingKey.constructorLines / constructorBodyLines / constructorReturnLines` (formal/Midfall/Generator/Templates.lean:363)
    sig: def Halo2VerifyingKey.constructorLines (self : Halo2VerifyingKey) : List Line := | def Halo2VerifyingKey.constructorBodyLines (self : Halo2VerifyingKey) : List Line := (337) | def Halo2VerifyingKey.constructorReturnLines (self : Halo2VerifyingKey) : List Line := (353)
    notes: This is the text channel for the same template, a List Line made only of Line.text with hex spellings from hexFilter/hexPaddedFilter. It is not derived from constructorStmts; the two are parallel expansions of the template. renderLines turns it into a String.
- `Midfall.Generator.verifierIncludes / evaluatorIncludes / fixtureAnchors` (formal/Midfall/Generator/Templates.lean:101)
    sig: def verifierIncludes : List String := | def evaluatorIncludes : List String := (120) | def fixtureAnchors : List (String × Nat) := (139)
    notes: This is registry data only, not renderers. There are 13 verifier partials in include order (Constants.sol, PrecompileSmoke.sol, Constructors.sol, AssemblyHelpers.yul, AccumulatorHelpers.yul, TraceAndGasHelpers.yul, VkLoading.yul, TranscriptProofParser.yul, Lagrange.yul, QuotientAndLinearization.yul, Pcs.yul, FinalPairing.yul, TraceReturn.yul; Halo2Verifier.sol lines 85,87,89,201,203,205,217,...,229) and 2 evaluator partials (QuotientHelpers.yul, QuotientNumeratorBlock.yul; Halo2QuotientEvaluator.sol:152-153). The fixture anchors are PrecompileSmoke 357, AssemblyHelpers 640, Lagrange 1509, QuotientAndLinearization 1902, Pcs 2744.
- `Midfall.Generator.typedErrorNames / errorSelectors / frModulusConstant / blsP* / pragmaLine` (formal/Midfall/Generator/Templates.lean:175)
    sig: def errorSelectors : List (String × String × BitVec 32) := | def typedErrorNames : List String := (164) | def frModulusConstant : Nat := 0x73eda753...00000001 (187) | def pragmaLine : String := "pragma solidity 0.8.30;" (153)
    notes: These are fixed literals from the Constants.sol partial: 8 typed errors (ERR_BAD_CALLDATA_SHAPE 0x1b99e37c ... ERR_MEMORY_LAYOUT_VIOLATED 0xc9888d23), checked against keccak. They are the only part of Constants.sol in Lean; the ~91 `uint256 internal constant` MPTR/CPTR declarations are NOT rendered.
- `Midfall.Generator.Line` (formal/Midfall/Generator/Render.lean:173)
    sig: inductive Line where | code (lvl : Nat) (s : Stmt EVM.Op) | text (raw : String) | tail (raw : String)
    notes: This is an output-stream element, not syntax (D-P2: no parallel AST). Under D-P13 it carries comments and layout that are outside the correctness relation.
- `Midfall.Generator.renderStmtFuel / renderStmt / renderBlock / renderBlockBraces / renderLines / renderObject / renderExpr / renderLit` (formal/Midfall/Generator/Render.lean:225)
    sig: def renderStmtFuel : Nat → Nat → Stmt EVM.Op → String | def renderStmt (lvl : Nat) (s : Stmt EVM.Op) : String := (256) | def renderBlock (lvl : Nat) (b : Block EVM.Op) : String := (261) | def renderBlockBraces (lvl : Nat) (b : Block EVM.Op) : String := (265) | def renderLines : List Line → String (283) | def renderObject : Nat → Object EVM.Op → String (291) | def renderExpr : Expr EVM.Op → String (162) | def renderLit : Literal → String (153)
    notes: Every output type is String. The renderer is fuel-bounded: renderFuel : Nat := 512 (:209), and fuel 0 prints "<fuel-exhausted>" (R-37: Lean 4.35 cannot recurse structurally through Stmt.switch). Literals print in decimal (loss class 2), so no AST-to-text function is byte-exact on the corpus. There is no `print : Lowered → String`, and no renderer call on any verifier block exists.
- `YulSemantics.SyntaxEq.stmtsBeq (vendored)` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:147)
    sig: def stmtsBeq : List (Stmt Op) → List (Stmt Op) → Bool
    notes: Declared under `variable {Op : Type} [BEq Op]` in namespace YulSemantics.SyntaxEq, inside a mutual block with stmtBeq/casesBeq/optionalStmtsBeq. This is the D-P13 relation: it compares identifiers as strings (no alpha-quotient), literals by value, and keeps .builtin apart from .call.
- `YulSemantics.SyntaxEq.stmtsBeq_eq (vendored)` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:288)
    sig: theorem stmtsBeq_eq : ∀ (left right : List (Stmt Op)), stmtsBeq left right = true → left = right
    notes: Needs [LawfulBEq Op], which EVM.Op has because it derives DecidableEq (Dialect/EVMOp.lean:54). This is the bridge from a Bool golden gate to propositional AST equality.
- `YulSemantics.EVM.print (vendored)` (formal/vendor/yul-semantics/YulSemantics/PrettyPrint.lean:141)
    sig: def print (b : Block EVM.Op) : String := ppProgram EVM.opName b
    notes: The debug printer, used by the secondary token gates. It prints .builtin and .call the same way, so the token relation is strictly weaker than stmtsBeq (R-38 F2; discriminates_builtinVsCall_ok YulGolden.lean:730).
- `Midfall.Generator.yulTokens` (formal/Midfall/Generator/YulGolden.lean:119)
    sig: def yulTokens (s : String) : List String :=
    notes: The SECONDARY relation: strip comments, split on punctuation and whitespace, and reduce hex literals to decimal.
- `Midfall.Generator.Golden.<base>_ast / <base>_direct / <base>_committed and golden_beq_all_ok / golden_all_ok` (formal/Midfall/Generator/YulGolden.lean:665)
    sig: def smoke_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq smoke_ast smoke_direct (…9 such) | def golden_beq_all_ok : Bool := (676) | def golden_all_ok : Bool := (636)
    notes: 9 fixtures: smoke D:357-380, scalarInv D:640-662, batchInv D:833-843, lagrangeFor D:1509-1511, vmSwitch D:1902-1917, pcsBasis D:2744-2773, spread D:399-408, vkHead DVK:62-72, vkComms DVK:103-132. Each `_ast` is a hand-transcribed yul% quotation, each `_direct` is the same slice written with raw constructors, and each `_committed` is a pasted token string. All are `def … : Bool` checked with `#eval -- expect true`. None is a theorem, and none compares Lean GENERATOR output, except the VK gates in Templates.lean. Provenance comes from scripts/check_golden_provenance.py, not from Lean (R-38 F1).
- `Midfall.Generator.TemplateConstants` (formal/Midfall/Generator/Models.lean:230)
    sig: structure TemplateConstants where wordBytes : Nat g1Bytes : Nat g1MsmPairBytes : Nat g1addInputBytes : Nat pairingTwoPairBytes : Nat eip2537 : Eip2537TemplateConstants gas : GasTemplateConstants modexp : ModexpTemplateConstants accumulator : AccumulatorTemplateConstants quotientVm : QuotientVmTemplateConstants
    notes: Default value: templateConstantsDefault : TemplateConstants (:290); wordBytes 0x20, g1Bytes 128, g1MsmPairBytes 160, g1addInputBytes 256, pairingTwoPairBytes 768, eip2537 g1add 0x0b, g1msm 0x0c, pairing 0x0f. Sub-records: Eip2537TemplateConstants (:101) {g1addAddress g1msmAddress pairingAddress smokeScratchBytes : Nat, g1Generator g1DoubleGenerator : G1Words}; GasTemplateConstants (:116) {g1add g1msmOnePair pairingTwoPair modexp : Nat}; ModexpTemplateConstants (:127) {address frameBytes outputBytes baseLenOffset expLenOffset modLenOffset baseOffset expOffset modOffset : Nat}; AccumulatorTemplateConstants (:148) {limbsPerWord identityFlagWords : Nat, pairingBatchDomainTagHex : String, pairingBatchVkDigestOffset pairingBatchRhsOffset pairingBatchLhsOffset pairingBatchAccRhsOffset pairingBatchAccLhsOffset pairingBatchHashBytes : Nat}; QuotientVmTemplateConstants (:218) {op : QuotientVmOpcodeTemplateConstants, mem : QuotientVmMemTokenTemplateConstants, byteU32Bytes limbCount limbPairwiseCoeffs : Nat}.
- `Midfall.Generator.Halo2Verifier` (formal/Midfall/Generator/Models.lean:757)
    sig: structure Halo2Verifier (Memory Proof : Type) where
    notes: The Askama model for Halo2Verifier.sol. There is no RenderModel or VerifierModel; this is it. The type parameters are NOT phantom: `memory : Memory` (intended VerifierMemoryLayout) and `codegenLayout : VerifierCodegenLayout Proof` (intended ProofCalldataLayout, Abi.lean:209). It is never instantiated anywhere in the tree, and no Lean function builds one. Fields in order: templateConstants : TemplateConstants; trace gasCheckpoints quotientProbe quotientPow5Helper quotientLimb7Helper quotientWideLimb7Helper : Bool; constructorG1msmSmokeInputBytes constructorG1msmSmokeGas accRhsMsmGas : Nat; limb7YulCoeffs wideLimb7YulCoeffs : List String; frDelta : String; embeddedVk : Option Halo2VerifyingKey; expectedVkCodehash : Option Word256; buildId : Word256; vkLen numInstances k proofLen : Nat; codegenLayout : VerifierCodegenLayout Proof; memory : Memory; vkHeader : VkHeaderTemplateSlots; vkMptr challengeMptr thetaMptr proofCptr : Ptr; abiSelectorBytes abiProofHeadOffset abiInstancesHeadCptr numInstanceCptr instanceCptr : Nat; quotientCommCptr : Ptr; numNegLagranges : Nat; userPhases : List UserPhase; numUserChallenges numLookups numPermutationZs lookupHPlusAcc numTrashcans numQuotients numEvals : Nat; commsMptrBase reversedEvalsMptr : Ptr; selectorAccMptr : Nat; quotientExternal : Option QuotientExternal; expectedQuotientLen : Option Nat; expectedQuotientCodehash : Option Word256; quotientInlineComputations quotientEvalNumerComputations quotientPostVmComputations : List (List String); quotientNativePermutationComputation quotientNativeLookupComputation : List String; quotientNativeIdentityComputations : List (List String); quotientProgram : Option QuotientProgram; quotientDirect : Option DirectQuotientRendering; pcsComputations : List (List String); simpleSelectorCols : List Nat; proofCommitTraceBase proofEvalTraceBase quotientIdentityTraceBase selectorTraceBase fixedCommMptr : Nat; truncatedChallenges expectedHasAccumulator : Bool; expectedHasAccumulatorWord expectedAccOffset expectedNumAccLimbs expectedNumAccLimbBits : Nat; expectedAccHasCarriedScalars : Bool; accFixedBases : List (Nat × Bool). The code-bearing fields (pcsComputations, quotient*Computations) are already-rendered TEXT (List String), not AST.
- `Midfall.Generator.Halo2QuotientEvaluator` (formal/Midfall/Generator/Models.lean:873)
    sig: structure Halo2QuotientEvaluator (Memory : Type) where
    notes: The model for Halo2QuotientEvaluator.sol. Fields: templateConstants, trace, quotientPow5Helper, quotientLimb7Helper, quotientWideLimb7Helper, limb7YulCoeffs, wideLimb7YulCoeffs, frDelta, memory : Memory, vkMptr : Ptr, vkLen, challengeMptr : Ptr, numUserChallenges, thetaMptr : Ptr, reversedEvalsMptr : Ptr, numEvals, quotientExternal : QuotientExternal (NOT optional), quotient*Computations : List (List String)/List String, quotientProgram : Option QuotientProgram, simpleSelectorCols, quotientIdentityTraceBase. It is never instantiated.
- `Midfall.Generator.VerifierCodegenLayout / VkHeaderTemplateSlots` (formal/Midfall/Generator/Models.lean:708)
    sig: structure VerifierCodegenLayout (Proof : Type) where proof : Proof | structure VkHeaderTemplateSlots where (713)
    notes: vkHeaderTemplateSlotsDefault (:734) gives WORD offsets from VK_MPTR: vkDigest 0, numInstances 1, k 2, nInv 3, omega 4, omegaInv 5, omegaInvToL 6, hasAccumulator 7, accOffset 8, numAccLimbs 9, numAccLimbBits 10, g1Base 11, g2Base 15, negSG2Base 23.
- `Midfall.Generator.Halo2VerifyingKey (+ len/runtimeLen/bytes/runtimeBytes)` (formal/Midfall/Generator/Models.lean:385)
    sig: structure Halo2VerifyingKey where constructorPayloadMptr : Nat constants : List (String × Word256) fixedComms : List G1Words permutationComms : List G1Words quotientConstOffsetWords : Option Nat quotientConstWords : Nat quotientProgramOffsetWords : Option Nat quotientProgramWords : Nat quotientConstLabels : List String quotientConstHeaders : List (Nat × List String)
    notes: def Halo2VerifyingKey.len (:462) = constants.length*32 + (fixed+perm)*128; runtimeLen (:466) = vkRuntimePrefixLen + len; bytes (:474) : Bytes; runtimeBytes (:484) : Bytes = 0xfe :: bytes. vkRuntimePrefix := 0xfe (:414), vkRuntimePrefixLen := 1 (:418). runtimeBytes is the natural target for the plan's `Lowered.vkRuntime`. Proving that `constructorStmts` returns exactly `runtimeBytes` is a natural vk-constructor theorem that is fully statable today.
- `Midfall.Generator.G1Words` (formal/Midfall/Generator/Models.lean:94)
    sig: structure G1Words where xHi : Word256 xLo : Word256 yHi : Word256 yLo : Word256
    notes: EIP-2537 padded G1 encoding, 4 words. Word256 := BitVec 256 (Common/Bytes.lean:21).
- `Midfall.Generator.Ptr / ptrMemory / ptrValue / valueFromNat` (formal/Midfall/Generator/Models.lean:506)
    sig: structure Ptr where loc : Location value : Value | def ptrMemory (v : Value) : Ptr := (511) | def ptrValue (p : Ptr) : Value := p.value (523) | def valueFromNat (n : Nat) : Value := Value.integer (Int.ofNat n) (528)
    notes: Location (Filters.lean:70) is `| calldata | memory`. Value (Filters.lean:78) is `| integer (i : Int) | identifier (name : String) (off : Int)`. Ptr arithmetic is WORD-wise: Ptr.add (Encoding.lean:276) calls Value.add (Encoding.lean:249), which adds rhs*wordBytes. Byte reads go through Value.asUsizeNat (Layout.lean:1010), which is total and maps the identifier case to 0.
- `Midfall.Generator layout constants` (formal/Midfall/Generator/Layout.lean:57)
    sig: def wordBytes : Nat := 0x20 | def solidityScratchSpaceBytes : Nat := 0x40 (60) | def solidityFreeMemoryPointerSlot : Nat := 0x40 (63) | def solidityZeroSlot : Nat := 0x60 (66) | def solidityAllocatableMemoryStart : Nat := 0x80 (69) | def solidityReservedMemoryBytes : Nat := solidityAllocatableMemoryStart (72) | def lowMemoryScratchStart : Nat := 0x1000 (76) | def vkConstructorPayloadStart : Nat := solidityAllocatableMemoryStart (79) | def g1WordsCount : Nat := 4 (88) | def g2WordsCount : Nat := 8 (92) | def g1Bytes : Nat := g1WordsCount * wordBytes (98) | def g2Bytes (101) | def g1MsmPairBytes (104) | def g1AddInputBytes (107) | def modexpFrameBytes : Nat := 6 * wordBytes (112) | def modexpScratchBytes : Nat := 8 * wordBytes (116) | def pairingPairBytes (119) | def pairingTwoPairBytes : Nat := 2 * pairingPairBytes (122) | def accMsmMinScratchBytes : Nat := 0x7000 (126) | def pcsStaticWorkingWords : Nat := 32 (130) | def pairingStaticWorkingWords : Nat := pairingTwoPairBytes / wordBytes + 1 (133) | def vkHeaderWords (151)
    notes: Lean names for the plan's names: SOLIDITY_RESERVED_MEMORY_BYTES = solidityReservedMemoryBytes (0x80); LOW_MEMORY_SCRATCH_START = lowMemoryScratchStart (0x1000). pairingTwoPairBytes = 768 = 0x300; pairingStaticWorkingWords = 25.
- `Midfall.Generator low-memory fixed addresses` (formal/Midfall/Generator/Layout.lean:728)
    sig: def transcriptBufferStart : Nat := lowMemoryScratchStart | def pcsPairingScratchStart : Nat := lowMemoryScratchStart (731) | def verifierReturnBufferStart : Nat := lowMemoryScratchStart (734) | def quotientReturnBufferStart : Nat := lowMemoryScratchStart (737) | def accumulatorPairingBatchPtr : Nat := lowMemoryScratchStart (740) | def accumulatorPairingBatchHashBytes : Nat := 2 * wordBytes + 4 * g1Bytes (745) | def finalPairingScratchStart : Nat := accumulatorPairingBatchPtr + accumulatorPairingBatchHashBytes (748)
    notes: TRANSCRIPT_MPTR, RETURN_MPTR and QUOTIENT_RETURN_MPTR are all 0x1000. Constants.sol:41-42 renders `TRANSCRIPT_MPTR = memory.transcript_mptr|hex()` and `RETURN_MPTR = memory.verifier_return_mptr|hex()`. There is no Lean def named returnMptr; the field is VerifierMemoryLayout.verifierReturnMptr : Nat. finalPairingScratchStart = 0x1240.
- `Midfall.Generator.ThetaSlot / ThetaSlot.word` (formal/Midfall/Generator/Layout.lean:756)
    sig: inductive ThetaSlot where | theta | beta | gamma | trashChallenge | y | x | x1 | x2 | x3 | x4 | fCom | pi | accLhs | accRhs | xN | xNMinus1Inv | lLast | lBlind | l0 | instanceEval | quotientEval | quotient | fEval | v | finalCom | pairingLhs | pairingRhs | def ThetaSlot.word : ThetaSlot → Nat (764)
    notes: WORD offsets from THETA_MPTR: theta 0, beta 1, gamma 2, trashChallenge 3, y 4, x 5, x1 6, x2 7, x3 8, x4 9, fCom 10, pi 14, accLhs 18, accRhs 22, xN 26, xNMinus1Inv 27, lLast 28, lBlind 29, l0 30, instanceEval 31, quotientEval 32, quotient 33, fEval 38, v 39, finalCom 40, pairingLhs 44, pairingRhs 48. So QUOTIENT_EVAL_MPTR = THETA_MPTR+0x400, PAIRING_LHS_MPTR = THETA_MPTR+0x580, PAIRING_RHS_MPTR = THETA_MPTR+0x600. Theta window (:794-832): rotPointsWord 52, x1PowersWord 80, qComWord = qEvalSetWord 145, qEvalCptrWord 201, g1IdentityWord 209, reversedEvalsWord 220; caps rot 28, x1 65, qEvalSet 56, qCom 0. ThetaWindowLayout (:836) and ThetaWindowLayout.compatibility (:855) carry the same numbers.
- `Midfall.Generator.VerifierMemoryLayout` (formal/Midfall/Generator/Layout.lean:903)
    sig: structure VerifierMemoryLayout where map : MemoryMap thetaWindows : ThetaWindowLayout constructorSmokeScratchMptr : Nat constructorG1msmSmokeScratchMptr : Nat constructorG1msmSmokeInputBytes : Nat transcriptMptr : Nat pcsPairingScratchMptr : Nat verifierReturnMptr : Nat quotientReturnMptr : Nat vkMptr : Ptr scalarInvScratchMptr : Nat challengeMptr : Ptr thetaMptr : Ptr ... (betaMptr … pairingRhsMptr : Ptr, one per ThetaSlot) rotPointsMptr x1PowersMptr qComMptr qEvalSetMptr qEvalCptrMptr g1IdentityMptr reversedEvalsMptr : Ptr commsMptrBase adviceCommsMptrBase lookupMCommsMptrBase permZCommsMptrBase lookupHelperCommsMptrBase lookupZCommsMptrBase trashcanCommsMptrBase quotientLimbCommsMptrBase : Ptr selectorAccMptr batchInvertScratchMptr lagrangeDenomsMptr quotientTmpMptr quotientStackMptr quotientStackHi pcsQEvalSourceTableMptr pcsQComTraceScratchMptr pcsFinalMsmScratchMptr accMsmScratch accumulatorPairingBatchMptr finalPairingScratchMptr traceU256Mptr : Nat pcs : PcsMemoryRequirements
    notes: Mirrors MEM:416-519 field for field. Lean names behind the template constants: VK_MPTR = vkMptr (Ptr); THETA_MPTR = thetaMptr; QUOTIENT_EVAL_MPTR = quotientEvalMptr; PAIRING_LHS_MPTR = pairingLhsMptr; PAIRING_RHS_MPTR = pairingRhsMptr (all Ptr); RETURN_MPTR = verifierReturnMptr (Nat); TRANSCRIPT_MPTR = transcriptMptr (Nat). Mixed Ptr/Nat typing is the Rust's. Config: VerifierMemoryLayoutConfig (:974) {transcriptWords numInstances quotientStateWords quotientStackWords accMsmTerms : Nat, pcs : PcsMemoryRequirements}.
- `Midfall.Generator.VerifierMemoryLayout.new` (formal/Midfall/Generator/LayoutMemory.lean:140)
    sig: def VerifierMemoryLayout.new (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) : VerifierMemoryLayout :=
    notes: Total, with no Except. It registers 30 regions on the poseidon-shaped fixture. vk_payload (permanent) at vkMptr, challenge_slots after it, theta block after that (length rotPointsWord*32 = 0x680), with every theta Ptr = ptrMemory (valueFromNat (thetaStart + slot.word*32)). So all Ptr fields produced by `new` are `.memory`/`.integer` by construction, a useful lemma. ConstraintSystemMeta is at Encoding.lean:364. In the real pipeline vkMptr is the fixed point from metaDataForStableStaticLayout (Vk.lean:1048); fixtures use 0x4000.
- `Midfall.Generator.VerifierMemoryLayout.validate` (formal/Midfall/Generator/Layout.lean:1023)
    sig: def VerifierMemoryLayout.validate (self : VerifierMemoryLayout) : Except String Unit := do
    notes: Checks the 7 fixed low-memory pointers against the constants, then every non-empty region.start >= lowMemoryScratchStart (0x1000, the via-IR spill guard), scalarInvScratchMptr = vkMptr - modexpScratchBytes, the 4 PCS window caps, and finally MemoryMap.validate self.map.
- `Midfall.Generator.MemoryPhase / MemoryLifetime / memoryLifetimeIntersects` (formal/Midfall/Generator/Layout.lean:407)
    sig: inductive MemoryPhase | vkConstructorPayload | constructorSmoke | transcript | scalarInv | lagrangeBatchInvert | quotientVm | pcsFixed | pcsQEvalSourceTable | pcsQComTrace | pcsFinalMsm | pcsPairing | accumulatorMsm | accumulatorPairingBatch | finalPairing | verifierReturn | quotientReturn deriving BEq, Ord | inductive MemoryLifetime | permanent | phase (memoryPhase : MemoryPhase) deriving BEq (443) | def memoryLifetimeIntersects : MemoryLifetime → MemoryLifetime → Bool (452)
    notes: These 16 constructors are SCRATCH LIFETIMES, not the PLAN 9.5 Inv checkpoints (.start/.vk/.transcript/.lagrange/.quotient/.pcs/.pairing). MemoryPhase derives only BEq and Ord (no DecidableEq or LawfulBEq), and MemoryLifetime only BEq.
- `Midfall.Generator.MemoryRegion / MemoryMap / MemoryMap.validate` (formal/Midfall/Generator/Layout.lean:458)
    sig: structure MemoryRegion where name : String start : Nat len : Nat lifetime : MemoryLifetime | def MemoryRegion.overlaps (self other : MemoryRegion) : Bool := (481) | structure MemoryMap where regions : List MemoryRegion (486) | def MemoryMap.validate (self : MemoryMap) : Except String Unit := do (552)
    notes: MemoryMap.validate = memoryMapValidateReserved (:508; start >= 0x80 when len != 0, start % 32, len % 32) then memoryMapValidatePairs (:543; reject overlaps && lifetimes intersect). MemoryArena/ScratchAllocator are at :558-632.
- `Midfall.Generator.MemoryMap.WellFormed / wellFormedBool / memoryRegionsPairwiseDisjoint` (formal/Midfall/Generator/Layout.lean:1127)
    sig: def MemoryMap.WellFormed (self : MemoryMap) : Prop := self.wellFormedBool = true | def MemoryMap.wellFormedBool (self : MemoryMap) : Bool := (1114) | def memoryRegionsPairwiseDisjoint : List MemoryRegion → Bool (1089) | instance (self : MemoryMap) : Decidable self.WellFormed := (1130)
    notes: Defined on MemoryMap, NOT on VerifierMemoryLayout. It is strictly weaker than validate: it omits the len%32 arm, bounds starts by 0x80 rather than 0x1000, and makes len=0 exemptions. Gates: LayoutMemory.lean new_wellFormed_ok (:868), new_phaseScopedOverlap_ok (:909; 54 same-byte different-phase pairs), new_wellFormed_weakerThanValidate_ok (:950).
- `Midfall.Generator.VkConstructorMemoryLayout / Halo2VerifyingKey.payloadLayout / validatePayloadLayout` (formal/Midfall/Generator/Layout.lean:635)
    sig: structure VkConstructorMemoryLayout where map : MemoryMap payloadMptr : Nat | def VkConstructorMemoryLayout.new (runtimeLen : Nat) : VkConstructorMemoryLayout := (642) | def Halo2VerifyingKey.payloadLayout (self : Halo2VerifyingKey) : Except String VkPayloadLayout := do (665) | def Halo2VerifyingKey.validatePayloadLayout (self : Halo2VerifyingKey) : Except String Unit := do (696)
    notes: VK payload sections are header, quotientConstants, quotientProgram, fixedCommitments, permutationCommitments (PayloadSectionKind :167; VkPayloadLayout :223). PackedProgramCodec.encodeWords (:371) and decodeWords (:380) are the QVM-program word codec.
- `Midfall.Generator.ProofReadPlan / CommitmentRead / EvalRead / PcsQuerySource` (formal/Midfall/Generator/Protocol.lean:315)
    sig: structure ProofReadPlan where commitments : List CommitmentRead evals : List EvalRead deriving BEq
    notes: This is the 'transcript schedule' on the generator side: commitments in transcript order, evals in proof order. CommitmentRead (:182) = advice | lookupMultiplicity | permutationProduct | lookupHelper | lookupAccumulator | trash | quotient (no payload). EvalRead (:212) = committedInstance q | advice q | fixed q | permutationCommon column | permutationZ set kind | lookupMultiplicity l | lookupHelper l chunk | lookupAccumulator l rot | trash i. PcsQuerySource (:240) is the multi-open order, a different variant order ending in linearization. There is no type called 'schedule'. The Exec side uses a separate schedule-driven decodeRust (Halo2/Exec/Native.lean:220).
- `Midfall.Generator.ProtocolPlan / ProtocolPlan.fromConstraintSystem` (formal/Midfall/Generator/Protocol.lean:627)
    sig: def ProtocolPlan.fromConstraintSystem {F : Type} (feat : Features) (cs : ConstraintSystem F) (nbCommittedInstances : Nat) : Except Fault ProtocolPlan := do
    notes: Produces the proof read order: `plan.proof : ProofReadPlan` and `plan.pcsQueries : List PcsQuerySource`. ProtocolPlan (:460) has 24 fields, including proof, pcsQueries, commonPolys, rotationLast : Int, numQuotients, challengeIndices. It is generic over F, which is a widening (no Fq in the tree). It sits in a mutual block with ProtocolPlan.validate (:864, `Except String Unit`), which it calls and turns into Fault.panic. Helpers: commitmentReadGroups (:827) : List Nat (group sizes in transcript order), numMainEvals (:805), numCommitments (:808), lookupIdentitySource (:842).
- `Midfall.Generator.computations (Kzg PCS emitter)` (formal/Midfall/Generator/Kzg.lean:1320)
    sig: def computations (meta_ : ConstraintSystemMeta) (data : Data) (memory : VerifierMemoryLayout) (truncatedChallenges : Bool) (trace : Bool) : Except Fault (List (List String)) := do
    notes: This is the body of Pcs.yul's `{% for code_block in pcs_computations %}`, and it is TEXT (lines of Yul source), not a vendored AST. Hex offsets use hashHex (unpadded), not hexFilter. Pcs.yul has no AST today.
- `Midfall.Lowering.Lowered / Supported / Deployment (existing placeholders)` (formal/Midfall/Lowering/Types.lean:34)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject | structure Supported (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat) (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where (51) | structure Deployment (vkRuntime : Bytes) (evaluator : Option YulObject) (vkCodehash quotientCodehash : H256) : Prop where (71)
    notes: These names are already taken in namespace Midfall.Lowering. Lowered lacks plan/shell/consts. Supported is over raw Nats, with no layout, noRotInst, acc or vkPoints fields. Deployment's fields are all `True`. Midfall.Lowering.GeneratorError (:41) differs from Midfall.Generator.GeneratorError (Api.lean:309). The untracked Lowering/SemanticEquivalence.lean:29 already proves contractRefAccepts_iff_verifyMsgs.

## verbatim excerpts

### formal/Midfall/Generator/Templates.lean:309
```lean
def Halo2VerifyingKey.constructorReturnStmt (self : Halo2VerifyingKey) : Stmt EVM.Op :=
  .exprStmt (.builtin EVM.Op.ret
    [ .var "runtime",
      .lit (Literal.number (1 + 32 * (self.constants.length
        + 4 * self.fixedComms.length + 4 * self.permutationComms.length))) ])

/-- The whole constructor body as a vendored block, braces excluded: what the
    template emits between `assembly {` and its closing brace. The final
    `return` is the dialect built-in `EVM.Op.ret`, whose source name is
    "return" (vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean:169). -/
def Halo2VerifyingKey.constructorStmts (self : Halo2VerifyingKey) : Block EVM.Op :=
  vkSetupStmts self ++ vkConstantStmts self
    ++ vkCommStmts self.constants.length self.fixedComms
    ++ vkCommStmts (self.constants.length + 4 * self.fixedComms.length) self.permutationComms
    ++ [(constructorReturnStmt self)]
```

### formal/Midfall/Generator/Render.lean:173
```lean
inductive Line where
  | code (lvl : Nat) (s : Stmt EVM.Op)
  | text (raw : String)
  /-- Template text appended to the PREVIOUS line: a trailing comment
      ('mstore(add(scratch, 0x00), 0x20)        // base len', dump:357) or a
      comment that shares a line with a closing brace ('}            // ===',
      deployed P:1413 - that one exists ONLY in the deployed artifact; no line of
      the dump has a '}' followed by a comment). Note what 'tail' cannot do: it
      extends the CURRENT line, so a comment inside a statement that is still
      open (loss class 3, dump:1902-1904) has nowhere to go. -/
  | tail (raw : String)
```

### formal/Midfall/Generator/YulGolden.lean:665
```lean
def smoke_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq smoke_ast smoke_direct
def scalarInv_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq scalarInv_ast scalarInv_direct
def batchInv_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq batchInv_ast batchInv_direct
def lagrangeFor_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq lagrangeFor_ast lagrangeFor_direct
def vmSwitch_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq vmSwitch_ast vmSwitch_direct
def pcsBasis_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq pcsBasis_ast pcsBasis_direct
def spread_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq spread_ast spread_direct
def vkHead_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq vkHead_ast vkHead_direct
def vkComms_beq_ok : Bool := YulSemantics.SyntaxEq.stmtsBeq vkComms_ast vkComms_direct

/-- All nine under the authoritative relation. -/
def golden_beq_all_ok : Bool :=
  smoke_beq_ok && scalarInv_beq_ok && batchInv_beq_ok && lagrangeFor_beq_ok &&
  vmSwitch_beq_ok && pcsBasis_beq_ok && spread_beq_ok && vkHead_beq_ok &&
  vkComms_beq_ok
```

### formal/Midfall/Generator/Layout.lean:443
```lean
inductive MemoryLifetime
  /-- MEM:161: live after being written; must never overlap another live region. -/
  | permanent
  /-- MEM:164: live only during the named phase. -/
  | phase (memoryPhase : MemoryPhase)
  deriving BEq

/-- rust: MEM:169-174 (`MemoryLifetime::intersects`) @formal-baseline. Private
    in the reference. -/
def memoryLifetimeIntersects : MemoryLifetime → MemoryLifetime → Bool
  | .permanent, _ => true
  | _, .permanent => true
  | .phase lhs, .phase rhs => lhs == rhs
```

### formal/Midfall/Generator/Layout.lean:1114
```lean
def MemoryMap.wellFormedBool (self : MemoryMap) : Bool :=
  self.regions.all (fun region =>
    region.len == 0 || region.start % wordBytes == 0)
    && self.regions.all (fun region =>
      region.len == 0 || solidityReservedMemoryBytes <= region.start)
    && memoryRegionsPairwiseDisjoint self.regions

/-- `WellFormed` is decidable BY CONSTRUCTION, and that is the whole claim: the
    Prop is the Bool equality `wellFormedBool = true`, so the instance below is
    `instDecidableEqBool` applied to that one value - no search and no proof
    component. Nothing further is claimed: it is not proved equivalent to
    `MemoryMap.validate = .ok ()`, and the two divergences listed on
    `wellFormedBool` make it strictly weaker than `validate`. -/
def MemoryMap.WellFormed (self : MemoryMap) : Prop := self.wellFormedBool = true

/-- Decidable by construction, for the reason stated on `MemoryMap.WellFormed`. -/
instance (self : MemoryMap) : Decidable self.WellFormed :=
  instDecidableEqBool self.wellFormedBool true
```

### formal/Midfall/Generator/Layout.lean:728
```lean
def transcriptBufferStart : Nat := lowMemoryScratchStart

/-- rust: LM:48 (`PCS_PAIRING_SCRATCH_START`) @formal-baseline. -/
def pcsPairingScratchStart : Nat := lowMemoryScratchStart

/-- rust: LM:50 (`VERIFIER_RETURN_BUFFER_START`) @formal-baseline. -/
def verifierReturnBufferStart : Nat := lowMemoryScratchStart

/-- rust: LM:52 (`QUOTIENT_RETURN_BUFFER_START`) @formal-baseline. -/
def quotientReturnBufferStart : Nat := lowMemoryScratchStart

/-- rust: LM:313 (`accumulator::PAIRING_BATCH_PTR`) @formal-baseline. -/
def accumulatorPairingBatchPtr : Nat := lowMemoryScratchStart

/-- rust: LM:348 (`accumulator::PAIRING_BATCH_HASH_BYTES`) @formal-baseline.
    Tag word, `vk_digest` word, then four G1 points, which is why the frame ends
    at `0x1240` rather than `0x1220` (LM:113-115). -/
def accumulatorPairingBatchHashBytes : Nat := 2 * wordBytes + 4 * g1Bytes

/-- rust: LM:121-122 (`FINAL_PAIRING_SCRATCH_START`) @formal-baseline. -/
def finalPairingScratchStart : Nat := accumulatorPairingBatchPtr
  + accumulatorPairingBatchHashBytes
```

### formal/Midfall/Generator/LayoutMemory.lean:190
```lean
  let (arena7, vkStart) :=
    arena6.allocFixed "vk_payload" ((ptrValue vkMptr).asUsizeNat) vk.len
      MemoryLifetime.permanent
  let (arena8, scalarInvScratchMptr) :=
    arena7.allocPhaseScratch "scalar_inv_scratch" (vkStart - modexpScratchBytes)
      modexpFrameBytes MemoryPhase.scalarInv
  let (arena9, challengeStart) :=
    arena8.allocAfter "challenge_slots" vkStart vk.len
      (meta_.challengeIndices.length * wordBytes) MemoryLifetime.permanent
  let (arena10, thetaStart) :=
    arena9.allocAfter "theta_scalar_and_g1_slots" challengeStart
      (meta_.challengeIndices.length * wordBytes)
      (thetaWindows.rotPointsWord * wordBytes) MemoryLifetime.permanent
  let challengeMptr := ptrMemory (valueFromNat challengeStart)
  let atTheta : Nat → Nat := fun words => thetaStart + words * wordBytes
  let ptrAtTheta : ThetaSlot → Ptr := fun slot => ptrMemory (valueFromNat (atTheta
  slot.word))
  let thetaMptr := ptrAtTheta ThetaSlot.theta
```

### formal/Midfall/Generator/Protocol.lean:315
```lean
structure ProofReadPlan where
  /-- rust: PM:152 (commitments: Vec<CommitmentRead>) - G1 commitment reads in
      transcript order. -/
  commitments : List CommitmentRead
  /-- rust: PM:154 (evals: Vec<EvalRead>) - scalar evaluation reads in proof
      order. -/
  evals : List EvalRead
  deriving BEq
```


# AREA: Generator port, encoding/abi/kzg/vk/api side: formal/Midfall/Generator/{Abi,Encoding,Kzg,Vk,Api}.lean, plus the adjacent defs they lean on (Quotient/VmTypes.lean RepackedProofLayoutPlan, Models.lean Halo2VerifyingKey/G1W

## constraints
- Nothing in Abi/Encoding/Kzg/Vk/Api is a theorem. Every item is an executable def with no sorry, partial or axiom. The '_ok' gates are #eval Bool KATs enforced by formal/scripts/kat_gate.py (run from checks.sh:67), not by lake build. A theorem file can only cite defs and must not rely on gates as lemmas.
- Location, Value (Filters.lean:70,78), Ptr (Models.lean:506), Word, EcPoint, Data, Query, CommitmentEntry, IntermediateSets and TrackedG1 have NO BEq/DecidableEq instance. Use Prop `=`, or the structural Bool comparators valueBeq/locationBeq/ptrBeq/wordBeq/ecPointBeq (Kzg.lean:260-281). ConstraintSystemMeta, ProofSection, ProofCalldataLayout, TranscriptBufferLayout, RepackedProofLayoutPlan, AccumulatorEncoding, GeneratorConfig, RenderOptions, RepackError, GeneratorError, ApiFault, DummyQuery and QEvalStrategy all derive BEq.
- Name trap: Midfall.Generator.Word (Encoding.lean:289) is a POINTER newtype that renders as calldataload/mload. Midfall.Word256 := BitVec 256 (Common/Bytes.lean:21) is the 256-bit value. Under `open Midfall.Generator`, `Word` means the pointer.
- Name trap: three error types. Midfall.Generator.GeneratorError (Api.lean:309) is the faithful one. Midfall.Lowering.GeneratorError (Lowering/Types.lean:41) is a placeholder with only planning/render arms. Midfall.Generator.ApiFault (Api.lean:396) wraps GeneratorError plus a panic site. Plan 9.5's `g.lower o : Except GeneratorError Lowered` must say which one it means.
- D-P16 (design.md): PLAN 9.5's Supported.acc, decodeAcc and encodeAccInstances refer to Midfall.Generator.AccumulatorEncoding (Api.lean:413), not the Exec stand-in Midfall.Halo2.AccumulatorEncoding (Exec/Accumulator.lean:167-261). Supported.acc as written uses `enc.validFor n`, a Bool on the Exec stand-in. The faithful form is `AccumulatorEncoding.validateForNumInstances enc n = .ok ()` in Except ApiFault Unit. A reconciliation lemma (validFor ↔ validateForNumInstances = ok, with agreeing word counts) is an owed obligation before any accumulator statement can be cited about the deployment.
- Error channels differ by file. Abi/Encoding/Kzg/Vk return `Except Fault _` (Fault = .error Halo2.Error | .panic site, with no payload, R-43 F2). Api returns `Except ApiFault _`. validateAgainstProtocol, VkHeaderBuilder.* and VkPayloadLayout.* return `Except String _`. validateAbsorbedG1PrecompileCoverage returns `Except Fault (Except String Unit)` and must not be collapsed. Statements can only distinguish panics by the site string.
- Kzg.computations returns Yul as TEXT, `Except Fault (List (List String))`, with block order [block1] ++ [block2 if nbX1Powers>0] ++ block3(per set) ++ [trace if trace] ++ [block4, block5, block6]. There is no Yul AST for the PCS partial in the tree, so pcs_spec cannot be stated over computations' output without a parse/elaboration step or an AST-producing lower. R-39 (REVIEW.md:1157): render_eq_print is false as a text equality (comments inside statements and 91 Solidity constants are not representable in the Yul AST). Restate it structurally, e.g. stmtsBeq (astOf (g.render o)) ((g.lower o).main), and leave formatting outside the obligation.
- Calldata vs memory: Data's eval Words are MEMORY pointers at reversedEvalsMptr (Encoding.lean:632-633, ENC:347-354), and its proof commitments are memory pointers at layout bases. The only calldata-offset model is ProofCalldataLayout (Abi.lean:209). In the Kzg Yul, only the q_evals are read straight from calldata, through `calldataload(add(Q_EVAL_CPTR, s*0x20))` with Q_EVAL_CPTR loaded from Q_EVAL_CPTR_MPTR. Any repack/calldata theorem must go through ProofCalldataLayout plus the transcript parser's copy-to-memory invariant.
- proofCptr: production uses abiVerifyProofProofCptr = 0x64 (Rust plan.rs:169-178). Vk.transcriptBufferLayoutForMeta (Vk.lean:948) and LayoutMemory.lean:656 call fromProtocol with proofCptr = 0 for sizing only. Section offsets are byte offsets relative to the start of calldata, including the 4-byte selector.
- Abi's ProofCalldataLayout.commitmentReadGroups is not ProtocolPlan.commitmentReadGroups. They agree only on layouts produced by fromProtocol (Abi.lean:446-458). Repack order is driven by the Abi one via RepackedProofLayoutPlan.fromProofLayout (VmTypes.lean:720).
- D-P14 truncation at use site: computations takes `truncatedChallenges : Bool` (deployed = true; Models.Halo2Verifier.truncatedChallenges, Models.lean:855). Block 2 keeps acc at full precision and stores `and(acc, truncMask128)` for x1^1..x1^(n-1), with x1^0 stored as literal 1 (Kzg.lean:1367-1379). Block 5 keeps x4_pow_full at full precision and binds x4_pow_s := and(x4_pow_full, mask) (Kzg.lean:1626-1633). The x4^0 coefficient is implicit 1 (`let v := calldataload(Q_EVAL_CPTR)`). x2 and x3 are read raw from X2_MPTR/X3_MPTR inside Kzg. x3's truncation happens at squeeze time in templates/partials/verifier/TranscriptProofParser.yul:354-365, outside Kzg. So pcs_spec must be parameterised on Features.truncatedChallenges, and the Inv .transcript precondition must already carry truncate(x3). The algebraic target is the Exec multiPrepare (Exec/Kzg/MultiOpen.lean:201) with truncated_powers.
- outerFewerPointSets is false in Features.solidity. intermediateSets therefore takes the raw branch (data.dummyEvalWords = []), and metaDataForVk sets numDummy = 0. Statements may assume this via Supported or state both branches.
- Commitment identity in the generator is POINTER identity (EcPoint over a symbolic Ptr; Kzg hazard 2). committedInstance commitments all alias G1_IDENTITY_MPTR. The Phase 4 bridge constructIntermediateSetsImpl ↔ Exec constructIntermediateSets (Exec/Kzg/Utils.lean:123, which takes eqC on CommitmentReference) needs a slot-to-commitment map that is injective on distinct slots. Point sets in the generator are rotations (List Int), not field points.
- Vk.lean: all defs share the variable block at Vk.lean:294-301. AdmissiblePairing has p and Gₜ as outParam (Common/Curve.lean:35-36), so Gₜ is inferred and not phantom here. By contrast DualMSM's Gₜ IS phantom and must be named explicitly (Lowering/Types.lean:93). VerifierBuildInputs.params is the generator ParamsKZG G₁ G₂ (gLagrange, g2, sG2), not ParamsVerifierKZG. A theorem linking the VK header to the Exec verifier needs a hypothesis relating ParamsKZG.{g2,sG2} to ParamsVerifierKZG.
- Point encoding in Vk goes through VkPointCodecs (g1Repr/g2Repr into G1AffineRepr/G2AffineRepr), not Common.G1Codec. No law in the tree relates VkPointCodecs.g1Repr followed by g1ToU256s to G1Codec.toEip. Any theorem tying VK payload words or calldata G1 words to curve points must take that compatibility as an explicit hypothesis. The concrete codec checks on-curve only, not subgroup (Codec.lean:69-74).
- srsTauIsConsistent's correctness lemma is NOT statable today (R-47, F-P08-2, Vk.lean:112-129). Nothing states that omega has order exactly n (needs FieldConsts.IsWellFormed / EvaluationDomain.IsPrimitive), and the Lagrange closed form is absent. Abstract it as a hypothesis structure.
- F-P08-9: PLAN 9.5 Supported has no field for 'quotient const table within VK reservation' (generateVk panic vk.rs:436). The only witness is generateVk returning .ok.
- R-25: decodeAcc_injective is FALSE as written. Identity-flagged coordinate words are neither decoded nor range-checked (AccumulatorHelpers.yul:130-141). The fix is to project accWords to (0,0,1) for flagged points. R-26 #2: decodeAcc_encode is only statable for collapsed accumulator shapes. R-26 tail: decodeAcc needs 4 args (encoding, codec, generated fixed-base list, instance words), not 2. The generated fixed-base list is Halo2Verifier.accFixedBases : List (Nat × Bool) (Models.lean:868), whose producer artifacts.rs:181-227 is unported. R-26 #3: the contract negates the public scalar and uses the positive base, while the circuit uses a negated base.
- calldata_canonical: Fr p = ZMod p cannot represent words ≥ r, and the contract rejects non-canonical scalars and instance words. decodeCalldata/calldataOf must therefore be typed over raw Bytes/Word256 (R-26 #7, PLAN.md:568). The plan comment allows weakening to ≈ if trailing bytes are accepted.
- PLAN 9.5 direct_correct's hypothesis `o.quotient = .direct` does not typecheck against Api.lean. o.quotient : RenderQuotient has only .inline and .externalPinned. The Direct lowering is `o.quotientLowering = QuotientLowering.direct` (Api.lean:886,950), and Rust says it is only supported with RenderQuotient.inline (API:459).
- points_subgroup_checked: the generator-side witness is validateAbsorbedG1PrecompileCoverage (Kzg.lean:1099), returning .ok (.ok ()). It proves coverage of absorbed points by later G1MSM/pairing inputs only, and EIP-2537 G1ADD does not subgroup-check (PLAN.md:567). Gates must use non-degenerate memory fixtures: the shared LayoutKats fixture has all PCS bases at 0, which makes point comparisons vacuous (R-48).
- AccumulatorEncoding.coordinateWords panics (ApiFault.panic "proofs/solidity-verifier/src/api.rs:104") when numLimbBits = 0, so it is reachable only via pub(crate) point_words. fixedScalarCount uses wrapping usize arithmetic (usizeAdd/usizeSub), and the usizeMax sentinel in fullyCollapsedPublicInputWords makes wrap reachable (F-3).
- Rust repack facts a repack_spec must match (calldata.rs:43-128, unported). Groups come from commitmentReadGroups, then numEvals scalars, then f_com, then numPointSets scalars, then pi. Each compressed G1 (48 B) is decoded via GroupEncoding::from_bytes, which is on-curve plus torsion-free: G1Codec.ofCompressed? (Common/Codec.lean:82). Each decoded point is emitted as 128 B: zeros for the identity, else 16 zero bytes ‖ x_BE ‖ 16 zero bytes ‖ y_BE, i.e. G1Codec.toEip. Each scalar is 32 B LE; non-canonical ones are rejected with RepackError.nonCanonicalScalar, and canonical ones are emitted as BE words. A wrong total length gives RepackError.lengthMismatch against RepackedProofLayoutPlan.compressedLen. encode_calldata (calldata.rs:132-149) first checks instances.len == num_instances, else GeneratorError.planning "calldata" "instance length mismatch: expected {n}, got {m}". It then emits evm.rs:22-38: selector 0x1e8e1e13 ‖ BE32(0x40) ‖ BE32(0x40+0x20+len) ‖ BE32(len) ‖ proof ‖ BE32(numInst) ‖ instances as BE32 of fe_to_u256 (LE repr).
- Data.new, the Kzg functions and memoryLayoutFor all take (meta_, data, memory) as produced by Vk.metaDataForStableStaticLayout. The Rust LoweringPlan (plan.rs:29) that bundles vk, vk_mptr, meta, data and proof_layout is unported, so L.plan in PLAN 9.5 must currently be modelled as a structure variable carrying these five fields plus the hypothesis that they came from metaDataForStableStaticLayout and fromProtocol at 0x64.

## missing
- repackProof: Rust calldata.rs:43-128 (VerifierBuildInputs::repack_proof). No Lean port. Lean has only its frame plan (RepackedProofLayoutPlan, Quotient/VmTypes.lean:703-765) and its error type (RepackError, Api.lean:257). It would be built from G1Codec.ofCompressed?/toEip (Common/Codec.lean:81-85) and a scalar LE→BE helper.
- scalar_le_to_be_word: Rust quotient_numerator/vm/mod.rs:934-944 (QVM). Explicitly not ported (VmTypes.lean:62-64, 'belongs with the repacker').
- encodeCalldata: Rust calldata.rs:132-149 (VerifierBuildInputs::encode_calldata) plus evm.rs:22-38 (encode_calldata) and evm.rs:15 (FN_SIG_VERIFY_PROOF = [0x1e,0x8e,0x1e,0x13]). Not ported. Only the helpers feToU256 and toU256BeBytes (Encoding.lean:1008,1024) exist.
- encodeContractProof / decodeCalldata / calldataOf (PLAN 9.5). No Lean defs and no Rust function counterpart. The contract-side decoder exists only as Yul (templates/partials/verifier/TranscriptProofParser.yul, VkLoading.yul). They must be defined fresh over ProofCalldataLayout (Abi.lean:209) + G1Codec.toEip + frWord (Exec/Accumulator.lean:433), typed over raw Bytes/Word256.
- LoweringPlan: Rust lowering/plan.rs:29-... (struct plus LoweringPlan::new / new_direct plan.rs:165-, and repacked_proof_layout_plan plan.rs:332-334). Not ported. Lean would bundle vk : Halo2VerifyingKey, vkMptr : Ptr, meta : ConstraintSystemMeta, data : Data, proofLayout : ProofCalldataLayout, quotient lowering and memory.
- SolidityGenerator / try_new / lower / render: Rust builder/api.rs (162 lines, try_new validation at :38-61) and builder/render.rs. Not ported. Lowering/Types.lean:34 Lowered lacks the plan/shell/consts fields.
- artifacts.rs (Halo2Verifier model assembly): Rust lowering/artifacts.rs. Not ported. This includes the accumulator fixed-base list computation (artifacts.rs:181-227 → Halo2Verifier.accFixedBases) and the truncated_challenges forwarding into computations (artifacts.rs:151-157).
- Halo2Verifier::validate_layout (render/models.rs:830-952) and Halo2QuotientEvaluator::validate_layout (models.rs:965-1005). Deferred (Abi.lean:35-38); needed for Supported.layout / memory WellFormed.
- quotient.rs callees threaded abstractly through VkBuildEnv (Vk.lean:405-421): compact_quotient_program_for (quotient.rs:165-181), quotient_program_plan (quotient.rs:425-430), build_quotient_program_items (quotient.rs:2101-2110). Needed to instantiate generateVk concretely.
- A Yul AST for the PCS partial: kzg/mod.rs computations is ported as String lines only. pcs_spec needs either an AST-producing variant or a parse of the emitted text into YulSemantics.Block.
- The Phase 4 bridge lemma: generator Kzg.constructIntermediateSetsImpl + sortSets (Kzg.lean:797,899) versus Exec constructIntermediateSets (Exec/Kzg/Utils.lean:123). No statement exists.
- A compatibility law between VkPointCodecs (Vk.lean:327) and Common.G1Codec.toEip. It does not exist and must be a hypothesis.
- EvaluationDomain.IsPrimitive / FieldConsts.IsWellFormed (plans/P-4a-roots.md) and the Lagrange closed form, needed to state srsTauIsConsistent's semantic content (R-47, F-P08-2). Missing.
- Reconciliation lemma between Midfall.Generator.AccumulatorEncoding.validateForNumInstances and the Exec stand-in validFor (D-P16 point 3). Missing.

## declarations
- `Midfall.Generator.abiVerifyProofProofCptr` (formal/Midfall/Generator/Abi.lean:132)
    sig: def abiVerifyProofProofCptr : Nat := abiSelectorBytes + abiVerifyProofHeadBytes + wordBytes
    notes: = 4 + 2*32 + 32 = 0x64. The calldata byte offset of the first proof payload byte. Production LoweringPlan passes it as proofCptr (Rust plan.rs:169-178). Siblings: abiSelectorBytes L120 (=4), abiVerifyProofHeadWords L123 (=2), abiVerifyProofHeadBytes L126, abiVerifyProofProofHeadOffset L139. transcriptWordAbsorbBytes L111 = wordBytes, transcriptG1AbsorbBytes L114 = g1Bytes (128), transcriptPostSqueezeCushionWords L117 = 32.
- `Midfall.Generator.ProofSection` (formal/Midfall/Generator/Abi.lean:145)
    sig: structure ProofSection where start : Nat itemCount : Nat itemBytes : Nat byteLen : Nat deriving BEq
    notes: AP:13-23. Byte offsets into calldata. byteLen is derived by ProofSection.new (L175 `def ProofSection.new (start itemCount itemBytes : Nat) : ProofSection`, byteLen := itemCount * itemBytes) and is never recomputed, so a hand-built section can be inconsistent. ProofSection.end L185 `def ProofSection.end (self : ProofSection) : Nat := self.start + self.byteLen`. proofSectionDefault L159.
- `Midfall.Generator.ProofCalldataLayout` (formal/Midfall/Generator/Abi.lean:209)
    sig: structure ProofCalldataLayout where proofCptr : Nat advicePhases : List ProofSection lookupMultiplicities : ProofSection permutationProducts : ProofSection lookups : List ProofLookupCommitmentsLayout trash : ProofSection quotientLimbs : ProofSection evals : ProofSection fCom : ProofSection qEvals : ProofSection pi : ProofSection quotientCommCptr : Nat evalCptr : Nat wCptr : Nat qEvalCptr : Nat proofEnd : Nat proofLen : Nat deriving BEq
    notes: AP:54-90. The contract-side proof calldata map: G1 sections have itemBytes = g1Bytes (128, EIP-2537 padded) and scalar sections have wordBytes (32). ProofLookupCommitmentsLayout L191 = {lookup : Nat, helpers accumulator : ProofSection} deriving BEq. proofCalldataLayoutDefault L254. This type is the only place proof calldata offsets exist in Lean.
- `Midfall.Generator.ProofCalldataLayout.takeCommitmentSection` (formal/Midfall/Generator/Abi.lean:292)
    sig: def ProofCalldataLayout.takeCommitmentSection (protocol : ProtocolPlan) (readIdx cursor : Nat) (expected : CommitmentRead) (count : Nat) (_label : String) : Except Fault (ProofSection × Nat × Nat)
    notes: AP:95-115, private in Rust. Reserves count G1s at cursor and checks protocol.proof.commitments[idx]? == some expected for each one. A mismatch is Fault.panic "proofs/solidity-verifier/src/lowering/abi/proof.rs:106". The label is dropped. Returns (section, readIdx', section.end). The scalar companion is wordSection L314 `def ProofCalldataLayout.wordSection (cursor itemCount : Nat) : ProofSection × Nat`.
- `Midfall.Generator.ProofCalldataLayout.fromProtocol` (formal/Midfall/Generator/Abi.lean:334)
    sig: def ProofCalldataLayout.fromProtocol (protocol : ProtocolPlan) (proofCptr numEvals numPointSets : Nat) : Except Fault ProofCalldataLayout
    notes: AP:122-245. Computes the proof read schedule as calldata byte offsets. Order: advice per user phase, lookup multiplicities, permutation products, per lookup (helpers then accumulator), trash, quotient limbs (quotientCommCptr snapshotted before them), then a check that every planned commitment was consumed (panic site abi/proof.rs:210). After that: evals (evalCptr, numEvals words), fCom (wCptr, 1 G1), qEvals (qEvalCptr, numPointSets words), pi (1 G1). proofEnd is the last cursor and proofLen = proofEnd - proofCptr. Production callers pass proofCptr = 0x64. The sizing callers pass 0: Vk.transcriptBufferLayoutForMeta (Vk.lean:948) and LayoutMemory.lean:656.
- `Midfall.Generator.ProofCalldataLayout.{nonQuotientG1Count,commitmentG1Count,totalG1Count}` (formal/Midfall/Generator/Abi.lean:423)
    sig: def ProofCalldataLayout.nonQuotientG1Count (self : ProofCalldataLayout) : Nat def ProofCalldataLayout.commitmentG1Count (self : ProofCalldataLayout) : Nat -- L432 def ProofCalldataLayout.totalG1Count (self : ProofCalldataLayout) : Nat -- L440
    notes: AP:248-268. totalG1Count = commitmentG1Count + fCom.itemCount + pi.itemCount. It is the RHS of Kzg.validateAbsorbedG1PrecompileCoverage's count check.
- `Midfall.Generator.ProofCalldataLayout.commitmentReadGroups` (formal/Midfall/Generator/Abi.lean:472)
    sig: def ProofCalldataLayout.commitmentReadGroups (self : ProofCalldataLayout) : List Nat
    notes: AP:271-292. G1 group sizes in repack order: non-zero advice phases, then non-zero [mult, permZ], then per-lookup [helpers, acc] UNFILTERED, then trash if non-zero, then quotient limbs always. This is not ProtocolPlan.commitmentReadGroups (Protocol.lean). The two agree only on fromProtocol outputs (Abi.lean:446-458, gated by commitmentReadGroups_agreesWithProtocolPlan_ok and _disagreeWhenHandBuilt_ok).
- `Midfall.Generator.TranscriptBufferLayout.fromProofLayout` (formal/Midfall/Generator/Abi.lean:530)
    sig: def TranscriptBufferLayout.fromProofLayout (proof : ProofCalldataLayout) (numInstances : Nat) (phaseChallengeCounts : List Nat) : TranscriptBufferLayout
    notes: AP:318-368. The struct is at L487 (initialRunBytes evalRunBytes totalRunBytes words : Nat, deriving BEq). It is a conservative streaming-Keccak buffer bound containing the 6b3d209 fix: the pre-squeeze run includes advice phases up to and including the first phase that has a challenge. It is relevant to transcriptParser_spec memory-safety (the buffer must not overrun VK_MPTR).
- `Midfall.Generator.RepackedProofLayoutPlan (+ fromProofLayout, prefixG1Count, compressedLen, repackedLen, scalarLayout)` (formal/Midfall/Generator/Quotient/VmTypes.lean:703)
    sig: structure RepackedProofLayoutPlan where g1Groups : List Nat numEvals : Nat numPointSets : Nat deriving BEq def RepackedProofLayoutPlan.fromProofLayout (layout : ProofCalldataLayout) : RepackedProofLayoutPlan -- L720 def RepackedProofLayoutPlan.prefixG1Count (self : RepackedProofLayoutPlan) : Nat -- L729 def RepackedProofLayoutPlan.compressedLen (self : RepackedProofLayoutPlan) : Nat -- L739 def RepackedProofLayoutPlan.repackedLen (self : RepackedProofLayoutPlan) : Nat -- L748 def RepackedProofLayoutPlan.scalarLayout (self : RepackedProofLayoutPlan) : RepackedProofScalarLayout -- L758
    notes: QVM:167-225. This is the only ported piece of the repack path: the frame shape. fromProofLayout = {g1Groups := layout.commitmentReadGroups, numEvals := layout.evals.itemCount, numPointSets := layout.qEvals.itemCount}. compressedLen uses g1CompressedBytes (48, Api.lean:164) and repackedLen uses g1Bytes (128). RepackedProofScalarLayout (L691) and scalarLayout are test-only in Rust. Rust calldata.rs:43 repack_proof itself is not ported.
- `Midfall.Generator.Location / Value / Ptr` (formal/Midfall/Generator/Filters.lean:70)
    sig: inductive Location where | calldata | memory -- Filters.lean:78 inductive Value where | integer (i : Int) | identifier (name : String) (off : Int) -- Models.lean:506 structure Ptr where loc : Location value : Value
    notes: ENC:573-592, ENC:680-684. NO BEq/DecidableEq on any of these. Value.identifier is a symbolic Yul identifier plus a signed byte offset. Display: printValue (Filters.lean:87), printPtr (Filters.lean:98), and printWord loc v (Filters.lean:104), which gives "calldataload(..)" or "mload(..)". Constructors: ptrMemory/ptrCalldata (Models.lean:509/512) and valueFromNat (Models.lean:525). Value.asUsize is at Layout.lean:996.
- `Midfall.Generator.Value.add / Value.sub / Ptr.new / Ptr.add / Ptr.sub` (formal/Midfall/Generator/Encoding.lean:249)
    sig: def Value.add (self : Value) (rhs : Nat) : Value def Value.sub (self : Value) (rhs : Nat) : Value -- L259 def Ptr.new (loc : Location) (value : Value) : Ptr -- L268 def Ptr.add (self : Ptr) (rhs : Nat) : Ptr -- L276 def Ptr.sub (self : Ptr) (rhs : Nat) : Ptr -- L280
    notes: Arithmetic is in WORDS: rhs * wordBytes is added to the byte offset. Ptr.add preserves loc.
- `Midfall.Generator.Word` (formal/Midfall/Generator/Encoding.lean:289)
    sig: structure Word where ptr : Ptr
    notes: ENC:743-744. A pointer handle to a 32-byte slot. It is NOT Midfall.Word256 (BitVec 256, Common/Bytes.lean:21). Related: Word.fromPtr L294, Word.ptrOf L299 (abbrev), Word.loc L302, Word.range L310 `def Word.range (w : Word) : Nat → Word` (stride 1 word), wordKey L318 (renders the emitted Yul load text). No BEq.
- `Midfall.Generator.EcPoint / EcPoint.range / LookupEvalSlots` (formal/Midfall/Generator/Encoding.lean:322)
    sig: structure EcPoint where base : Ptr def EcPoint.range (p : EcPoint) : Nat → EcPoint -- L343 abbrev LookupEvalSlots := Option Word × List (Option Word) × Option Word × Option Word -- L352
    notes: EcPoint is the base pointer of a 4-word EIP-2537 G1. EcPoint.range's stride is the literal 4 words, not g1WordsCount. LookupEvalSlots holds the multiplicity, helpers, accumulator-cur and accumulator-next slots. Also EcPoint.new L331, EcPoint.fromPtr L334, EcPoint.ptr L347.
- `Midfall.Generator.ConstraintSystemMeta` (formal/Midfall/Generator/Encoding.lean:364)
    sig: structure ConstraintSystemMeta where protocol : ProtocolPlan numFixeds : Nat permutationColumns : List Column permutationChunkLen : Nat numLookups : Nat lookupChunks : List Nat numTrashcans : Nat numPermutationZs : Nat numQuotients : Nat adviceQueries : List (Nat × Int) instanceQueries : List (Nat × Int) numSimpleSelectors : Nat simpleSelectorCols : List Nat numCommittedInstances : Nat numEvals : Nat numDummyEvals : Nat numPointSets : Nat numUserAdvices : List Nat numUserChallenges : List Nat adviceIndices : List Nat challengeIndices : List Nat rotationLast : Int deriving BEq
    notes: ENC:70-132. numPointSets and numDummyEvals start at 0 and are filled later by Vk.metaDataForVk. Defined in a `mutual` block (443-529): ConstraintSystemMeta.new L454, validateAgainstProtocol L490 `(self : ConstraintSystemMeta) : Except String Unit`, setNumPointSets L505, setNumDummyEvals L513 (also increments numEvals), numMainEvals L526 (= numEvals - numDummyEvals).
- `Midfall.Generator.ConstraintSystemMeta.new` (formal/Midfall/Generator/Encoding.lean:454)
    sig: def ConstraintSystemMeta.new {F : Type} (feat : Features) (cs : ConstraintSystem F) (nbCommittedInstances : Nat) : Except Fault ConstraintSystemMeta
    notes: ENC:141-168. Wraps ProtocolPlan.fromConstraintSystem feat cs nbCommittedInstances. The Rust has no Features arg; R8 makes it explicit.
- `Midfall.Generator.Data` (formal/Midfall/Generator/Encoding.lean:551)
    sig: structure Data where challengeMptr : Ptr thetaMptr : Ptr fixedComms : List EcPoint permutationComms : List (Column × EcPoint) adviceComms : List EcPoint committedInstanceComms : List EcPoint permutationZComms : List EcPoint lookupMComms : List EcPoint lookupHelperComms : List (List EcPoint) lookupZComms : List EcPoint trashcanComms : List EcPoint challenges : List Word instanceEval : Word committedInstanceEvals : List ((Nat × Int) × Word) adviceEvals : List ((Nat × Int) × Word) fixedEvals : List ((Nat × Int) × Word) permutationEvals : List (Column × Word) permutationZEvals : List (Word × Word × Option Word) lookupEvals : List (Word × List Word × Word × Word) trashcanEvals : List Word computedQuotientComm : EcPoint computedQuotientEval : Word commsMptrBase : Ptr reversedEvalsMptr : Ptr dummyEvalWords : List Word
    notes: ENC:226-294. The four HashMaps are association lists (hashMapInsert L179, hashMapGet L187). No BEq, no Default. Every eval Word is a MEMORY pointer at reversedEvalsMptr + i words, not a calldata pointer. Every proof commitment is a memory pointer at a layout base. committedInstanceComms are all G1_IDENTITY_MPTR. Helper record DataEvalSlots L537.
- `Midfall.Generator.Data.new` (formal/Midfall/Generator/Encoding.lean:623)
    sig: def Data.new (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (memory : VerifierMemoryLayout) : Except Fault Data
    notes: ENC:302-553. The binding table every emitter uses. Panic sites (encoding/mod.rs): :432 (eval plan length), :453/:461/:468/:472/:476/:480 (slot index or rotation), :489/:490/:498/:504/:508/:510/:517 (unfilled slot). Data.setDummyEvalWords L854 `def Data.setDummyEvalWords (self : Data) (numMainEvals n : Nat) : Data`.
- `Midfall.Generator.fp48BeToHiLo / G1AffineRepr / G2AffineRepr / g1ToU256s / g2ToU256s / feToU256 / toU256BeBytes` (formal/Midfall/Generator/Encoding.lean:898)
    sig: def fp48BeToHiLo (be : List Nat) : Except Fault (Word256 × Word256) structure G1AffineRepr where -- L930 coordinates : Option (List Nat × List Nat) isIdentity : Bool deriving BEq structure G2AffineRepr where -- L939 coordinates : Option ((List Nat × List Nat) × (List Nat × List Nat)) isIdentity : Bool deriving BEq def g1ToU256s (point : G1AffineRepr) : Except Fault (List Word256) -- L950 def g2ToU256s (point : G2AffineRepr) : Except Fault (List Word256) -- L976 def feToU256 (repr : List Nat) : Except Fault Word256 -- L1008 def toU256BeBytes (value : Nat) : List Nat -- L1024
    notes: ENC:816-924, the EIP-2537 encoders. The curve is abstract (D-P1), so a point enters as its LE coordinate reprs. g1ToU256s returns [xHi,xLo,yHi,yLo] with hi = 16 zero bytes ‖ first 16 BE bytes and lo = the last 32 BE bytes, which is the same 128 bytes as Common.G1Codec.toEip's convention. The identity gives 4 zero words. coordinates = none with isIdentity = false panics at encoding/mod.rs:845 (off-curve guard). feToU256 reads a 32-byte LE repr (U256::from_le_bytes). toU256BeBytes truncates mod 2^256 and has no Rust counterpart above that.
- `Midfall.Generator.{valueBeq,locationBeq,ptrBeq,wordBeq,ecPointBeq,g1Identity,truncMask128,linearizationComm}` (formal/Midfall/Generator/Kzg.lean:260)
    sig: def valueBeq : Value → Value → Bool def locationBeq : Location → Location → Bool -- L266 def ptrBeq (a b : Ptr) : Bool := locationBeq a.loc b.loc && valueBeq a.value b.value -- L273 def wordBeq (a b : Word) : Bool := ptrBeq a.ptr b.ptr -- L277 def ecPointBeq (a b : EcPoint) : Bool := ptrBeq a.base b.base -- L281 def g1Identity : EcPoint := EcPoint.new (ptrMemory (valueFromStr "G1_IDENTITY_MPTR")) -- L295 def truncMask128 : String := "0xffffffffffffffffffffffffffffffff" -- L394 def linearizationComm (data : Data) : EcPoint := data.computedQuotientComm -- L400
    notes: Structural pointer comparators, top-level in Midfall.Generator. They are the ONLY Bool equality on these types: commitment identity in the generator is pointer identity (hazard 2). Duplicate copies live in the EncodingKats namespace (Encoding.lean:1083-1094).
- `Midfall.Generator.Query / Query.new` (formal/Midfall/Generator/Kzg.lean:415)
    sig: structure Query where rotation : Int comm : EcPoint eval : Word def Query.new (comm : EcPoint) (rotation : Int) (eval : Word) : Query -- L427
    notes: KZ:68-87. The parameter order (comm, rotation, eval) differs from the field order. No BEq.
- `Midfall.Generator.DummyQuery / computeDummyQueries / augmentQueriesWithDummies` (formal/Midfall/Generator/Kzg.lean:479)
    sig: structure DummyQuery where queryIndex : Nat rotation : Int deriving BEq def computeDummyQueries (queries : List Query) : List DummyQuery -- L499 def augmentQueriesWithDummies (rawQueries : List Query) (dummyEvalWords : List Word) : Except Fault (List Query) -- L545
    notes: The fewer-point-sets helpers. They are dead in the deployed profile (outerFewerPointSets = false), but both branches are ported.
- `Midfall.Generator.CommitmentEntry / IntermediateSets` (formal/Midfall/Generator/Kzg.lean:565)
    sig: structure CommitmentEntry where setIndex : Nat comm : EcPoint evals : List Word structure IntermediateSets where -- L576 commitments : List CommitmentEntry pointSets : List (List Int)
    notes: KZ:397-414. This is the shape the 'Phase 4' lemma (generator partition = Exec constructIntermediateSets) is to be stated over. pointSets are ROTATIONS (Int), not field points. No BEq.
- `Midfall.Generator.queries / assertPermutationQueryOrderIsUpstreamEquivalent / queryFromPlan / constructIntermediateSetsImpl (mutual, L583-875)` (formal/Midfall/Generator/Kzg.lean:596)
    sig: def queries (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault (List Query) def assertPermutationQueryOrderIsUpstreamEquivalent (meta_ : ConstraintSystemMeta) (data : Data) (generatorOrder : List Query) : Except Fault Unit -- L628 def queryFromPlan (source : PcsQuerySource) (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault Query -- L684 def constructIntermediateSetsImpl (queries : List Query) : Except Fault IntermediateSets -- L797
    notes: KZ:96-510. queries maps meta_.protocol.pcsQueries through queryFromPlan. It then asserts the L-2 identity pin (kzg/mod.rs:114: only committed-instance sources may be the identity) and the I-6 upstream permutation-order equivalence. constructIntermediateSetsImpl: dedup by ecPointBeq; a repeated (comm, rot) with a conflicting eval panics at :446; set numbering is BTreeMap insertion order (hazard 1).
- `Midfall.Generator.sortSets / intermediateSets / numPointSets` (formal/Midfall/Generator/Kzg.lean:899)
    sig: def sortSets (input : IntermediateSets) : Except Fault IntermediateSets def intermediateSets (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault IntermediateSets -- L929 def numPointSets (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault Nat -- L940
    notes: sortSets orders by key (len, original index), using a stable insertionSortBy (L342). intermediateSets = queries, then (if data.dummyEvalWords.isEmpty then raw else augment), then constructIntermediateSetsImpl, then sortSets.
- `Midfall.Generator.TrackedG1 / quotientLimbComms / proofAbsorbedG1s / precompileValidatedG1s / validateG1PrecompileCoverage / validateAbsorbedG1PrecompileCoverage` (formal/Midfall/Generator/Kzg.lean:1099)
    sig: structure TrackedG1 where -- L953 label : String point : EcPoint def quotientLimbComms (meta_ : ConstraintSystemMeta) (memory : VerifierMemoryLayout) : List EcPoint -- L978 def proofAbsorbedG1s (meta_ : ConstraintSystemMeta) (data : Data) (memory : VerifierMemoryLayout) : List TrackedG1 -- L993 def precompileValidatedG1s (meta_ : ConstraintSystemMeta) (data : Data) (memory : VerifierMemoryLayout) : Except Fault (List TrackedG1) -- L1037 def validateG1PrecompileCoverage (absorbed : List TrackedG1) (precompileInputs : List TrackedG1) : Except String Unit -- L1066 def validateAbsorbedG1PrecompileCoverage (meta_ : ConstraintSystemMeta) (data : Data) (memory : VerifierMemoryLayout) (proofLayout : ProofCalldataLayout) : Except Fault (Except String Unit) -- L1099
    notes: The generator-side check behind points_subgroup_checked. Absorbed order: advice, lookupM, permZ, helpers, lookupZ, trash, quotient limbs, f_com (memory.fComMptr), pi (memory.piMptr). Its length must equal proofLayout.totalG1Count. The identity is skipped, and linearizationComm is replaced by the limbs. The return type nests Fault (panics) outside String (invariant failure); do not collapse them.
- `Midfall.Generator.{commitmentsBySet, linearizationTermCount, qComTermsForSet, qComTraceTerms, finalMsmShape, qEvalRollThreshold, QEvalStrategy, qEvalStrategy, memoryRequirements, numDummyQueries, staticWorkingMemorySize}` (formal/Midfall/Generator/Kzg.lean:1123)
    sig: def commitmentsBySet (sets : IntermediateSets) (nSets : Nat) : Except Fault (List (List CommitmentEntry)) def linearizationTermCount (meta_ : ConstraintSystemMeta) : Nat -- L1137 def qComTermsForSet (meta_ : ConstraintSystemMeta) (data : Data) (commitmentsInSet : List CommitmentEntry) : Nat -- L1147 def qComTraceTerms (meta_ : ConstraintSystemMeta) (data : Data) (bySet : List (List CommitmentEntry)) : Nat -- L1160 def finalMsmShape (meta_ : ConstraintSystemMeta) (data : Data) (bySet : List (List CommitmentEntry)) : FinalMsmShape -- L1170 def qEvalRollThreshold : Nat := 4 -- L1183 inductive QEvalStrategy | rolled | unrolled deriving BEq -- L1189 def qEvalStrategy (commitments : List CommitmentEntry) : QEvalStrategy -- L1205 def memoryRequirements (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault PcsMemoryRequirements -- L1235 def numDummyQueries (meta_ : ConstraintSystemMeta) (data : Data) : Except Fault Nat -- L1271 def staticWorkingMemorySize : Nat := pcsStaticWorkingWords -- L1282
    notes: The final MSM shape is the sum over non-identity entries (linearization contributes numQuotients + |simpleSelectorCols|) plus 1 for f_com. FinalMsmShape (Layout.lean:872): {terms inputBytes : Nat}, and fromTerms (L880) sets inputBytes := terms * g1MsmPairBytes. PcsMemoryRequirements is at Layout.lean:885.
- `Midfall.Generator.computations` (formal/Midfall/Generator/Kzg.lean:1320)
    sig: def computations (meta_ : ConstraintSystemMeta) (data : Data) (memory : VerifierMemoryLayout) (truncatedChallenges : Bool) (trace : Bool) : Except Fault (List (List String))
    notes: KZ:925-1922, the multi_prepare lowering, emitted as Yul TEXT blocks. If nSets == 0 it returns []. Block order (L1769-1773): [block1] ++ (if nbX1Powers > 0 then [block2]) ++ block3 (one per set) ++ (if trace then [traceBlock]) ++ [block4, block5, block6]. Block1: rotation points ROT_POINTS_MPTR. Block2: x1 powers into X1_POWERS_MPTR, read from X1_MPTR. Block3: per set q_eval/q_com. Block4: f_eval by Horner, reads X2_MPTR and X3_MPTR. Block5: the fused final MSM with x4 powers, reads X4_MPTR and Q_EVAL_CPTR from Q_EVAL_CPTR_MPTR, writes V_MPTR and FINAL_COM_MPTR, with panic site kzg/mod.rs:1677 and a pair-counter assert. Block6: PAIRING_LHS_MPTR := PI_MPTR and PAIRING_RHS_MPTR := final_com - v*G + x3*pi, via G1MSM (0x0c) and G1ADD (0x0b) staticcalls. Its output lands in Models.Halo2Verifier.pcsComputations : List (List String) (Models.lean:843).
- `Vk.lean section variables` (formal/Midfall/Generator/Vk.lean:294)
    sig: variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] [DecidableEq G₂] {Plan : Type}
    notes: AdmissiblePairing (Common/Curve.lean:35) has p and Gₜ as outParam, so Gₜ is resolved by instance search here and is NOT phantom. Contrast DualMSM, where Gₜ is phantom (Lowering/Types.lean:93). [DecidableEq G₂] is an extra binder (VK:180 compares G2 elements).
- `Midfall.Generator.{VkPointCodecs, ParamsKZG, VerifierBuildInputs, VkQuotientBuild, VkTableWord, VkBuildEnv}` (formal/Midfall/Generator/Vk.lean:327)
    sig: structure VkPointCodecs (G₁ G₂ : Type) where g1Repr : G₁ → G1AffineRepr g2Repr : G₂ → G2AffineRepr structure ParamsKZG (G₁ G₂ : Type) where -- L339 gLagrange : List G₁ g2 : G₂ sG2 : G₂ structure VerifierBuildInputs (p : ℕ) (G₁ G₂ : Type) where -- L359 params : ParamsKZG G₁ G₂ vk : VerifyingKey (Fr p) G₁ numInstances : Nat numCommittedInstances : Nat accEncoding : Option Midfall.Generator.AccumulatorEncoding meta_ : ConstraintSystemMeta structure VkQuotientBuild where -- L386 bytes : Bytes consts : List Word256 structure VkTableWord where -- L393 value : Word256 label : String headers : List String structure VkBuildEnv (Plan : Type) where -- L405 newVerifierMemoryLayout : ConstraintSystemMeta → Halo2VerifyingKey → Ptr → VerifierMemoryLayoutConfig → VerifierMemoryLayout compactQuotientProgramFor : ConstraintSystemMeta → Data → Except Fault VkQuotientBuild quotientProgramPlan : ConstraintSystemMeta → Data → Except Fault Plan buildQuotientProgramItems : Plan → Except Fault VkQuotientBuild
    notes: VerifierBuildInputs is MOD:37-45 (the g of PLAN 9.5 in spirit); vk is the Exec VerifyingKey. ParamsKZG is the prover SRS narrowed to 3 fields. It is not ParamsVerifierKZG. VkBuildEnv makes the unported callees explicit. newVerifierMemoryLayout now matches the signature of the ported VerifierMemoryLayout.new (LayoutMemory.lean:140) and can be instantiated with it. The quotient.rs callees remain abstract.
- `Midfall.Generator.{omegaPowers, srsTauCommitment, srsTauIsConsistent, srsFingerprintPreimage, srsFingerprint}` (formal/Midfall/Generator/Vk.lean:701)
    sig: def omegaPowers (omega : Fr p) (n : Nat) : List (Fr p) -- L679 def srsTauCommitment (g_lagrange : List G₁) (omega : Fr p) : G₁ -- L691 def srsTauIsConsistent (g_lagrange : List G₁) (omega : Fr p) (s_g2 : G₂) : Bool -- L701 def srsFingerprintPreimage (codecs : VkPointCodecs G₁ G₂) (inputs : VerifierBuildInputs p G₁ G₂) (tau_g1 : G₁) : Except Fault Bytes -- L709 def srsFingerprint (codecs : VkPointCodecs G₁ G₂) (inputs : VerifierBuildInputs p G₁ G₂) : Except Fault H256 -- L738
    notes: srsTauIsConsistent is defined as e([tau]G1, g₂) = e(g₁, s_g2), with [tau]G1 = Σ omega^i · gLagrange[i] (a fold, not Pippenger). Its semantic lemma is unstatable today (R-47 / F-P08-2).
- `Midfall.Generator.generateBaseVk` (formal/Midfall/Generator/Vk.lean:758)
    sig: def generateBaseVk (codecs : VkPointCodecs G₁ G₂) (inputs : VerifierBuildInputs p G₁ G₂) : Except Fault Halo2VerifyingKey
    notes: VK:95-299. Builds the VK header in slot order. Slot 0 is vk_digest = feToU256(frToRepr vk.transcriptRepr). Then num_instances, k, n_inv, omega, omega_inv, omega_inv_to_l (|rotationLast|), has_accumulator, acc_offset, num_acc_limbs, num_acc_limb_bits, G1_BASE (=P.g₁), G2_BASE (=params.g2), and NEG_S_G2_BASE (=sG2⁻¹). After the header come fixedComms then permutationComms as G1Words. SRS panics: vk.rs:151 (Σ gLagrange ≠ g₁), :180 (g2 ≠ g₂), :189 (srsTauIsConsistent false). Header schema: VkHeaderSlot L445 / .word L479, vkHeaderFields L510, VkHeaderBuilder L569 (insert L591, finish L650, Except String).
- `Midfall.Generator.generateVkDirect` (formal/Midfall/Generator/Vk.lean:885)
    sig: def generateVkDirect (codecs : VkPointCodecs G₁ G₂) (inputs : VerifierBuildInputs p G₁ G₂) (tableWords : List VkTableWord) : Except Fault Halo2VerifyingKey
    notes: VK:301-357. Direct quotient lowering: table words appended as quotient_const, program section of size 0.
- `Midfall.Generator.{transcriptBufferLayoutForMeta, staticWorkingMemorySizeForMeta, transcriptBufferWordsBound, memoryLayoutFor, metaDataForVk, metaDataForStableStaticLayout}` (formal/Midfall/Generator/Vk.lean:945)
    sig: def transcriptBufferLayoutForMeta (meta_ : ConstraintSystemMeta) (numInstances : Nat) : Except Fault TranscriptBufferLayout def staticWorkingMemorySizeForMeta (inputs : VerifierBuildInputs p G₁ G₂) (meta_ : ConstraintSystemMeta) : Except Fault Nat -- L958 def transcriptBufferWordsBound (meta_ : ConstraintSystemMeta) (numInstances : Nat) : Except Fault Nat -- L983 (test-only) def memoryLayoutFor (env : VkBuildEnv Plan) (inputs : VerifierBuildInputs p G₁ G₂) (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) : Except Fault VerifierMemoryLayout -- L992 def metaDataForVk (feat : Features) (env : VkBuildEnv Plan) (inputs : VerifierBuildInputs p G₁ G₂) (vk : Halo2VerifyingKey) (vkMptr : Ptr) : Except Fault (ConstraintSystemMeta × Data × VerifierMemoryLayout) -- L1011 def metaDataForStableStaticLayout (feat : Features) (env : VkBuildEnv Plan) (inputs : VerifierBuildInputs p G₁ G₂) (vk : Halo2VerifyingKey) : Except Fault (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) -- L1049
    notes: metaDataForVk: the second pass sets numDummyEvals (only when feat.outerFewerPointSets) and then numPointSets := numPointSets meta1 data, then the final memory layout. metaDataForStableStaticLayout is a 3-iteration vk_mptr fixpoint with panic site vk.rs:546. Its (meta, data, memory) are the inputs every Kzg/Encoding statement needs.
- `Midfall.Generator.generateVk` (formal/Midfall/Generator/Vk.lean:1093)
    sig: def generateVk (feat : Features) (env : VkBuildEnv Plan) (codecs : VkPointCodecs G₁ G₂) (inputs : VerifierBuildInputs p G₁ G₂) : Except Fault Halo2VerifyingKey
    notes: VK:353-472. An 8-iteration reservation loop (panic site vk.rs:396), payload asserts :414 :420 :426 :436 (hazard 5: const table within reservation) :438, write-back sites :444 :447, and rematerialisation equality :457 :461. VkReservationState is at L1081.
- `Midfall.Generator.Halo2VerifyingKey (+ len, runtimeLen, bytes, runtimeBytes, G1Words, accFixedBases)` (formal/Midfall/Generator/Models.lean:385)
    sig: structure Halo2VerifyingKey where constructorPayloadMptr : Nat constants : List (String × Word256) fixedComms : List G1Words permutationComms : List G1Words quotientConstOffsetWords : Option Nat quotientConstWords : Nat quotientProgramOffsetWords : Option Nat quotientProgramWords : Nat quotientConstLabels : List String quotientConstHeaders : List (Nat × List String) -- Models.lean:94 structure G1Words where xHi : Word256; xLo : Word256; yHi : Word256; yLo : Word256 -- L462 def Halo2VerifyingKey.len (self : Halo2VerifyingKey) : Nat -- L474 def Halo2VerifyingKey.bytes (self : Halo2VerifyingKey) : Bytes -- L484 def Halo2VerifyingKey.runtimeBytes (self : Halo2VerifyingKey) : Bytes -- L868 accFixedBases : List (Nat × Bool) (field of Halo2Verifier)
    notes: The VK payload byte image is constants (32 B BE each), then fixed G1Words, then perm G1Words. runtimeBytes = 0xfe ‖ bytes, which is Lowered.vkRuntime. Payload layout: VkPayloadLayout.forVk (Layout.lean:331) and Halo2VerifyingKey.validatePayloadLayout (Layout.lean:696). accFixedBases (the fixed-base list the accumulator decoder needs) is only a FIELD of the Halo2Verifier model. Its producer, artifacts.rs:181-227, is unported.
- `Midfall.Generator.VerifierMemoryLayout.new` (formal/Midfall/Generator/LayoutMemory.lean:140)
    sig: def VerifierMemoryLayout.new (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) : VerifierMemoryLayout
    notes: MEM:591-973, now ported, so VkBuildEnv.newVerifierMemoryLayout can be filled with it. VerifierMemoryLayout (Layout.lean:903) has Ptr fields x1Mptr..x4Mptr, fComMptr, piMptr, pairingLhsMptr, pairingRhsMptr, vMptr, finalComMptr, qEvalCptrMptr, reversedEvalsMptr, commsMptrBase, and others. These are the names Inv .pcs must reference.
- `Midfall.Generator.{usizeMax, usizeSaturatingAdd, usizeAdd, usizeSub}` (formal/Midfall/Generator/Api.lean:204)
    sig: def usizeMax : Nat := 2^64 - 1 def usizeSaturatingAdd (a b : Nat) : Nat -- L209 def usizeAdd (a b : Nat) : Nat := (a + b) % 2^64 -- L216 def usizeSub (a b : Nat) : Nat := (a + (2^64 - b % 2^64)) % 2^64 -- L221
    notes: Wrapping usize arithmetic, needed only by AccumulatorEncoding. The layout constants are also here: g1CompressedBytes L164 = 48, accumulatorLimbBits L168 = 56, accumulatorLimbs L172 = 7, accumulatorLimbsPerWord L180 = 4, accumulatorIdentityFlagWords L184 = 1, accumulatorCarriedScalars L188 = 2.
- `Midfall.Generator.RepackError / printRepackError` (formal/Midfall/Generator/Api.lean:257)
    sig: inductive RepackError | lengthMismatch (expected actual prefixG1 numEvals numPointSets : Nat) | invalidCompressedG1 (offset : Nat) (bytesHex : String) | nonCanonicalScalar (offset : Nat) (bytesHex : String) deriving BEq def printRepackError (self : RepackError) : String -- L282
    notes: API:531-588. This is the error type of the unported repack_proof.
- `Midfall.Generator.GeneratorError / printGeneratorError / GeneratorError.fromRepackError / ApiFault` (formal/Midfall/Generator/Api.lean:309)
    sig: inductive GeneratorError | noAdviceColumns | unsupportedInstanceColumnShape (total committed expectedCommitted expectedNonCommitted : Nat) | rotatedInstanceQuery (column : Nat) (rotation : Int) | unsupportedAccumulatorEncoding (offset numLimbs numLimbBits numInstances : Nat) (reason : String) | planning (stage message : String) | render (artifact : String) | repack (err : RepackError) deriving BEq def printGeneratorError (self : GeneratorError) : String -- L349 def GeneratorError.fromRepackError (err : RepackError) : GeneratorError -- L388 inductive ApiFault where -- L396 | error (e : GeneratorError) | panic (site : String) deriving BEq
    notes: This is the faithful API:595-636 type. It collides by short name with the placeholder Midfall.Lowering.GeneratorError (Lowering/Types.lean:41, only planning/render). Qualify names fully.
- `Midfall.Generator.AccumulatorEncodingKind / AccumulatorEncoding` (formal/Midfall/Generator/Api.lean:413)
    sig: inductive AccumulatorEncodingKind -- L228 | pointAndScalar | pointPair deriving BEq structure AccumulatorEncoding where offset : Nat numLimbs : Nat numLimbBits : Nat kind : AccumulatorEncodingKind deriving BEq
    notes: Per D-P16, this is the type PLAN 9.5 means. The Exec stand-in Midfall.Halo2.AccumulatorEncoding (Exec/Accumulator.lean:167-261) is a different object. Methods: AccumulatorEncoding.new L454 / pointPair L462 `(offset numLimbs numLimbBits : Nat) : AccumulatorEncoding`; coordinateWords L509, pointWords L527, pointPairWords L534 and fixedPayloadWords L551, all `(self : AccumulatorEncoding) : Except ApiFault Nat`; hasCarriedScalars L545 : Bool; constants supportedNumLimbs L427, supportedNumLimbBits L431, fullyCollapsedPublicInputWordsConst L444 = 12, pointPairPublicInputWordsConst L451 = 10.
- `Midfall.Generator.AccumulatorEncoding.{fullyCollapsedPublicInputWords, validateForNumInstances, fixedScalarCount} (mutual L562-633)` (formal/Midfall/Generator/Api.lean:586)
    sig: def AccumulatorEncoding.fullyCollapsedPublicInputWords (self : AccumulatorEncoding) : Except ApiFault Nat -- L572 def AccumulatorEncoding.validateForNumInstances (self : AccumulatorEncoding) (numInstances : Nat) : Except ApiFault Unit -- L586 def AccumulatorEncoding.fixedScalarCount (self : AccumulatorEncoding) (numInstances : Nat) : Except ApiFault Nat -- L622
    notes: validateForNumInstances checks the shape first ((7,56) only), then offset ⊕sat fixedPayloadWords ≤ numInstances. fixedScalarCount uses WRAPPING usizeSub/usizeAdd (F-3) and rejects a non-zero tail for pointPair.
- `Midfall.Generator.Quotient* API types` (formal/Midfall/Generator/Api.lean:652)
    sig: structure QuotientProbeArtifacts where verifier : String; verifyingKey : String; selectorColumns : List Nat -- L652, no BEq, test-only inductive QuotientIdentityExecution | inline | interpreted | nativePermutation | nativeLookup | nativeIdentity (nativeIndex : Nat) | structuredTail deriving BEq -- L668 inductive QuotientIdentitySource | gate (gateIndex : Nat) (gateName : String) (constraintIndex : Nat) (constraintName : String) (polynomialIndex : Nat) | permutation (identityIndex : Nat) | lookup (identityIndex : Nat) (lookupIndex : Nat) (lookupName : String) | trash (trashIndex : Nat) (trashName : String) deriving BEq -- L693 inductive QuotientIdentityManifestTarget | main | selector (selectorIndex : Nat) (fixedColumn : Nat) deriving BEq -- L707 structure QuotientIdentityManifestEntry where globalIndex : Nat; source : QuotientIdentitySource; target : QuotientIdentityManifestTarget -- L717 structure QuotientIdentityManifest where entries : List QuotientIdentityManifestEntry; gateIdentities permutationIdentities lookupIdentities trashIdentities : Nat; simpleSelectorCols : List Nat -- L729 structure QuotientCertificateEntry where globalIndex; source; target; selectorGap : Option Nat; execution : QuotientIdentityExecution; expressionHash : Word256; expressionEncodingLen : Nat -- L749 structure QuotientCertificate where version : Nat; entries; gate/permutation/lookup/trashIdentities : Nat; simpleSelectorCols selectorTailExponents : List Nat; vmBytecodeHash quotientConstantsHash certificateHash : Word256 -- L774
    notes: Field lists condensed; see the file for one-field-per-line. These are host-side artifacts, not checked by any contract. Useful for indexing qvm_compile_correct per identity (globalIndex = y-batch position).
- `Midfall.Generator.GeneratorConfig (+ new, withAccumulator)` (formal/Midfall/Generator/Api.lean:812)
    sig: structure GeneratorConfig where numInstances : Nat numCommittedInstances : Nat accumulator : Option AccumulatorEncoding deriving BEq def GeneratorConfig.new (numInstances numCommittedInstances : Nat) : GeneratorConfig -- L827 def GeneratorConfig.withAccumulator (self : GeneratorConfig) (accumulator : AccumulatorEncoding) : GeneratorConfig -- L838
    notes: This is g.cfg of PLAN 9.5. The builder (try_new, builder/api.rs:38-51) that validates it is not ported.
- `Midfall.Generator.{RenderVk, RenderQuotient, QuotientLowering, RenderDiagnostics, RenderOptions, RenderedArtifacts}` (formal/Midfall/Generator/Api.lean:942)
    sig: inductive RenderVk | embedded | separate deriving BEq -- L849; RenderVk.default L860 = .embedded inductive RenderQuotient | inline | externalPinned (runtimeLen : Nat) (codehash : Word256) deriving BEq -- L863; default L873 = .inline inductive QuotientLowering | vm | direct deriving BEq -- L886; default L901 = .vm def solidityTraceEnabled : Bool := false -- L912 def solidityGasCheckpointsEnabled : Bool := false -- L918 structure RenderDiagnostics where trace : Bool; gasCheckpoints : Bool deriving BEq -- L923; default L935 structure RenderOptions where vk : RenderVk quotient : RenderQuotient quotientLowering : QuotientLowering diagnostics : RenderDiagnostics provenance : Option Bytes deriving BEq def RenderOptions.default : RenderOptions -- L966 structure RenderedArtifacts where verifier : String; verifyingKey quotientEvaluator quotientListing quotientManifest : Option String deriving BEq -- L985
    notes: Supported.production = (o.diagnostics.trace = false ∧ o.diagnostics.gasCheckpoints = false) types as written. The quotient lowering choice is o.quotientLowering, not o.quotient. ProofEvaluationCounts is at L1017 (13 Nat fields), with proofMainTotal L1076 and proofTotal L1083.
- `Midfall.Lowering.{Lowered, GeneratorError, Supported, Deployment, ContractRefAccepts}` (formal/Midfall/Lowering/Types.lean:34)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject -- L51 structure Supported (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat) (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where ... -- L83 def ContractRefAccepts {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} ... [AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool
    notes: These are existing placeholders, outside this area but where the theorem file will live. Lowered lacks plan/shell/consts. Supported is a Nat-parameterised placeholder missing noRotInst/acc/vkPoints/layout. Deployment fields are all True. ContractRefAccepts has only the no-acc arm. The untracked file Lowering/SemanticEquivalence.lean:29 already proves contractRefAccepts_iff_verifyMsgs.

## verbatim excerpts

### formal/Midfall/Generator/Abi.lean:372
```lean
  let (trash, readIdx5, cursor5) ←
    ProofCalldataLayout.takeCommitmentSection protocol readIdx4 cursor4
      CommitmentRead.trash protocol.numTrashcans "trash"
  -- AP:201: the cursor is snapshotted BEFORE the quotient limbs are reserved.
  let quotientCommCptr := cursor5
  let (quotientLimbs, readIdx6, cursor6) ←
    ProofCalldataLayout.takeCommitmentSection protocol readIdx5 cursor5
      CommitmentRead.quotient protocol.numQuotients "quotient limb"
  -- AP:210-214
  if readIdx6 != protocol.proof.commitments.length then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/abi/proof.rs:210")
  -- AP:215-216
  let evalCptr := cursor6
  let (evals, cursor7) := ProofCalldataLayout.wordSection cursor6 numEvals
  -- AP:217-219
  let wCptr := cursor7
  let fCom := ProofSection.new cursor7 1 g1Bytes
  let cursor8 := fCom.end
  -- AP:220-223
  let qEvalCptr := cursor8
  let (qEvals, cursor9) := ProofCalldataLayout.wordSection cursor8 numPointSets
  let pi := ProofSection.new cursor9 1 g1Bytes
  let cursor10 := pi.end
  -- AP:224
  let proofEnd := cursor10
```

### formal/Midfall/Generator/Abi.lean:472
```lean
def ProofCalldataLayout.commitmentReadGroups (self : ProofCalldataLayout) : List Nat :=
  let groups0 := (self.advicePhases.map fun sect => sect.itemCount).filter fun count => count != 0
  let pair := [self.lookupMultiplicities.itemCount, self.permutationProducts.itemCount]
  let groups1 := groups0 ++ pair.filter (fun count => count != 0)
  let perLookup := self.lookups.flatMap fun lookup =>
    [lookup.helpers.itemCount, lookup.accumulator.itemCount]
  let groups2 := groups1 ++ perLookup
  let groups3 := if self.trash.itemCount != 0 then groups2 ++ [self.trash.itemCount] else groups2
  groups3 ++ [self.quotientLimbs.itemCount]
```

### formal/Midfall/Generator/Quotient/VmTypes.lean:739
```lean
def RepackedProofLayoutPlan.compressedLen (self : RepackedProofLayoutPlan) : Nat :=
  self.prefixG1Count * g1CompressedBytes + self.numEvals * wordBytes
    + g1CompressedBytes + self.numPointSets * wordBytes + g1CompressedBytes

/-- rust: QVM:203-210 (`repacked_len`) @formal-baseline. "Solidity-facing
    EIP-2537-padded proof byte length after repacking." The only difference from
    `compressedLen` is the G1 width: `G1_BYTES` (128, the EIP-2537 padded form)
    against `G1_COMPRESSED_BYTES` (48). Swapping those two is the mistake this pair
    of defs exists to make testable - see `repackedProofLayout_widthsDiffer_ok`. -/
def RepackedProofLayoutPlan.repackedLen (self : RepackedProofLayoutPlan) : Nat :=
  self.prefixG1Count * g1Bytes + self.numEvals * wordBytes
    + g1Bytes + self.numPointSets * wordBytes + g1Bytes
```

### formal/Midfall/Generator/Encoding.lean:343
```lean
def EcPoint.range (p : EcPoint) : Nat → EcPoint :=
  fun idx => EcPoint.new (Ptr.add p.base (4 * idx))

/-- rust: ENC:803-805 (EcPoint::ptr) @formal-baseline. -/
def EcPoint.ptr (self : EcPoint) : Ptr := self.base

/-- rust: ENC:33 (type LookupEvalSlots) @formal-baseline, moved below Word. The
    four planned slots of one lookup's eval block: multiplicity, the helper list,
    accumulator current, accumulator next. -/
abbrev LookupEvalSlots := Option Word × List (Option Word) × Option Word × Option Word
```

### formal/Midfall/Generator/Kzg.lean:1367
```lean
  -- KZ:1063-1115: Block 2, x1 powers, emitted only when there is at least one.
  let block2 := ["// pre-compute " ++ toString nbX1Powers ++ " x1 power(s)",
      "let x1 := mload(X1_MPTR)", "mstore(X1_POWERS_MPTR, 1)"]
      ++ (if nbX1Powers > 1 then
            ["let acc := 1", "let p := X1_POWERS_MPTR",
             "for { let i := 0 } lt(i, " ++ hashHex (nbX1Powers - 1) ++ ") { i := add(i, 1) } {",
             "    p := add(p, " ++ hashHex wordBytes ++ ")",
             "    acc := mulmod(acc, x1, r)"]
            ++ [if truncatedChallenges
                  then "    mstore(p, and(acc, " ++ truncMask128 ++ "))"
                  else "    mstore(p, acc)"]
            ++ ["}"]
          else [])
```

### formal/Midfall/Generator/Kzg.lean:1626
```lean
    let x4Lines := (if truncatedChallenges then ["let x4_pow_full := 1"]
        else ["let x4_pow_0 := 1"])
      ++ (List.range nSets).flatMap fun k =>
        let s := k + 1
        if truncatedChallenges then
          ["x4_pow_full := mulmod(x4_pow_full, x4, r)",
           "let x4_pow_" ++ toString s ++ " := and(x4_pow_full, " ++ truncMask128 ++ ")"]
        else ["let x4_pow_" ++ toString s ++ " := mulmod(x4_pow_" ++ toString (s - 1)
                ++ ", x4, r)"]
```

### formal/Midfall/Generator/Api.lean:586
```lean
def AccumulatorEncoding.validateForNumInstances (self : AccumulatorEncoding)
    (numInstances : Nat) : Except ApiFault Unit := do
  if self.numLimbs ≠ AccumulatorEncoding.supportedNumLimbs
      || self.numLimbBits ≠ AccumulatorEncoding.supportedNumLimbBits then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "expected 7 radix-2^56 limbs per BLS12-381 base-field coordinate")))
  -- API:159. Safe with respect to the panic at API:104: the check above has
  -- already rejected every num_limb_bits other than 56.
  let requiredWords ← self.fixedPayloadWords
  if usizeSaturatingAdd self.offset requiredWords > numInstances then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "accumulator public-input tail exceeds num_instances")))
  pure ()
```

### formal/Midfall/Generator/Vk.lean:294
```lean
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]
  [DecidableEq G₂]
  {Plan : Type}
```


# AREA: Documentary constraints on stating the PLAN 9.5 semantic-equivalence theorems (REVIEW.md findings, design.md D-P decisions, PLAN 6/7/9.5/9.6/10-14, ROADMAP, plans/*, SORRY/gate tooling)

## constraints
- lowering_equivalence_noAcc / end_to_end_noAcc: the hypothesis `h : g.cfg.accumulator = none` is NECESSARY, not cosmetic. Rust verify_final batches with a sponge r (no vk_digest, truncated) while the contract uses keccak α. Counterexample: Y≠1, X:=Y^{-r} makes Rust accept and the contract reject. State it on Midfall.Generator.GeneratorConfig.accumulator (R-10, docs/REVIEW.md:172-220; PLAN.md:468-474, :569; R-26.1 truncation reaches the accumulator too, REVIEW.md:612-616)
- lowering_equivalence (acc mode) / contractRef_acc_complete: the RHS must be ContractRef.accepts built on the CONTRACT's keccak alphaOf. Never strengthen it to Rust verify_final; acc-mode conformance compares against ContractRef (R-10 consequences 2 and 4, REVIEW.md:206-217)
- alphaOf / finalPairing_spec: the preimage must keep vk_digest. Order is rhs before lhs on both pairs (FinalPairing.yul:23-26). The domain tag is a 29-byte literal left-padded by mstore. The tree's alphaOf takes (H vkDigest:Word256 codec kzgLhs kzgRhs accLhs accRhs), not the plan's (H vkd:Fr d a) (R-10.3, REVIEW.md:210-214; R-26 tail, REVIEW.md:649-651; Accumulator.lean:994-1020)
- pcs_spec / finalPairing_spec / pairing reorder: Rust DualMSM.check is e(left,sG2)·e(right,−G2)=1. The contract evaluates e(PAIRING_RHS,G2)·e(PAIRING_LHS,−sG2)=1. ec_pairing lays out [lhs_mptr|G2|rhs_mptr|NEG_S_G2] (AssemblyHelpers.yul:269-287), and the swap is at the CALL SITE FinalPairing.yul:88 `ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)`, with PAIRING_LHS = pi and PAIRING_RHS = final_com − v·G + x3·pi. pcs_spec's 'PAIRING_LHS/RHS = DualMSM left/right' must cite :88. Do NOT copy the stale citations in Spec/Lemmas.lean:19-20 ([RHS|G2|LHS|NEG_S_G2]) or plans/P-13-templates.md:58-59 (AssemblyHelpers 213-232, which is the modexp helper) (R-11, REVIEW.md:221-248; PLAN.md:214)
- finalPairing_spec / lowering_equivalence completeness: a failed pairing staticcall fails closed with ERR_PRECOMPILE_FAILED (MF-4), which is distinct from ProofRejected. Eip2537.Holds must say which one it rules out. ec_pairing compares the output with 1 rather than masking a bit. decodeAcc's Option merges decode failure and precompile failure (gas differs, the decision does not) (R-11 tail, REVIEW.md:250-256; R-26.6, REVIEW.md:639-641)
- lowering_equivalence ('only two outcomes') / verifier_sound / traceReturn_spec: true only under Supported.production. Trace renders do NOT revert on a failed final check: they return success=0 (FinalPairing.yul:81-84 template text), so the production field is load-bearing (PLAN.md:424; templates/partials/verifier/FinalPairing.yul:81-87)
- decodeAcc_injective: FALSE as written. With the identity flag set, coordinate words are neither decoded nor range-checked (AccumulatorHelpers.yul:130-141); the witness is accIdentityKats_ok. Restate over a normalised accWords, per point `if flag = 1 then (0,0,1) else (x,y,0)` with the flag kept. accWords does not exist in the tree, and the change of meaning needs §9.5 sign-off (R-25, REVIEW.md:564-604; Accumulator.lean:943-950)
- decodeAcc_encode: statable ONLY for collapsed shapes. The contract reads point, scalar, point, scalar, tail, while Rust as_public_input emits all bases then all scalars. The honest form is `decodeAcc enc codec fixedBases (prefix ++ encodeAccInstances enc codec a) = some a` with |prefix| = enc.offset and the shape side condition via fullyCollapsedPublicInputWords (R-26.2, REVIEW.md:617-623; Accumulator.lean:863-871)
- decodeAcc (all uses): it takes 4 args (enc, codec : G1Codec G₁, fixedBases : Array (AccFixedBase G₁), inst : Array Word256) with phantom G₂ Gₜ, where the plan writes 2. batchedCheck takes a 5th fixedBases : Array (String × G₁). The real ContractRef.accepts must supply both from generator state (R-26 tail, REVIEW.md:651-655; Accumulator.lean:891-896, :955-958, :1036-1044)
- calldata_canonical / decodeAcc: rejection of non-canonical instance words (≥ r) is expressible ONLY over Array Word256. Fr p = ZMod p cannot represent such words, and lifting through frWord loses the rejection, so those statements must take raw Word256 calldata/instances (R-26.7, REVIEW.md:642-647; Accumulator.lean:433, :924-925; PLAN.md:490, :568)
- calldata_canonical: in acc mode it is false over raw cd, because identity-flagged coordinate words are malleable (R-25). Per the plan's own fallback, weaken it to ≈ (canonicalised through accWords) and document the malleability. Trailing bytes fail closed via VkLoading.yul:102-112 (R-25, REVIEW.md:600-601; PLAN.md:489-490; R-26.5, REVIEW.md:635-638)
- decodeAcc / fixed-base tail proofs: negation is represented the opposite way. The contract embeds the POSITIVE VK base and negates the scalar, rejecting s ≥ r BEFORE negating; the circuit uses a negated base. A proof must pick one representation and say so (R-26.3, REVIEW.md:624-630; Accumulator.lean:986-987)
- contractRef_acc_complete: the contract curve- and subgroup-checks every decoded accumulator point, even under scalar 0, which Rust never does. The contract is strictly stronger, so the implication only goes Rust-accepts → ContractRef-accepts with `∃ a, decodeAcc … = some a` as a premise (R-26.4, REVIEW.md:631-634; PLAN.md:477-478)
- Supported.acc / decodeAcc / encodeAccInstances: these must refer to Midfall.Generator.AccumulatorEncoding (Api.lean:413) via `validateForNumInstances g.cfg.numInstances = .ok ()` (Api.lean:586). The Generator type has no `validFor`. The Exec stand-in Midfall.Halo2.AccumulatorEncoding (Accumulator.lean:180, validFor :245) masks the api.rs:104 panic. A reconciliation lemma (Exec validFor ↔ Generator validate, plus equal word counts) is OWED, and until it exists no §9.5 statement may be proved against the Exec type and cited as about the deployment. With both namespaces open the name is ambiguous, so fully qualify it (D-P16, docs/design.md:335-367)
- Supported.layout: `g.plan.memory.WellFormed` alone does NOT deliver 'aligned, above solc spill window'. The recommended (still OPEN, needs sign-off) form is `WellFormed ∧ validate = .ok ()`. In the tree WellFormed is on the MemoryMap (`L.map.WellFormed`, Layout.lean:1127), while the 0x1000 spill guard and the length alignment live in VerifierMemoryLayout.validate (Layout.lean:1023), as the gate LayoutMemory.lean:950-961 shows. 'disjoint' is lifetime-relative: global byte-disjointness is FALSE on the poseidon layout (54 same-byte, different-phase pairs) (D-P18, docs/design.md:395-436)
- QVM.run / qvm_compile_correct: there is no whole-stream entry point and no Program/Frame/Output. The tree's QVM.run is per identity, `(bytes : List Nat) (consts : List Word256) (mem : Memory) : Except Fault (Fr × Memory)`, and QVMFr is Nat mod a hard-coded r rather than ZMod p. Either restate per identity plus a separately ported segment walker, or define the whole-stream version ourselves and prove it decomposes. The FOLD (FOLD_MAIN/FOLD_SELECTOR/NATIVE_*, y-batch, negation to QUOTIENT_EVAL_MPTR) is executed by NO ported component, so it must enter via the Yul emitter (P-09h) or be explicitly excluded by name (D-P20 item 1 + addendum, docs/design.md:483-500, :533-551; VmReference.lean:909-934)
- qvm_validated_noOOB: a `.oob` fault cannot arise, because certifier memory is a PRNG over the whole u32 address space. Restate over the two real classes, QVMFault.readPastEnd (program end, VmReference.lean:289) and .constSlotOutOfRange (table, :291), or over the Yul-side memory model, and reconcile with the P-09e validator's bounds (D-P20 item 2, docs/design.md:502-510; plans/P-09e-validator.md:38-43)
- qvm_compile_correct: the literal PLAN form is unstatable. It needs L.plan.qprog → LoweringPlan (P-11), and the certifier seed is keccak over the finalized bytecode. The per-identity form over a real multi-identity program IS statable now (D-P20 item 3 + addendum, docs/design.md:512-522, :533-541)
- qvm_yul_refines / direct_correct: these are originated theorems with no Rust proof structure (reference.rs relies on conformance plus a trace differential). Do not invent a Rust-side argument to hang them on (D-P20 item 4, docs/design.md:524-530; ROADMAP.md:142-153)
- Supported.qvm: validateQuotientProgramOperands does not exist yet (P-09e in flight), so a real Supported cannot be constructed. Abstract it as a Prop field, as Lowering/Types.lean:53 already does (plans/P-09e-validator.md:20-27)
- All statements touching instances (verifier_sound, LeanAccepts, Supported.instShape): keep `inst : Array (Fr p)` flat. The two columns are a stated view, column c at entries [c*n, c*n+n) via instanceAt/instLen (Relation.lean:77-83); do not widen the type. It is OPEN whether format_instance emits [committed…, public…]. The Exec path passes committed `[[1]]`, not the plan's `[[0]]` (D-P11, docs/design.md:223-241; R-35, REVIEW.md:1018-1022; Native.lean:216)
- Hash agnosticism (∀ H) of lowering_equivalence/verifier_*: the vendored keccak is an ENVIRONMENT field ExecEnv.keccakOf : List UInt8 → U256 (EVMExec.lean:160), not a dialect parameter, so ∀ H is achievable at the env level, which is P-BR item 4's question. But YulSemantics.RunCommitted (Observation.lean:39) is hard-wired to EVM.evm, so the run must be Midfall.Yul.Bridge.Run (not in the tree). DERIVED: under ExecEnv.WF, extcodehash = keccakOf(code) (EVMExec.lean:293-305), so a ∀H theorem whose Deployment pins vkHash/qHash constrains H(vkRuntime) to the generation-time codehash. An adapter Bytes→H256 ↔ List UInt8→U256 is needed (plans/P-BR-bridge-run.md:48-51; PLAN.md:526)
- lowering_equivalence / RunVerifier / RunContractIR: state these over Midfall.Yul.Bridge.Run, with EVM.RunCommitted used only inside the bridging lemmas. Determinism conditions on `calls` (functionality plus gas oracle) become named fields of an Assumptions/ hypothesis structure, and Bridge.RunCommitted.det must ship a non-functional-calls counterexample (D-P10, docs/design.md:201-221; plans/P-BR-bridge-run.md:40-62)
- lagrange_spec and every Lagrange/Z_H/telescoping lemma: these need an explicit primitive-root hypothesis, FieldConsts.IsWellFormed in Assumptions/TwoAdicity.lean (NOT in the tree; P-4a). lagrange_spec is to be stated against `lIRange_delta`. CONFLICT (derived): P-4a's sketched field `zeta_order : orderOf fc.zeta = 3` cannot be discharged for fc17, the only decidable instance, because ZMod 17 has no order-3 element (Domain.lean:304-307, zeta = 2 has order 8). P-4a's own rule (every field used and discharged; no decorative fields) therefore forces dropping zeta_order or choosing another test field, e.g. one with 3 | p-1 (R-47, REVIEW.md:1553-1588; plans/P-4a-roots.md:33-70)
- Every quotient-identity / multi-open / logUp statement (verifier_complete, quotientLin_spec, pcs_spec, Spec.accepts): needs an explicit side condition that the squeezed challenges miss a finite bad set. There are three manifestations: l_i_range returns ALL ZEROS at x = ω^i (domain.rs:463); multi_prepare den.invert().unwrap() PANICS when x3 hits a point-set point (kzg/mod.rs:479), which is reachable from a proof byte (R-35); logup.rs:460 f.invert().unwrap() PANICS when f_j(x)+β=0. 'Rejects bad proofs with Error::Opening' is false as written. On-chain an abort is a revert, which the observational equivalence must absorb (R-2, REVIEW.md:71-86, :300-319; R-35, REVIEW.md:990-1016)
- Supported (rotation bounds) / noRotInst: rotations are unbounded. permutation/verifier.rs:152 `Rotation(-((blinding_factors+1) as i32))` truncates and then wraps (2^31 → −2^31, 2^32+5 → 5); only the blinding_factors i32::MAX panic bounds it. Any Supported rotation bound must cite this, and the plan's noRotInst (∀ q ∈ instanceQueries, q.2 = .cur) is missing from the tree's Supported (R-9, REVIEW.md:159-171, :321-331)
- Supported (additional fields the plan omits): a malformed but parseable VK can abort the verifier through logup.rs:237 (division by zero) or :318/:329 chunks(0) (R-13), and through verifier.rs:400-411 Vec::insert past the end when a fixed column is queried at two rotations (R-14). Supported must say whether deployed VKs avoid these, or the theorem must allow Fault.panic↔revert (REVIEW.md:268-299)
- FieldConsts users / Assumptions: rootOfUnity primitive 2^S, zeta of order 3 and delta (order ≥ #columns, ≠ 0; delta is not even a FieldConsts field) must be named hypotheses in Assumptions/. Assumptions/Pairing.lean:17-19 claims to state a structure `BLS12_381Data`, but grep finds no such declaration: it is a stale header claim of the R-46/R-49 class, so do not cite it (R-3, REVIEW.md:88-95, :367-376)
- quotientLin_spec / qvm_compile_correct (batching order): reproduce the R-16 ordering traps (permutation .enumerate().rev().skip(1); last-set constraint SECOND; trash left fold, so the first constraint takes the highest power) and R-19 (linearization BTreeMap: None first, then Some ascending; y powers walked in reverse, so the last identity gets y^0) (REVIEW.md:345-365, :415-427)
- All lowering lemmas: Supported.singlePhase and the single-proof shape are load-bearing. The R-30 phase-interleaving and fold bugs were invisible at one phase/one proof, so lemmas over the supported profile must not be cited for multi-phase keys, and KATs need every collapsed dimension ≥ 2 (R-30, REVIEW.md:758-786)
- Feature profile of lowering theorems: fix Features.solidity (committedInstances = true, truncatedChallenges = true). The generator's Default render model sets truncated_challenges = false (models.rs:1289), so gates rendered from defaults test the non-deployed profile. Under truncation, x3 is masked after the squeeze and x1/x4 powers are masked AT USE with full precision kept, which transcriptParser_spec/pcs_spec must model. Features.solidity still carries TODO(BASELINE) (plans/PROOF-PLAN.md:171-182; Features.lean:20-34; R-32, REVIEW.md:835-858)
- S1/S3 vs lowering: truncated challenges stay in the profile. The x1/x4 rows are re-derived in security.tex, which gates M9, and 'nothing in M2-M8 changes' (D-P14, docs/design.md:556-583; R-22, REVIEW.md:481-531)
- render_eq_print: FALSE as a text equality, because comments inside one statement and the 91 Solidity constant names are not representable in the AST. Restate structurally, e.g. `SyntaxEq.stmtsBeq (astOf (g.render o)) ((g.lower o).main) = true` or as propositional AST equality via stmtsBeq_eq. Needs sign-off. stmtsBeq is syntactic (free names like FR_MODULUS/ERR_* compared as unbound) and strictly finer than token equality (builtin vs call, R-38.2). Distinct texts 0x00/0x0 share one AST (R-36.3). The Solidity half (961 lines) has only a normalised-byte tripwire (R-39, REVIEW.md:1157-1187; D-P13, docs/design.md:297-334; PLAN.md:249, :412; plans/P-13-templates.md:18-39)
- ir_refines / lowering_equivalence (M8): the IR of record is the via-ir TEXTUAL IR imported as generated yul% quotations (elaborator as checker), pinning viaIR + optimizer enabled + runs 200. solc --ir-ast-json describes the legacy pipeline, which cannot compile the contract. The vendored dialect must first gain memoryguard and setimmutable. ObsEquiv, irCheck and ShellModel do not exist (R-42, REVIEW.md:1337-1413; D-P15, docs/design.md:585-620)
- Per-partial *_spec and irCheck: Lean 4.35 cannot do structural recursion through Stmt.switch. Recursions over generated Yul need explicit fuel with a loud exhaustion marker (Render.lean uses a constant 512) (R-37, REVIEW.md:1061-1074)
- deployed_equivalence (M11): it cannot be tested against the stale moonlight-wrap artifact (generated 2026-05-19, 0 of 10 typed-error sites). The correct path is proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/. A revm oracle must use the LINKED runtime (R-36, REVIEW.md:1023-1059; R-44, REVIEW.md:1465-1494, :1686-1691)
- points_subgroup_checked: the risk lives in validate_absorbed_g1_precompile_coverage (Kzg.lean:1077). Gates comparing points must build their own fixture with distinct bases or assert distinctness; LayoutKats.verifierLayoutFixture has all PCS bases = 0 (R-48, REVIEW.md:1592-1619)
- Transcript / byte-order statements (transcriptParser_spec, repack_spec): anchor them to constants the implementation did not produce (keccak256(""), EIP modulus), never self-round-trips. The R-20 BE/LE bug survived self-consistent KATs (R-20, REVIEW.md:428-460)
- verifyNative_iff_msgs / repack_spec: decodeRust's schedule depends on inst (D-P9 re-pin), and the iff is only statable with the Solidity shape hard-coded. The Transcript now carries `hash`, so prepareMsgs honours H. Blake2b is unmodelled (R-27, REVIEW.md:656-721; D-P9, docs/design.md:186-199)
- Gₜ phantom (all pairing statements): DualMSM (F G₁ G₂ Gₜ) and KzgAcc carry G₂/Gₜ as phantom parameters. Write `(Gₜ := Gₜ)` at every call where nothing pins it. AdmissiblePairing has `Gₜ : outParam` and decEqG₁/decEqGₜ fields; do not add [DecidableEq _] binders (D-P7, docs/design.md:150-184; Lowering/Types.lean:92-93). AdmissiblePairing has no 'generators are bases' field (R-33, REVIEW.md:925-931)
- Spec.accepts / verifyMsgs_iff_spec: Spec.accepts is `:= sorry` (Piop.lean:56). Any new theorem whose hypothesis or conclusion mentions it is currently about an opaque term, and defining it via the Exec pipeline would trivialise the theorem (Piop.lean:22-50)
- CommittedInstanceZero (Relation.lean:137) is `: Prop := True`, a decorative placeholder. Do not treat it as discharging assessment F3 in any lowering statement (PLAN.md:308, :573)
- Deployment (Lowering/Types.lean:71-76): all four fields are `True`. A theorem using the current structure as its world hypothesis is vacuous in W, so abstract over a real Deployment or keep it as a variable with named fields (Types.lean:67-76)
- Statements.lean is FROZEN. CI runs `sha256sum -c Midfall/Statements.sha256` (checks.sh:7), and the pinned hash d4984965…a3f3 matches the file today. NO edits there, not even comments. New statements go in a new file, e.g. Midfall/Lowering/* (PLAN.md:549; Statements.lean:4-7)
- SORRY.md registration: rows have the form `| <file> | <line> | `<first 44 chars of the trimmed source line>` | <removed by> |`, with no `|---|` separator. The gate compares only the set of file:line pairs, with listed = `sed -nE 's/^\| ([^ |]+) \| ([0-9]+) \|.*/\1:\2/p' SORRY.md | sort` (checks.sh:14) and found = scripts/sorries.sh. 'removed by' comes from the owner() case table keyed by FILE in scripts/gen_sorry.sh:10-18, so a new file prints 'UNOWNED - assign a work package' unless an arm is added. Regenerate with `bash scripts/gen_sorry.sh` after ANY line shift. The line recorded is where the `sorry` TOKEN sits, not the theorem header (e.g. Statements.lean:46 for the theorem at :43) (SORRY.md:1-17; scripts/gen_sorry.sh)
- sorries.sh detection: `python3 scripts/lean_grep.py '\bsorry\b' $(find Midfall -name '*.lean' -not -path 'Midfall/Probe/*' | sort) | sort -t: -k1,1 -k2,2n`. Comments, nested block comments and strings are stripped, and there is one entry per matching LINE (scripts/sorries.sh:9-12)
- TOOLING BUG (derived, verified by running both sorts on stdin): checks.sh sorts `found` NUMERICALLY (-k2,2n) but `listed` LEXICOGRAPHICALLY (plain `sort`). A file whose sorry lines have different digit counts (e.g. 98 and 120) therefore makes the register gate fail even when SORRY.md is exactly in sync. Today all tracked sorry lines are two-digit. A new many-sorry theorem file must keep its sorry lines in one digit band, or checks.sh needs fixing (checks.sh:13-19)
- TOOLING HAZARD (derived, verified in memory with python3 -B): lean_grep.py treats `'` as a char-literal delimiter. A primed identifier (h', G₁') enters in_char mode, where `--` and `/-` are not recognised, so an apostrophe in later prose (e.g. don't) closes it and the word sorry in that comment is counted as a proof hole. Do not spell the word in comments of theorem files; R-29 precedent (REVIEW.md:750-756; scripts/lean_grep.py:30-46)
- House convention for not-yet-proved statements: the ONLY precedent is `theorem name … : P := by sorry`, registered in SORRY.md (Statements.lean:43-46, :57-59, :73-75), plus one sorry'd Prop def (Spec/Piop.lean:54-56). There is NO `def fooStatement : Prop := …` precedent (grep for Statement/Obligation/Claim finds none). Gap policy: 'a bare sorry outside this register is never allowed; a missing proof becomes a named hypothesis structure in Midfall/Assumptions/' (SORRY.md:8-11). Unported objects are abstracted as placeholder structures (Lowering/Types.lean). Every hypothesis must ship non-vacuity evidence in the dualMsm_scale_check style (Spec/Lemmas.lean:91-141; plans/P-4a-roots.md:82-88; plans/P-BR-bridge-run.md:57-61)
- Instances/ import confinement: a file outside Midfall/Instances/ that both imports Midfall.Instances.* and has a column-0 `theorem `/`lemma ` line fails CI. The theorem file must not import ExponentModel, Bls12_381 or NativeE2E. DERIVED: the grep `^(theorem|lemma) ` misses `private theorem`/`@[simp] theorem`, but the rule still applies (D-P17, docs/design.md:369-394; checks.sh:47-60)
- Module registration: every new .lean file must be reachable from the Midfall root (Midfall.lean imports) or check_orphans.py fails CI. SemanticEquivalence.lean is currently registered only by an uncommitted edit to Midfall.lean (R-50, REVIEW.md:1651-1683; checks.sh:28-31)
- KAT gates in a theorem file: `#eval <expr> -- expect <token>`. The token stops at whitespace or a comma and trailing .,:; is stripped. Output must match `^(true|false|-?\d+|"[^"]*"|\[.*\])$`, the number of printed values must equal the number of #eval lines, and the file must elaborate under `lake env lean` with exit 0 (sorry warnings are fine). Unannotated #eval lines are not gated. Each KAT doc must name the concrete wrong implementation it rules out (scripts/kat_gate.py:30-41, :78-108; R-38 rule, REVIEW.md:1154-1156; R-41, REVIEW.md:1301-1336)
- Build options: lakefile.toml sets autoImplicit = false, so every binder must be explicit. `lake env lean` does NOT apply it, so report only `lake build` results. native_decide is banned outside Midfall/Instances/ (checks.sh:22-27, :36; plans/README.md standing notes)
- Axioms: checks.sh `#print axioms` covers only verifyNative_iff_msgs and verifyMsgs_iff_spec (checks.sh:68-71). New theorems must report their own #print axioms within the trusted base, and ArkLib sorries (rbr→KS, FS completeness, AGM.run, append_*) must not enter the closure (PLAN.md:553; SORRY.md:19-29; plans/PROOF-PLAN.md:24-30)
- Review boundary: per-task adversarial review is OFF through M5-M7 (and M8 on the current reading). Every theorem and gate must carry the author's own perturbation evidence, and anything that cannot be evidenced must be flagged rather than asserted (PLAN.md:559; ROADMAP.md:122-140)
- S7 / security statements: the PLAN 9.4 notation `Pr[= true | …]` is not Lean. Use VCVio `Pr{ doSeq }[ event ]` (plans/PROOF-PLAN.md:36, :193-197)
- ORDER (PLAN §10 step 2, PLAN.md:520): deterministic algebra lemmas (Phase 4) → codec lemmas (repack, calldata, accumulator) → per-partial contracts → verifier_sound / verifier_complete on the VM path → ir_refines → lowering_equivalence (VM) → S5 → S2 (gates/vanishing, permutation, logUp, trash) → S3 → S4 → S1 → S7 → Direct → deployed_equivalence
- SEQUENCE (PLAN §14.5, PLAN.md:639-649): M3 package 1 → M3 packages 2-4 ∥ Phase 4a algebra → M4-Lean (Bridge.Run + determinism conditions) → finalPairing_spec → M5 → M6 → M7. Hard prerequisites: P-4a TwoAdicity before M5-M7 (R-47), P-BR Bridge before finalPairing_spec and every semantic equivalence, P-09e before Supported.qvm, P-11 before LoweringPlan/Supported/qprog, P-12 before repack/calldata, P-13 (AssemblyHelpers.yul + FinalPairing.yul FIRST) before finalPairing_spec
- PULLED FORWARD (PLAN §14.4, PLAN.md:624-637): finalPairing_spec moves out of M7 to right after M3. Its statement is 'the emitted ec_pairing call frame in the generated Yul is equivalent to DualMSM.check', and it needs only the pairing block AST, the EIP-2537 relation in Yul/Externals.lean and DualMSM.check, with no QVM, Lagrange or calldata. It is the first calibration point and the gate the review batch waits for (ROADMAP.md:137-140, :177-183; plans/P-13-templates.md:56-61)
- MILESTONES (PLAN §11, PLAN.md:530-545): M3 = render_eq_print / golden AST equality. M5 = repack_spec, calldata_roundtrip, calldata_canonical, decodeAcc_encode, decodeAcc_injective, vkLoading_spec, transcriptParser_spec, lagrange_spec. M6 = qvm_compile_correct, qvm_validated_noOOB, qvm_yul_refines + evaluator frame theorem. M7 = pcs_spec, finalPairing_spec (pulled forward), verifier_sound, verifier_complete, end_to_end_noAcc. M8 = irCheck verified, ir_refines, lowering_equivalence with no sorry. M9 = S1-S7 (S7 contract_knowledgeSound uses lowering_equivalence). M10 = direct_correct + lowering_equivalence for Direct (direct/ port deferred to M10, PLAN 14.8). M11 = deployed_equivalence. NOT assigned in §11: quotientLin_spec and traceReturn_spec (per-partial contracts, so before verifier_sound in M7 by the §10 order), lowering_equivalence_noAcc (a prerequisite of end_to_end_noAcc, so M7), contractRef_acc_complete, points_subgroup_checked. The frozen §9.2 trio is owned by 'frozen statements (S1..S7 land later)'

## missing
- LoweringPlan / g.plan (incl. L.plan.qprog, plan.memory, vkCodehash, quotientCodehash): rust proofs/solidity-verifier/src/lowering/{mod,config,plan}.rs. Package P-11 (DRAFT)
- SolidityGenerator, g.lower, g.render, tryNew, g.vk / g.params / g.cfg bundle: rust builder/{mod,api,render}.rs (try_new validation in builder/api.rs:38-51). Package P-12. GeneratorConfig and RenderOptions already exist in Generator/Api.lean
- repackProof: rust builder/repack.rs. encodeCalldata / FN_SIG_VERIFY_PROOF: rust evm.rs. decodeCalldata, calldataOf, encodeContractProof: rust lowering/calldata.rs. All P-12
- Lowered.plan / .shell (SolShell) / .consts and the Lean fns for the 13 verifier + 2 evaluator partials: rust templates/partials/verifier/*.yul, templates/contracts/*.sol, lowering/render/{mod,models,yul}.rs. P-13 (Models/Templates partly exist; TemplateConstants sub-records exist in Models.lean)
- validateQuotientProgramOperands (Supported.qvm, QVM-01): rust lowering/quotient_numerator/vm/mod.rs:2139-~2500 (+2009-2138 structural validator). P-09e, in flight; target file Generator/Quotient/VmValidator.lean does not exist
- QVM Yul emitter (for qvm_yul_refines and the fold): rust quotient_numerator/yul_emit.rs (P-09h). Shape recognizers vm/mod.rs:3156-3227, 3649-3813 (P-09f). quotient.rs + direct/folds.rs (P-10)
- QVM.Program / QVM.Frame / QVM.Output / frameOf / outputOf / quotientParts: NO Rust counterpart (D-P20). Deliberately not invented (VmReference.lean:909-915)
- Direct lowering (direct_correct): rust quotient_numerator/direct/{mod,emit,layout,validate}.rs. Deferred to M10 (PLAN 14.8)
- Midfall.Yul.Bridge.Run / Bridge.RunCommitted / Bridge.RunCommitted.det + determinism hypothesis structure (D-P10, P-BR): no Rust source; wraps vendor BigStep.Run over evmWithExternal (Dialect/EVM.lean:135-164)
- RunVerifier, RunContractIR, RunShell, ObsEquiv, honestCalls, calls L W, Eip2537.Holds, Modexp.Holds, Evaluator.rel, bindLocals, initState/callState, abiTrue: no Rust source (PLAN 7/9.5). Only ExternalCallRelation and honestRelations exist in Yul/Externals.lean
- ShellModel.lean (solc dispatcher for verifyProof(bytes,uint256[]), selector 0x1e8e1e13), ImportSolcIR.lean (generated yul% quotes of solc via-ir `ir`), IRCheck.lean (irCheck): PLAN 7, D-P15. They need memoryguard + setimmutable added to the vendored dialect
- Inv k per-phase memory invariants for the *_spec theorems: rust lowering/layout/memory.rs (VerifierMemoryLayout regions/lifetimes exist in Layout.lean / LayoutMemory.lean, but no Inv)
- accWords (normalised, identity-flag aware) for decodeAcc_injective: no Rust counterpart (R-25 fix)
- Reconciliation lemma Exec AccumulatorEncoding.validFor ↔ Generator validateForNumInstances (D-P16 item 3): no Rust counterpart
- Real ContractRef.accepts with the accumulator arm (decodeAcc + alphaOf + batchedCheck from generator state): rust templates FinalPairing.yul + AccumulatorHelpers.yul. Only the no-acc ContractRefAccepts exists (Lowering/Types.lean:83)
- Real Deployment fields (W.code, W.extcodehash, W.object, addresses): needs a Midfall/Yul world model. The placeholder has True fields
- Real Supported(g o) fields noRotInst, acc, vkPoints, layout, plus the instShape committed-count conjunct: need P-11/P-12 types
- Assumptions/TwoAdicity.lean FieldConsts.IsWellFormed (P-4a) plus an Assumptions hypothesis for delta order (R-3 extended). The BLS12_381Data structure claimed by Assumptions/Pairing.lean's header does not exist
- Spec.accepts body (Spec/Piop.lean:56 sorry): Phase 4 declarative PIOP spec, no direct Rust counterpart
- Lowered.print / astOf (text→AST): no runtime Yul parser exists (yul% is elaboration-time only, D-P2 amendment); render is Generator/Render.lean renderBlock/renderObject
- Instances/MoonlightWrap.lean (deployed_equivalence) plus a regenerated Moonlight artifact (R-36)

## declarations
- `Midfall.Statements.verifyNative_iff_msgs` (formal/Midfall/Statements.lean:43)
    sig: theorem verifyNative_iff_msgs : verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔ ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧ verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by sorry
    notes: FROZEN (sha256 d4984965...a3f3 in Midfall/Statements.sha256, matches today). Section variables (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes); file variable block lines 28-33 binds the instance as named `[P : AdmissiblePairing G₁ G₂ Gₜ]`. sorry token is on line 46 (that is the SORRY.md line, not 43). Precedent for the house convention `theorem … := by sorry`.
- `Midfall.Statements.verifyMsgs_iff_spec` (formal/Midfall/Statements.lean:57)
    sig: theorem verifyMsgs_iff_spec (hwf : vk.WellFormed F) : (verifyMsgs (Gₜ := Gₜ) E H F params vk inst ms).isOk ↔ Spec.accepts H F params vk inst ms := by sorry
    notes: FROZEN. Right side is Spec.accepts, which is itself `:= sorry` (Piop.lean:56), so this cannot be proved until Phase 4 writes a declarative spec. The sorry is registered at line 59.
- `Midfall.Statements.contractRef_noAcc` (formal/Midfall/Statements.lean:73)
    sig: theorem contractRef_noAcc : Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms ↔ verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () := by sorry
    notes: FROZEN, keccak only. Bool on the left is coerced to Prop. It has a PROVEN, hash-generic twin in the untracked file Lowering/SemanticEquivalence.lean:29. Do not duplicate it.
- `Midfall.Lowering.contractRefAccepts_iff_verifyMsgs` (formal/Midfall/Lowering/SemanticEquivalence.lean:29)
    sig: theorem contractRefAccepts_iff_verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : ContractRefAccepts E H params vk inst ms = true ↔ verifyMsgs E H Features.solidity params vk inst ms = .ok ()
    notes: The file is UNTRACKED (git status shows `??`), and its import in Midfall.lean is an uncommitted change. Its variable block uses an anonymous `[AdmissiblePairing G₁ G₂ Gₜ]`. It is proved by case analysis on prepareMsgs/DualMSM.check. Its docstring says not to use it for accumulator-mode parity. The header promises contract obligations 'stated separately so no missing execution step can be hidden in a vacuous implication'.
- `Midfall.Lowering.ContractRefAccepts` (formal/Midfall/Lowering/Types.lean:83)
    sig: def ContractRefAccepts {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool := match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with | .error _ => false | .ok d => DualMSM.check d params
    notes: Covers only the NO-accumulator arm. PLAN 9.5's ContractRef.accepts also takes g, matches g.cfg.accumulator and calls decodeAcc/alphaOf/batchedCheck. Gₜ must be named because it is phantom in DualMSM (D-P7).
- `Midfall.Lowering.Supported` (formal/Midfall/Lowering/Types.lean:51)
    sig: structure Supported (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat) (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where advice : numAdvice ≠ 0 instShape : numInstances = 2 singlePhase : numChallenges = 0 hLimbs : numQuotientLimbs = csDegree - 1 qvm : qvmValidated production : trace = false ∧ gasCheckpoints = false
    notes: A numeric PLACEHOLDER, not the plan's `Supported (g o)`. It lacks noRotInst, acc, vkPoints and layout, because their types are not ported. instShape here drops the plan's `∧ g.cfg.numCommittedInstances = 1`. qvm is an opaque Prop because validateQuotientProgramOperands does not exist yet (P-09e).
- `Midfall.Lowering.Deployment` (formal/Midfall/Lowering/Types.lean:71)
    sig: structure Deployment (vkRuntime : Bytes) (evaluator : Option YulObject) (vkCodehash quotientCodehash : H256) : Prop where vkCode : True vkHash : True qObj : True qHash : True
    notes: Every field is True, so it is vacuous. A theorem with this as its only world hypothesis says nothing about W. The real fields need the world model W and addresses (Midfall/Yul, not yet written).
- `Midfall.Lowering.Lowered` (formal/Midfall/Lowering/Types.lean:34)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject
    notes: YulBlock = YulSemantics.Block YulSemantics.EVM.Op. The plan's plan/shell/consts fields are missing (P-11/P-13).
- `Midfall.Halo2.decodeAcc` (formal/Midfall/Halo2/Exec/Accumulator.lean:955)
    sig: def decodeAcc {G₁ G₂ Gₜ : Type} (enc : AccumulatorEncoding) (codec : G1Codec G₁) (fixedBases : Array (AccFixedBase G₁)) (inst : Array Word256) : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)
    notes: File variable `{p : ℕ} [Fact (Nat.Prime p)]` (line 77). G₂ and Gₜ are PHANTOM (KzgAcc carries them, D-P7) and need no pairing instance. It takes 4 args where the plan has 2 (R-26). inst is Word256, not Fr p, so it is the only place the ≥ r rejection is expressible. enc is the EXEC stand-in Midfall.Halo2.AccumulatorEncoding, not the Generator one (D-P16).
- `Midfall.Halo2.alphaOf` (formal/Midfall/Halo2/Exec/Accumulator.lean:1014)
    sig: def alphaOf {G₁ : Type} (H : Bytes → H256) (vkDigest : Word256) (codec : G1Codec G₁) (kzgLhs kzgRhs accLhs accRhs : G₁) : Fr p
    notes: Takes 7 args over EVALUATED points, unlike the plan's (H vkd d a) with vkd : Fr. The preimage is tag ‖ vk_digest ‖ toEip kzgRhs ‖ kzgLhs ‖ accRhs ‖ accLhs, so RHS comes before LHS. Zero is mapped to 1.
- `Midfall.Halo2.batchedCheck` (formal/Midfall/Halo2/Exec/Accumulator.lean:1036)
    sig: def batchedCheck {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (params : ParamsVerifierKZG G₁ G₂) (alpha : Fr p) (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (fixedBases : Array (String × G₁)) : Bool
    notes: Has an extra 5th argument fixedBases : Array (String × G₁), whose type differs from decodeAcc's Array (AccFixedBase G₁). Written in DualMSM orientation (left with sG2).
- `Midfall.Halo2.encodeAccInstances` (formal/Midfall/Halo2/Exec/Accumulator.lean:872)
    sig: def encodeAccInstances {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (enc : AccumulatorEncoding) (codec : G1Codec G₁) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256
    notes: Emits the TAIL only (Rust as_public_input: all bases, then all scalars). The honest round trip is decodeAcc enc codec fb (prefix ++ encodeAccInstances enc codec a), where prefix has enc.offset words. That holds for collapsed shapes only (R-26.2).
- `Midfall.Halo2.frWord` (formal/Midfall/Halo2/Exec/Accumulator.lean:433)
    sig: def frWord (x : Fr p) : Word256 := BitVec.ofNat 256 x.val
    notes: Lifts Fr into Word256. It loses the contract's ≥ r rejection by construction (R-26.7).
- `Midfall.Halo2.AccumulatorEncoding.validFor` (formal/Midfall/Halo2/Exec/Accumulator.lean:245)
    sig: def validFor (enc : AccumulatorEncoding) (numInstances : Nat) : Bool := enc.limbShapeOk && enc.offset + enc.fixedPayloadWords ≤ numInstances
    notes: EXEC STAND-IN. It masks the api.rs:104 panic behind `max 1`, uses Nat arithmetic where the Rust wraps, and returns Bool. D-P16 says the plan's Supported.acc must NOT be stated with this.
- `Midfall.Generator.AccumulatorEncoding.validateForNumInstances` (formal/Midfall/Generator/Api.lean:586)
    sig: def AccumulatorEncoding.validateForNumInstances (self : AccumulatorEncoding) (numInstances : Nat) : Except ApiFault Unit
    notes: The FAITHFUL port (D-P16). Supported.acc should read `enc.validateForNumInstances g.cfg.numInstances = .ok ()`; there is NO `validFor` on this type. Namespace Midfall.Generator (Api.lean:150), which opens Midfall.Halo2, so both AccumulatorEncoding names are in scope: always fully qualify.
- `Midfall.Generator.GeneratorConfig` (formal/Midfall/Generator/Api.lean:812)
    sig: structure GeneratorConfig where numInstances : Nat numCommittedInstances : Nat accumulator : Option AccumulatorEncoding deriving BEq
    notes: This is g.cfg in PLAN 9.5. `accumulator` holds the Generator AccumulatorEncoding, which is the hypothesis target of `h : g.cfg.accumulator = none`.
- `Midfall.Generator.MemoryMap.WellFormed / MemoryMap.validate / VerifierMemoryLayout.validate` (formal/Midfall/Generator/Layout.lean:1127)
    sig: def MemoryMap.WellFormed (self : MemoryMap) : Prop := self.wellFormedBool = true -- Layout.lean:552 def MemoryMap.validate (self : MemoryMap) : Except String Unit := do -- Layout.lean:1023 def VerifierMemoryLayout.validate (self : VerifierMemoryLayout) : Except String Unit := do
    notes: WellFormed is STRICTLY WEAKER than validate. It has no length-alignment arm, its spill bound is 0x80 rather than the 0x1000 LOW_MEMORY_SCRATCH_START, and it exempts len = 0. The 0x1000 guard lives only in VerifierMemoryLayout.validate. Gate LayoutMemory.lean:950-961 shows `lowVk.map.WellFormed` together with `lowVk.validate = error`. Decidable instance at Layout.lean:1130.
- `Midfall.Generator.QVM.run` (formal/Midfall/Generator/Quotient/VmReference.lean:930)
    sig: def run (bytes : List Nat) (consts : List Word256) (mem : Memory) : Except Fault (Fr × Memory) := evalQuotientIdentity bytes consts mem
    notes: Namespace Midfall.Generator.QVM, with abbrev Fault := QVMFault, Fr := QVMFr, Memory := QuotientRefMemory. QVMFr is `Nat` (VmReference.lean:252) under mod qvmFrModulus, a hard-coded BLS12-381 r. It is NOT ZMod p, so relating it to the generic Fr p needs a cast bridge and p = qvmFrModulus. It runs ONE identity only, with no Program/Frame/Output (D-P20).
- `Midfall.Generator.QVMFault` (formal/Midfall/Generator/Quotient/VmReference.lean:284)
    sig: inductive QVMFault | stackUnderflow (idx : Nat) | readPastEnd (idx : Nat) | constSlotOutOfRange (slot idx : Nat) | zeroLengthRun (idx : Nat) | affineSumZeroCounts (idx : Nat) | modarith7UnknownFlags (flags idx : Nat) | streamOpcodeInIdentity (op idx : Nat) | unknownOpcode (op idx : Nat) | stackLengthMismatch (len : Nat) | panic (site : String) deriving BEq
    notes: There is no `.oob` constructor. The real out-of-range classes are readPastEnd (program) and constSlotOutOfRange (table), which is how qvm_validated_noOOB must be restated (D-P20 item 2).
- `Midfall.Halo2.FieldConsts` (formal/Midfall/Halo2/Exec/Arith.lean:64)
    sig: structure FieldConsts (F : Type) where numBits : Nat s : Nat rootOfUnity : F zeta : F
    notes: Bare data: no root-order or zeta-order hypothesis, and no delta field (R-3, R-47). The planned FieldConsts.IsWellFormed in Assumptions/TwoAdicity.lean does NOT exist yet.
- `Midfall.Halo2.EvaluationDomain.lIRange` (formal/Midfall/Halo2/Exec/Domain.lean:251)
    sig: def EvaluationDomain.lIRange (d : EvaluationDomain F) (x xn : F) (rotations : List Int) : Array F
    notes: File variable `{F : Type} [Field F] [DecidableEq F]` (line 48). It returns zeros at a domain point (R-2). rotateOmega is at line 232.
- `Midfall.Halo2.fc17` (formal/Midfall/Halo2/Exec/Domain.lean:317)
    sig: def fc17 : FieldConsts (Fr 17) := { numBits := 5, s := 4, rootOfUnity := 3, zeta := 2 }
    notes: This is the only decidable FieldConsts. ZMod 17 has NO element of order 3; Domain.lean:304-307 says so and uses zeta = 2 as a placeholder of order 8.
- `Midfall.Halo2.DualMSM / DualMSM.check` (formal/Midfall/Halo2/Exec/Kzg/Msm.lean:171)
    sig: structure DualMSM (F G₁ G₂ Gₜ : Type) where left : MSMKZG F G₁ right : MSMKZG F G₁ -- Msm.lean:222 def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) : Bool
    notes: G₂ and Gₜ are PHANTOM type parameters (D-P7). check evaluates e(left, sG2Prepared) + e(right, nG2Prepared) = 1 in Gₜ via P.decEqGₜ. That is the Rust orientation, the opposite of the contract's (R-11).
- `Midfall.Halo2.Spec.Lemmas.pairing_reorder / dualMsm_scale_check` (formal/Midfall/Halo2/Spec/Lemmas.lean:31)
    sig: theorem pairing_reorder {R : Type*} [CommRing R] (xL xR s : R) : rustEq xL xR s ↔ contractEq xL xR s -- Lemmas.lean:100 theorem dualMsm_scale_check {R : Type*} [Field R] (xL xR s c : R) (hc : c ≠ 0) : rustEq (c * xL) (c * xR) s ↔ rustEq xL xR s
    notes: Stated in the exponent ring, not over a pairing. These set the house pattern for non-vacuity: `example`s with ZMod 17 counterexamples at lines 127-141. The prose at lines 19-20 still cites the STALE layout [RHS|G2|LHS|NEG_S_G2]; R-11 corrected it.
- `YulSemantics.SyntaxEq.stmtsBeq / stmtsBeq_eq` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:147)
    sig: def stmtsBeq : List (Stmt Op) → List (Stmt Op) → Bool -- Ast.lean:288, under variable [LawfulBEq Op] (line 170) theorem stmtsBeq_eq : ∀ (left right : List (Stmt Op)), stmtsBeq left right = true → left = right
    notes: Variable `{Op : Type} [BEq Op]` (line 102). This is purely syntactic equality: names are compared, so there is no α-equivalence. It is the D-P13 relation of record, and the structural render_eq_print should use it or stmtsBeq_eq.
- `YulSemantics.RunCommitted` (formal/vendor/yul-semantics/YulSemantics/Observation.lean:39)
    sig: def RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm) (stObs : EvmState) (o : Outcome) : Prop := ∃ st', Run EVM.evm prog st0 V' st' o ∧ stObs = committedState st0 st'
    notes: Namespace YulSemantics, not EVM.RunCommitted as the plan writes. It is HARD-WIRED to the closed EVM.evm dialect with no external calls (Y-3), so the PLAN 9.5 RunVerifier/RunContractIR need Midfall.Yul.Bridge.Run (D-P10, P-BR), which does not exist yet.
- `YulSemantics.EVM.ExecEnv.keccakOf` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:160)
    sig: keccakOf : List UInt8 → U256 := keccakBytes
    notes: The keccak oracle is an ENVIRONMENT field (structure ExecEnv, line 114), not a dialect parameter. Its default is `opaque keccakBytes`. projectedCodeHash (line 293) and ExecEnv.WF make extcodehash = keccakOf(code). Its type differs from Midfall.Halo2.Hash := Bytes → H256 (ByteArray → BitVec 256).
- `Midfall.Halo2.Spec.accepts` (formal/Midfall/Halo2/Spec/Piop.lean:54)
    sig: def accepts (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Prop := sorry
    notes: This is a sorry DEFINITION, registered at line 56. Defining it by calling the Exec pipeline would make verifyMsgs_iff_spec trivial (Piop.lean:22-30).
- `Midfall.Halo2.verifyNative` (formal/Midfall/Halo2/Exec/Native.lean:207)
    sig: def verifyNative {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) : Except Fault Unit
    notes: The committed instance is hard-coded to `[[1]]` (identity in multiplicative G₁), where PLAN 9.2 writes `[[0]]`. R-35 confirmed [[1]] is correct. decodeRust (line 228) also takes inst (D-P9).
- `Midfall.Halo2.Spec.instanceAt / instLen / CommittedInstanceZero` (formal/Midfall/Halo2/Spec/Relation.lean:77)
    sig: def instanceAt (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (c r : Nat) : Fr p := inst.getD (c * idx.n + r) 0 -- :82 def instLen (idx : CircuitIndex (Fr p)) : Nat := idx.cs.numInstanceColumns * idx.n -- :137 def CommittedInstanceZero (idx : CircuitIndex (Fr p)) : Prop := True
    notes: These implement D-P11, the flat-with-view instance model. CommittedInstanceZero is a decorative `True` placeholder for assessment F3 and discharges nothing.
- `Midfall.Halo2.Features.solidity / Fault` (formal/Midfall/Halo2/Exec/Features.lean:30)
    sig: def Features.solidity : Features where committedInstances := true truncatedChallenges := true outerFewerPointSets := false outerSingleHCommitment := false -- Error.lean:56 inductive Fault where | error (e : Error) | panic (site : String)
    notes: There is a TODO(BASELINE) at Features.lean:29: the deploy command line is not yet confirmed. Fault.panic carries only a site string (R-43 F2).
- `Midfall.Yul.honestRelations` (formal/Midfall/Yul/Externals.lean:1006)
    sig: def honestRelations (product : PairingProduct) : List ExternalCallRelation := [g1AddRelation, g1MsmRelation, pairingRelation product, modexpRelation]
    notes: This is the closest existing object to the plan's honestCalls/calls. It is a List of ExternalCallRelation records, not an EVM.ExternalCalls (Y-1: that is a structure). It has no evaluator relation and no Eip2537.Holds/Modexp.Holds. PairingProduct := Bytes -> Bool (line 941).

## verbatim excerpts

### formal/Midfall/Statements.lean:36
```lean
section
variable (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
  (params : ParamsVerifierKZG G₁ G₂)
  (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes)

/-- Plan 9.2: the byte-level verifier and the message-level verifier accept
    exactly the same proofs, and every accepted proof decodes. -/
theorem verifyNative_iff_msgs :
    verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔
      ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧
        verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by sorry

end
```

### formal/Midfall/Lowering/Types.lean:45
```lean
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
```

### formal/SORRY.md:8
```lean
A bare `sorry` outside this register is never allowed; a missing proof becomes a
named hypothesis structure in `Midfall/Assumptions/` instead (plan Section 3, gap
policy). The Phase 1 exit criterion is explicitly `Statements.lean compiles with
sorry`, so what is listed here is the planned Phase 1 state, not sloppiness.

| file | line | declaration | removed by |
| Midfall/Halo2/Spec/Piop.lean | 56 | `(ms : List (Msg (Fr p) G₁)) : Prop := sorry` | Phase 4 (spec layer) |
| Midfall/Statements.lean | 46 | `verifyMsgs (Gₜ := Gₜ) E keccak256 F params v` | frozen statements (S1..S7 land later) |
| Midfall/Statements.lean | 59 | `Spec.accepts H F params vk inst ms := by sor` | frozen statements (S1..S7 land later) |
| Midfall/Statements.lean | 75 | `verifyMsgs (Gₜ := Gₜ) E keccak256 Features.s` | frozen statements (S1..S7 land later) |
```

### formal/scripts/checks.sh:6
```lean
echo '== frozen statements hash =='
sha256sum -c Midfall/Statements.sha256

echo '== sorry register =='
# The inventory comes from scripts/sorries.sh, which is also what generates the
# register table (scripts/gen_sorry.sh), so gate and register cannot drift apart.
found=$(bash scripts/sorries.sh)
listed=$(sed -nE 's/^\| ([^ |]+) \| ([0-9]+) \|.*/\1:\2/p' SORRY.md | sort)
if [ "$found" != "$listed" ]; then
  echo 'sorry register out of sync with the tree'
  diff <(echo "$listed") <(echo "$found") || true
  exit 1
fi
```

### formal/Midfall/Halo2/Exec/Accumulator.lean:943
```lean
    `decodeAcc_injective` (plan 9.5) is FALSE for this decoder as written, and
    the reason is in the contract, not here: with the identity flag set the
    coordinate words are neither decoded nor range-checked (yul:130-141), so two
    instance tails that differ only in the coordinate words of an identity side
    both decode to the same accumulator. `accIdentityKats_ok` below exhibits the
    pair. The statement survives only if `accWords` projects the coordinate
    words away for identity-flagged points; that is a decision for whoever
    states the theorem, and it is recorded here rather than smoothed over.

    No pairing binder here, and that is deliberate: decoding is arithmetic plus a
    point decode, so unlike `KzgAcc.check` and `batchedCheck` it needs no
    `AdmissiblePairing` - only the phantom G₂ Gₜ that `KzgAcc` carries (D-P7). -/
def decodeAcc {G₁ G₂ Gₜ : Type}
    (enc : AccumulatorEncoding) (codec : G1Codec G₁)
    (fixedBases : Array (AccFixedBase G₁)) (inst : Array Word256) :
    Option (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
```

### formal/docs/PLAN.md:467
```lean
/-- Exact equivalence to the Rust-faithful Lean verifier (no accumulator). -/
theorem lowering_equivalence_noAcc (h : g.cfg.accumulator = none) :
  LeanAccepts keccak256 g L cd ↔ ∃ ms inst, decodeCalldata L.plan cd = some (ms, inst) ∧
      verifyMsgs keccak256 .solidity g.params g.vk inst ms = .ok ()
theorem end_to_end_noAcc (h : g.cfg.accumulator = none) (hL hsup hdep hpc hir) :
  verifyNative .solidity g.params g.vk inst π = .ok () ↔
  ∃ cd, (repackProof L.plan π >>= (encodeCalldata L.plan · inst)) = .ok cd ∧
        ∀ obs, RunContractIR keccak256 L W ir cd (honestCalls L W) obs → obs = .return abiTrue
/-- Accumulator mode: exact w.r.t. ContractRef; against separate checks, exact one way,
    S5 the other. -/
theorem contractRef_acc_complete (h : g.cfg.accumulator = some enc) :
  verifyMsgs … = .ok () → (∃ a, decodeAcc enc inst = some a ∧ a.check g.params) → ContractRef.accepts H g ms inst
```

### formal/Midfall/Generator/Quotient/VmReference.lean:909
```lean
/-! ## The PLAN 9.5 bridge -/

-- PLAN 9.5 names its anchor QVM.run over QVM.Program, QVM.Frame, QVM.Fault and
-- QVM.Output. Only two of those exist in the reference, and this namespace says which:
-- Fault (the closed taxonomy of hazard 2) and run (the per-identity evaluator).
-- Program, Frame and Output have no counterpart - see DOMAIN OF QVM.run and WHAT PLAN
-- 9.5 STILL OWNS in the header - and are deliberately NOT invented here.
namespace QVM

/-- PLAN 9.5's QVM.Fault. -/
abbrev Fault : Type := QVMFault

/-- PLAN 9.5's Fq: the concrete scalar field the reference interprets over. -/
abbrev Fr : Type := QVMFr

/-- The reference's memory: a seed and a memo table. There is no Frame, because there is
    no frame: memory is derived from addresses, never loaded from one. -/
abbrev Memory : Type := QuotientRefMemory

/-- PLAN 9.5's QVM.run, at the reference's granularity: one identity expression
    subprogram, evaluated against a seeded assignment and a constant table. -/
def run (bytes : List Nat) (consts : List Word256) (mem : Memory) :
    Except Fault (Fr × Memory) :=
  evalQuotientIdentity bytes consts mem

end QVM
```

### proofs/solidity-verifier/templates/partials/verifier/FinalPairing.yul:70
```lean
            // i.e.  e(arg0, [1]_2) = e(arg1, [s]_2).
            //
            // The KZG pairing identity is
            //   e(final_com - v*G + x3*pi, [1]_2) = e(pi, [s]_2),
            // so arg0 must be (final_com - v*G + x3*pi) and arg1 must be
            // pi. The PAIRING_*_MPTR slots store
            //   PAIRING_LHS_MPTR := pi
            //   PAIRING_RHS_MPTR := final_com - v*G + x3*pi
            // -- the historical "LHS"/"RHS" naming follows the dual MSM
            // accumulator (left = pi, right = combined) and *not* the
            // pairing argument order. Pass them swapped to ec_pairing.
            {%- if self.trace %}
            // Trace renders do not revert on a failed final check: `success`
            // (0 or 1) is traced and returned by TraceReturn, so the logs of
            // a rejected proof remain observable. Production renders revert.
            {%- else %}
            if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
            {%- endif %}
            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)
```


# AREA: accumulator + spec + security + lowering-types (formal/Midfall/Halo2/Exec/Accumulator.lean, Halo2/Spec/{Relation,Degrees,Piop,Lemmas}.lean, Security/{SRS,Challenges}.lean, Lowering/{Types,SemanticEquivalence}.lean, State

## constraints
- D-P16 (design.md:335-367): there are TWO AccumulatorEncoding types. Midfall.Halo2.AccumulatorEncoding (Accumulator.lean:180) is the Exec stand-in and is what decodeAcc and encodeAccInstances are typed over. Midfall.Generator.AccumulatorEncoding (Api.lean:413) is the faithful port and is what PLAN 9.5 means (Supported.acc, g.cfg.accumulator : Option Generator.AccumulatorEncoding at Api.lean:822). No conversion exists. The owed reconciliation lemma has to be stated as follows. Take `toExec : Generator.AccumulatorEncoding → Halo2.AccumulatorEncoding` mapping kinds pointAndScalar↦pointAndScalar and pointPair↦pointPair. Then (a) `∀ e n, n < 2^64 - 1 → (e.validateForNumInstances n = .ok () ↔ (toExec e).validFor n = true)`. The bound is NECESSARY: at n = usizeMax with offset + payload > usizeMax, usizeSaturatingAdd makes Generator accept while Exec's unbounded `≤` rejects. (b) `∀ e n t, n < 2^64 - 1 → (e.fixedScalarCount n = .ok t ↔ (toExec e).fixedScalarCount n = some t)`. (c) `∀ e, (match e.fullyCollapsedPublicInputWords with | .ok w => some w | .error _ => none) = (toExec e).fullyCollapsedPublicInputWords`, unconditionally. (d) `e.numLimbBits ≠ 0 → e.coordinateWords = .ok (toExec e).coordinateWords`. Until (a)-(d) exist, no accumulator theorem over the Exec type may be cited as about the deployment. D-P16 item 4 also calls the Exec `max 1` panic masking an R-30-class defect.
- Phantom and implicit parameters. KzgAcc (F G₁ G₂ Gₜ) has G₂ and Gₜ phantom. DualMSM (F G₁ G₂ Gₜ) has G₂ and Gₜ phantom. ParamsVerifierKZG (G₁ G₂) has G₁ phantom. decodeAcc, KzgAcc.trivial, KzgAcc.new, DualMSM.new and DualMSM.init have p, G₂ and/or Gₜ determined only by the expected type, so write (p := p) (G₂ := G₂) (Gₜ := Gₜ) or type-ascribe. AccMsm.asPublicInput and asPublicInputPoint need (G₂ := G₂) (Gₜ := Gₜ) at call sites (see Accumulator.lean:638, :858). AdmissiblePairing has p and Gₜ as outParams (Curve.lean:35-36), so [P : AdmissiblePairing G₁ G₂ Gₜ] pins Gₜ. decodeAcc and accumulate take NO pairing instance. check, batchedCheck, fromDualMsm and encodeAccInstances do.
- PLAN arity mismatches (R-26 tail). decodeAcc has 4 explicit args (enc, codec : G1Codec G₁, fixedBases : Array (AccFixedBase G₁), inst : Array Word256); the PLAN has 2. KzgAcc.check has 3 (a, params, fixedBases : Array (String × G₁)); the PLAN has 2. batchedCheck has 5 (params, alpha, d, a, fixedBases); the PLAN has 4. alphaOf has 7 (H, vkDigest : Word256, codec, kzgLhs, kzgRhs, accLhs, accRhs : G₁); the PLAN has 4 and takes vkd : Fr plus DualMSM/KzgAcc values. PLAN `g.vk.digest` does not exist: VerifyingKey (Exec/VerifyingKey.lean:41) has no digest field. The deployed vk_digest is `feToU256 (bytesToNats (frToRepr vk.transcriptRepr))` (Generator/Vk.lean:763), and the lemma owed is that it equals `.ok (frWord vk.transcriptRepr)`.
- Lean form of the contract accumulator arm (PLAN 9.5 ContractRef.accepts, :440-446). Let tbl := fb.map (fun b => (b.name, b.base)). Then: | some enc => match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb (inst.map frWord) with | none => false | some a => batchedCheck params (alphaOf H (frWord vk.transcriptRepr) E.g1 d.left.eval d.right.eval (a.fullyCollapse tbl).1 (a.fullyCollapse tbl).2) d a tbl. The table MUST be the contract's positive-base table built from the AccFixedBase list, NOT `fixedBases vkName ...`. Argument order for alphaOf is (kzgLhs kzgRhs accLhs accRhs). The hashed order is tag, vk_digest, kzg RHS, kzg LHS, acc RHS, acc LHS (FinalPairing.yul:21-26, Accumulator.lean:1017-1018). A zero draw maps to 1 (yul:30-31, Accumulator.lean:1020), so `alphaOf … ≠ 0` holds by construction. The domain tag is the 29-byte literal LEFT-padded by mstore (Accumulator.lean:132-139).
- R-10 (REVIEW.md:172-220). In accumulator mode the contract and Rust verify_final check different predicates: X·Y^α = 1 versus X·Y^r = 1, with r from the POW2 sponge, which is not ported. Under truncated-challenges the Rust also truncates its powers (R-26.1). Never state an acc-mode contract-vs-Rust equivalence. lowering_equivalence_noAcc and end_to_end_noAcc NEED `g.cfg.accumulator = none`. contractRef_acc_complete is about ContractRef, not Rust. KzgAcc.accumulate takes the batching scalar as an argument for exactly this reason.
- R-25 (REVIEW.md:564-604): decodeAcc_injective is FALSE as written. Under flag = 1, loadAccPoint never reads or range-checks the coordinate words (Accumulator.lean:404-405; AccumulatorHelpers.yul:130-141). accIdentityKats_ok (:1269-1287) is the counterexample. A second, trivial failure: decodeAcc never reads inst words below enc.offset, so any accWords that includes the prefix is also non-injective. For the statement to be true, accWords enc i must (1) be the tail window i.extract enc.offset i.size; (2) for each of the two point slots src ∈ {offset, offset + pointWords + (carried ? 1 : 0)} with i[src + 2*coordinateWords] = 1, replace the 2*coordinateWords coordinate words by 0 (R-25 writes it as `if flag = 1 then (0, 0, 1) else (x, y, 0)`); and (3) keep the flag words, the carried scalar words and the tail words verbatim. Extra hypotheses the proof needs: codec.eipRoundtrip (decoder-first, Codec.lean:106), and Nodup of (fb.map AccFixedBase.name), because accMapInsert overwrites duplicate names (Accumulator.lean:466-474), which loses tail words. i₁.size = i₂.size follows from both decodes succeeding with the same enc and fb (fixedScalarCount = fb.size). Changing the meaning of accWords needs sign-off (R-25 Owner).
- R-26 item 2 (REVIEW.md:617-623), decodeAcc_encode. It is statable ONLY for collapsed shapes: a.lhs = {bases := #[L], scalars := #[sL], fixedBaseScalars := #[]} and a.rhs = {bases := #[R], scalars := #[sR], fixedBaseScalars := tail}. Otherwise AccMsm.asPublicInput's all-bases-then-all-scalars order (:637-640) is mis-read against the decoder's point, scalar, point, scalar, tail order. The honest form is `decodeAcc (toExec enc) codec fb (prefix ++ encodeAccInstances enc' codec a) = some a'` with prefix.size = enc.offset and (toExec enc).limbShapeOk. NEW and not in REVIEW: encodeAccInstances emits the two carried scalars unconditionally, so for enc.kind = .pointPair the tail is 2 words too long and fixedScalarCount returns none. The round trip is therefore FALSE for pointPair unless a kind-aware encoder exists, and Models.lean:863-865 says Moonlight wraps do NOT carry scalars. Restrict to .pointAndScalar or add the encoder.
- R-26 item 3 (REVIEW.md:624-630), negation convention. decodeAcc stores `-w` for fixed bases with negate = true (Accumulator.lean:986-987, the contract reading: positive base, negated scalar). encodeAccInstances emits frWord s verbatim. `= some a` therefore holds only when no base has negate = true. In general the result is the contract-convention relabelling a' (negate the tail scalars whose base has negate = true), and the proof must say which convention it uses. In addition, fb names must be ascending and equal to a.rhs.fixedBaseScalars.map Prod.fst (artifacts.rs:225 sorts by name), because accMapInsert re-sorts while the tail words arrive in fb order. Bridge lemma owed: AccMsm.eval with (name ↦ base, -s) equals eval with (name ↦ base⁻¹, s).
- R-26 item 7 / calldata_canonical. Fr p = ZMod p cannot represent a word ≥ r, so decodeAcc's `< p` checks (Accumulator.lean:974-975) are vacuous when it is fed inst.map frWord. The contract rejects every instance word ≥ r BEFORE absorption: TranscriptProofParser.yul:59-68, `success := and(success, lt(inst_be, r))`, then ERR_NON_CANONICAL_SCALAR. It rejects trailing or missing bytes at VkLoading.yul:102-111 (calldatasize must equal INSTANCE_CPTR + 32*num_instances, then ERR_BAD_CALLDATA_SHAPE). So PLAN §13's worry is answered by the templates. calldata_canonical can be stated strictly IF decodeCalldata is typed over raw Word256s and mirrors both rejections; if it reduces mod r it is false. frWord needs p ≤ 2^256 for (frWord x).toNat = x.val, so add a hypothesis or use p = Midfall.Assumptions.r.
- Codec hypotheses decodeAcc_encode needs and that do NOT exist in the tree. (i) Encoder-first: `∀ Q, codec.ofEip? (codec.toEip Q) = some Q`, deliberately removed from Codec.lean (:97-105). (ii) EIP shape: toEip Q is 16 zero bytes ‖ x_BE(48) ‖ 16 zero bytes ‖ y_BE(48) with x, y < accFpModulus, because loadAccPoint rebuilds bytes as wordToBytesBE hi ‖ lo per coordinate. (iii) `codec.toEip 1 = natToBytesBE 0 128` and `codec.ofEip? (natToBytesBE 0 128) = some 1`, because the encoder's flag uses P.decEqG₁ while the decoder maps flag 1 to zero bytes. (iv) `(x,y) = (0,0) → Q = 1`, because non-identity (0,0) is rejected (Accumulator.lean:409). Codec.lean:69-75 says the concrete codec checks on-curve only, so ofEip?'s subgroup property is itself an open obligation.
- NEW DEFECT, not recorded in REVIEW.md. Midfall.Halo2.fixedBases (Accumulator.lean:500-506) inserts "-G" ↦ `((1 : G₁)⁻¹)`, which is the group IDENTITY. Rust circuits/src/verifier/mod.rs:119 inserts `-S::C::generator()`, and MultiOpen.lean:244-246 builds the "-G" DualMSM term with base `P.g₁⁻¹`. As a result, `KzgAcc.fromDualMsm d "self_vk" (fixedBases "self_vk" ...)` fails sameFixedBase for "-G" on every real proof (P.hG₁ : g₁ ≠ 1) and returns Fault.panic accumulator.rs:114. Any statement routed through fixedBases is about the wrong object. Take the table as a parameter, or fix fixedBases to take the generator (it currently has only [Group G₁]).
- Alignment and totality side conditions. msmSpecific zips with truncation (Msm.lean:52-56), so additivity of addMsm, and hence batched_complete, needs `d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size` (implied by MSMKZG.Wf, Msm.lean:68). A `prepareMsgs`-output-is-Wf lemma is owed. AccMsm has no Wf predicate. AccMsm.eval needs m.scalars.size = m.bases.size, and every fixed name present in the lookup table, because lookupFixedBase returns 1 on a miss (Accumulator.lean:544-548). decodeAcc outputs satisfy both by construction when tbl = fb.map (name, base).
- Orientation. KzgAcc.check and batchedCheck are in DualMSM orientation, e(left, params.sG2Prepared)·e(right, params.nG2Prepared) = 1 (Msm.lean:222-233). PLAN 9.5/S5 writes batchedCheck in contract orientation, e(g.right + α·a.right, g2)·e(g.left + α·a.left, -sg2) = 1. They are bridged by Spec.Lemmas.pairing_reorder (exponent-level only), plus bilinearity and hypotheses tying params.nG2Prepared to the contract's G2_BASE⁻¹ and params.sG2Prepared to NEG_S_G2⁻¹ (R-4 n_g2 divergence; R-11: the swap is at the FinalPairing.yul:88 call site). batched_atMostOneRoot uses [PrimeOrderWith Gₜ p] (available). batched_complete needs no hypothesis on α.
- Instance representation. Exec inst (prepareMsgs/verifyMsgs/ContractRefAccepts) is the SINGLE PUBLIC COLUMN: verifyNative passes committed [[1]] and [[inst.toList]] (Native.lean:215), so decodeAcc sees inst.size = g.cfg.numInstances (enforced on chain by VkLoading.yul:102). Spec.Relation's inst is the D-P11 flat layout over ALL instance columns (instanceAt c r = inst.getD (c*n + r) 0, instLen = numInstanceColumns*n). Any theorem linking ContractRef or verifyMsgs to Spec.Rel must state this mapping explicitly. D-P11 records the [committed, public] order as unconfirmed.
- Naming hazards. Lowering.Supported's `numInstances` parameter is the instance COLUMN count (= 2), unrelated to GeneratorConfig.numInstances (the public word count). Midfall.Lowering.GeneratorError (Types.lean:41) is a placeholder distinct from Midfall.Generator.GeneratorError (Api.lean:309). Spec.Chal/Spec.chalMass (ℝ≥0, Degrees.lean:177/241) duplicate Security.Chal/Security.chalMass (ENNReal, Challenges.lean:23/31) (R-24). Spec.CircuitIndex.blindingFactors : Nat shadows ConstraintSystem.blindingFactors : Except. With both Midfall.Halo2 and Midfall.Generator open, AccumulatorEncoding and AccumulatorEncodingKind are ambiguous, so always qualify.
- Placeholders that are vacuous or incomplete. Lowering.Deployment's four fields are all `True` (Types.lean:71-76), so it is useless as a hypothesis (R-30/R-32 vacuity pattern). Spec.CommittedInstanceZero := True (Relation.lean:137). Lowering.Supported lacks noRotInst, acc, vkPoints, layout and the numCommittedInstances = 1 conjunct. D-P18 (OPEN) says Supported.layout should be `WellFormed ∧ validate = .ok ()`. Supported is meant to be decidable, but ApiFault and GeneratorError derive only BEq, so state acc as `(enc.validateForNumInstances n).isOk = true` or as a match, not as `= .ok ()` under `decide`. ContractRefAccepts has no accumulator arm, and Lowering/Types.lean does not import Exec/Accumulator.
- Frozen file and CI gates. Statements.lean is SHA-256 pinned (Midfall/Statements.sha256, scripts/checks.sh). Do not edit it; filling contractRef_noAcc's sorry, even though it is now provable from Lowering.contractRefAccepts_iff_verifyMsgs, needs a re-pin with sign-off. New statements go in a NEW file. Every new `sorry` must be registered in formal/SORRY.md (generated by scripts/gen_sorry.sh), or CI fails. D-P17: a file containing `theorem` or `lemma` must not import Midfall.Instances.* (checks.sh:42-60). native_decide is banned outside Instances/. The gap policy says a missing proof becomes a named hypothesis structure in Midfall/Assumptions/, and Assumptions/ currently has only Pairing.lean.
- Spec.accepts is a `sorry` DEFINITION (Piop.lean:54-56). Any theorem over it, such as verifyMsgs_iff_spec or verifier_sound/complete against a spec, is about an opaque term. Piop.lean:23-51 forbids defining it by calling Exec, because that would make verifyMsgs_iff_spec a tautology.
- Error-budget constraints (REVIEW R-22, R-23; D-P14). Under Features.solidity (truncatedChallenges := true, Features.lean:30-34) the x1 and x4 rows of roundErr are NOT provable by degree arguments; D-P14 says re-derive them. The .x3 chalMass under truncation is short by about ×1.5 and so is not an upper bound. roundErr .x3 = maxSetSize*n can be below the honest badPointsX3Count = n + badPointsX3Denominator. srsBound = nextPowerOfTwo(n*(csDegree-1)) may be too small. Security/SRS.lean has no AGM adversary, q-DLOG game, ROM or ksGame, so S1/S3/S5/S7 cannot yet be stated over existing types and must abstract them.
- R-39 (REVIEW.md:1157-1187): PLAN render_eq_print (text equality) is false. Restate it structurally, e.g. stmtsBeq (astOf (g.render o)) (L.main), per D-P13. D-P20 (design.md:477-552): qvm_compile_correct, qvm_validated_noOOB, qvm_yul_refines and direct_correct are not statable as written; there is no whole-stream QVM.run/Program/Frame/Output, and the `.oob` fault cannot arise. R-47: there is no FieldConsts.IsWellFormed and no Assumptions/TwoAdicity.lean, so lagrange_spec and the roots-of-unity lemmas need that hypothesis first.
- Unverified compile detail. In decodeAcc (Accumulator.lean:986-987) the tail scalar `s` is a Nat taken from tailWords, and `-s` relies on elaboration resolving the map value type to Fr p. No .olean is present (formal/.lake has no build output for this module), and no KAT calls decodeAcc: the KATs cover only loadAccPoint, decodeAccCoord and encodeAccCoordWords, because decodeAcc needs a curve. Confirm with `#check @Midfall.Halo2.decodeAcc` before stating theorems over it.

## missing
- The ContractRef.accepts accumulator arm: Lowering/Types.lean:83-96 has only the no-acc arm. Port sources: FinalPairing.yul:14-60 and :88, AccumulatorHelpers.yul:190-371, and PLAN 9.5 :440-446. It also needs the generator config g.cfg.accumulator and the AccFixedBase list.
- A Generator.AccumulatorEncoding → Halo2.AccumulatorEncoding conversion plus the D-P16 reconciliation lemma (validFor vs validateForNumInstances, fixedScalarCount, fullyCollapsedPublicInputWords, word counts). Source: proofs/solidity-verifier/src/api.rs:35-188.
- accWords, the normalised accumulator tail words of R-25. It has no Rust counterpart and is derived from AccumulatorHelpers.yul:119-165 (load_acc_point) and :190-371.
- acc_fixed_bases computation: Halo2Verifier.accFixedBases : List (Nat × Bool) exists only as a field (Generator/Models.lean:868), and nothing computes it or names the bases. Producing the Array (AccFixedBase G₁) that decodeAcc needs requires porting proofs/solidity-verifier/src/lowering/artifacts.rs:181-245 (sorted names, VK-point mptrs, negate flags), plus a VK-memory-to-point bridge.
- A kind-aware (PointPair) accumulator public-input encoder: encodeAccInstances always emits carried scalars. Rust: whatever produces the Moonlight point-pair instance, starting from ecc_chip.rs:226-239 as_public_input on fully collapsed points; this was not located in the port.
- An AccMsm.Wf predicate (bases.size = scalars.size), which mirrors the msm.rs:88 and :118 assertions, plus a lemma that prepareMsgs/prepare outputs satisfy MSMKZG.Wf on both DualMSM channels.
- A fix for Midfall.Halo2.fixedBases' "-G" entry: it must be the negated generator, as in circuits/src/verifier/mod.rs:119.
- G1Codec hypotheses for the accumulator round trip (encoder-first ofEip?∘toEip, the EIP-2537 byte shape, and the identity ↔ 128 zero bytes correspondence), as named hypothesis structures in Midfall/Assumptions/. Rust: proofs/src/transcript/implementors.rs:283-299 and the EIP-2537 spec.
- A lemma that the vk_digest word equals frWord vk.transcriptRepr (Generator/Vk.lean:763, feToU256 at Generator/Encoding.lean:1008). Rust: proofs/solidity-verifier/src/lowering/vk.rs:109 (fe_to_u256).
- S5 statements batched_complete, batched_atMostOneRoot and alpha_batching_sound (PLAN :382-386), plus alphaRO. Only the defs alphaOf and batchedCheck exist.
- contractRef_acc_complete (PLAN :477-478): not stated anywhere.
- The POW2 SpongeChip::hash (circuits/src/verifier/accumulator.rs:224-230), deliberately not ported (R-10). Rust-side acc-mode replay would need it.
- Security layer: AGM adversary, qdlogGame, ksGame, the ROM (randomOracle and verifyRO), keygenVK/Spec.Keygen and honestProve. Only SRS, SRS.gen, Rep, Rep.Valid, Chal and chalMass exist.
- Lowering surface: Lowered.plan/shell/consts, SolidityGenerator.lower/render, LoweringPlan, the full Supported g o fields (noRotInst, acc, vkPoints, layout) and a real Deployment world model. Also missing: decodeCalldata, encodeCalldata, calldataOf, repackProof, encodeContractProof, LeanAccepts, RunVerifier, RunContractIR and RunShell (over Midfall.Yul.Bridge.Run per D-P10), irCheck, ObsEquiv, calls/honestCalls, Eip2537.Holds, Modexp.Holds, abiTrue, the per-phase Inv predicates, and QVM.Program/Frame/Output (D-P20). Rust: proofs/solidity-verifier/src/{api.rs, builder/, lowering/, templates/}.
- Assumptions/TwoAdicity.lean with FieldConsts.IsWellFormed (R-47, plans/P-4a-roots.md), needed by lagrange_spec and the domain lemmas.
- A pairing-level bilinearity lemma that lifts Spec.Lemmas.rustEq/contractEq/pairing_reorder to DualMSM.check and batchedCheck over AdmissiblePairing.

## declarations
- `(file-level variable) Accumulator.lean` (Midfall/Halo2/Exec/Accumulator.lean:77)
    sig: variable {p : ℕ} [Fact (Nat.Prime p)]
    notes: Only p is a file variable. Every group binder ({G₁ G₂ Gₜ}, Group, PrimeOrderWith, Module, [P : AdmissiblePairing G₁ G₂ Gₜ]) is written per declaration (D-P7). Every def below whose result mentions Fr p has an implicit {p} that must be pinned by the expected type or (p := p).
- `Midfall.Halo2.AccumulatorEncodingKind` (Midfall/Halo2/Exec/Accumulator.lean:169)
    sig: inductive AccumulatorEncodingKind where | pointAndScalar | pointPair deriving BEq
    notes: Exec stand-in kind (api.rs:48-57). It is a different type from Midfall.Generator.AccumulatorEncodingKind (Api.lean:228).
- `Midfall.Halo2.AccumulatorEncoding` (Midfall/Halo2/Exec/Accumulator.lean:180)
    sig: structure AccumulatorEncoding where offset : Nat numLimbs : Nat numLimbBits : Nat kind : AccumulatorEncodingKind
    notes: The EXEC STAND-IN (D-P16). It derives nothing (no BEq, no DecidableEq). decodeAcc and encodeAccInstances are typed over THIS type only. It masks the api.rs:104 div-by-zero with `max 1` at :206-207, returns Bool/Option, and uses plain Nat + and truncated - where Rust saturates or wraps. Constructors: AccumulatorEncoding.new (:193) and .pointPair (:197), both `(offset numLimbs numLimbBits : Nat) : AccumulatorEncoding`.
- `Midfall.Halo2.AccumulatorEncoding.limbsPerInstance / coordinateWords / pointWords / pointPairWords / hasCarriedScalars / fixedPayloadWords / limbShapeOk` (Midfall/Halo2/Exec/Accumulator.lean:206)
    sig: def limbsPerInstance (enc : AccumulatorEncoding) : Nat := max 1 (254 / enc.numLimbBits) def coordinateWords (enc : AccumulatorEncoding) : Nat := divCeil enc.numLimbs enc.limbsPerInstance def pointWords (enc : AccumulatorEncoding) : Nat := 2 * enc.coordinateWords + accIdentityFlagWords def pointPairWords (enc : AccumulatorEncoding) : Nat := 2 * enc.pointWords def hasCarriedScalars (enc : AccumulatorEncoding) : Bool := enc.kind == .pointAndScalar def fixedPayloadWords (enc : AccumulatorEncoding) : Nat := enc.pointPairWords + if enc.hasCarriedScalars then accCarriedScalars else 0 def limbShapeOk (enc : AccumulatorEncoding) : Bool := enc.numLimbs == accLimbs && enc.numLimbBits == accLimbBits
    notes: Lines 206, 211, 215, 219, 222, 226, 233. At 7x56 the values are limbsPerInstance=4, coordinateWords=2, pointWords=5, and fixedPayloadWords is 12 for pointAndScalar or 10 for pointPair (pinned by accLayoutKats_ok, :1178). Constants: accLimbBits=56 (:89), accLimbs=7 (:93), accLimbsPerWord=4 (:100), accIdentityFlagWords=1 (:104), accCarriedScalars=2 (:108), accFpModulus := Midfall.Assumptions.pBase (:121).
- `Midfall.Halo2.AccumulatorEncoding.validFor` (Midfall/Halo2/Exec/Accumulator.lean:245)
    sig: def validFor (enc : AccumulatorEncoding) (numInstances : Nat) : Bool := enc.limbShapeOk && enc.offset + enc.fixedPayloadWords ≤ numInstances
    notes: Bool. This is the PLAN `enc.validFor g.cfg.numInstances` reading, but over the Exec type. Unbounded Nat + (Rust uses saturating_add).
- `Midfall.Halo2.AccumulatorEncoding.fullyCollapsedPublicInputWords` (Midfall/Halo2/Exec/Accumulator.lean:249)
    sig: def fullyCollapsedPublicInputWords (enc : AccumulatorEncoding) : Option Nat := if enc.limbShapeOk then some enc.fixedPayloadWords else none
    notes: Option rather than Except. It drops the Rust validate(usize::MAX) call, which Nat makes unnecessary.
- `Midfall.Halo2.AccumulatorEncoding.fixedScalarCount` (Midfall/Halo2/Exec/Accumulator.lean:255)
    sig: def fixedScalarCount (enc : AccumulatorEncoding) (numInstances : Nat) : Option Nat :=
    notes: Body: `none` unless validFor holds. Otherwise tail := numInstances - (offset + fixedPayloadWords) (truncated Nat), and pointPair with tail ≠ 0 gives none. decodeAcc calls it with inst.size.
- `Midfall.Halo2.frWord` (Midfall/Halo2/Exec/Accumulator.lean:433)
    sig: def frWord (x : Fr p) : Word256 := BitVec.ofNat 256 x.val
    notes: Implicit {p} [Fact (Nat.Prime p)] comes from the file variable. This is the lift Array (Fr p) -> Array Word256. It loses the contract's `>= r` rejection (R-26.7). BitVec.ofNat wraps, so (frWord x).toNat = x.val needs p ≤ 2^256.
- `Midfall.Halo2.encodeAccCoordWords / checkAccCoordPacking / loadAccCoordShifted / decodeAccCoord / loadAccPoint / coordOfEip` (Midfall/Halo2/Exec/Accumulator.lean:312)
    sig: def encodeAccCoordWords (enc : AccumulatorEncoding) (c : Nat) : Array Word256 := def checkAccCoordPacking (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) : Bool := def loadAccCoordShifted (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) : Nat := def decodeAccCoord (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) : Option (Nat × Nat) := do def loadAccPoint (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) : Option (Bytes × Bool) := do def coordOfEip (b : Bytes) (i : Nat) : Nat :=
    notes: Lines 312, 326, 338, 362, 400, 420. The encoding is coordinate-minus-one mod Fp, so 0 maps to p-1 (the sentinel), with 7 LE limbs of 56 bits packed 4 per word. decodeAccCoord applies three rejections: packing, in-field via (hi,lo) against accFpHi/accFpMinusOneLo, and hi < 2^128. loadAccPoint checks the flag first (flag ≥ 2 → none). For flag = 1 it returns (128 zero bytes, true) WITHOUT reading or range-checking the coordinate words (AccumulatorHelpers.yul:130-141). This is the R-25 malleability. For flag = 0 a decoded (0,0) is rejected.
- `Midfall.Halo2.AccMsm` (Midfall/Halo2/Exec/Accumulator.lean:455)
    sig: structure AccMsm (F G₁ : Type) where bases : Array G₁ scalars : Array F fixedBaseScalars : Array (String × F)
    notes: circuits/src/verifier/msm.rs Msm. fixedBaseScalars is name-ascending (the BTreeMap order). There is NO Wf predicate. Only AccMsm.new (:524) and fromTerms (:531) enforce bases.size = scalars.size, and both return Except Fault.
- `Midfall.Halo2.AccMsm.eval` (Midfall/Halo2/Exec/Accumulator.lean:557)
    sig: def eval {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (m : AccMsm (Fr p) G₁) (fixedBases : Array (String × G₁)) : G₁ :=
    notes: Computes msmSpecific (scalars ++ fixedScalars) (bases ++ looked-up bases). msmSpecific zips with truncation, so the result is mis-aligned unless m.scalars.size = m.bases.size. lookupFixedBase (:544) returns 1 on a name miss, which drops the term silently.
- `Midfall.Halo2.AccMsm.accumulateWithR` (Midfall/Halo2/Exec/Accumulator.lean:569)
    sig: def accumulateWithR {G₁ : Type} (m other : AccMsm (Fr p) G₁) (r : Fr p) : AccMsm (Fr p) G₁ :=
    notes: self + r*other, with the fixed maps merged by accMapInsertAdd (:480).
- `Midfall.Halo2.fixedBases` (Midfall/Halo2/Exec/Accumulator.lean:500)
    sig: def fixedBases {G₁ : Type} [Group G₁] (vkName : String) (fixedCommitments permCommitments : Array G₁) : Array (String × G₁) :=
    notes: DEFECT, newly found and not in REVIEW.md. Line 502 inserts "-G" ↦ `((1 : G₁)⁻¹)`, which is the IDENTITY. Rust circuits/src/verifier/mod.rs:119 inserts `-S::C::generator()`, and Exec/Kzg/MultiOpen.lean:245 uses `P.g₁⁻¹` for the "-G" DualMSM term. The function has only [Group G₁], so it cannot name the generator. Related: fixedBaseNames (:513), fixedCommitmentName (:489), permCommitmentName (:493).
- `Midfall.Halo2.AccMsm.asPublicInputPoint / AccMsm.asPublicInput` (Midfall/Halo2/Exec/Accumulator.lean:600)
    sig: def asPublicInputPoint {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (enc : AccumulatorEncoding) (codec : G1Codec G₁) (Q : G₁) : Array Word256 := def asPublicInput {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (enc : AccumulatorEncoding) (codec : G1Codec G₁) (m : AccMsm (Fr p) G₁) : Array Word256 :=
    notes: Lines 600 and 629. Coordinates come from coordOfEip (codec.toEip Q). The flag is decideBool (P.decEqG₁ Q 1). Output order is ALL bases, then ALL scalars (frWord), then the fixed scalars. Callers must pass (G₂ := G₂) (Gₜ := Gₜ) explicitly.
- `Midfall.Halo2.KzgAcc` (Midfall/Halo2/Exec/Accumulator.lean:662)
    sig: structure KzgAcc (F G₁ G₂ Gₜ : Type) where lhs : AccMsm F G₁ rhs : AccMsm F G₁
    notes: Port of the Rust Accumulator<S> (accumulator.rs:64-73). G₂ and Gₜ are PHANTOM parameters (D-P7), so every use site must pin them.
- `Midfall.Halo2.AccFixedBase` (Midfall/Halo2/Exec/Accumulator.lean:682)
    sig: structure AccFixedBase (G₁ : Type) where name : String base : G₁ negate : Bool
    notes: Uses the contract convention: positive base, negated scalar (artifacts.rs:200, yul:322-326). The generator side has only Halo2Verifier.accFixedBases : List (Nat × Bool) (Models.lean:868), a list of (mptr, negate) pairs with no name and no point.
- `Midfall.Halo2.KzgAcc.new` (Midfall/Halo2/Exec/Accumulator.lean:691)
    sig: def new {F G₁ G₂ Gₜ : Type} (lhs rhs : AccMsm F G₁) : KzgAcc F G₁ G₂ Gₜ :=
    notes: accumulator.rs:190-193.
- `Midfall.Halo2.KzgAcc.fromDualMsm` (Midfall/Halo2/Exec/Accumulator.lean:711)
    sig: def fromDualMsm {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (d : DualMSM (Fr p) G₁ G₂ Gₜ) (namePrefix : String) (fixedBases : Array (String × G₁)) : Except Fault (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
    notes: accumulator.rs:82-133. Terms labelled .fixed i, .permutation i or .custom "-G" move into the name map after sameFixedBase checks the base against the table. A mismatch or a missing key is Fault.panic (accumulator.rs:105/110/114). With the Exec `fixedBases` table, the "-G" check fails on every real DualMSM, because its base is P.g₁⁻¹ ≠ 1.
- `Midfall.Halo2.KzgAcc.check` (Midfall/Halo2/Exec/Accumulator.lean:763)
    sig: def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) (fixedBases : Array (String × G₁)) : Bool :=
    notes: Takes THREE arguments, where the PLAN writes `a.check g.params`. Body: DualMSM.check (DualMSM.new (MSMKZG.fromBase (a.lhs.eval fb)) (MSMKZG.fromBase (a.rhs.eval fb))) params. In DualMSM orientation that is e(lhs, sG2Prepared)·e(rhs, nG2Prepared) = 1.
- `Midfall.Halo2.KzgAcc.trivial / collapse / fullyCollapse` (Midfall/Halo2/Exec/Accumulator.lean:781)
    sig: def trivial {G₁ G₂ Gₜ : Type} [Group G₁] (fixedBaseNames : Array String) : KzgAcc (Fr p) G₁ G₂ Gₜ := def collapse {G₁ G₂ Gₜ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : KzgAcc (Fr p) G₁ G₂ Gₜ := def fullyCollapse {G₁ G₂ Gₜ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (fixedBases : Array (String × G₁)) : G₁ × G₁ :=
    notes: Lines 781, 789, 798. fullyCollapse returns (lhs.eval fb, rhs.eval fb). Those are the ACC_LHS/ACC_RHS points that feed alphaOf.
- `Midfall.Halo2.KzgAcc.accumulate` (Midfall/Halo2/Exec/Accumulator.lean:824)
    sig: def accumulate {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] (F : Features) (numBits : Nat) (r : Fr p) (accs : Array (KzgAcc (Fr p) G₁ G₂ Gₜ)) : Except Fault (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
    notes: No pairing instance. The batching scalar r is an ARGUMENT, which makes R-10 structural: the POW2 sponge is not ported. Powers are truncatedPowers numBits r n when F.truncatedChallenges, else powers r n (R-26.1). An empty array is Fault.panic accumulator.rs:232.
- `Midfall.Halo2.KzgAcc.asPublicInput` (Midfall/Halo2/Exec/Accumulator.lean:850)
    sig: def asPublicInput {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (enc : AccumulatorEncoding) (codec : G1Codec G₁) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 :=
    notes: Output is AccMsm.asPublicInput of lhs followed by that of rhs. It emits the TAIL only, with no prefix.
- `Midfall.Halo2.encodeAccInstances` (Midfall/Halo2/Exec/Accumulator.lean:872)
    sig: def encodeAccInstances {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (enc : AccumulatorEncoding) (codec : G1Codec G₁) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 := KzgAcc.asPublicInput enc codec a
    notes: Same object as KzgAcc.asPublicInput. It does NOT branch on enc.kind: carried scalars are always emitted (via :640). It also never negates scalars for negate bases.
- `Midfall.Halo2.decodeAcc` (Midfall/Halo2/Exec/Accumulator.lean:955)
    sig: def decodeAcc {G₁ G₂ Gₜ : Type} (enc : AccumulatorEncoding) (codec : G1Codec G₁) (fixedBases : Array (AccFixedBase G₁)) (inst : Array Word256) : Option (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
    notes: FOUR explicit args, where the PLAN has two (R-26 tail). There is no pairing or Group instance, and p, G₂, Gₜ are pinned only by the expected type. Port of validate_public_accumulator (AccumulatorHelpers.yul:190-371). The output is always collapsed: lhs = {#[L], #[sL], #[]} and rhs = {#[R], #[sR], fixed}, where fixed is name-keyed via accMapInsert and negated when b.negate. No KAT exercises decodeAcc. Line 987 writes `-s` with s : Nat from tailWords, which type-checks only if the map value type elaborates to Fr p. No .olean is present to confirm, so run `#check @decodeAcc` first.
- `Midfall.Halo2.alphaOf` (Midfall/Halo2/Exec/Accumulator.lean:1014)
    sig: def alphaOf {G₁ : Type} (H : Bytes → H256) (vkDigest : Word256) (codec : G1Codec G₁) (kzgLhs kzgRhs accLhs accRhs : G₁) : Fr p :=
    notes: Preimage order (verbatim): wordToBytesBE accPairingBatchDomainTag ++ wordToBytesBE vkDigest ++ codec.toEip kzgRhs ++ codec.toEip kzgLhs ++ codec.toEip accRhs ++ codec.toEip accLhs, so RHS comes before LHS on both pairs. The ARGUMENT order is the opposite (kzgLhs kzgRhs accLhs accRhs). Then a := frOfDigest (p := p) (H preimage) and `if a = 0 then 1 else a`. Intended instantiation: kzgLhs := d.left.eval (PAIRING_LHS = π), kzgRhs := d.right.eval, (accLhs, accRhs) := a.fullyCollapse tbl. vkDigest is a Word256, not the PLAN's `g.vk.digest : Fr`. The tag (:138) is a 29-byte literal, LEFT-padded.
- `Midfall.Halo2.batchedCheck` (Midfall/Halo2/Exec/Accumulator.lean:1036)
    sig: def batchedCheck {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (params : ParamsVerifierKZG G₁ G₂) (alpha : Fr p) (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (fixedBases : Array (String × G₁)) : Bool :=
    notes: Five args (the PLAN has four, with no lookup table). It EXISTS. It is in DualMSM orientation: check(new (d.left.addMsm (fromBase(a.lhs.eval fb)).scale α) (d.right.addMsm (fromBase(a.rhs.eval fb)).scale α)). The PLAN states it in contract orientation; pairing_reorder bridges the two.
- `Midfall.Halo2.accIdentityKats_ok` (Midfall/Halo2/Exec/Accumulator.lean:1269)
    sig: def accIdentityKats_ok : Bool :=
    notes: Concrete R-25 counterexample: coordinates 12345/54321 under flag=1 decode to the same 128 zero bytes as the canonical identity.
- `Midfall.Generator.AccumulatorEncodingKind` (Midfall/Generator/Api.lean:228)
    sig: inductive AccumulatorEncodingKind | pointAndScalar | pointPair deriving BEq
    notes: Faithful-port kind. A distinct type from Midfall.Halo2.AccumulatorEncodingKind.
- `Midfall.Generator.AccumulatorEncoding` (Midfall/Generator/Api.lean:413)
    sig: structure AccumulatorEncoding where offset : Nat numLimbs : Nat numLimbBits : Nat kind : AccumulatorEncodingKind deriving BEq
    notes: The FAITHFUL port (D-P16). PLAN 9.5's Supported.acc, decodeAcc and encodeAccInstances refer to THIS type. No conversion to the Exec type exists. new (:454) and pointPair (:462) take (offset numLimbs numLimbBits : Nat).
- `Midfall.Generator.AccumulatorEncoding.coordinateWords` (Midfall/Generator/Api.lean:509)
    sig: def AccumulatorEncoding.coordinateWords (self : AccumulatorEncoding) : Except ApiFault Nat := do
    notes: numLimbBits == 0 gives ApiFault.panic api.rs:104. Otherwise the result is divCeil numLimbs (Nat.max (254/bits) 1). pointWords (:527), pointPairWords (:534) and fixedPayloadWords (:551) are all Except ApiFault Nat, and hasCarriedScalars (:545) is Bool.
- `Midfall.Generator.AccumulatorEncoding.fullyCollapsedPublicInputWords` (Midfall/Generator/Api.lean:572)
    sig: def AccumulatorEncoding.fullyCollapsedPublicInputWords (self : AccumulatorEncoding) : Except ApiFault Nat := do
    notes: Defined in a mutual block (:562-633) as validateForNumInstances usizeMax followed by fixedPayloadWords.
- `Midfall.Generator.AccumulatorEncoding.validateForNumInstances` (Midfall/Generator/Api.lean:586)
    sig: def AccumulatorEncoding.validateForNumInstances (self : AccumulatorEncoding) (numInstances : Nat) : Except ApiFault Unit := do
    notes: Checks the shape first, then the tail with usizeSaturatingAdd offset required > numInstances (usizeMax = 2^64-1, :204; usizeSaturatingAdd at :209).
- `Midfall.Generator.AccumulatorEncoding.fixedScalarCount` (Midfall/Generator/Api.lean:622)
    sig: def AccumulatorEncoding.fixedScalarCount (self : AccumulatorEncoding) (numInstances : Nat) : Except ApiFault Nat := do
    notes: tail := usizeSub numInstances (usizeAdd self.offset required), with wrapping arithmetic (:216, :221). pointPair with tail ≠ 0 is an error.
- `Midfall.Generator.ApiFault / GeneratorConfig` (Midfall/Generator/Api.lean:396)
    sig: inductive ApiFault where | error (e : GeneratorError) | panic (site : String) deriving BEq structure GeneratorConfig where numInstances : Nat numCommittedInstances : Nat accumulator : Option AccumulatorEncoding deriving BEq
    notes: GeneratorConfig is at :812 and is the PLAN's g.cfg. Its numInstances is the PUBLIC WORD count, not the column count. ApiFault and GeneratorError (:309) derive BEq only, with no DecidableEq. Midfall.Lowering.GeneratorError (Lowering/Types.lean:41) is a different placeholder type.
- `Midfall.Generator.Halo2Verifier.accFixedBases (field)` (Midfall/Generator/Models.lean:868)
    sig: accFixedBases : List (Nat × Bool)
    notes: A field of `structure Halo2Verifier (Memory Proof : Type) where` (:757), described as (point_mptr, negate_scalar) in BTreeMap order. Nothing in the tree computes it: artifacts.rs:181-245 is unported. Siblings: expectedAccOffset (:860), expectedNumAccLimbs, expectedNumAccLimbBits, and expectedAccHasCarriedScalars (:865, documented 'Moonlight wraps do not').
- `(vk_digest in generator)` (Midfall/Generator/Vk.lean:763)
    sig: let vkDigest ← feToU256 (bytesToNats (frToRepr inputs.vk.transcriptRepr))
    notes: Inside generateBaseVk. VerifyingKey (Exec/VerifyingKey.lean:41) has no digest field, so the PLAN's g.vk.digest does not exist. The contract's VK_DIGEST word is the LE→U256 value of transcriptRepr, i.e. frWord vk.transcriptRepr, but that equality is an owed lemma.
- `Midfall.Halo2.DualMSM / DualMSM.check / MSMKZG.Wf` (Midfall/Halo2/Exec/Kzg/Msm.lean:171)
    sig: structure DualMSM (F G₁ G₂ Gₜ : Type) where left : MSMKZG F G₁ right : MSMKZG F G₁ def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) : Bool := def MSMKZG.Wf {F G : Type} (m : MSMKZG F G) : Prop := m.scalars.size = m.bases.size ∧ m.bases.size = m.labels.size
    notes: DualMSM.check is at :222 and MSMKZG.Wf at :68. G₂ and Gₜ are phantom on DualMSM. check is decideBool (P.decEqGₜ (toMul (e left sG2Prepared + e right nG2Prepared)) 1). DualMSM has no Wf of its own.
- `Midfall.Halo2.ParamsVerifierKZG` (Midfall/Halo2/Exec/Kzg/Params.lean:18)
    sig: structure ParamsVerifierKZG (G₁ G₂ : Type) where sG2 : G₂ nG2Prepared : G₂ sG2Prepared : G₂
    notes: G₁ is phantom. There is no g2 field: the contract's G2_BASE and NEG_S_G2 relate to it only through nG2Prepared = g2⁻¹ (ofParams, :29) and R-4.
- `Midfall.G1Codec / G1Codec.eipRoundtrip / frOfDigest` (Midfall/Common/Codec.lean:81)
    sig: structure G1Codec (G₁ : Type) where ofCompressed? : Bytes → Option G₁ toCompressed : G₁ → Bytes toEip : G₁ → Bytes ofEip? : Bytes → Option G₁ def G1Codec.eipRoundtrip {G₁ : Type} (c : G1Codec G₁) : Prop := ∀ b : Bytes, ∀ P : G₁, c.ofEip? b = some P → c.toEip P = b def frOfDigest {p : ℕ} [Fact (Nat.Prime p)] (d : H256) : Fr p := Nat.cast d.toNat
    notes: eipRoundtrip (:106) is DECODER-first. The encoder-first ofEip? (toEip P) = some P was deliberately removed (:97-105). The concrete codec does not subgroup-check (:69-75). frOfDigest is at :27.
- `Midfall.Halo2.VerifierEnv / Hash / prepareMsgs / verifyMsgs` (Midfall/Halo2/Exec/Native.lean:38)
    sig: structure VerifierEnv (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type) [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where g1 : G1Codec G₁ field : FieldConsts (Fr p) delta : Fr p fewerPointSetsRuntime : Bool abbrev Hash := Bytes → H256 def prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ) := do def verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Except Fault Unit := do
    notes: Hash is at :50, prepareMsgs at :255 and verifyMsgs at :273. The file variables (:30-35) include [P : AdmissiblePairing G₁ G₂ Gₜ]. E.g1 is the codec decodeAcc and alphaOf need. inst here is the single public column (verifyNative :215 passes committed [[1]] and [[inst.toList]]), so in acc mode inst.size = g.cfg.numInstances. verifyNative is at :207 and decodeRust at :228.
- `Midfall.Halo2.Spec.CircuitIndex` (Midfall/Halo2/Spec/Relation.lean:24)
    sig: structure CircuitIndex (Fr : Type) where cs : ConstraintSystem Fr k : Nat fixed : Nat -> Nat -> Fr perm : PermutationAssembly cs k repr : Fr
    notes: The file variable is `variable {p : Nat} [Fact (Nat.Prime p)]` (:18). perm DEPENDS on cs, so a record update of cs alone is rejected (:229-231). Related: CircuitIndex.n (:37) `def CircuitIndex.n (idx : CircuitIndex (Fr p)) : Nat := 2 ^ idx.k`; rowAt (:42); usable (:55) `def CircuitIndex.usable (idx : CircuitIndex (Fr p)) : Array Nat :=`, which is EMPTY if blindingFactors faults.
- `Midfall.Halo2.Spec.Witness / instanceAt / instLen / evalRow / cell / rowTuple` (Midfall/Halo2/Spec/Relation.lean:61)
    sig: structure Witness (idx : CircuitIndex (Fr p)) where advice : Nat -> Nat -> Fr p def instanceAt (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (c r : Nat) : Fr p := inst.getD (c * idx.n + r) 0 def instLen (idx : CircuitIndex (Fr p)) : Nat := idx.cs.numInstanceColumns * idx.n def evalRow (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx) (e : Expression (Fr p)) (i : Nat) : Fr p :=
    notes: Lines 61, 77, 82, 98; cell is at :119 and rowTuple at :130. The Spec instance layout is FLAT over all columns (c*n+r, D-P11). That differs from the Exec inst, which holds only the public column.
- `Midfall.Halo2.Spec.CommittedInstanceZero / Satisfies / Rel` (Midfall/Halo2/Spec/Relation.lean:137)
    sig: def CommittedInstanceZero (idx : CircuitIndex (Fr p)) : Prop := True structure Satisfies (idx : CircuitIndex (Fr p)) (inst : Array (Fr p)) (w : Witness idx) : Prop where committedInstanceZero : CommittedInstanceZero idx gatesVanish : ∀ g ∈ idx.cs.gates, ∀ p' ∈ g.polys, ∀ i ∈ idx.usable, evalRow idx inst w p' i = 0 permutes : ∀ c ∈ idx.perm.cycles, ∀ a ∈ c, ∀ b ∈ c, cell idx inst w a = cell idx inst w b lookupsContained : ∀ L ∈ idx.cs.lookups, ∀ inp ∈ L.inputExpressions, ∀ i ∈ idx.usable, ∃ j ∈ idx.usable, rowTuple idx inst w inp i = rowTuple idx inst w L.tableExpressions j trashcansHold : ∀ T ∈ idx.cs.trashcans, ∀ i ∈ idx.usable, evalRow idx inst w T.selector i = 1 → ∀ c ∈ T.constraintExpressions, evalRow idx inst w c i = 0 def Rel (idx : CircuitIndex (Fr p)) : Set (Array (Fr p) × Witness idx) := { q | Satisfies idx q.1 q.2 }
    notes: Satisfies is at :142 and Rel at :158. CommittedInstanceZero is a vacuous True placeholder. There is no CircuitIndex.Satisfies and no keygen. `Satisfies` exists.
- `Midfall.Halo2.Spec.accepts` (Midfall/Halo2/Spec/Piop.lean:54)
    sig: def accepts (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Prop := sorry
    notes: The variable block (:16-21) has the full pairing binders, but Gₜ does not occur in the signature, so Gₜ and P are not threaded into it. It is a SORRY definition listed in SORRY.md, and Piop.lean:23-51 forbids defining it via Exec.
- `Midfall.Halo2.Spec.Chal / Chal.all / chalMass` (Midfall/Halo2/Spec/Degrees.lean:177)
    sig: inductive Chal where | theta | beta | gamma | trash | y | x | x1 | x2 | x3 | x4 deriving BEq def Chal.all : List Chal := noncomputable def chalMass (F : Features) (s : Nat) : ℝ≥0 := if F.truncatedChallenges then (s : ℝ≥0) / (2 : ℝ≥0) ^ 128 else 3 * (s : ℝ≥0) / (2 : ℝ≥0) ^ 256
    notes: The file variable is `variable {p : ℕ} [Fact (Nat.Prime p)]` (:59). chalMass is at :241 and duplicates Midfall.Security.chalMass (ENNReal), see R-24. Also scalarOrder (:193), scalarOrder_prime (:199), scalarOrder_bracket (:214) and chal_mass_ceiling (:225) `(2 ^ 256 + scalarOrder - 1) / scalarOrder = 3`.
- `Midfall.Halo2.Spec.CircuitIndex.degTheta / degBeta / degGamma / degTrash / numConstraints / degX` (Midfall/Halo2/Spec/Degrees.lean:265)
    sig: def CircuitIndex.degTheta (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.degBeta (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.degGamma (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.degTrash (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.numConstraints (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.degX (idx : CircuitIndex (Fr p)) : Nat := idx.csDegree * idx.n + idx.n
    notes: Lines 265, 290, 303, 318, 374, 394. Helpers: csDegree (:77), blindingFactors (:90; Nat, which shadows the Except-valued ConstraintSystem.blindingFactors), numPermSets (:104), numPermEvalChunks (:112), numGateIdentities (:328), numPermIdentities (:342), numLogupIdentities (:351), numTrashIdentities (:358). degTheta and degBeta are marked CONSERVATIVE.
- `Midfall.Halo2.Spec.CircuitIndex.numPointSets / maxSetSize / maxPolysPerSet / verifierQueries / srsBound / badPointsX / badPointsX3Count / badPointsBetaCount` (Midfall/Halo2/Spec/Degrees.lean:558)
    sig: def CircuitIndex.numPointSets (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.maxSetSize (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.maxPolysPerSet (idx : CircuitIndex (Fr p)) : Nat := def CircuitIndex.verifierQueries (idx : CircuitIndex (Fr p)) : Nat := 10 + idx.cs.numChallenges def CircuitIndex.srsBound (idx : CircuitIndex (Fr p)) : Nat := nextPowerOfTwo (idx.n * (idx.csDegree - 1)) def CircuitIndex.badPointsX (idx : CircuitIndex (Fr p)) (x : Fr p) : Bool := x ^ idx.n == 1 def CircuitIndex.badPointsX3Count (idx : CircuitIndex (Fr p)) : Nat := idx.n + idx.badPointsX3Denominator
    notes: Lines 558, 570, 584, 608, 626, 640, 676; badPointsBetaCount is at :685. All are computed from the shape model queryShapes (:481), shapeSets (:530) and ShapeCom (:417).
- `Midfall.Halo2.Spec.Degrees / CircuitIndex.degrees / roundErrDegrees / roundErr / ksErrDegrees / ksErr` (Midfall/Halo2/Spec/Degrees.lean:696)
    sig: structure Degrees where degTheta : Nat degBeta : Nat degGamma : Nat degTrash : Nat numConstraints : Nat degX : Nat maxPolysPerSet : Nat numPointSets : Nat maxSetSize : Nat n : Nat verifierQueries : Nat noncomputable def roundErrDegrees (F : Features) (d : Degrees) : Chal → ℝ≥0 noncomputable def roundErr (F : Features) (idx : CircuitIndex (Fr p)) : Chal → ℝ≥0 := roundErrDegrees F idx.degrees noncomputable def ksErrDegrees (F : Features) (d : Degrees) (qH : Nat) : ℝ≥0 := noncomputable def ksErr (F : Features) (idx : CircuitIndex (Fr p)) (qH : Nat) : ℝ≥0 := ksErrDegrees F idx.degrees qH
    notes: Lines 696, 722, 738, 752, 765, 770. The .x3 row is chalMass (maxSetSize*n) and the .x4 row is chalMass (numPointSets+1), both verbatim from the plan.
- `Midfall.Halo2.Spec.CircuitIndex.WellFormed` (Midfall/Halo2/Spec/Degrees.lean:810)
    sig: structure CircuitIndex.WellFormed (idx : CircuitIndex (Fr p)) (F : Features) : Prop where csDegreeOk : idx.cs.degree = .ok idx.csDegree blindingFactorsOk : idx.cs.blindingFactors = .ok idx.blindingFactors chunkLenPositive : 3 ≤ idx.csDegree singlePhase : idx.cs.numChallenges = 0 committedInstancesOn : F.committedInstances = true fewerPointSetsOff : F.outerFewerPointSets = false nBelowField : idx.n ≤ p lookupRectangular : ∀ L ∈ idx.cs.lookups, 1 ≤ L.inputExpressions.size ∧ 1 ≤ L.tableExpressions.size ∧ ∀ inner ∈ L.inputExpressions, inner.size == L.tableExpressions.size sigmaCountMatches : idx.perm.sigmaCommitments.size == idx.cs.permutation.columns.size shapesGroup : (idx.shapeSets).toOption.isSome usableNonempty : idx.blindingFactors + 3 < idx.n
    notes: Index-level well-formedness. The VK-level twin is VerifyingKey.WellFormed (Exec/VerifyingKey.lean:109).
- `Midfall.Halo2.Spec.Lemmas.rustEq / contractEq / pairing_reorder / rustEq_iff / contractEq_iff / dualMsm_scale_check / contractEq_scale / zH_vanishes / rotate_omega_eq` (Midfall/Halo2/Spec/Lemmas.lean:26)
    sig: def rustEq {R : Type*} [CommRing R] (xL xR s : R) : Prop := xL * s - xR = 0 def contractEq {R : Type*} [CommRing R] (xL xR s : R) : Prop := xR - s * xL = 0 theorem pairing_reorder {R : Type*} [CommRing R] (xL xR s : R) : rustEq xL xR s ↔ contractEq xL xR s theorem dualMsm_scale_check {R : Type*} [Field R] (xL xR s c : R) (hc : c ≠ 0) : rustEq (c * xL) (c * xR) s ↔ rustEq xL xR s theorem contractEq_scale {R : Type*} [Field R] (xL xR s c : R) (hc : c ≠ 0) : contractEq (c * xL) (c * xR) s ↔ contractEq xL xR s theorem zH_vanishes {F : Type*} [Field F] (ω : F) (n i : ℕ) (h : ω ^ n = 1) : (ω ^ i) ^ n = 1 theorem rotate_omega_eq {F : Type*} [Field F] (ω : F) (i rot : ℕ) : ω ^ (i + rot) = ω ^ i * ω ^ rot
    notes: Lines 26, 29, 31, 48, 52, 100, 115, 64, 81. All are proved. They are EXPONENT-level only, so lifting them to the AdmissiblePairing needs a bilinearity lemma that is not yet stated. The reduced-index rotate form is deferred (R-47).
- `Midfall.Security.SRS / SRS.gen / Rep / Rep.Valid` (Midfall/Security/SRS.lean:33)
    sig: structure SRS (G₁ G₂ : Type) (N : Nat) where g1Pow : Fin N → G₁ g2 : G₂ sg2 : G₂ def SRS.gen (N : Nat) (τ : ZMod p) : SRS G₁ G₂ N where structure Rep (p : Nat) (G₁ : Type) (N : Nat) where pt : G₁ coeff : Fin N → ZMod p def Rep.Valid {N : Nat} (s : SRS G₁ G₂ N) (r : Rep p G₁ N) : Prop := Additive.toMul (∑ i : Fin N, (r.coeff i) • Additive.ofMul (s.g1Pow i)) = r.pt
    notes: SRS.gen is at :43, Rep at :50, Rep.Valid at :56. The file variables (:24-29) include [P : AdmissiblePairing G₁ G₂ Gₜ], which SRS.gen uses in its body (P.g₁, P.g₂). There is NO AGM adversary type, no q-DLOG game, no ROM and no ksGame, even though the header claims 'q-DLOG hardness is stated over it'.
- `Midfall.Security.Chal / chalMass / challenge_mass_constant` (Midfall/Security/Challenges.lean:23)
    sig: inductive Chal where | theta | beta | gamma | trash | y | x | x1 | x2 | x3 | x4 noncomputable def chalMass (F : Halo2.Features) (s : Nat) : ENNReal := if F.truncatedChallenges then (s : ENNReal) / (2 : ENNReal) ^ 128 else 3 * (s : ENNReal) / (2 : ENNReal) ^ 256 theorem challenge_mass_constant : 2 * 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 < 2 ^ 256 ∧ 2 ^ 256 < 3 * 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
    notes: chalMass is at :31 and challenge_mass_constant at :39. Security.Chal derives nothing (no BEq), unlike Spec.Chal. Statements.lean imports this file. This is the duplicate R-24 records.
- `Midfall.Lowering.Lowered` (Midfall/Lowering/Types.lean:34)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject
    notes: The PLAN fields plan, shell and consts are missing. YulBlock is YulSemantics.Block Op and YulObject is YulSemantics.Object Op, with Op := YulSemantics.EVM.Op (:22-28).
- `Midfall.Lowering.Supported` (Midfall/Lowering/Types.lean:51)
    sig: structure Supported (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat) (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where advice : numAdvice ≠ 0 instShape : numInstances = 2 singlePhase : numChallenges = 0 hLimbs : numQuotientLimbs = csDegree - 1 qvm : qvmValidated production : trace = false ∧ gasCheckpoints = false
    notes: A Nat-parameterised placeholder, not Supported g o. Its `numInstances` is the instance COLUMN count. It lacks noRotInst, acc, vkPoints, layout (D-P18 open) and the `numCommittedInstances = 1` half of instShape.
- `Midfall.Lowering.Deployment` (Midfall/Lowering/Types.lean:71)
    sig: structure Deployment (vkRuntime : Bytes) (evaluator : Option YulObject) (vkCodehash quotientCodehash : H256) : Prop where vkCode : True vkHash : True qObj : True qHash : True
    notes: Every field is True, so the structure is VACUOUS.
- `Midfall.Lowering.ContractRefAccepts` (Midfall/Lowering/Types.lean:83)
    sig: def ContractRefAccepts {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool :=
    notes: Body: match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with | .error _ => false | .ok d => DualMSM.check d params. It covers the NO-ACCUMULATOR case only, has no generator config, and hard-codes Features.solidity. Lowering/Types does not import Exec/Accumulator.
- `Midfall.Lowering.contractRefAccepts_iff_verifyMsgs` (Midfall/Lowering/SemanticEquivalence.lean:29)
    sig: theorem contractRefAccepts_iff_verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : ContractRefAccepts E H params vk inst ms = true ↔ verifyMsgs E H Features.solidity params vk inst ms = .ok ()
    notes: PROVED (cases on prepareMsgs, then simp). It holds for any H. The file variables (:18-23) use the anonymous [AdmissiblePairing G₁ G₂ Gₜ].
- `Midfall.Statements.verifyNative_iff_msgs` (Midfall/Statements.lean:43)
    sig: theorem verifyNative_iff_msgs : verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔ ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧ verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by sorry
    notes: Section variables (:37-39): (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes). The file variables (:29-34) include [P : AdmissiblePairing G₁ G₂ Gₜ]. The file is FROZEN and SHA-pinned (Statements.sha256).
- `Midfall.Statements.verifyMsgs_iff_spec` (Midfall/Statements.lean:57)
    sig: theorem verifyMsgs_iff_spec (hwf : vk.WellFormed F) : (verifyMsgs (Gₜ := Gₜ) E H F params vk inst ms).isOk ↔ Spec.accepts H F params vk inst ms := by sorry
    notes: Section variables (:51-54) add (H : Hash) and (ms : List (Msg (Fr p) G₁)). hwf is VerifyingKey.WellFormed, not CircuitIndex.WellFormed. Unprovable until Spec.accepts exists.
- `Midfall.Statements.contractRef_noAcc` (Midfall/Statements.lean:73)
    sig: theorem contractRef_noAcc : Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms ↔ verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () := by sorry
    notes: The Bool is coerced to Prop. It follows immediately from Lowering.contractRefAccepts_iff_verifyMsgs with H := keccak256, but filling the sorry changes the pinned SHA.

## verbatim excerpts

### Midfall/Halo2/Exec/Accumulator.lean:662
```lean
structure KzgAcc (F G₁ G₂ Gₜ : Type) where
  /-- rust: lhs -/
  lhs : AccMsm F G₁
  /-- rust: rhs -/
  rhs : AccMsm F G₁

/-- One of the fixed bases the generated verifier embeds for the accumulator
    RHS tail. rust: proofs/solidity-verifier/src/lowering/artifacts.rs:181-227,
    where each entry is `(name, mptr, negate)` and the list is sorted by name at
    :225 to match the BTreeMap order the circuit encodes in.

    `negate` is a sign convention that exists only on the contract side: the
    circuit's fixed base for `-G` is the negated generator
    (circuits/src/verifier/mod.rs:119), while the contract embeds the *positive*
    G1 base from the VK header and negates the public scalar instead
    (artifacts.rs:200 and AccumulatorHelpers.yul:322-326, which is careful to
    reject `s >= r` *before* negating because `mod(sub(r, s), r)` is not `-s`
    for a non-canonical `s`). Both compute the same group element; the port
    models the contract's reading, so the base is positive and the scalar
    carried in `fixedBaseScalars` is the negated one. -/
structure AccFixedBase (G₁ : Type) where
  name : String
  base : G₁
  /-- rust: the `bool` third component of the `(String, usize, bool)` triple. -/
  negate : Bool
```

### Midfall/Halo2/Exec/Accumulator.lean:955
```lean
def decodeAcc {G₁ G₂ Gₜ : Type}
    (enc : AccumulatorEncoding) (codec : G1Codec G₁)
    (fixedBases : Array (AccFixedBase G₁)) (inst : Array Word256) :
    Option (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
  let tail ← AccumulatorEncoding.fixedScalarCount enc inst.size
  if fixedBases.size != tail then none
  else
    let carried := enc.hasCarriedScalars
    let pw := enc.pointWords
    let lhsSrc := enc.offset
    -- yul:211, :273-280: the scalar slot exists only in the carried-scalar
    -- layout, and the rhs point follows it.
    let lhsScalarIdx := lhsSrc + pw
    let rhsSrc := lhsScalarIdx + if carried then 1 else 0
    let rhsScalarIdx := rhsSrc + pw
    let tailIdx := rhsScalarIdx + if carried then 1 else 0
    let lhsScalarWord := (inst.getD lhsScalarIdx 0).toNat
    let rhsScalarWord := (inst.getD rhsScalarIdx 0).toNat
    let tailWords := (List.range tail).map (fun j => (inst.getD (tailIdx + j) 0).toNat)
    if (carried && ! (lhsScalarWord < p)) || (carried && ! (rhsScalarWord < p)) ||
       tailWords.any (fun w => ! (w < p)) then none
    else
      let (lhsBytes, _) ← loadAccPoint enc inst lhsSrc
      let (rhsBytes, _) ← loadAccPoint enc inst rhsSrc
      let lhs ← codec.ofEip? lhsBytes
```

### Midfall/Halo2/Exec/Accumulator.lean:980
```lean
      let rhs ← codec.ofEip? rhsBytes
      let lhsScalar : Fr p := Nat.cast (if carried then lhsScalarWord else 1)
      let rhsScalar : Fr p := Nat.cast (if carried then rhsScalarWord else 1)
      -- yul:314-337: the tail scalars pair with the generated bases in name
      -- order, and a negated base takes the negated scalar. A zero tail scalar
      -- is left out of the MSM input (yul:327) which is the same value.
      let fixed := (List.zip fixedBases.toList tailWords).foldl
        (fun acc (b, s) => accMapInsert acc b.name (if b.negate then -s else s)) #[]
      let lhsMsm : AccMsm (Fr p) G₁ :=
        { bases := #[lhs], scalars := #[lhsScalar], fixedBaseScalars := #[] }
      let rhsMsm : AccMsm (Fr p) G₁ :=
        { bases := #[rhs], scalars := #[rhsScalar], fixedBaseScalars := fixed }
      return { lhs := lhsMsm, rhs := rhsMsm }
```

### Midfall/Halo2/Exec/Accumulator.lean:1014
```lean
def alphaOf {G₁ : Type}
    (H : Bytes → H256) (vkDigest : Word256) (codec : G1Codec G₁)
    (kzgLhs kzgRhs accLhs accRhs : G₁) : Fr p :=
  let preimage := wordToBytesBE accPairingBatchDomainTag ++ wordToBytesBE vkDigest ++
    codec.toEip kzgRhs ++ codec.toEip kzgLhs ++ codec.toEip accRhs ++ codec.toEip accLhs
  let a := frOfDigest (p := p) (H preimage)
  if a = 0 then 1 else a
```

### Midfall/Halo2/Exec/Accumulator.lean:1036
```lean
def batchedCheck {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (params : ParamsVerifierKZG G₁ G₂) (alpha : Fr p)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (fixedBases : Array (String × G₁)) : Bool :=
  let accL := (MSMKZG.fromBase (a.lhs.eval fixedBases)).scale alpha
  let accR := (MSMKZG.fromBase (a.rhs.eval fixedBases)).scale alpha
  DualMSM.check (DualMSM.new (d.left.addMsm accL) (d.right.addMsm accR)) params
```

### Midfall/Halo2/Exec/Accumulator.lean:245
```lean
def validFor (enc : AccumulatorEncoding) (numInstances : Nat) : Bool :=
  enc.limbShapeOk && enc.offset + enc.fixedPayloadWords ≤ numInstances

/-- rust: api.rs:134-139 (fully_collapsed_public_input_words). -/
def fullyCollapsedPublicInputWords (enc : AccumulatorEncoding) : Option Nat :=
  if enc.limbShapeOk then some enc.fixedPayloadWords else none

/-- rust: api.rs:173-188 (fixed_scalar_count). `none` is the Rust's `Err`:
    either the encoding is not the supported one / does not fit
    (`validate_for_num_instances`) or it is a point-pair with a non-empty tail. -/
def fixedScalarCount (enc : AccumulatorEncoding) (numInstances : Nat) : Option Nat :=
  if ! (enc.validFor numInstances) then none
  else
    let tail := numInstances - (enc.offset + enc.fixedPayloadWords)
    if enc.kind == .pointPair && tail != 0 then none else some tail
```

### Midfall/Generator/Api.lean:586
```lean
def AccumulatorEncoding.validateForNumInstances (self : AccumulatorEncoding)
    (numInstances : Nat) : Except ApiFault Unit := do
  if self.numLimbs ≠ AccumulatorEncoding.supportedNumLimbs
      || self.numLimbBits ≠ AccumulatorEncoding.supportedNumLimbBits then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "expected 7 radix-2^56 limbs per BLS12-381 base-field coordinate")))
  -- API:159. Safe with respect to the panic at API:104: the check above has
  -- already rejected every num_limb_bits other than 56.
  let requiredWords ← self.fixedPayloadWords
  if usizeSaturatingAdd self.offset requiredWords > numInstances then
    throw (ApiFault.error (GeneratorError.unsupportedAccumulatorEncoding
      (offset := self.offset) (numLimbs := self.numLimbs)
      (numLimbBits := self.numLimbBits) (numInstances := numInstances)
      (reason := "accumulator public-input tail exceeds num_instances")))
  pure ()
```

### Midfall/Halo2/Exec/Accumulator.lean:500
```lean
def fixedBases {G₁ : Type} [Group G₁] (vkName : String)
    (fixedCommitments permCommitments : Array G₁) : Array (String × G₁) :=
  let m0 : Array (String × G₁) := accMapInsert #[] "-G" ((1 : G₁)⁻¹)
  let m1 := (List.range fixedCommitments.size).foldl
    (fun m i => accMapInsert m (fixedCommitmentName vkName i) (fixedCommitments.getD i 1)) m0
  (List.range permCommitments.size).foldl
    (fun m i => accMapInsert m (permCommitmentName vkName i) (permCommitments.getD i 1)) m1
```


# AREA: Quotient VM: Midfall.Generator.Quotient.{VmTypes,VmReference,VmBuilder,VmCertify} (formal/Midfall/Generator/Quotient/*.lean), plus the Rust it ports (vm/{mod,reference,certify}.rs, quotient.rs) and the Yul fold and evalu

## constraints
- D-P20 item 1 (design.md:479-505, addendum after P-09d): the PLAN form `QVM.run L.plan.qprog (frameOf ...) = .ok (outputOf ...)` is NOT statable. There is no QVM.Program, QVM.Frame or QVM.Output, no LoweringPlan (P-11), and no frameOf, outputOf or quotientParts. The reference entry point is per-identity: `Midfall.Generator.evalQuotientIdentity seg consts mem` (= QVM.run) applied to `seg := (bytes.drop cursor).take (exprEnd - cursor)`, where `QuotientCertify.identitySegment bytes cursor = .ok (exprEnd, foldOp)`.
- qvm_compile_correct is STATABLE TODAY per identity, over: `r : QuotientBuilder.QuotientShapeRecognizers`, `s : QuotientBuilder.QuotientProgramBuilder` (builderDefault / withLimbVmOps b), `QuotientExpr`, `QuotientTarget`, `Option Nat` gap, `QuotientProgramBuild` (from `QuotientBuilder.finish`), `qvmBytesToNats build.bytes : List Nat`, `build.consts : List Word256`, Nat cursors, `QuotientRefMemory`, `QVMFr` and `QVMFault`. Two forms: (a) whole program as certifier success: build = local driver over plan.items, then for every consistent mem `certifyItemWalk plan build bytes mem = .ok (bytes.length, _)`, hence `certifyQuotientProgram plan build vk = .ok ()` for every vk; (b) a value lemma for each `.identity i` item. The plan-items driver must be defined locally, because quotient.rs:2120 build_quotient_program_items_with_limb_ops is not ported. Mirror `QuotientCertifyKats.buildStream` (VmCertify.lean:855), but thread `r` and use `plan.selectorFold.gapFor i`.
- Builder success must be a hypothesis (`= .ok _`): emitExpr, identityExpr and finish are `M _ = Except QVMFault _` and carry about 40 panic sites, including more than 65536 constants, u16/u24 overflow, a selector index > 255 and a gap > 0xffff.
- Compile correctness is FALSE for arbitrary hooks. Required: a RecognizersSound r predicate (to be defined). pow5Base e = some b means e ≡ b^5. limbShape e = some sh means sh.wellFormed, every pointer ≤ 0xffff, and denote sh ≡ e. limbSubshape e = some (sh, res, matched) means e ≡ denote sh + res, denote sh ≡ Σ matched, and matched ≠ [] (KAT emptyMatchedHookIsAFrontier_ok shows an empty list breaks the stack). modarith7Shape e = some sh means each lin block has 7 terms, each row 7 terms, each pairwise block 13 coefficients, block counts ≤ 255, and denote ≡ e. noShapeRecognizers is sound vacuously; it is the baseline build. A shape denotation must be written by the author: VmReference has only byte decoders.
- Memory is threaded state. The VM and the oracle read addresses in different orders: emitBinaryExpr's lhs-leaf path emits rhs first; tryEmitAddProduct is tried with swapped operands; AFFINE_SUM puts linear terms before products; certifyItemWalk feeds the VM's output memory into the oracle. Theorems must compare VALUES only (Prod.fst) under a cache-consistency invariant, e.g. ∀ (d,a,v) ∈ mem.cache, v = deriveReferenceMemory mem.seed d a. They must never equate returned memories.
- Quantifying over QuotientRefMemory only ranges over Keccak-PRNG assignments, so it cannot be instantiated to real EVM memory. To compose with Yul, define a valuation-parametric shadow evaluator with ρ : Nat → Nat → QVMFr (domain, address), where literal p ↦ ρ 0 p and token t o ↦ ρ (1+t) o. Prove the ported evaluators equal it at ρ := deriveReferenceMemory seed (domain % 256, address mod 2^32 via natToBytesBE · 4). Then prove compile correctness ∀ ρ, which is strictly stronger than the Rust's Schwartz-Zippel sample (VmCertify.lean:31-48).
- QVMFr is `abbrev QVMFr : Type := Nat`, mod qvmFrModulus, and is not ZMod. To bridge to Midfall.Halo2 `Fr p` (ZMod p, [Fact (Nat.Prime p)]) you need a lemma qvmFrModulus = Midfall.Assumptions.r (Halo2/Spec/Degrees.lean:193; primality from BLS12_381.ScalarField_is_prime, :199). Today the tie is only the Bool KAT qvmFrModulus_agreesWithBlsR_ok. `native_decide` is banned outside Instances/ (scripts/checks.sh:26-33).
- D-P17 (design.md:369-394): the theorem file must not import Midfall.Instances.* (CI gate in checks.sh:42-60). None of VmTypes, VmReference, VmBuilder, VmCertify or Models imports Instances, so they are safe to import.
- qvm_validated_noOOB is NOT statable as written. D-P20 item 2: QVMFault has no `.oob`, and the PRNG memory makes every read succeed. PLAN's `validateQuotientProgramOperands g.plan` also has the wrong arity: Rust is `validate_quotient_program_operands(bytes: &[u8], model: &QuotientOperandModel) -> Result<(), String>` (vm/mod.rs:2139), with the model built by plan.rs:626 `quotient_operand_model(meta, data, vk, vk_mptr, memory, build, selector_fold)`. No Lean port exists: P-09e is READY (plans/P-09e-validator.md), formal/Midfall/Generator/Quotient/VmValidator.lean does not exist, and no work is in flight in git status. Restatable today, as our own definition, over the two real fault classes: segments of builder-produced programs never return .readPastEnd/.constSlotOutOfRange (nor any non-panic fault) when all consts are canonical. The memory-window bound is about the Yul/EVM layer: QuotientReadModel windows (plan.rs:570-618) are vk_payload, user_challenges, theta..instance_eval+0x20 and decoded_proof_evals. It can only be stated with abstract variables until P-09e lands.
- qvm_yul_refines can only be stated ABSTRACTLY. There is no Lean Yul AST for QuotientNumeratorBlock.yul or Halo2QuotientEvaluator.sol (templates are P-13; Generator renders strings), no RunContract and no evaluatorObject. The only Yul types are Midfall.Lowering.YulObject and Lowered.evaluator. D-P20 item 4: there is no Rust proof structure for this leg (reference.rs:20-27 assigns it to conformance tests and trace differentials).
- THE FOLD LIVES ONLY IN YUL and nothing in Lean executes it (D-P20 addendum, P-09d F-6). FOLD_MAIN (QuotientNumeratorBlock.yul:1284-1299): qn := qn*y + q_eval at program.eval_numer_mptr (init 0 at :162). FOLD_SELECTOR (:1303-1341): qn := qn*y, then bucket[sel] := bucket[sel] * y^gap (only if gap ≠ 0) + q_eval, with y-powers precomputed. Selector tails (:1382) multiply each bucket by y^tailExponent. Final (:1393-1394): QUOTIENT_EVAL_MPTR := addmod(0, sub(r, qn), r). The inline prefix (:198) runs before the VM, structured-tail blocks (:1368) after it, and native arms (:1205-1279) fold whole families themselves. Those snippets are produced by quotient.rs push_structured_main_fold (1342), push_structured_fold_advance (1092), push_quotient_eval_numer_add (1076), direct_quotient_block (997) and compact_quotient_computation_blocks (2000), none of them ported. yul_emit.rs does NOT emit the fold: it is the Expression→Yul-lines Evaluator. So the P-09 overview table row 'P-09e yul_emit.rs → qvm_yul_refines' is misattributed.
- A whole-stream fold must be a NEW definition. Proof obligation: Horner over the global y-order (inlineIdentities ++ expanded items ++ structuredTailIdentities) equals Σ e_i y^(m-1-i). This must match computeLinearizationCommitment's reverse fold (R-16, and REVIEW.md:420-427 on the None bucket and reverse y). The bucket key needs translating: QVM selector index s maps to fixed column plan.sortedSimple[s], which is sorted, so the ordering matches. identityValues' zeros for native items must NOT be used as y-position values.
- EVALUATOR FRAME (calldata of Halo2QuotientEvaluator). Calldata is exactly memory[frame_base, frame_base+frame_len), with frame_base = vk_mptr and frame_len = max(vk_mptr + vk_len, reversed_evals_mptr + num_evals*32) - vk_mptr. It is built by VerifierBuildInputs::quotient_external_frame (quotient.rs:760-776) via quotient_external_frame_from_bounds (quotient.rs:778-794), into record QuotientExternal (models.rs:640; Lean Models.lean:531, builders unported). The contract reverts (revert(0,0)) iff calldatasize ≠ QUOTIENT_FRAME_LEN, otherwise it calldatacopies to QUOTIENT_FRAME_BASE (Halo2QuotientEvaluator.sol:110-118). It returns output_len = 0x40 + 32*numSimpleSelectors bytes from QUOTIENT_OUTPUT_MPTR: [QUOTIENT_MAGIC, mload(QUOTIENT_EVAL_MPTR) = -ν_y(x), SELECTOR_ACC buckets] (:156-167). Other failures go through q_program_fail.
- The frame CONTAINS THE PROGRAM. The const table sits at vk_mptr + quotient_const_offset_words and the packed bytecode at vk_mptr + quotient_program_offset_words (quotient.rs:189-217, PackedProgramCodec.encodeWords). The evaluator therefore interprets whatever bytecode the caller supplies. Any qvm_yul_refines frame well-formedness hypothesis must pin the frame's VK window to the pinned payload (L.vkRuntime / Halo2VerifyingKey.bytes), or the statement is false for adversarial calldata.
- Yul and reference diverge in two places. (1) Constants: fqFromU256 panics on value ≥ r, while Yul PUSH_CONST does a raw mload and only addmod/mulmod reduce. A hypothesis is needed: ∀ c ∈ build.consts, c.toNat < qvmFrModulus, or the result must be stated mod r. (2) Tokens: in the reference, token t reads independent domain 1+t, while Yul resolves token t to tokenBase(t) + offset (QuotientNumeratorBlock.yul:538-566, 591-620). The two are only related through the ∀ρ statement with ρ(1+t, o) := mload(tokenBase t + o). The token must be one of the nine table tokens; token 0xff wraps into the literal domain (KAT tokenDomainU8Wrap_releaseProfile_ok).
- Width hazards in the builder. emitU32 truncates mod 2^32 silently (VmBuilder.lean:348). pushByte pushes a raw token Nat into `bytes : List Nat`, and only finish's qvmBytesOfNats truncates it. So state theorems on `qvmBytesToNats build.bytes` (post-finish), never on the builder's `s.bytes`, or carry a hypothesis that pointers are < 2^32 and tokens < 256.
- Compaction runs once over the whole stream (finish), but it only merges adjacent fused affine ops, which cannot straddle a fold or native byte. Proof obligation: segments of compactQuotientRuns(raw) are the compactions of the raw segments, and compaction preserves value. Today this is backed only by KATs.
- Fuel everywhere: evalQuotientIdentityLoop.go, identitySegment.go, compactGo/compactScan, usageGo, emitExpr (emitFuel = 8*(nodeCount+1)), parseExpr (parseFuel) and segmentMaxStackGo. The 'fuel never binds' facts are Bool KATs only; proofs need fuel-adequacy lemmas. `where`-local defs unfold as e.g. `QuotientCertify.identitySegment.go`.
- BEq-only derivations: QuotientExpr, QuotientMem, QuotientTarget, QuotientIdentity, QuotientProgramPlan, QVMFault and QuotientProgramBuild derive BEq, not DecidableEq or LawfulBEq. checkFold uses `identity.target == QuotientTarget.main`. Use `=` in statements and prove `==`-to-`=` lemmas by cases.
- Error types differ by layer: interpreter and builder use `Except QVMFault`, while certifier and identitySegment use `Except String` (QVMFault.message). Do not equate Excepts across layers. Map with faultToString (VmCertify.lean:374).
- The per-identity domain excludes inline identities, structured-tail identities and native callbacks. They never reach bytecode (VmReference.lean:42-56). Their correctness must be stated separately, over Yul (direct_correct-style) or over QuotientIdentity.lines; direct mode is deferred to M10 (PLAN 14.8).
- Stale or naming hazards. The P-09 overview (plans/P-09-quotient-vm.md) letters differ from the landed packages: P-09d is certify.rs and P-09e is the validator, while recognizers are P-09f per P-09e hazard 6. VmBuilder's header 'A DIVERGENCE IN P-09a' is stale since commit 8bd7b37, which fixed VmTypes coefficientOperands (VmTypes.lean:585-592 now has the != 0 guard), so it now agrees with QuotientBuilder.modarith7Coeffs.
- R-16 (REVIEW.md:345-365) ordering traps bind any fold or batching lemma: permutation .enumerate().rev().skip(1), last-set constraint second, and trash left-fold Horner.

## missing
- validateQuotientProgramOperands (QVM-01): Rust vm/mod.rs:2139 validate_quotient_program_operands(bytes, &QuotientOperandModel). It needs validate_quotient_program (2009), QuotientReadWindow (2031), QuotientReadModel (2054), QuotientOperandModel (2085), QuotientOperand (2100), validate_quotient_const_slots (2186), visit_quotient_operands (2314), validate_quotient_mem_token (~2758), decode_byte_quotient_instruction / apply_quotient_stack_effect, plan.rs quotient_operand_model (626) and quotient_read_model (570). P-09e is READY and not started: no VmValidator.lean exists.
- Shape recognizers: quotient_limb_shape (QVM:3157), quotient_pow5_base (3176), quotient_limb_subshape (3190), quotient_modarith7_shape (3231), collect_quotient_sum_terms (3605), try_quotient_lin7_shape (3654), try_quotient_bilin7_row_shape (3683), try_quotient_bilin7_pairwise_shape (3736), quotient_mem_term/product_mem_pair/factors (3989-4013), limb7_* (4042-4059). These are P-09f. Today they exist only as QuotientShapeRecognizers hooks.
- The Halo2 Expression to QuotientExpr bridge: quotient_expr_from_expression (QVM:2870), DataQuotientExpressionEnv (2894), word_to_quotient_expr (2955), ptr_to_quotient_mem (2965), plus quotient.rs quotient_expr_from_plonk_expr (987). It is required to link QuotientIdentity.expr to Midfall.Halo2.partiallyEvaluateIdentities.
- The plan-items driver: quotient.rs build_quotient_program_items (2102) / build_quotient_program_items_with_limb_ops (2120). It is a short loop of identityExpr, native* and finish, and must be defined in the theorem file.
- The plan producer: quotient.rs quotient_program_plan (426), quotient_identity_parts (804) with QuotientIdentityParts (vm/mod.rs:229), selector_fold_plan (356), native_gate_indices (529), and vm/mod.rs execution_manifest / validate_execution_manifest (388/442).
- The evaluator frame builders: quotient.rs quotient_external_frame (760) and quotient_external_frame_from_bounds (778), quotient_template_program (189), quotient_vm_guards (242), QuotientStateSlots (43), and models.rs Halo2QuotientEvaluator::validate_layout (963+).
- Yul-side fold and blocks: compact_quotient_computation_blocks (quotient.rs:2000), direct_quotient_block (997), push_structured_main_fold (1342), push_structured_fold (1354), push_structured_fold_advance (1092), push_quotient_eval_numer_add (1076), structured_permutation_loop_block (1471), structured_lookup_loop_block (1688), structured_trash_loop_block (1941), and yul_emit.rs Evaluator (gate/permutation/lookup/trashcan computations).
- A Lean Yul AST or semantics for templates/partials/quotient_numerator/QuotientNumeratorBlock.yul (1442 lines), QuotientHelpers.yul (81) and templates/contracts/Halo2QuotientEvaluator.sol (170). Also RunContract, evaluatorObject, frameOf/outputOf, and a Frame.WellFormed predicate. These are P-13 and the Yul layer.
- PLAN objects with no reference counterpart, which must be invented: QVM.Program, QVM.Frame, QVM.Output, a `.oob` fault, a whole-stream QVM run including folds, a shape denotation (QuotientLimbShape/QuotientModarith7Shape → value under a valuation), a valuation-parametric evaluator, and a CacheConsistent invariant on QuotientRefMemory.
- The direct quotient path (quotient_numerator/direct/{mod,emit,layout,validate}.rs, quotient_direct.rs), which direct_correct needs. It is deferred to M10 by PLAN 14.8; direct/folds.rs stays in M3.

## declarations
- `Midfall.Generator.qOpPushConst .. qOpAffineSum (opcode constants)` (formal/Midfall/Generator/Quotient/VmTypes.lean:1022)
    sig: def qOpPushConst : Nat := 0x01 -- ... qOpPushMemLiteral 0x02, qOpPushMemToken 0x03, qOpPushMemTokenOffset 0x04, qOpPushMemU16 0x05, qOpAdd 0x06, qOpMul 0x07, qOpNeg 0x08, qOpPushConstU8 0x09, qOpFoldMain 0x0a, qOpFoldSelector 0x0b, qOpAddConstU8 0x0c, qOpMulConstU8 0x0d, qOpAddConst 0x0e, qOpMulConst 0x0f, qOpAddMemU16 0x10, qOpMulMemU16 0x11, qOpAddMulMemMemConstU8 0x12, qOpAddMulConstU8MemU16 0x13, qOpAddMulMemMem 0x14, qOpRunAddMulMemMemConstU8 0x15, qOpRunAddMulConstU8MemU16 0x16, qOpNativePermutation 0x19, qOpNativeIdentity 0x1b, qOpLin7 0x1c, qOpBilin7Row 0x1d, qOpBilin7Pairwise 0x1e, qOpNativeLookup 0x1f, qOpPow5 0x20, qOpModarith7 0x21, qOpAffineSum 0x22 (lines 1022-1096)
    notes: There is NO opcode inductive/enum. The opcodes are 31 bare `Nat` constants (0x17, 0x18 and 0x1a are unused; 0x1a must hit Yul `default`). The interpreter dispatches with an `if op == ...` chain. MODARITH7 flags are qModarith7FlagCond 0x01 and qModarith7FlagConst 0x02 (1102-1105). The memory tokens are bare Nats too: qMemL0 0x01 .. qMemInstanceEval 0x09 (1113-1130).
- `Midfall.Generator.QuotientOpcodeEncoding / QuotientOpcodeSpec / quotientOpcodeTable / quotientOpcodeSpec / quotientOpcodeByteLen` (formal/Midfall/Generator/Quotient/VmTypes.lean:910)
    sig: inductive QuotientOpcodeEncoding | none | u8 | u16 | u24 | u32 | tokenOffset | addMulMemMemConstU8 | addMulConstU8MemU16 | addMulMemMem | runAddMulMemMemConstU8 | runAddMulConstU8MemU16 | limbLin | limbBilinRow | limbBilinPairwise | limbModarith7 | affineSum deriving BEq structure QuotientOpcodeSpec where name : String; opcode : Nat; byteLen : Nat; encoding : QuotientOpcodeEncoding (946) def quotientOpcodeTable : List QuotientOpcodeSpec := (1146) def quotientOpcodeSpec (opcode : Nat) : Option QuotientOpcodeSpec := (1246) def quotientOpcodeByteLen (opcode : Nat) : Option Nat := (1253)
    notes: An encoding-class enum plus the ABI table. It is not an opcode type. Template conformance is only checked by IO Bool KATs that read the .yul from disk; there is no theorem. quotientOpcodeByteLen is static only. The four dynamic lengths are in QuotientBuilder.quotientOpLen.
- `Midfall.Generator.QuotientMem` (formal/Midfall/Generator/Quotient/VmTypes.lean:343)
    sig: inductive QuotientMem | literal (ptr : Nat) | token (token : Nat) | tokenOffset (token : Nat) (offset : Nat) deriving BEq
    notes: In Rust these are u32, u8 and (u8, u32). Here they are unbounded Nat. BEq only: no DecidableEq, no LawfulBEq.
- `Midfall.Generator.QuotientExpr` (formal/Midfall/Generator/Quotient/VmTypes.lean:367)
    sig: inductive QuotientExpr | const (value : Word256) | mem (mem : QuotientMem) | add (lhs rhs : QuotientExpr) | mul (lhs rhs : QuotientExpr) | neg (inner : QuotientExpr) deriving BEq
    notes: The builder compiles FROM this AST (QVM:946-964). Word256 = BitVec 256 (Common/Bytes.lean:21). Helpers: QuotientExpr.memLeaves (484) and QuotientExpr.nodeCount (495). It is produced in Rust by quotient_expr_from_expression (QVM:2870, NOT ported) from a Halo2 Expression<Fq>, or by parsing Yul lines with QuotientBuilder.assignment/parseExprTop.
- `Midfall.Generator.QuotientLimbShape / QuotientModarith7Shape / QuotientLimbShape.wellFormed / coefficientOperands` (formal/Midfall/Generator/Quotient/VmTypes.lean:408)
    sig: inductive QuotientLimbShape | lin7 (terms : List (Word256 × Nat)) | bilin7Row (lhs : Nat) (terms : List (Word256 × Nat)) | bilin7Pairwise (lhsBase rhsBase : Nat) (coeffs : List Word256) deriving BEq structure QuotientModarith7Shape where cond : Option Nat; constant : Word256; lin : List (List (Word256 × Nat)); rows : List (Nat × List (Word256 × Nat)); pairwise : List (Nat × Nat × List Word256); memTerms : List (Word256 × Nat); productTerms : List (Word256 × Nat × Nat) deriving BEq (430) def QuotientLimbShape.wellFormed (shape : QuotientLimbShape) : Bool := (511) def QuotientLimbShape.coefficientOperands (shape : QuotientLimbShape) : List Word256 := (549)
    notes: Arity is not enforced by the type. wellFormed is lin7/row: 7 terms, pairwise: 13 coeffs. emitLimbShape does NOT re-check it, so a recognizer-soundness hypothesis must include it. No denotation of a shape over memory exists in Lean. Only the byte decoders limbLinearForm, limbRowForm, limbPairwiseForm and modarith7Form in VmReference exist.
- `Midfall.Generator.QuotientTarget / QuotientIdentityMetadata / QuotientIdentity` (formal/Midfall/Generator/Quotient/VmTypes.lean:600)
    sig: inductive QuotientTarget | main | selector (selectorIndex : Nat) deriving BEq structure QuotientIdentityMetadata where globalIndex : Nat; source : QuotientIdentitySource deriving BEq (618) structure QuotientIdentity where meta_ : QuotientIdentityMetadata lines : List String var : String target : QuotientTarget expr : QuotientExpr deriving BEq (665)
    notes: selectorIndex indexes plan.sortedSimple. It is NOT the fixed-column index that Midfall.Halo2.computeLinearizationCommitment keys on. QuotientIdentitySource is at Generator/Api.lean:693 and has gate, permutation, lookup and trash variants. `meta_` is named that way because meta is a reserved word. `lines`/`var` are the Yul text used by the inline, native and tail paths. `expr` is the VM source.
- `Midfall.Generator.QuotientProgramBuild` (formal/Midfall/Generator/Quotient/VmTypes.lean:636)
    sig: structure QuotientProgramBuild where bytes : Bytes consts : List Word256 maxStack : Nat usedOps : Bytes usedMemTokens : Bytes deriving BEq
    notes: This is the program/bytecode artifact and the constant table. The constant table type is `List Word256`. `bytes` is ByteArray, and the interpreter reads `List Nat` through VmReference.qvmBytesToNats (371). It is the only 'program' object. There is no QVM.Program.
- `Midfall.Generator.QuotientProgramItem / QuotientExecutionKind` (formal/Midfall/Generator/Quotient/VmTypes.lean:772)
    sig: inductive QuotientProgramItem | identity (identity : QuotientIdentity) | nativePermutation | nativeLookup | nativeIdentity (nativeIndex : Nat) deriving BEq inductive QuotientExecutionKind | inline | interpreted | nativePermutation | nativeLookup | nativeIdentity (nativeIndex : Nat) | structuredTail deriving BEq (797)
    notes: Only `.identity` reaches the interpreter. QuotientExecutionKind has no consumer. Api.lean:668 has the parallel QuotientIdentityExecution.
- `Midfall.Generator.SelectorFoldPlan / SelectorFoldPlan.gapFor / QuotientProgramPlan` (formal/Midfall/Generator/Quotient/VmTypes.lean:826)
    sig: structure SelectorFoldPlan where gapsByIdentity : List (Option Nat) tailExponents : List Nat maxPower : Nat deriving BEq def SelectorFoldPlan.gapFor (self : SelectorFoldPlan) (identity : QuotientIdentity) : Option Nat := (855) structure QuotientProgramPlan where inlineIdentities : List QuotientIdentity; items : List QuotientProgramItem; nativeIdentities : List QuotientIdentity; nativePermutationIdentities : List QuotientIdentity; nativeLookupIdentities : List QuotientIdentity; structuredTailIdentities : List QuotientIdentity; sortedSimple : List Nat; hasNativePermutation : Bool; hasNativeLookup : Bool; selectorFold : SelectorFoldPlan deriving BEq (868)
    notes: gapFor = gapsByIdentity.getD identity.meta_.globalIndex none. The plan is a hand-built record. Its producer quotient_program_plan (quotient.rs:426) and validate_execution_manifest (QVM:442) are NOT ported. The global y-order is inlineIdentities ++ (items with natives expanded) ++ structuredTailIdentities.
- `Midfall.Generator.qvmFrModulus / QVMFr / qvmFrAdd / qvmFrMul / qvmFrNeg` (formal/Midfall/Generator/Quotient/VmReference.lean:244)
    sig: def qvmFrModulus : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 abbrev QVMFr : Type := Nat def qvmFrAdd (lhs rhs : QVMFr) : QVMFr := (lhs + rhs) % qvmFrModulus def qvmFrMul (lhs rhs : QVMFr) : QVMFr := (lhs * rhs) % qvmFrModulus def qvmFrNeg (value : QVMFr) : QVMFr := (qvmFrModulus - value) % qvmFrModulus
    notes: The field is Nat with canonical representatives, not ZMod. qvmFrZero is at 255. Bridging to Halo2 `Fr p` needs p = qvmFrModulus plus a cast. The only tie to Midfall.Assumptions.r is a Bool KAT (qvmFrModulus_agreesWithBlsR_ok).
- `Midfall.Generator.QVMFault (PLAN's QVM.Fault)` (formal/Midfall/Generator/Quotient/VmReference.lean:284)
    sig: inductive QVMFault | stackUnderflow (idx : Nat) | readPastEnd (idx : Nat) | constSlotOutOfRange (slot idx : Nat) | zeroLengthRun (idx : Nat) | affineSumZeroCounts (idx : Nat) | modarith7UnknownFlags (flags idx : Nat) | streamOpcodeInIdentity (op idx : Nat) | unknownOpcode (op idx : Nat) | stackLengthMismatch (len : Nat) | panic (site : String) deriving BEq
    notes: This is the fault type with its constructors. There is NO `.oob`. readPastEnd means past the end of the PROGRAM bytes, and constSlotOutOfRange means past the end of the TABLE. `panic` covers reference.rs:548 (non-canonical const), reference.rs:427 (unreachable), the fuel arm 'reference VM fuel exhausted', and every builder panic site (the builder reuses this type). QVMFault.message (319) renders the Rust strings.
- `Midfall.Generator.fqFromU256 / constAt / byteAt / readU16 / readU32` (formal/Midfall/Generator/Quotient/VmReference.lean:346)
    sig: def fqFromU256 (value : Word256) : Except QVMFault QVMFr := def byteAt (bytes : List Nat) (idx : Nat) : Except QVMFault Nat := (485) def readU16 (bytes : List Nat) (idx : Nat) : Except QVMFault Nat := do (492) def readU32 (bytes : List Nat) (idx : Nat) : Except QVMFault Nat := do (498) def constAt (consts : List Word256) (slot idx : Nat) : Except QVMFault QVMFr := (509)
    notes: fqFromU256 REJECTS with `.panic "...reference.rs:548"` when value.toNat >= qvmFrModulus. It does not reduce. The Yul PUSH_CONST does a raw mload, so Yul and the reference diverge on non-canonical constants.
- `Midfall.Generator.deriveReferenceMemory / QuotientRefMemory / quotientRefMemoryNew / quotientRefMemoryCacheGet` (formal/Midfall/Generator/Quotient/VmReference.lean:395)
    sig: def deriveReferenceMemory (seed : Bytes) (domain address : Nat) : QVMFr := structure QuotientRefMemory where seed : Bytes cache : List (Nat × Nat × QVMFr) deriving BEq (409) def quotientRefMemoryNew (seed : Bytes) : QuotientRefMemory := (419) def quotientRefMemoryCacheGet (mem : QuotientRefMemory) (domain address : Nat) : Option QVMFr := (424)
    notes: This is the memory model, and it confirms D-P20 item 2. It is a Keccak PRNG over (domain : u8, address : u32): literal p -> derive 0 p, token t o -> derive (1+t) o. The cache key is (domain % 256, address % 2^32). Every read succeeds, so there is no frame and no out-of-bounds read. `∀ mem` quantifies only over Keccak-derived assignments.
- `Midfall.Generator.QuotientRefMemory.derive / .literal / .token` (formal/Midfall/Generator/Quotient/VmReference.lean:433)
    sig: def QuotientRefMemory.derive (mem : QuotientRefMemory) (domain address : Nat) : QVMFr × QuotientRefMemory := def QuotientRefMemory.literal (mem : QuotientRefMemory) (ptr : Nat) : QVMFr × QuotientRefMemory := (443) def QuotientRefMemory.token (mem : QuotientRefMemory) (token offset : Nat) : QVMFr × QuotientRefMemory := (451)
    notes: Stateful: it returns a new memory, so the memo state is threaded through every evaluator.
- `Midfall.Generator.evalQuotientExpr (oracle side)` (formal/Midfall/Generator/Quotient/VmReference.lean:459)
    sig: def evalQuotientExpr (expr : QuotientExpr) (mem : QuotientRefMemory) : Except QVMFault (QVMFr × QuotientRefMemory) :=
    notes: Port of eval_quotient_expr (QVR:110-125). Structural. Evaluates the left subtree first. Fails only through fqFromU256.
- `Midfall.Generator.foldRangeIdxM` (formal/Midfall/Generator/Quotient/VmReference.lean:536)
    sig: def foldRangeIdxM {ε α : Type} (n : Nat) (init : α) (f : Nat → α → Except ε α) : Except ε α :=
    notes: The R3 loop combinator used by every *_form decoder. Proofs need an induction lemma for it.
- `Midfall.Generator.affineLinearTerm / affineProductTerm / limbLinearForm / limbRowForm / limbPairwiseForm / modarith7Form` (formal/Midfall/Generator/Quotient/VmReference.lean:551)
    sig: def limbLinearForm (bytes : List Nat) (consts : List Word256) (mem : QuotientRefMemory) (idx : Nat) : Except QVMFault (QVMFr × Nat × QuotientRefMemory) := do -- identical binder/return shape for affineLinearTerm (551), affineProductTerm (562), limbRowForm (592), limbPairwiseForm (605), modarith7Form (636)
    notes: Byte-level decoders that return (value, bytes consumed, memory). Each limb form reads exactly quotientVmLimbs = 7 terms, and pairwise reads 13 coefficients. The modarith7 condition multiplies the whole accumulator at the end. The mem block is (slot, ptr); the standalone affine term is (ptr, slot).
- `Midfall.Generator.IdentityStep / popStack / evalQuotientIdentityStep` (formal/Midfall/Generator/Quotient/VmReference.lean:708)
    sig: structure IdentityStep where stack : List QVMFr consumed : Nat hConsumed : 0 < consumed mem : QuotientRefMemory def popStack (stack : List QVMFr) (idx : Nat) : Except QVMFault (QVMFr × List QVMFr) := (722) def evalQuotientIdentityStep (bytes : List Nat) (consts : List Word256) (idx : Nat) (op : Nat) (stack : List QVMFr) (mem : QuotientRefMemory) : Except QVMFault IdentityStep := (730)
    notes: The stack head is the top. IdentityStep carries a proof field. The five stream opcodes (fold main/selector, native permutation/lookup/identity) give `.streamOpcodeInIdentity op idx` (861-865). ADD_MEM_U16/MUL_MEM_U16 read memory BEFORE popping.
- `Midfall.Generator.evalQuotientIdentityLoop (+ .go)` (formal/Midfall/Generator/Quotient/VmReference.lean:874)
    sig: def evalQuotientIdentityLoop (bytes : List Nat) (consts : List Word256) (idx : Nat) (stack : List QVMFr) (mem : QuotientRefMemory) : Except QVMFault (List QVMFr × QuotientRefMemory) := go bytes.length idx stack mem where go : Nat → Nat → List QVMFr → QuotientRefMemory → Except QVMFault (List QVMFr × QuotientRefMemory)
    notes: Fuel = bytes.length. Fuel exhaustion gives `.panic "reference VM fuel exhausted"`, which is unreachable because consumed > 0. Proofs unfold `evalQuotientIdentityLoop.go`.
- `Midfall.Generator.evalQuotientIdentity (port of eval_quotient_identity)` (formal/Midfall/Generator/Quotient/VmReference.lean:902)
    sig: def evalQuotientIdentity (bytes : List Nat) (consts : List Word256) (mem : QuotientRefMemory) : Except QVMFault (QVMFr × QuotientRefMemory) := do
    notes: This is the reference interpreter entry point. Body: run the loop from idx 0 with an empty stack. `[value]` returns `.ok (value, mem')`; anything else returns `.error (QVMFault.stackLengthMismatch xs.length)`. It is ONE identity's segment, with the fold excluded.
- `Midfall.Generator.QVM.run / QVM.Fault / QVM.Fr / QVM.Memory` (formal/Midfall/Generator/Quotient/VmReference.lean:930)
    sig: abbrev Fault : Type := QVMFault abbrev Fr : Type := QVMFr abbrev Memory : Type := QuotientRefMemory def run (bytes : List Nat) (consts : List Word256) (mem : Memory) : Except Fault (Fr × Memory) := evalQuotientIdentity bytes consts mem
    notes: These are PLAN-name aliases inside `namespace QVM` (inside Midfall.Generator), lines 916-934. They are per-identity only. QVM.Program, QVM.Frame and QVM.Output are deliberately absent.
- `Midfall.Generator.qvmBytesToNats / qvmBytesOfNats` (formal/Midfall/Generator/Quotient/VmReference.lean:371)
    sig: def qvmBytesToNats (bs : Bytes) : List Nat := bs.data.toList.map UInt8.toNat def qvmBytesOfNats (ns : List Nat) : Bytes := (366)
    notes: The bridge between QuotientProgramBuild.bytes and the interpreter input. qvmBytesOfNats truncates each Nat with Nat.toUInt8.
- `Midfall.Generator.QuotientBuilder.M / QuotientShapeRecognizers / noShapeRecognizers` (formal/Midfall/Generator/Quotient/VmBuilder.lean:131)
    sig: abbrev M (α : Type) := Except QVMFault α structure QuotientShapeRecognizers where pow5Base : QuotientExpr → Option QuotientExpr limbShape : QuotientExpr → Option QuotientLimbShape limbSubshape : QuotientExpr → Option (QuotientLimbShape × QuotientExpr × List QuotientExpr) modarith7Shape : QuotientExpr → Option QuotientModarith7Shape (221) def noShapeRecognizers : QuotientShapeRecognizers := (235)
    notes: These are the shape recognizers, and they exist ONLY as hooks. The real ones (QVM:3157/3176/3190/3231 and the try_* functions at 3654/3683/3736) are not ported (P-09f). Compile correctness must take a soundness hypothesis on r. noShapeRecognizers is trivially sound.
- `Midfall.Generator.QuotientBuilder.QuotientProgramBuilder / builderDefault / withLimbVmOps / defaultQuotientLimbVmOps` (formal/Midfall/Generator/Quotient/VmBuilder.lean:258)
    sig: structure QuotientProgramBuilder where bytes : List Nat consts : List Word256 constSlots : List (Word256 × Nat) vars : List (String × QuotientExpr) stackDepth : Nat maxStack : Nat limbVmOps : Bool deriving BEq def builderDefault : QuotientProgramBuilder := (280) def withLimbVmOps (enabled : Bool) : QuotientProgramBuilder := (291) def defaultQuotientLimbVmOps : Bool := true (213)
    notes: The deployed build uses limbVmOps = true. The baseline build (withLimbVmOps false) still consults r.pow5Base, because tryEmitPow5 does not check limbVmOps.
- `Midfall.Generator.QuotientBuilder.emitExpr / emitExprTop` (formal/Midfall/Generator/Quotient/VmBuilder.lean:708)
    sig: def emitExpr (r : QuotientShapeRecognizers) : Nat → QuotientProgramBuilder → QuotientExpr → M QuotientProgramBuilder def emitExprTop (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder) (expr : QuotientExpr) : M QuotientProgramBuilder := (898)
    notes: This is the builder entry point. It compiles a QuotientExpr into appended bytes (List Nat) plus constant-table growth. It sits in a `mutual` block (700-894) with tryEmitPow5, tryEmitLimbDecomposition, emitAffineTerms, emitAffineTermsRest, tryEmitAddProduct and emitBinaryExpr. Fuel is emitFuel expr = 8*(nodeCount+1) (244).
- `Midfall.Generator.QuotientBuilder.foldIdentity / identityExpr / nativePermutation / nativeLookup / nativeIdentity` (formal/Midfall/Generator/Quotient/VmBuilder.lean:909)
    sig: def foldIdentity (s : QuotientProgramBuilder) (target : QuotientTarget) (selectorGap : Option Nat) : M QuotientProgramBuilder := def identityExpr (r : QuotientShapeRecognizers) (s : QuotientProgramBuilder) (expr : QuotientExpr) (target : QuotientTarget) (selectorGap : Option Nat) : M QuotientProgramBuilder := do (934) def nativePermutation (s : QuotientProgramBuilder) : M QuotientProgramBuilder := (948) def nativeLookup (s : QuotientProgramBuilder) : M QuotientProgramBuilder := (955) def nativeIdentity (s : QuotientProgramBuilder) (nativeIdx : Nat) : M QuotientProgramBuilder := do (964)
    notes: identityExpr resets vars and stackDepth, calls emitExprTop then foldIdentity, and panics (siteStackLeak) if stackDepth != 0. FOLD_SELECTOR is followed by a u24 equal to (idx*65536) ||| gap. The plan-item driver (Rust build_quotient_program_items*, quotient.rs:2102/2120) is NOT ported. The only analogue is the KAT helper QuotientCertifyKats.buildStream (VmCertify.lean:855), which uses noShapeRecognizers.
- `Midfall.Generator.QuotientBuilder.assignment / parseExprTop` (formal/Midfall/Generator/Quotient/VmBuilder.lean:1232)
    sig: def assignment (s : QuotientProgramBuilder) (line : String) : M QuotientProgramBuilder := do def parseExprTop (s : QuotientProgramBuilder) (expr : String) : M QuotientExpr := (1224)
    notes: The Yul-text to QuotientExpr bridge (quotient_yul_expr, quotient.rs:978). It is a second producer of QuotientExpr.
- `Midfall.Generator.QuotientBuilder.quotientOpLen / compactQuotientRuns / quotientProgramUsage` (formal/Midfall/Generator/Quotient/VmBuilder.lean:1287)
    sig: def quotientOpLen (bytes : List Nat) (idx : Nat) : M Nat := do def compactQuotientRuns (bytes : List Nat) : M (List Nat) := (1398) def quotientProgramUsage (bytes : List Nat) : M (List Nat × List Nat) := (1442)
    notes: Compaction only merges adjacent ADD_MUL_CONST_U8_MEM_U16 / ADD_MUL_MEM_MEM_CONST_U8 runs. AFFINE_SUM reorders the terms as all linear first, then all products.
- `Midfall.Generator.QuotientBuilder.finish / finishBytes / finalizedIdentitySegment / segmentMaxStack / finishValidatorLeg` (formal/Midfall/Generator/Quotient/VmBuilder.lean:1460)
    sig: def finish (s : QuotientProgramBuilder) : M QuotientProgramBuild := do def finishBytes (s : QuotientProgramBuilder) : M (List Nat) := (1471) def finalizedIdentitySegment (bytes : List Nat) : Option (List Nat) := (1480) def segmentMaxStack (bytes : List Nat) (consts : List Word256) (mem : QuotientRefMemory) : M Nat := (1509) def finishValidatorLeg : String := (1450)
    notes: finish is the artifact boundary: compact, then usage, then a Bytes wrap. The Rust validator leg (validate_quotient_program + the max_stack assert) is OMITTED. finishValidatorLeg is a String placeholder naming it. finalizedIdentitySegment is a one-identity modelling helper.
- `Midfall.Generator.QuotientCertify.quotientCertifySeedDomain / hashQuotientExpr / certifySeedPreimage / deriveCertifySeed` (formal/Midfall/Generator/Quotient/VmCertify.lean:307)
    sig: def quotientCertifySeedDomain : Bytes := asciiBytes "midfall/quotient-vm/certify-seed/v3" (241) def hashQuotientExpr (expr : QuotientExpr) : Bytes := (257) def certifySeedPreimage (builds : List QuotientProgramBuild) (exprs : List QuotientExpr) (vkPayload : Bytes) : Bytes := (281) def deriveCertifySeed (builds : List QuotientProgramBuild) (exprs : List QuotientExpr) (vkPayload : Bytes) : Bytes :=
    notes: The derive_certify_seed port: Keccak over the tag, the builds (finalized bytes and consts), the tagged expr trees, and vk.bytes. A ∀-valuation theorem makes the seed irrelevant. It matters only for a theorem that restates the Rust's single-sample check.
- `Midfall.Generator.QuotientCertify.interpretedExprs` (formal/Midfall/Generator/Quotient/VmCertify.lean:315)
    sig: def interpretedExprs (plan : QuotientProgramPlan) : List QuotientExpr :=
    notes: The `.expr` of every `.identity` item, in order.
- `Midfall.Generator.QuotientCertify.identitySegment (+ .go, .neverFolded)` (formal/Midfall/Generator/Quotient/VmCertify.lean:409)
    sig: def identitySegment (bytes : List Nat) (start : Nat) : Except String (Nat × Nat) :=
    notes: The general segment walker. It returns (exprEnd, foldOp) with foldOp ∈ {qOpFoldMain, qOpFoldSelector}, and errors on a native marker. Its error type is String, not QVMFault. Fuel = bytes.length.
- `Midfall.Generator.QuotientCertify.checkFold` (formal/Midfall/Generator/Quotient/VmCertify.lean:447)
    sig: def checkFold (bytes : List Nat) (foldIdx foldOp : Nat) (identity : QuotientIdentity) (plan : QuotientProgramPlan) : Except String Unit :=
    notes: A positional check only: target against fold op, and bucket/gap bytes against plan.selectorFold.gapFor. It uses BEq on QuotientTarget. It never executes a fold.
- `Midfall.Generator.QuotientCertify.certifyItemWalk (+ .go)` (formal/Midfall/Generator/Quotient/VmCertify.lean:499)
    sig: def certifyItemWalk (plan : QuotientProgramPlan) (build : QuotientProgramBuild) (bytes : List Nat) (mem : QuotientRefMemory) : Except String (Nat × QuotientRefMemory) :=
    notes: This is the comparison (the Rust's Schwartz-Zippel check). For each identity item it does: segment, then evalQuotientIdentity seg build.consts mem, then evalQuotientExpr identity.expr mem1 (memory threaded from the VM run into the oracle), then `actual != expected` gives an error. It returns the end cursor. Native items are checked positionally.
- `Midfall.Generator.QuotientCertify.certifyProgramSeed / certifyQuotientProgram` (formal/Midfall/Generator/Quotient/VmCertify.lean:590)
    sig: def certifyProgramSeed (plan : QuotientProgramPlan) (build : QuotientProgramBuild) (vk : Halo2VerifyingKey) : Bytes := (582) def certifyQuotientProgram (plan : QuotientProgramPlan) (build : QuotientProgramBuild) (vk : Halo2VerifyingKey) : Except String Unit := do
    notes: The seed is deriveCertifySeed [build] (interpretedExprs plan) vk.bytes. It then runs certifyItemWalk and requires cursor = bytes.length. Halo2VerifyingKey is Generator/Models.lean:385, and .bytes is at :474.
- `Midfall.Generator.QuotientCertify.identityValues / certifyBuildsAgreeSeed / certifyQuotientBuildsAgree` (formal/Midfall/Generator/Quotient/VmCertify.lean:607)
    sig: def identityValues (plan : QuotientProgramPlan) (build : QuotientProgramBuild) (mem : QuotientRefMemory) : Except String (List QVMFr × QuotientRefMemory) := def certifyBuildsAgreeSeed (plan : QuotientProgramPlan) (optimized baseline : QuotientProgramBuild) (vk : Halo2VerifyingKey) : Bytes := (631) def certifyQuotientBuildsAgree (plan : QuotientProgramPlan) (optimized baseline : QuotientProgramBuild) (vk : Halo2VerifyingKey) : Except String Unit := do (651)
    notes: identityValues pushes qvmFrZero for each native item. That is NOT a y-position value, because a native callback folds many identities.
- `Midfall.Generator.QuotientExternal (+ frameEnd, containsRange, disjointRange, validateContains)` (formal/Midfall/Generator/Models.lean:531)
    sig: structure QuotientExternal where frameBase : Nat frameLen : Nat outputLen : Nat magic : Nat
    notes: This is the evaluator frame record. Its builders, quotient_external_frame (quotient.rs:760) and quotient_external_frame_from_bounds (quotient.rs:778), are NOT ported. The magic value is quotientExternalMagic := 0x5155_4556_414c_0001 (VmTypes.lean:253).
- `Midfall.Generator.QuotientProgram / QuotientVmGuards / QuotientSelectorTail / Halo2QuotientEvaluator` (formal/Midfall/Generator/Models.lean:666)
    sig: structure QuotientProgram where len : Nat; opUsage : QuotientVmOpcodeUsage; memUsage : QuotientVmMemUsage; constMptr : Nat; evalNumerMptr : Nat; traceIdMptr : Nat; selectorPowerMptr : Nat; selectorMaxPower : Nat; selectorTailUpdates : List QuotientSelectorTail; stackMptr : Nat; programMptr : Nat; guards : QuotientVmGuards structure QuotientVmGuards where constMax : Nat; numSelectorBuckets : Nat; stackLast : Nat deriving BEq (582) structure Halo2QuotientEvaluator (Memory : Type) where ... memory : Memory ... quotientExternal : QuotientExternal ... quotientInlineComputations : List (List String) ... quotientPostVmComputations : List (List String) ... quotientNativePermutationComputation : List String ... quotientProgram : Option QuotientProgram ... simpleSelectorCols : List Nat ... (873)
    notes: These are the Askama models for the Yul interpreter and the evaluator. `Memory` is a genuine type parameter (used by the field `memory`), not a phantom. They render text. There is no Yul AST.
- `Midfall.Generator.PackedProgramCodec.encodeWords` (formal/Midfall/Generator/Layout.lean:371)
    sig: def PackedProgramCodec.encodeWords (bytes : Bytes) : List Word256 :=
    notes: How the bytecode is packed into the VK payload words that the evaluator frame carries (quotient.rs:198).
- `Midfall.Lowering.Lowered / Supported / YulObject` (formal/Midfall/Lowering/Types.lean:34)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject structure Supported (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat) (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where (51) abbrev YulObject := YulSemantics.Object Op (28)
    notes: Supported.qvm : qvmValidated abstracts QVM-01 as an opaque Prop. Lowered has no plan, consts or qprog field. The untracked formal/Midfall/Lowering/SemanticEquivalence.lean (42 lines, registered in the working-copy Midfall.lean) already holds contractRefAccepts_iff_verifyMsgs.
- `Midfall.Halo2.partiallyEvaluateIdentities` (formal/Midfall/Halo2/Exec/Verifier.lean:253)
    sig: def partiallyEvaluateIdentities {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (fixedEvals : Array (Fr p)) (instanceEvals : Array (Array (Fr p))) (adviceEvals : Array (Array (Fr p))) (permutationEvals : Array (Array (Permutation.SetEvaluated (Fr p)))) (lookupEvals : Array (Array (Logup.Evals (Fr p)))) (trashcanEvals : Array (Array (Trash.Eval (Fr p)))) (permutationsCommon : Permutation.CommonEvaluated (Fr p)) (x xn beta gamma theta trashChallenge : Fr p) (challenges : Array (Fr p)) : Except Fault (Array (Option Nat × Fr p)) := do
    notes: The Lean-verifier side the QVM must match (PLAN's 'quotientParts'). Each entry is (fixed selector column or none, value) in gate/permutation/lookup/trash order.
- `Midfall.Halo2.computeLinearizationCommitment` (formal/Midfall/Halo2/Exec/Linearization.lean:68)
    sig: def computeLinearizationCommitment {F G₁ : Type} [Field F] [BEq F] (expressions : Array (Option Nat × F)) (vk : VerifyingKey F G₁) (x : F) (y : F) (xn : F) (splittingFactor : F) (quotientLimbCommitments : Array G₁) : Except Fault (VerifierQuery F G₁) := do
    notes: The y fold the Yul Horner fold must equal: it walks expressions in REVERSE (the last identity gets y^0), uses groupedAdd keyed by Option Nat in ascending key order, and does expected_eval -= eval for the None bucket. The Yul returns -ν_y(x), which corresponds to this expectedEval.

## verbatim excerpts

### formal/Midfall/Generator/Quotient/VmReference.lean:433
```lean
def QuotientRefMemory.derive (mem : QuotientRefMemory) (domain address : Nat) :
    QVMFr × QuotientRefMemory :=
  match quotientRefMemoryCacheGet mem domain address with
  | some value => (value, mem)
  | none =>
      let value := deriveReferenceMemory mem.seed domain address
      (value, { mem with cache := (domain % 256, address % 2^32, value) :: mem.cache })

/-- rust: QVR:72-75 (QuotientRefMemory::literal) @formal-baseline. "Value at an absolute
    memory pointer." Domain 0. -/
def QuotientRefMemory.literal (mem : QuotientRefMemory) (ptr : Nat) :
    QVMFr × QuotientRefMemory :=
  mem.derive 0 ptr

/-- rust: QVR:77-82 (QuotientRefMemory::token) @formal-baseline. "Value behind a
    symbolic memory token, optionally offset." The Rust's comment is the reason the
    domain is 1 + token and not token: "Tokens resolve to generated addresses disjoint
    from the literal pointer space, so they get their own domain tag." -/
def QuotientRefMemory.token (mem : QuotientRefMemory) (token offset : Nat) :
    QVMFr × QuotientRefMemory :=
  mem.derive (1 + token) offset
```

### formal/Midfall/Generator/Quotient/VmReference.lean:459
```lean
def evalQuotientExpr (expr : QuotientExpr) (mem : QuotientRefMemory) :
    Except QVMFault (QVMFr × QuotientRefMemory) :=
  match expr with
  | .const value => do
      let v ← fqFromU256 value
      .ok (v, mem)
  | .mem (.literal ptr) => .ok (mem.literal ptr)
  | .mem (.token token) => .ok (mem.token token 0)
  | .mem (.tokenOffset token offset) => .ok (mem.token token offset)
  | .add lhs rhs => do
      let (l, m1) ← evalQuotientExpr lhs mem
      let (r, m2) ← evalQuotientExpr rhs m1
      .ok (qvmFrAdd l r, m2)
  | .mul lhs rhs => do
      let (l, m1) ← evalQuotientExpr lhs mem
      let (r, m2) ← evalQuotientExpr rhs m1
      .ok (qvmFrMul l r, m2)
  | .neg inner => do
      let (v, m1) ← evalQuotientExpr inner mem
      .ok (qvmFrNeg v, m1)
```

### formal/Midfall/Generator/Quotient/VmReference.lean:886
```lean
  | fuel + 1, idx, stack, mem =>
      if idx < bytes.length then do
        let s ← evalQuotientIdentityStep bytes consts idx (bytes.getD idx 0) stack mem
        go fuel (idx + s.consumed) s.stack s.mem
      else
        .ok (stack, mem)
  termination_by fuel _ _ _ => fuel

/-- rust: QVR:131-347 (eval_quotient_identity) @formal-baseline. "Evaluate one identity
    expression subprogram, up to but excluding its fold." This is PLAN 9.5's QVM.run at
    the granularity the reference actually has: one identity, not a program; a seeded
    PRNG memory, not a frame; one field element, not an output object. See the header's
    DOMAIN OF QVM.run.

    The Rust's Ok(stack.pop().expect("checked length")) at QVR:346 is discharged here by
    the singleton pattern match, so it needs no fault (R4 note in the header). -/
def evalQuotientIdentity (bytes : List Nat) (consts : List Word256)
    (mem : QuotientRefMemory) : Except QVMFault (QVMFr × QuotientRefMemory) := do
  let (stack, mem') ← evalQuotientIdentityLoop bytes consts 0 ([] : List QVMFr) mem
  match stack with
  | [value] => .ok (value, mem')
  | xs => .error (QVMFault.stackLengthMismatch xs.length)
```

### formal/Midfall/Generator/Quotient/VmBuilder.lean:221
```lean
structure QuotientShapeRecognizers where
  /-- rust: QVM:3176-3187 (quotient_pow5_base). -/
  pow5Base : QuotientExpr → Option QuotientExpr
  /-- rust: QVM:3157-3173 (quotient_limb_shape). -/
  limbShape : QuotientExpr → Option QuotientLimbShape
  /-- rust: QVM:3190-3227 (quotient_limb_subshape). -/
  limbSubshape : QuotientExpr → Option (QuotientLimbShape × QuotientExpr × List QuotientExpr)
  /-- rust: QVM:3231-3238 (quotient_modarith7_shape). -/
  modarith7Shape : QuotientExpr → Option QuotientModarith7Shape

/-- The conservative instantiation: nothing is recognized, so every expression takes the
    generic Fr path. This is the state the QVM:966-971 doc comment describes ("If a shape
    is not recognized exactly, the builder falls back to ordinary Fr VM opcodes") and it is
    what the gates in this file run under unless they say otherwise. -/
def noShapeRecognizers : QuotientShapeRecognizers :=
  { pow5Base := fun _ => none
    limbShape := fun _ => none
    limbSubshape := fun _ => none
    modarith7Shape := fun _ => none }
```

### formal/Midfall/Generator/Quotient/VmBuilder.lean:909
```lean
def foldIdentity (s : QuotientProgramBuilder) (target : QuotientTarget)
    (selectorGap : Option Nat) : M QuotientProgramBuilder :=
  match target with
  | .main => do
      let s := op0 s qOpFoldMain
      popStackAcct s
  | .selector idx => do
      let gap ← match selectorGap with
        | none => panicAt siteNoSelectorGap
        | some gap => .ok gap
      if idx > 255 then
        panicAt siteSelectorIdxWidth
      else if gap > 0xffff then
        panicAt siteSelectorGapWidth
      else do
        let s := pushByte s qOpFoldSelector
        let s ← emitU24 s ((idx * 65536) ||| gap)
        popStackAcct s
```

### formal/Midfall/Generator/Quotient/VmCertify.lean:409
```lean
def identitySegment (bytes : List Nat) (start : Nat) : Except String (Nat × Nat) :=
  go bytes.length start
where
  neverFolded : String :=
    "identity expression starting at byte " ++ toString start ++ " is never folded"
  go : Nat → Nat → Except String (Nat × Nat)
  | 0, idx =>
      if idx < bytes.length then
        .error "quotient VM segment walk fuel exhausted - port-only bound, see the header"
      else
        .error neverFolded
  | fuel + 1, idx =>
      if idx < bytes.length then
        let op := bytes.getD idx 0
        if op == qOpFoldMain || op == qOpFoldSelector then
          .ok (idx, op)
        else if op == qOpNativePermutation || op == qOpNativeLookup
            || op == qOpNativeIdentity then
          .error ("native marker " ++ qvmHex op ++ " at byte " ++ toString idx ++
                  " interrupts an identity expression")
        else
          match quotientOpLen bytes idx with
          | .error f => .error f.message
          | .ok len => go fuel (idx + len)
      else
```

### formal/Midfall/Generator/Quotient/VmCertify.lean:509
```lean
      | QuotientProgramItem.identity identity => do
          let (exprEnd, foldOp) ←
            wrapError ("quotient item " ++ toString itemIdx ++ ": ")
              (identitySegment bytes cursor)
          let seg := (bytes.drop cursor).take (exprEnd - cursor)
          let (actual, mem1) ←
            wrapError (identityErrorPrefix identity)
              (faultToString (evalQuotientIdentity seg build.consts mem))
          let (expected, mem2) ←
            wrapError (identityErrorPrefix identity)
              (faultToString (evalQuotientExpr identity.expr mem1))
          if actual != expected then
            .error ("quotient VM miscompiled identity " ++
                    toString identity.meta_.globalIndex ++ " (" ++
                    certifySourceDebug identity.meta_.source ++
                    "): bytecode evaluates to " ++ certifyFrDebug actual ++
                    " but its expression evaluates to " ++ certifyFrDebug expected ++
                    ". This is a codegen bug in the quotient lowering (shape recognizer, " ++
                    "operand packing, or run compaction), not a proof or verifying-key " ++
                    "problem.")
          else
            let _ ← wrapError (identityErrorPrefix identity)
              (checkFold bytes exprEnd foldOp identity plan)
            let len ← faultToString (quotientOpLen bytes exprEnd)
            go rest (itemIdx + 1) (exprEnd + len) mem2
```

### proofs/solidity-verifier/templates/partials/quotient_numerator/QuotientNumeratorBlock.yul:1317
```lean
                        {% call q_fold_guard() %}
                        let q_eval := q_top
                        q_has_top := 0
                        {%- if self.trace %}
                        trace_u256(mload({{ program.trace_id_mptr|hex() }}), q_eval)
                        mstore({{ program.trace_id_mptr|hex() }}, add(mload({{ program.trace_id_mptr|hex() }}), 1))
                        {%- endif %}
                        // Simple-selector identity: keep the same y-batch
                        // position as main identities, then advance only this
                        // selector bucket by its codegen-known gap.
                        //
                        // The global fully-evaluated accumulator is still
                        // multiplied by y so later main identities land at the
                        // same y powers as Rust's reverse fold.
                        mstore({{ program.eval_numer_mptr|hex() }}, mulmod(mload({{ program.eval_numer_mptr|hex() }}), y, r))
                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))
                        let q_sel_acc := mload(q_target_ptr)
                        if q_sel_gap {
                            // Selector buckets are sparse in the global
                            // identity stream. Precomputed y^gap advances only
                            // this selector's local accumulator.
                            q_sel_acc := mulmod(q_sel_acc, mload(add({{ program.selector_power_mptr|hex() }}, shl(5, q_sel_gap))), r)
                        }
                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
```


# AREA: Rust NOT yet ported that PLAN 9.5 must anticipate: lowering/{calldata,plan,config,mod}.rs, builder/{mod,api,render,repack}.rs, evm.rs, api.rs render surface, the Halo2Verifier.sol shell and verifier partials (VkLoading, 

## constraints
- (1) NO RUST CALLDATA DECODER EXISTS. The only codecs are evm::encode_calldata (evm.rs:22) and VerifierBuildInputs::encode_calldata / repack_proof (lowering/calldata.rs:43,132). PLAN 9.5's decodeCalldata, calldataOf and encodeContractProof are theorem-side definitions we originate. decodeCalldata must replicate EXACTLY the contract's acceptance checks: selector 0x1e8e1e13 (solc dispatcher); head words (Halo2Verifier.sol:148: word@0x04 = 0x40 and word@0x24 = NUM_INSTANCE_CPTR - 4 = 0x60 + proof_len); word@0x44 = proof_len (VkLoading.yul:101); word@NUM_INSTANCE_CPTR = num_instances (:102); calldatasize = INSTANCE_CPTR + 32*num_instances (:106-109); every instance word < r (TranscriptProofParser.yul:63,68,420); G1 hi words with top 128 bits zero and both coordinates < p (AssemblyHelpers.yul:94-104); evals and q_evals < r (TranscriptProofParser.yul:319,382); parser consumes exactly to NUM_INSTANCE_CPTR (:416).
- (2) EXACT ABI of verifyProof(bytes proof, uint256[] instances), production render. Byte layout: [0x00,0x04) = 1e8e1e13; [0x04,0x24) = 0x40; [0x24,0x44) = 0x60 + proof_len; [0x44,0x64) = proof_len; [0x64, 0x64+proof_len) = repacked proof; NUM_INSTANCE_CPTR = 0x64 + proof_len holds num_instances; INSTANCE_CPTR = 0x84 + proof_len starts the BE instance words. PROOF_CPTR = 0x64 (layout/mod.rs:388). PROOF_LEN_CPTR = proof_cptr - 1 = 0x44, because Ptr arithmetic is in words (Constants.sol:35). num_instance_cptr = proof_layout.proof_end and instance_cptr = proof_end + 0x20 (artifacts.rs:307-308). The Yul reads proof items by calldataload/calldatacopy at a running proof_cptr. Instances are read twice: in TranscriptProofParser.yul:55-67 for canonicality and absorption, and again in Lagrange.yul:65-73 for instance_eval. Cross-checked on target/poseidon-fixture-dump/calldata.bin: 4484 bytes, proof_len 0x10e0, instances head 0x1140, n = 1. That file is NOT git-tracked; only the two .sol files in the dump are.
- (3) calldata_canonical can be stated EXACTLY (not ≈) for the no-accumulator part, because the contract rejects trailing bytes and instance words >= r. But inst : Array (Fr p) cannot represent words >= r (R-26 item 7), so decodeCalldata must be typed over raw Bytes/Word256 and lift. G1 identity is 128 zero bytes (calldata.rs:74-77): it passes common_uncompressed_g1 and is EIP-2537's infinity encoding. Off-curve or off-subgroup points pass the parser and are rejected only later, by G1MSM/pairing (AssemblyHelpers.yul:80-84). So either decodeCalldata validates curve and subgroup membership, or the theorem needs points_subgroup_checked, whose Rust counterpart is kzg::validate_absorbed_g1_precompile_coverage (kzg/mod.rs:723; Kzg.lean:1099). Accumulator tail: decodeAcc_injective is FALSE as written (R-25). Use the accWords projection that treats identity-flagged points as (0,0,1). decodeAcc_encode holds only for collapsed shapes (R-26 item 2). decodeAcc must use Generator.AccumulatorEncoding (D-P16) and needs 4 arguments (R-26).
- (4) encode_calldata never pads the proof to a 32-byte multiple. Its output is standard ABI only because repackedLen is a sum of 128s and 32s. Owe a lemma repackedLen % 32 = 0 before calldata_roundtrip. encode_calldata checks instances.len() against GeneratorConfig.num_instances, not the plan (calldata.rs:137-146), and reports Planning{stage:"calldata"}. RepackError is lifted via GeneratorError.fromRepackError (Api.lean:388).
- (5) repack_proof ALWAYS builds the compact-VM plan (calldata.rs:157-159 calls self.lowering_plan(), i.e. LoweringPlan::new, plan.rs:124), whatever RenderOptions.quotientLowering says. LoweringPlan::new can PANIC (plan.rs:309-310 invariant violation; 320-326 dual-build certification). So state repackProof over RepackedProofLayoutPlan.fromProofLayout L.plan.proofLayout (VmTypes.lean:720). Owe a lemma that VM and Direct plans share proof_layout: both call ProofCalldataLayout::from_protocol(meta.protocol, 0x64, meta.num_evals, meta.num_point_sets) (plan.rs:173-178 and 239-244). A faithful Rust-shaped wrapper should return Except ApiFault (Api.lean:396). Lean's ProofCalldataLayout.fromProtocol is Except Fault (Abi.lean:334), so L.plan.proofLayout must come from an .ok.
- (6) repack_spec right-hand side: Lean decodeRust has arity (E F vk inst π) with phantom Gₜ (Native.lean:228), not PLAN's (.solidity g.vk π). The repack walk order is g1_groups, then num_evals LE->BE scalars, then f_com, then num_point_sets q_evals, then pi (calldata.rs:109-126); the length check comes first (49-57). This must equal the transcript read order in TranscriptProofParser.yul. Messages are interleaved with squeezes, but byte order is the plain concatenation.
- (7) The instance model for calldata is the NON-committed column only. GeneratorConfig.numInstances is documented as 'non-committed public-input values verifyProof expects' (Api.lean:812-815). Exec's verifyNativeWith uses committed=[[1]] and inst=[[inst.toList]] (Native.lean:185). The committed instance commitment is the identity, absorbed as 128 zero bytes (TranscriptProofParser.yul:36-46) and never present in calldata. D-P11's flat [committed, public] view lives in Spec/Relation.lean:77 (instanceAt), not in Exec, so do NOT route decodeCalldata through instanceAt.
- (8) Phantom Gₜ: prepareMsgs, verifyMsgs, decodeRust, verifyNative and ContractRefAccepts must all be called with (Gₜ := Gₜ) (Types.lean:92-94; D-P7). Any new statement file must carry the same variable block as Statements.lean:29-34 / SemanticEquivalence.lean:18-23. It must not import Midfall.Instances.* (D-P17 CI gate) and must not edit Statements.lean, which is SHA-256 pinned.
- (9) Lowering/Types.lean placeholders. Lowered lacks plan, shell and consts (Types.lean:34-38). Lowering.GeneratorError (Types.lean:41-43) is a placeholder distinct from the faithful Generator.GeneratorError (Api.lean:309). Supported (Types.lean:51-65) is over raw Nat/Prop/Bool: it misses noRotInst, acc, vkPoints and layout, and instShape lacks numCommittedInstances = 1 (Rust: builder/api.rs:12-14 and 42-45). Deployment (Types.lean:71-76) is VACUOUS (every field True). ContractRefAccepts has only the no-accumulator arm.
- (10) Supported.layout: D-P18 is OPEN. MemoryMap.WellFormed delivers neither 'above solc spill window' nor 'aligned'. Use VerifierMemoryLayout.validate = .ok () (Layout.lean:1023), which LoweringPlan already enforces (plan.rs:418-420 via validate_generator_invariants). Likewise Supported.qvm is enforced inside validate_generator_invariants (vm::validate_quotient_program_operands). That validator is not yet in Lean (plans/P-09e). If lower ports the panics as errors, both fields become derivable from hL : g.lower o = .ok L.
- (11) Instrumentation that Supported.production must exclude (o.diagnostics.trace = false ∧ o.diagnostics.gasCheckpoints = false). Gas checkpoints, each a LOG1 with topic (id<<248)|gas(), helper at TraceAndGasHelpers.yul:20-22: VkLoading.yul:1-3 (id 1), 139-141 (id 2); TranscriptProofParser.yul:71-73 (3), 131-133 (4), 161-163 (5), 191-193 (6), 232-234 (7), 261-263 (8), 292-294 (9), 422-424 (10); Lagrange.yul:89-91 (11); QuotientAndLinearization.yul:84-86 (12), 163-165 (13); Pcs.yul:21-23 (17+i per sub-block), 27-29 (14); FinalPairing.yul:64-66 (15), 90-92 (16). Trace emission: TraceAndGasHelpers.yul:1-13 (trace_u256, trace_point); TranscriptProofParser.yul:98-103, 116-119, 152-155, 182-185, 212-215, 223-226, 252-255, 284-287, 326-329, 346-349, 384-387, 402-405; Pcs.yul:31-39; QuotientAndLinearization.yul:129-161; QuotientNumeratorBlock.yul:165, 1291-1292, 1321-1322, 1410-1412; TraceReturn.yul:1-53; Halo2QuotientEvaluator.sol:123-131. Semantic changes under trace or gas: the view qualifier is dropped (Halo2Verifier.sol:139). Trace renders also return false instead of reverting (AssemblyHelpers.yul:302-309; FinalPairing.yul:81-87; TraceReturn.yul:55-61). The evaluator is invoked with call instead of staticcall (QuotientAndLinearization.yul:27-28). There is an extra G1MSM forwarding gas() (QuotientAndLinearization.yul:153). There are non-selector reverts carrying TRACE_U256_MPTR data (QuotientAndLinearization.yul:155-158; kzg/mod.rs:1411). quotient_probe is not a RenderOptions field: render hard-codes false (render.rs:73) and only render_quotient_probe sets it (render.rs:185, feature evm), so it needs no Supported field.
- (12) Truncation is a compile-time cargo feature, not an option: truncated_challenges = cfg!(feature = "truncated-challenges") (artifacts.rs). It masks X3 to 128 bits (TranscriptProofParser.yul:355-366) and truncates x1/x4 powers in PCS (kzg/mod.rs:1091-1107, 1696-1707). Lean Features.solidity must agree (D-P14, R-22).
- (13) External quotient evaluator. The call is staticcall(gas(), quotientEvaluator, frame_base, frame_len, q_out, output_len) (QuotientAndLinearization.yul:35). In evmWithExternal, gas() is an ExternalGas oracle, so completeness ('every run with honest calls returns true') needs honestCalls/Evaluator.rel to force that call to succeed. The verifier then checks returndatasize and magic (:37-38), copies word 1 to QUOTIENT_EVAL_MPTR (:41) and the selector buckets to SELECTOR_ACC_MPTR (:47-49). Evaluator fallback: it reverts empty if calldatasize != QUOTIENT_FRAME_LEN (Halo2QuotientEvaluator.sol:114), calldatacopies the frame into the same MPTRs (:119), and returns [magic, -nu_y(x), sel_acc...] (:157-167). Direct lowering combined with ExternalPinned is rejected (render.rs:57-64). D-P20 is OPEN: QVM.run/Frame/Output have no reference counterpart; the fold is Yul-side; the .oob fault cannot arise; qvm_yul_refines and direct_correct are theorems we originate.
- (14) Pairing orientation, R-11. The swap happens at the call site, FinalPairing.yul:88, which calls ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR). Slot contents: PAIRING_LHS = pi and PAIRING_RHS = final_com - v*G + x3*pi (FinalPairing.yul:76-77). ec_pairing lays out [lhs|G2_BASE|rhs|NEG_S_G2_BASE] (AssemblyHelpers.yul:284-287), so the contract checks e(PAIRING_RHS, G2)·e(PAIRING_LHS, -sG2) = 1, the inverse of Rust's DualMSM::check. It accepts only output word == 1 (:301). It reverts PrecompileFailed on call failure or wrong size (:296) and ProofRejected otherwise (:307). Accumulator mode: alpha = keccak256(tag || vk_digest || kzg_rhs || kzg_lhs || acc_rhs || acc_lhs) mod r, with 0 replaced by 1 (FinalPairing.yul:21-31). This differs from Rust verify_final (R-10), so accumulator-mode equivalence is only ever to ContractRef, never to Rust. The tag is a 29-byte literal, left-padded by mstore (R-26).
- (15) Production revert map. The typed selectors are at Constants.sol:225-232: BadCalldataShape 0x1b99e37c, VkMismatch 0xa447d73e, NonCanonicalScalar 0x77530042, BadPointEncoding 0xf27905ec, PrecompileFailed 0x84e81692, ProofRejected 0xc3b0d8cd, QuotientProgramInvalid 0x3cc81b89 (q_program_fail, QuotientHelpers.yul:6-9), MemoryLayoutViolated 0xc9888d23. In addition, the solc dispatcher (selector, callvalue, ABI bounds) and the evaluator size check produce EMPTY reverts. The production function is view and has no SSTORE or LOG, so the 'only two outcomes, read-only' conjunct is plausible. PLAN maps all Lean error classes to revert, so selectors need not be distinguished.
- (16) Inv-chain rows, entry side (in execution order). Shell/dispatcher (solc): reads calldata[0..4), callvalue and the ABI heads/lengths; writes mem[0x40] = memoryguard(..) plus ABI scratch; reverts empty. headGuard (Halo2Verifier.sol:147-154): reads calldata@0x04 and @0x24; reverts BadCalldataShape (writes mem[0..4) only on fail). bindLocals: vk := AUTHORIZED_VK (loadimmutable, separate-VK renders only; :161); quotientEvaluator := AUTHORIZED_QUOTIENT (external renders only; :168). memory guard (:188-191): reads mem[0x40]; reverts MemoryLayoutViolated if it is > TRANSCRIPT_MPTR = 0x1000. Then let r := FR_MODULUS and let success := true (:214-215).
- (17) Inv row vkLoading (VkLoading.yul:21-141). Reads, embedded VK: none, it mstores constants and commitments to VK_MPTR.. (:33-56). Reads, separate VK: extcodesize/extcodehash(vk), then extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH) (:67-74). Header checks read NUM_INSTANCES_MPTR, K_MPTR, HAS_ACCUMULATOR_MPTR, ACC_OFFSET_MPTR, NUM_ACC_LIMBS_MPTR and NUM_ACC_LIMB_BITS_MPTR (:82-88), then calldata@0x44, @NUM_INSTANCE_CPTR and calldatasize (:101-109). Reverts: VkMismatch (:70, :88); BadCalldataShape (:112). With an accumulator: validate_public_accumulator reads the instance calldata tail and writes ACC_LHS_MPTR / ACC_RHS_MPTR (AccumulatorHelpers.yul:190-365) via G1MSM; it reverts PrecompileFailed or BadPointEncoding (VkLoading.yul:129-136). Post-condition Inv.vk: the VK payload image is at VK_MPTR and the calldata shape is exact.
- (18) Inv row transcriptParser (TranscriptProofParser.yul:19-420). Reads: VK_DIGEST_MPTR, calldata instances, proof bytes [0x64, NUM_INSTANCE_CPTR). Writes the transcript buffer [TRANSCRIPT_MPTR = 0x1000, buf_len); CHALLENGE_MPTR + 32*(offset+j); THETA, BETA, GAMMA, TRASH_CHALLENGE, Y, X, X1, X2, X3 and X4 _MPTR; ADVICE, LOOKUP_M, PERM_Z, LOOKUP_HELPER, LOOKUP_Z, TRASHCAN and QUOTIENT_LIMB _COMMS_MPTR_BASE regions; REVERSED_EVALS_MPTR..; F_COM_MPTR; Q_EVAL_CPTR_MPTR (stores a CALLDATA cursor; q_evals are not spilled); PI_MPTR. Absorb order: vk_digest, 128 zero bytes for committed_pi, num_instances word, then instances. The trash_challenge squeeze is unconditional (:241). squeeze_to computes keccak256(mem[TRANSCRIPT_MPTR..buf_len)), reseeds the buffer with the digest and stores digest mod r (AssemblyHelpers.yul:115-123). Reverts: NonCanonicalScalar (:68, :319, :382, :420); BadPointEncoding (common_uncompressed_g1); BadCalldataShape (:416).
- (19) Inv row lagrange (Lagrange.yul:7-99). Reads X_MPTR, OMEGA_MPTR, OMEGA_INV_TO_L_MPTR, N_INV_MPTR and the calldata instances. Writes LAGRANGE_DENOMS_MPTR.. (num_instances + num_neg_lagranges (+1 if num_instances == 0) + 1 words), BATCH_INV_SCRATCH_MPTR.., X_N_MPTR, X_N_MINUS_1_INV_MPTR, L_LAST_MPTR, L_BLIND_MPTR, L_0_MPTR and INSTANCE_EVAL_MPTR (:81-86). Reverts PrecompileFailed if modexp fails; ProofRejected if a denominator is zero, i.e. x landed in the domain (:93-99).
- (20) Inv row quotientLin (QuotientAndLinearization.yul:1-165). Compact VM (QuotientNumeratorBlock.yul) reads Y, X, L_0, L_LAST, L_BLIND, BETA, GAMMA, THETA, TRASH_CHALLENGE and INSTANCE_EVAL _MPTR (operand table :471-479), REVERSED_EVALS_MPTR and the VK payload (program bytes and constants). It writes the quotient stack/state slots, SELECTOR_ACC_MPTR[0..n) and QUOTIENT_EVAL_MPTR = -nu_y(x) (:1393-1394, :1440). It reverts QuotientProgramInvalid. The External and Direct variants are covered in (13). The linearization prep (:104-127) reads X_MPTR and writes QUOTIENT_MPTR word0 = x^(n-1) and word1 = 1 - x^n. QUOTIENT_MPTR is NOT a G1 point in production. That prep has no revert.
- (21) Inv rows pcs, finalPairing and traceReturn. pcs: Pcs.yul:11-25 wraps the generated kzg::computations text. It reads X1..X4, X, OMEGA and OMEGA_INV _MPTR, REVERSED_EVALS, calldata q_evals via Q_EVAL_CPTR_MPTR, the commitment regions, the VK fixed/permutation commitments, QUOTIENT_MPTR (2 scalars), SELECTOR_ACC, QUOTIENT_EVAL, F_COM, PI and G1_BASE. It writes ROT_POINTS, X1_POWERS, Q_COM, Q_EVAL_SET, G1_IDENTITY, F_EVAL, V, FINAL_COM, PAIRING_LHS (= pi) and PAIRING_RHS. Precompile failures are folded into success, not reverted on the spot (kzg/mod.rs:1826, 1873, 1886, 1898, 1906); they are enforced at FinalPairing.yul:86 (PrecompileFailed). finalPairing: see (14); it writes accumulator_pairing_batch_mptr = 0x1000 and the final_pairing_scratch at PAIRING_BATCH_PTR + PAIRING_BATCH_HASH_BYTES = 0x1240. traceReturn (production, TraceReturn.yul:70-72): if iszero(success) fail ProofRejected; else mstore(RETURN_MPTR, 1) and return(RETURN_MPTR, 0x20), with RETURN_MPTR = verifier_return_mptr = 0x1000. That makes abiTrue = the 32-byte BE word 1. Memory regions are phase-scoped and intentionally overlap at 0x1000 (D-P18: 54 same-byte, different-phase pairs), so Inv k must be stated per phase lifetime, not as global disjointness.
- (22) R-42 / D-P15 for RunContractIR. The IR of record is the standard-json 'ir' artifact compiled with viaIR:true, optimizer enabled, runs 200, evmVersion cancun, metadata.bytecodeHash none, solc 0.8.30+commit.73712a01 (pinned binary at proofs/solidity-verifier/.solc/solc). NOT --ir-ast-json: that is the legacy pipeline's IR, which cannot even compile this contract (stack too deep), and it is insensitive to --via-ir. Import it as a generated Lean file of yul% quotations, with the elaborator as checker and no runtime parser. Measured on the poseidon dump: zero ': u256' annotations, exactly one hex"..." literal (a DSL gap), 76 user functions, 40 builtins. Prerequisite: the vendored dialect lacks memoryguard and setimmutable (EVMOp.lean:39-52). EVMExec.lean:47-50 and 73-76 DELIBERATELY exclude both as solc extensions, which conflicts with D-P15's 'dialect must gain both'. For the runtime sub-object only memoryguard is needed; setimmutable lives in creation code.
- (23) Vendored-API mismatches with the PLAN 9.5 text. RunCommitted (Observation.lean:39) is fixed to EVM.evm, so define RunCommittedWith over Run (D) (BigStep.lean:366). evmWithExternal takes 3 arguments (EVMExec.lean:953). keccak comes from ExecEnv.keccakOf : List UInt8 → U256 (EVMExec.lean:160), while Midfall Hash := Bytes → H256 (Native.lean:50), so a bridge is required. Object has no .runtime: use Object.subObject (Object.lean:80) with the '<Contract>_<id>_deployed' name. obs.isReturn ≙ EvmState.halted = some (.ret, data), with HaltKind at EVMOp.lean:62-63.
- (24) Dispatcher shape that ShellModel/irCheck must recognise. Runtime prologue mstore(64, memoryguard(..)). Selector switch with case 0x1e8e1e13 plus public getters: AUTHORIZED_VK() (separate VK, Constants.sol:5), AUTHORIZED_QUOTIENT() (external quotient, Constants.sol:19) and BUILD_ID() (Constants.sol:157). There is no fallback or receive, so unknown selectors revert empty. Then a callvalue check (non-payable) and ABI decode of (bytes calldata, uint256[] calldata) with offset/length bounds checks that revert empty. The solc locals vk / quotientEvaluator are loadimmutable reads placed BETWEEN the two assembly blocks. R-44: the deployed Moonlight runtime has exactly two immutable slots, at bytes 81 and 293. On memoryguard: soundness holds for any value, because the guard at Halo2Verifier.sol:188-191 only reverts; completeness needs memoryguard <= 0x1000. Expect inline-assembly identifiers to be renamed and Solidity constants (R-38: 91 free constant identifiers) to be inlined in the IR. This is unverified here because no IR file is committed, so irCheck should be α-equivalence modulo constant substitution, checked against the real 'ir' text.
- (25) render_eq_print is FALSE as written (R-39). Restate it structurally with stmtsBeq over the AST (D-P13, R-38 item 2: token equality is weaker than stmtsBeq). Also, render can return Err AFTER the Solidity is produced, at the quotient-listing translation validation (render.rs:84-104), so lower must include that step or the error sides of the equation diverge.
- (26) Stale artifact (R-36). The deployed Moonlight Halo2Verifier.sol predates the typed errors and the current partials; for example it has 'success := validate_public_accumulator(success, r)' (deployed .sol:974) where the current template has a two-result call (VkLoading.yul:130). Use proofs/solidity-verifier/target/poseidon-fixture-dump/*.sol as the current-generator reference. Moonlight bytecode reproduces exactly modulo the 12-byte CBOR trailer and the linked immutables (R-44). The deployment path is proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/.
- (27) The PCS emitter (kzg::computations, kzg/mod.rs:930; Kzg.lean:1320) produces List (List String) text, not AST. Since no runtime Yul parser is permitted (R-42/D-P2 amendment), pcs_spec and the 'main' block of Lowered need an AST-producing re-port of that emitter, or yul% quotation of its output shapes, before a Yul.Block exists to reason about.
- (28) Review the accuracy of these citations before relying on them. They were read at HEAD 69a3472 on 2026-10-26, with formal/Midfall/Lowering/SemanticEquivalence.lean untracked.

## missing
- SolidityGenerator struct, inputs, new and tryNew (Rust: builder/mod.rs:43-68, builder/api.rs:21-73, validate_instance_column_shape at api.rs:80+). PLAN Section 8 calls this 'Builder'. Nothing in formal/Midfall/Generator defines SolidityGenerator.
- VerifierBuildInputs (Rust: lowering/mod.rs:37-45).
- LoweringPlan, PlannedQuotient, QuotientRendering, QuotientEvaluatorRendering, LoweringPlan.new / newDirect / validateGeneratorInvariants / repackedProofLayoutPlan / quotientOperandModel / quotientReadModel, and lowering_plan / lowering_plan_for (Rust: lowering/plan.rs:29-643). This is package P-11; PLAN's L.plan and L.plan.qprog depend on it.
- repackProof and encodeCalldata, the Lean ports of VerifierBuildInputs::repack_proof / encode_calldata (Rust: lowering/calldata.rs:43-149; public wrappers builder/repack.rs:8-19).
- evm.encodeCalldata and FN_SIG_VERIFY_PROOF (Rust: evm.rs:15-39, re-exported at lib.rs:30).
- decodeCalldata, calldataOf and encodeContractProof. There is NO Rust source; they must originate on the theorem side and mirror the acceptance checks in Halo2Verifier.sol:148, VkLoading.yul:101-112, TranscriptProofParser.yul:63-68, 319, 382, 416-420 and AssemblyHelpers.yul:89-110.
- SolidityGenerator.lower : Except GeneratorError Lowered and Lowered.print, plus the full Lowered (plan, headGuard, main, shell, vkRuntime, evaluator, consts). Rust sources: builder/render.rs:35-218 (render, render_with_listing, render_verifier_source_with_plan, render_quotient_evaluator, render_quotient_probe) and lowering/artifacts.rs:77-340 (generate_verifier_from_plan).
- Yul AST builders for the template partials (Rust/Askama: templates/contracts/Halo2Verifier.sol:136-231; partials/verifier/{AssemblyHelpers,AccumulatorHelpers,TraceAndGasHelpers,VkLoading,TranscriptProofParser,Lagrange,QuotientAndLinearization,Pcs,FinalPairing,TraceReturn}.yul; partials/quotient_numerator/{QuotientHelpers,QuotientNumeratorBlock}.yul; Constants.sol for constant substitution). Only the VK constructor (Templates.lean) and model records (Models.lean) exist so far.
- An AST-producing PCS emitter. kzg::computations is ported, but only as text (Kzg.lean:1320).
- The Halo2QuotientEvaluator object: fallback, frame size check, return frame (Rust template: templates/contracts/Halo2QuotientEvaluator.sol:104-170).
- Phase 5 layer: ShellModel (dispatcher incl. AUTHORIZED_VK/AUTHORIZED_QUOTIENT/BUILD_ID getters), bindLocals, RunVerifier, RunShell, RunContractIR, a dialect-generic RunCommitted, ObsEquiv, irCheck, ImportSolcIR (generated yul% file), Bridge (ExternalCalls.mk from Externals.lean relations), calls L W, honestCalls, Evaluator.rel, noCreates, abiTrue, initState / callState, Eip2537.Holds and Modexp.Holds. None exists; only Midfall/Yul/Externals.lean is present.
- memoryguard in the vendored EVM dialect (D-P15 prerequisite; absent from EVMOp.lean). setimmutable is also absent but is only needed for creation code.
- validateQuotientProgramOperands and quotient_operand_model (Rust: lowering/quotient_numerator/vm validate_quotient_program_operands; lowering/plan.rs:367). This is package P-09e, needed for Supported.qvm.
- QVM.run, QVM.Frame and QVM.Output, frameOf, outputOf and quotientParts. Per D-P20 these have NO Rust counterpart: the reference entry is the per-identity eval_quotient_identity, and the fold is Yul-side.
- decodeAcc, encodeAccInstances, accWords, alphaOf and batchedCheck over Midfall.Generator.AccumulatorEncoding (D-P16), plus the accumulator arm of ContractRefAccepts. Rust/Yul sources: AccumulatorHelpers.yul:22-365 and FinalPairing.yul:14-61.
- Inv k memory invariants per MemoryPhase, the per-partial *_spec contracts, and Deployment with real fields (vkAddr, quotientAddr, W.code, W.extcodehash). The current Deployment is all True.

## declarations
- `VerifierBuildInputs::repack_proof` (proofs/solidity-verifier/src/lowering/calldata.rs:43)
    sig: pub(crate) fn repack_proof(&self, compressed: &[u8]) -> Result<Vec<u8>, RepackError>
    notes: impl<'params, 'meta> VerifierBuildInputs<'params, 'meta>. Turns native compressed proof bytes into Solidity proof bytes. Checks length first (calldata.rs:49-57, LengthMismatch). Then walks plan.g1_groups G1s, num_evals scalars, f_com, num_point_sets q_evals, pi (109-126). G1: ZCash 48B from_bytes, else InvalidCompressedG1. Identity becomes 128 zero bytes; any other point becomes 16 zero || x_be[0..16] || x_be[16..48] || 16 zero || y_be[0..16] || y_be[16..48]. Scalar: LE 32B; from_repr is checked, else NonCanonicalScalar; then byte-reversed to BE. Not ported to Lean.
- `VerifierBuildInputs::encode_calldata` (proofs/solidity-verifier/src/lowering/calldata.rs:132)
    sig: pub(crate) fn encode_calldata( &self, compressed_proof: &[u8], instances: &[Fq], ) -> Result<Vec<u8>, GeneratorError>
    notes: First checks instances.len() == self.num_instances, the GeneratorConfig count rather than the plan count. On mismatch it returns GeneratorError::Planning { stage: "calldata", message: "instance length mismatch: expected {}, got {}" }. Then repack_proof(...)? (RepackError lifted via From, = Lean GeneratorError.fromRepackError) and crate::evm::encode_calldata(&proof, instances). It does not check instance canonicality, because the Fq type already guarantees it.
- `VerifierBuildInputs::repacked_proof_layout_plan` (proofs/solidity-verifier/src/lowering/calldata.rs:157)
    sig: fn repacked_proof_layout_plan(&self) -> RepackedProofLayoutPlan
    notes: Body is self.lowering_plan().repacked_proof_layout_plan(). So repack ALWAYS builds the compact-VM LoweringPlan (LoweringPlan::new), whatever RenderOptions.quotient_lowering says, and that builder can panic.
- `SolidityGenerator::repack_proof / encode_calldata (public)` (proofs/solidity-verifier/src/builder/repack.rs:8)
    sig: pub fn repack_proof(&self, compressed: &[u8]) -> Result<Vec<u8>, RepackError> ... pub fn encode_calldata( &self, compressed_proof: &[u8], instances: &[Fq], ) -> Result<Vec<u8>, GeneratorError>
    notes: Thin wrappers over self.inputs().repack_proof / encode_calldata (repack.rs:8-19). These are the public names PLAN's repackProof / encodeCalldata mirror.
- `evm::FN_SIG_VERIFY_PROOF` (proofs/solidity-verifier/src/evm.rs:15)
    sig: pub const FN_SIG_VERIFY_PROOF: [u8; 4] = [0x1e, 0x8e, 0x1e, 0x13];
    notes: Selector of verifyProof(bytes,uint256[]). Re-exported at lib.rs:30. Not in the Lean tree; grep finds no 1e8e1e13 under formal/Midfall.
- `evm::encode_calldata` (proofs/solidity-verifier/src/evm.rs:22)
    sig: pub fn encode_calldata<F>(proof: &[u8], instances: &[F]) -> Vec<u8> where F: PrimeField, F::Repr: AsRef<[u8]>,
    notes: Total function: selector || u256(0x40) || u256(0x40+0x20+proof.len()) || u256(proof.len()) || proof || u256(n) || n BE instance words (fe_to_u256 then to_u256_be_bytes). It never pads proof to a 32-byte multiple. The output is valid ABI only because repacked_len is a sum of 128s and 32s. This is the ONLY calldata codec in Rust: there is NO decoder anywhere in proofs/solidity-verifier/src.
- `LoweringPlan` (proofs/solidity-verifier/src/lowering/plan.rs:29)
    sig: pub(crate) struct LoweringPlan { pub(crate) vk: Halo2VerifyingKey, pub(crate) vk_mptr: Ptr, pub(crate) meta: ConstraintSystemMeta, pub(crate) data: Data, pub(crate) proof_layout: ProofCalldataLayout, pub(crate) lowering: QuotientLowering, pub(crate) sorted_simple: Vec<usize>, pub(crate) quotient: Option<PlannedQuotient>, pub(crate) direct: Option<DirectQuotientPlanned>, pub(crate) pcs_memory_requirements: PcsMemoryRequirements, pub(crate) memory: VerifierMemoryLayout, }
    notes: Owned by P-11, not ported. PlannedQuotient (plan.rs:49-55) has fields plan: QuotientProgramPlan, build: QuotientProgramBuild, program: QuotientProgram, stack_mptr: usize, state_slots: QuotientStateSlots. Exactly one of quotient/direct is Some, which validate_generator_invariants checks. PLAN's L.plan.qprog corresponds to quotient.build.bytes.
- `VerifierBuildInputs::lowering_plan / lowering_plan_for` (proofs/solidity-verifier/src/lowering/plan.rs:124)
    sig: pub(crate) fn lowering_plan(&self) -> LoweringPlan ... pub(crate) fn lowering_plan_for( &self, lowering: QuotientLowering, ) -> Result<LoweringPlan, GeneratorError>
    notes: Lowering entry point (124, 129-137). Vm maps to Ok(LoweringPlan::new(self)), which panics instead of returning Err. Direct maps to LoweringPlan::new_direct(self), which returns Err(GeneratorError::Planning{..}).
- `LoweringPlan::new / new_direct` (proofs/solidity-verifier/src/lowering/plan.rs:235)
    sig: pub(crate) fn new(inputs: &VerifierBuildInputs<'_, '_>) -> Self ... pub(crate) fn new_direct(inputs: &VerifierBuildInputs<'_, '_>) -> Result<Self, GeneratorError>
    notes: new (235) panics in two places: 'generator invariant violation' (309-310) and 'quotient dual-build certification failed' (320-326). new_direct is at line 165. Both compute proof_layout = ProofCalldataLayout::from_protocol(&meta.protocol, VERIFY_PROOF_PROOF_CPTR, meta.num_evals, meta.num_point_sets) (173-178 and 239-244). The same proof layout across VM and Direct is likely by construction, but it is an owed lemma.
- `LoweringPlan::validate_generator_invariants` (proofs/solidity-verifier/src/lowering/plan.rs:413)
    sig: fn validate_generator_invariants(&self) -> Result<(), String>
    notes: Runs meta.validate_against_protocol, memory.validate() (the STRONG VerifierMemoryLayout::validate including the 0x1000 bound; D-P18), kzg::validate_absorbed_g1_precompile_coverage (the points_subgroup_checked counterpart) and the PCS-requirement drift check. Then, for Direct, the constant-table checks; for VM, program/const/stack checks and vm::validate_quotient_program_operands (QVM-01). So Supported.layout and Supported.qvm are already ENFORCED by a successful plan build.
- `VerifierBuildInputs` (proofs/solidity-verifier/src/lowering/mod.rs:38)
    sig: pub(crate) struct VerifierBuildInputs<'params, 'meta> { pub(crate) params: &'params ParamsKZG<Bls12>, pub(crate) vk: &'params VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>, pub(crate) num_instances: usize, pub(crate) num_committed_instances: usize, pub(crate) acc_encoding: Option<AccumulatorEncoding>, pub(crate) meta: &'meta ConstraintSystemMeta, }
    notes: Built by SolidityGenerator::inputs (builder/mod.rs:59-68). num_committed_instances comes from meta.num_committed_instances. Not ported.
- `SolidityGenerator` (proofs/solidity-verifier/src/builder/mod.rs:44)
    sig: pub struct SolidityGenerator<'a> { params: &'a ParamsKZG<Bls12>, vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>, num_instances: usize, acc_encoding: Option<AccumulatorEncoding>, meta: ConstraintSystemMeta, }
    notes: PLAN's g. Note there is no stored GeneratorConfig: g.cfg.numCommittedInstances lives in meta and g.cfg.accumulator is acc_encoding. Not ported.
- `SolidityGenerator::try_new` (proofs/solidity-verifier/src/builder/api.rs:33)
    sig: pub fn try_new( params: &'a ParamsKZG<Bls12>, vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>, config: GeneratorConfig, ) -> Result<Self, GeneratorError>
    notes: Checks run in this order (38-61): NoAdviceColumns; validate_instance_column_shape(num_instance_columns, num_committed_instances) with SUPPORTED_COMMITTED_INSTANCE_COLUMNS=1 and SUPPORTED_NON_COMMITTED_INSTANCE_COLUMNS=1 (api.rs:12-14); acc_encoding.validate_for_num_instances; RotatedInstanceQuery if any instance query rotation is not cur. new (21-28) panics on Err. These are the Supported.advice/instShape/acc/noRotInst sources.
- `SolidityGenerator::render` (proofs/solidity-verifier/src/builder/render.rs:35)
    sig: pub fn render(&self, options: RenderOptions) -> Result<RenderedArtifacts, GeneratorError>
    notes: Calls render_with_listing(options, true) (41-45). Direct combined with ExternalPinned is an Err (57-64). The flow is lowering_plan_for, then render_verifier_source_with_plan (154-176), then the optional VK and evaluator. quotient_probe is hard-coded false (73). AFTER the Solidity is produced, quotient_listing_artifacts can still fail with stage "quotient listing" (84-104). So render can be Err even when the Solidity rendered fine.
- `VerifierBuildInputs::generate_verifier_from_plan` (proofs/solidity-verifier/src/lowering/artifacts.rs:77)
    sig: pub(crate) fn generate_verifier_from_plan( &self, plan: &LoweringPlan, separate: bool, trace: bool, gas_checkpoints: bool, external_quotient: bool, expected_quotient: Option<(usize, U256)>, provenance: Option<[u8; 32]>, ) -> Halo2Verifier
    notes: Builds the Askama model; this is the place to port 'lower'. Key bindings: abi_selector_bytes = 0x04, abi_proof_head_offset = 0x40, abi_instances_head_cptr = SELECTOR_BYTES + WORD_BYTES = 0x24 (304-306); num_instance_cptr = proof_layout.proof_end and instance_cptr = proof_end + 0x20 (307-308); pcs_computations = kzg::computations(...) (151); truncated_challenges = cfg!(feature = "truncated-challenges"). It panics on validate_layout failure (338-340).
- `layout::abi constants` (proofs/solidity-verifier/src/lowering/layout/mod.rs:378)
    sig: pub(crate) const SELECTOR_BYTES: usize = 0x04; pub(crate) const VERIFY_PROOF_HEAD_WORDS: usize = 2; pub(crate) const VERIFY_PROOF_HEAD_BYTES: usize = VERIFY_PROOF_HEAD_WORDS * super::WORD_BYTES; pub(crate) const VERIFY_PROOF_PROOF_CPTR: usize = SELECTOR_BYTES + VERIFY_PROOF_HEAD_BYTES + super::WORD_BYTES; pub(crate) const VERIFY_PROOF_PROOF_HEAD_OFFSET: usize = VERIFY_PROOF_HEAD_BYTES;
    notes: Values: 0x04, 0x40, 0x64, 0x40 (test at 800-803). Already ported as Midfall.Generator.abiSelectorBytes / abiVerifyProofHeadBytes / abiVerifyProofProofCptr / abiVerifyProofProofHeadOffset (Abi.lean:120,126,132,139).
- `layout::trace namespaces` (proofs/solidity-verifier/src/lowering/layout/mod.rs:774)
    sig: pub(crate) const PCS_QUERY_BASE: u64 = 2_000; pub(crate) const PROOF_COMMIT_BASE: usize = 10_000; pub(crate) const PROOF_EVAL_BASE: usize = 20_000; pub(crate) const QUOTIENT_IDENTITY_BASE: u64 = 30_000; pub(crate) const PCS_SERIALIZED_POINT_SET_BASE: u64 = 41_000; pub(crate) const SELECTOR_FOLD_BASE: usize = 60_000;
    notes: LOG1 topic IDs, used only by trace renders. Ported, e.g. Midfall.Generator.Trace.proofCommitBase (Layout.lean:1161).
- `ProofCalldataLayout (Rust)` (proofs/solidity-verifier/src/lowering/abi/proof.rs:55)
    sig: pub(crate) struct ProofCalldataLayout { proof_cptr, advice_phases: Vec<ProofSection>, lookup_multiplicities, permutation_products, lookups: Vec<ProofLookupCommitmentsLayout>, trash, quotient_limbs, evals, f_com, q_evals, pi, quotient_comm_cptr, eval_cptr, w_cptr, q_eval_cptr, proof_end, proof_len }
    notes: Fields summarised from proof.rs:55-89. The faithful port is Midfall.Generator.ProofCalldataLayout (Abi.lean:209).
- `kzg::validate_absorbed_g1_precompile_coverage` (proofs/solidity-verifier/src/lowering/kzg/mod.rs:723)
    sig: pub(crate) fn validate_absorbed_g1_precompile_coverage( meta: &ConstraintSystemMeta, data: &Data, memory: &VerifierMemoryLayout, proof_layout: &ProofCalldataLayout, ) -> Result<(), String>
    notes: Rust counterpart of PLAN points_subgroup_checked. Ported as Midfall.Generator.validateAbsorbedG1PrecompileCoverage (Kzg.lean:1099).
- `kzg::computations` (proofs/solidity-verifier/src/lowering/kzg/mod.rs:930)
    sig: pub(crate) fn computations( meta: &ConstraintSystemMeta, data: &Data, memory: &VerifierMemoryLayout, truncated_challenges: bool, trace: bool, ) -> Vec<Vec<String>>
    notes: PCS sub-blocks emitted as TEXT lines. The Lean port Midfall.Generator.computations (Kzg.lean:1320) also returns Except Fault (List (List String)). There is no runtime Yul parser (R-42/D-P2), so pcs_spec over a Yul.Block needs an AST-building re-port of this emitter.
- `Midfall.Lowering.Lowered` (formal/Midfall/Lowering/Types.lean:34)
    sig: structure Lowered where headGuard : YulBlock main : YulBlock vkRuntime : Bytes evaluator : Option YulObject
    notes: Placeholder. PLAN's plan / shell / consts fields are missing. YulBlock = YulSemantics.Block YulSemantics.EVM.Op and YulObject = YulSemantics.Object Op (Types.lean:22-28).
- `Midfall.Lowering.GeneratorError` (formal/Midfall/Lowering/Types.lean:41)
    sig: inductive GeneratorError where | planning (stage message : String) | render (artifact : String)
    notes: A 2-constructor placeholder that COLLIDES in spirit with the faithful Midfall.Generator.GeneratorError (Api.lean:309: noAdviceColumns, unsupportedInstanceColumnShape, rotatedInstanceQuery, unsupportedAccumulatorEncoding, planning, render, repack ...). New statements should use Midfall.Generator.GeneratorError.
- `Midfall.Lowering.Supported` (formal/Midfall/Lowering/Types.lean:51)
    sig: structure Supported (numAdvice numInstances numChallenges numQuotientLimbs csDegree : Nat) (qvmValidated : Prop) (trace gasCheckpoints : Bool) : Prop where advice : numAdvice ≠ 0 instShape : numInstances = 2 singlePhase : numChallenges = 0 hLimbs : numQuotientLimbs = csDegree - 1 qvm : qvmValidated production : trace = false ∧ gasCheckpoints = false
    notes: Placeholder over raw numbers. noRotInst, acc, vkPoints and layout are absent. instShape lacks the numCommittedInstances = 1 half.
- `Midfall.Lowering.Deployment` (formal/Midfall/Lowering/Types.lean:71)
    sig: structure Deployment (vkRuntime : Bytes) (evaluator : Option YulObject) (vkCodehash quotientCodehash : H256) : Prop where vkCode : True vkHash : True qObj : True qHash : True
    notes: VACUOUS: every field is True. Any theorem that takes it as a hypothesis gains nothing from it, so it must be replaced before lowering_equivalence is stated.
- `Midfall.Lowering.ContractRefAccepts` (formal/Midfall/Lowering/Types.lean:83)
    sig: def ContractRefAccepts {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool
    notes: Gₜ is a phantom of DualMSM, so callers must write (Gₜ := Gₜ). Only the no-accumulator arm exists. Proven equivalent to verifyMsgs as contractRefAccepts_iff_verifyMsgs (SemanticEquivalence.lean:29). The frozen copy is Statements.contractRef_noAcc (Statements.lean:73, sorry).
- `Midfall.Generator.ProofCalldataLayout / fromProtocol` (formal/Midfall/Generator/Abi.lean:209)
    sig: structure ProofCalldataLayout where (proofCptr advicePhases lookupMultiplicities permutationProducts lookups trash quotientLimbs evals fCom qEvals pi quotientCommCptr evalCptr wCptr qEvalCptr proofEnd proofLen) ... def ProofCalldataLayout.fromProtocol (protocol : ProtocolPlan) (proofCptr numEvals numPointSets : Nat) : Except Fault ProofCalldataLayout
    notes: Faithful port. fromProtocol (Abi.lean:334) is FALLIBLE in Lean (Except Fault), while the Rust from_protocol is infallible-or-panic. Related: commitmentReadGroups (472) and totalG1Count (440).
- `Midfall.Generator.RepackedProofLayoutPlan` (formal/Midfall/Generator/Quotient/VmTypes.lean:703)
    sig: structure RepackedProofLayoutPlan where g1Groups : List Nat numEvals : Nat numPointSets : Nat ... def RepackedProofLayoutPlan.fromProofLayout (layout : ProofCalldataLayout) : RepackedProofLayoutPlan def RepackedProofLayoutPlan.compressedLen (self : RepackedProofLayoutPlan) : Nat def RepackedProofLayoutPlan.repackedLen (self : RepackedProofLayoutPlan) : Nat
    notes: fromProofLayout is at 720, compressedLen at 739, repackedLen at 748. This is the natural argument for a Lean repackProof : RepackedProofLayoutPlan -> Bytes -> Except RepackError Bytes, which is not yet written.
- `Midfall.Generator.RepackError / GeneratorError / ApiFault` (formal/Midfall/Generator/Api.lean:257)
    sig: inductive RepackError | lengthMismatch (expected actual prefixG1 numEvals numPointSets : Nat) | invalidCompressedG1 (offset : Nat) (bytesHex : String) | nonCanonicalScalar (offset : Nat) (bytesHex : String) ... def GeneratorError.fromRepackError (err : RepackError) : GeneratorError := GeneratorError.repack err ... inductive ApiFault where | error (e : GeneratorError) | panic (site : String)
    notes: GeneratorError is at 309, fromRepackError at 388, ApiFault at 396. A faithful lower/repack that ports the LoweringPlan::new panics should return Except ApiFault.
- `Midfall.Generator.GeneratorConfig / RenderDiagnostics / RenderOptions` (formal/Midfall/Generator/Api.lean:812)
    sig: structure GeneratorConfig where numInstances : Nat numCommittedInstances : Nat accumulator : Option AccumulatorEncoding ... structure RenderDiagnostics where (trace : Bool) (gasCheckpoints : Bool) structure RenderOptions where vk : RenderVk quotient : RenderQuotient quotientLowering : QuotientLowering diagnostics : RenderDiagnostics provenance : Option Bytes
    notes: RenderDiagnostics is at 923 and RenderOptions at 942. Supported.production can be stated directly as o.diagnostics.trace = false ∧ o.diagnostics.gasCheckpoints = false. Per D-P16, Supported.acc must use this Generator.AccumulatorEncoding, not the Exec stand-in.
- `Midfall.Generator.validateAbsorbedG1PrecompileCoverage` (formal/Midfall/Generator/Kzg.lean:1099)
    sig: def validateAbsorbedG1PrecompileCoverage (meta_ : ConstraintSystemMeta) (data : Data) (memory : VerifierMemoryLayout) (proofLayout : ProofCalldataLayout) : Except Fault (Except String Unit)
    notes: Returns a nested Except: the outer one is the panic channel, the inner one is the Rust Result.
- `Midfall.Generator.VerifierMemoryLayout.validate` (formal/Midfall/Generator/Layout.lean:1023)
    sig: def VerifierMemoryLayout.validate (self : VerifierMemoryLayout) : Except String Unit
    notes: Use this, not MemoryMap.WellFormed, for Supported.layout (D-P18 OPEN). WellFormed omits the 0x1000 bound and alignment.
- `Midfall.Generator.Halo2Verifier` (formal/Midfall/Generator/Models.lean:757)
    sig: structure Halo2Verifier (Memory Proof : Type) where
    notes: Askama-model port. Memory and Proof are type PARAMETERS standing in for VerifierMemoryLayout and ProofCalldataLayout; they are not instantiated by any builder yet. Fields include trace, gasCheckpoints, quotientProbe, embeddedVk, numInstances, k and proofLen.
- `Midfall.Halo2.decodeRust / prepareMsgs / verifyMsgs / verifyNative / Hash` (formal/Midfall/Halo2/Exec/Native.lean:228)
    sig: abbrev Hash := Bytes → H256 def verifyNative {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ] (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (proof : Bytes) : Except Fault Unit def decodeRust (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) : Option (List (Msg (Fr p) G₁)) def prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ) def verifyMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (F : Features) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Except Fault Unit
    notes: Line numbers: Hash at 50, verifyNative at 207, decodeRust at 228, prepareMsgs at 255, verifyMsgs at 273. Section variables (Native.lean:30-34) supply p, G₁, G₂, Gₜ and the instances; Gₜ is a phantom and must be passed as (Gₜ := Gₜ). PLAN writes decodeRust .solidity g.vk π, but the real arity is E F vk inst π. inst is the NON-committed column only: verifyNativeWith passes committed=[[1]] and inst=[[inst.toList]] (Native.lean:185).
- `YulSemantics.RunCommitted` (formal/vendor/yul-semantics/YulSemantics/Observation.lean:39)
    sig: def RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm) (stObs : EvmState) (o : Outcome) : Prop := ∃ st', Run EVM.evm prog st0 V' st' o ∧ stObs = committedState st0 st'
    notes: HARDWIRED to the deterministic dialect EVM.evm, in which staticcall/call/gas are stuck. PLAN's EVM.RunCommitted (EVM.evmWithExternal (calls L W) noCreates) (keccak := H) does not exist. You need a dialect-generic copy built on Run (D : Dialect) (BigStep.lean:366).
- `YulSemantics.Run` (formal/vendor/yul-semantics/YulSemantics/BigStep.lean:366)
    sig: def Run (D : Dialect) [DecidableEq D.Value] (prog : Block D.Op) (st0 : D.State) (V' : VEnv D) (st' : D.State) (o : Outcome) : Prop := ExecStmt D [] [] st0 (.block prog) V' st' o
    notes: Dialect-generic big-step run. Outcome (Ast.lean:353) is control-flow only (normal/break/continue/leave/halt). Return/revert data lives in EvmState.halted : Option (HaltKind × List UInt8) (EVMExec.lean:227).
- `YulSemantics.EVM.evmWithExternal` (formal/vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:953)
    sig: @[reducible] def evmWithExternal (calls : ExternalCalls) (creates : ExternalCreates) (gasOracle : ExternalGas) : Dialect where
    notes: Takes THREE arguments, while PLAN passes two. Keccak is ExecEnv.keccakOf : List UInt8 → U256 (EVMExec.lean:160), an environment field rather than a parameter. ExternalGas.any makes gas() arbitrary.
- `YulSemantics.Object / Object.subObject` (formal/vendor/yul-semantics/YulSemantics/Ast.lean:327)
    sig: inductive Object (Op : Type) | mk (name : String) (code : Block Op) (subObjects : List (Object Op)) (data : List (String × Data)) ... def subObject (o : Object Op) (name : String) : Option (Object Op) := o.subObjects.find? (fun s => s.name = name)
    notes: subObject is at Object.lean:80. There is NO .runtime field: PLAN's ir.runtime must become (ir.subObject "<C>_<id>_deployed").map Object.code, or an equivalent new def.
- `Midfall.Yul.ExternalCallRelation / honestRelations` (formal/Midfall/Yul/Externals.lean:779)
    sig: structure ExternalCallRelation where address : Word256 validInput : Bytes -> Bool outputLen : Bytes -> Option Nat gas : Bytes -> Nat output : Bytes -> Option Bytes ... def honestRelations (product : PairingProduct) : List ExternalCallRelation := [g1AddRelation, g1MsmRelation, pairingRelation product, modexpRelation]
    notes: honestRelations is at 1006. These are the four precompiles only. The fold into EVM.ExternalCalls (Bridge.lean) and the evaluator relation are not written yet. The comment at Externals.lean:756 says the gas field is 'never gas()'; that is true for precompiles only, because the evaluator call forwards gas().

## verbatim excerpts

### proofs/solidity-verifier/src/evm.rs:22
```lean
pub fn encode_calldata<F>(proof: &[u8], instances: &[F]) -> Vec<u8>
where
    F: PrimeField,
    F::Repr: AsRef<[u8]>,
{
    let offset = 0x40;
    let num_instances = instances.len();
    chain![
        FN_SIG_VERIFY_PROOF,                           // function signature
        to_u256_be_bytes(offset),                      // offset of proof
        to_u256_be_bytes(offset + 0x20 + proof.len()), // offset of instances
        to_u256_be_bytes(proof.len()),                 // length of proof
        proof.iter().cloned(),                         // proof
        to_u256_be_bytes(num_instances),               // length of instances
        instances.iter().map(fe_to_u256::<F>).flat_map(to_u256_be_bytes), // instances
    ]
    .collect()
}
```

### proofs/solidity-verifier/src/lowering/calldata.rs:67
```lean
            let Some(pt) = Option::<G1Affine>::from(<G1Affine as GroupEncoding>::from_bytes(&comp))
            else {
                return Err(RepackError::InvalidCompressedG1 {
                    offset: cur,
                    bytes_hex: hex::encode(comp.as_ref()),
                });
            };
            if bool::from(pt.is_identity()) {
                out.extend_from_slice(&[0u8; 128]);
                return Ok(());
            }
            let x_be = pt.x().to_bytes_be();
            let y_be = pt.y().to_bytes_be();
            out.extend_from_slice(&[0u8; 16]);
            out.extend_from_slice(&x_be[0..16]);
            out.extend_from_slice(&x_be[16..48]);
            out.extend_from_slice(&[0u8; 16]);
            out.extend_from_slice(&y_be[0..16]);
            out.extend_from_slice(&y_be[16..48]);
            Ok(())
```

### proofs/solidity-verifier/src/lowering/calldata.rs:109
```lean
        for &n in &plan.g1_groups {
            for _ in 0..n {
                push_g1(&mut cursor, &mut out)?;
            }
        }
        // evals (Fr 32-byte LE in native proof) -> BE calldata words
        // (incl. dummy slots).
        for _ in 0..plan.num_evals {
            push_scalar_be(&mut cursor, &mut out)?;
        }
        // f_com
        push_g1(&mut cursor, &mut out)?;
        // q_evals (Fr 32-byte LE in native proof) -> BE calldata words.
        for _ in 0..plan.num_point_sets {
            push_scalar_be(&mut cursor, &mut out)?;
        }
        // pi
        push_g1(&mut cursor, &mut out)?;
        debug_assert_eq!(cursor, compressed.len());
        Ok(out)
```

### proofs/solidity-verifier/templates/contracts/Halo2Verifier.sol:136
```lean
    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) external {%- if self.trace || self.gas_checkpoints %} returns (bool) {%- else %} view returns (bool) {%- endif %} {
        // Cheap ABI-shape guard before any generated memory work:
        //   - proof head must point at the bytes payload;
        //   - instances head must point at the generated instance array.
        //
        // The verifier below is a hand-rolled calldata parser. Failing here
        // keeps malformed dynamic-argument layouts from being interpreted as a
        // valid Midfall proof stream.
        assembly ("memory-safe") {
            if iszero(and(eq(calldataload({{ abi_selector_bytes|hex() }}), {{ abi_proof_head_offset|hex() }}), eq(calldataload({{ abi_instances_head_cptr|hex() }}), sub(NUM_INSTANCE_CPTR, {{ abi_selector_bytes|hex() }})))) {
                // BadCalldataShape() -- fail() is not in scope in this early
                // guard block, so write the selector inline.
                mstore(0x00, shl(224, ERR_BAD_CALLDATA_SHAPE))
                revert(0x00, 0x04)
            }
        }
```

### proofs/solidity-verifier/templates/partials/verifier/VkLoading.yul:101
```lean
                success := and(success, eq({{ proof_len|hex() }}, calldataload(PROOF_LEN_CPTR)))
                success := and(success, eq({{ num_instances }}, calldataload(NUM_INSTANCE_CPTR)))
                // Calldata must contain exactly the ABI selector, proof bytes,
                // instance-array length, and generated number of instance
                // words. Any trailing bytes fail closed.
                success := and(
                    success,
                    eq(calldatasize(), add(INSTANCE_CPTR, {{ (num_instances * 32)|hex() }}))
                )
                // Stop before any transcript absorption if the ABI/proof shape
                // is not exactly the generated one.
                if iszero(success) { fail(ERR_BAD_CALLDATA_SHAPE) }
```

### proofs/solidity-verifier/templates/partials/verifier/AssemblyHelpers.yul:89
```lean
            function common_uncompressed_g1(buf_len, cptr) -> ret {
                let x_hi_word := calldataload(cptr)
                let x_lo := calldataload(add(cptr, 0x20))
                let y_hi_word := calldataload(add(cptr, 0x40))
                let y_lo := calldataload(add(cptr, 0x60))
                if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }
                if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }

                let x_hi := and(x_hi_word, 0xffffffffffffffffffffffffffffffff)
                let y_hi := and(y_hi_word, 0xffffffffffffffffffffffffffffffff)
                if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {
                    fail(ERR_BAD_POINT_ENCODING)
                }
                if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {
                    fail(ERR_BAD_POINT_ENCODING)
                }

                // Memcpy the 4 calldata words (128 bytes) verbatim
                // into the keccak buffer.
                calldatacopy(buf_len, cptr, 0x80)
                ret := add(buf_len, 0x80)
            }
```

### proofs/solidity-verifier/templates/partials/verifier/FinalPairing.yul:68
```lean
            // The Yul `ec_pairing` helper checks
            //   e(arg0, G2_BASE) * e(arg1, NEG_S_G2_BASE) == 1
            // i.e.  e(arg0, [1]_2) = e(arg1, [s]_2).
            //
            // The KZG pairing identity is
            //   e(final_com - v*G + x3*pi, [1]_2) = e(pi, [s]_2),
            // so arg0 must be (final_com - v*G + x3*pi) and arg1 must be
            // pi. The PAIRING_*_MPTR slots store
            //   PAIRING_LHS_MPTR := pi
            //   PAIRING_RHS_MPTR := final_com - v*G + x3*pi
            // -- the historical "LHS"/"RHS" naming follows the dual MSM
            // accumulator (left = pi, right = combined) and *not* the
            // pairing argument order. Pass them swapped to ec_pairing.
            {%- if self.trace %}
            // Trace renders do not revert on a failed final check: `success`
            // (0 or 1) is traced and returned by TraceReturn, so the logs of
            // a rejected proof remain observable. Production renders revert.
            {%- else %}
            if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
            {%- endif %}
            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)
```

### proofs/solidity-verifier/templates/partials/verifier/TraceReturn.yul:62
```lean
            {%- else -%}
            // Success path is terminal. Invalid inputs have already reverted,
            // so the Solidity ABI observes `true`.
            //
            // The guard is redundant today -- every failure path above reverts
            // rather than clearing `success` -- but it keeps acceptance a local
            // property of this file instead of an invariant split across
            // FinalPairing.yul and ec_pairing.
            if iszero(success) { fail(ERR_PROOF_REJECTED) }
            mstore(RETURN_MPTR, 1)
            return(RETURN_MPTR, 0x20)
            {%- endif %}
```
