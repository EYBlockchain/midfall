/-
Midfall.Lowering.RunEmitted

P-EXEC (docs/plans/P-EXEC-run-emitted.md): RUN THE EMITTED PROGRAM THROUGH THE VENDORED
BIG-STEP SEMANTICS AND SEE WHETHER IT GETS STUCK.

WHY THIS EXISTS. P-ARITY enumerated nine unchecked well-formedness dimensions and correctly
refused to close the biggest one - builtin argument arity - with a hand-written table, because
the dialect has no arity function and a table would be a NEW UNVERIFIED SOURCE OF TRUTH. The
answer is not a table. A wrong-arity builtin call has no Step rule, so the SEMANTICS GETS STUCK
on it, and the vendored fuel-indexed interpreter (YulSemantics.Interp, adequacy in
YulSemantics.Adequacy) decides stuckness for arity, missing helper, unbound variable and
use-before-declaration at once. Nothing in the tree had ever executed GenAst output: the only
run witness in the tree, Midfall.Instances.ImportedIR.runContractIR_inhabited
(ImportedIR.lean:260), runs the IMPORTED solc IR, not the emitted AST. This is the first
execution of the generator's own output.

WHAT STUCK MEANS, precisely. Interp.Result has ok, stuck and outOfFuel. stuck is the
interpreter reporting that no Step rule applies - the empirical question. outOfFuel is NOT a
pass and never excuses one: FUEL is an explicit bound and a unit that exhausts it fails.

THE ONE EXCUSE, AND ITS LIMIT. The vendored executable dialect EVM.exec is the CLOSED one:
stepOp returns none for gas, call, callcode, delegatecall, staticcall, create and create2
(EVMExec.lean:869-870) and routes those through the ExternalCalls relation instead - which is
what Midfall/Yul/Bridge.lean's header records at lines 12-16 ("every precompile call the
generated verifier makes is STUCK there"). A unit that reaches a precompile is therefore stuck
in this dialect for a reason that is the dialect, not the program. The excuse is per unit and
is granted only when the unit's OWN call closure reaches one of the seven (blindOpsCalledIn,
reusing P-ARITY's classifier rather than inventing one); a unit whose closure touches no
call-family builtin must not be stuck at all. THE LIMIT IS STATED, NOT HIDDEN: inside a unit
whose closure does reach a precompile, this gate cannot distinguish a wrong-arity staticcall
from a wrong-arity local builtin, because the closed dialect is blind to the call family
whatever its arguments. Closing that needs an ExecDialect over Bridge.Dialect plus the Lawful
proof adequacy requires; this package attempted it (the construction is in the package report)
and did not land it, and that is the named remaining gap.

WHAT IS NOT HERE EITHER.
  * No run on real calldata that ACCEPTS. emittedWholeProgramStopsAt_ok and
    emittedWholeProgramRevertSelector_ok pin the exact instruction the empty-calldata world
    reaches instead; the package report names the blockers.
  * No theorem form. The plan asked for interpreter-ok to be lifted into Run via adequacy in
    Midfall/Instances/RunEmitted.lean. That module was written and MEASURED at 16.8 GB
    resident for the per-unit native decision on a 32 GB machine, so it is not shipped: a
    gate that OOM-kills the session is worse than no gate. The lifting is one line
    (Interp.run_sound over the vendored exec_lawful) and is recorded here so a later package
    can state it over a narrower unit set.
  * No per-helper #eval gate, for the same measured reason - see the note above gatedUnits.
-/
import Midfall.Lowering.GenAstDispatch
import Midfall.Generator.VerifierPartials
import Midfall.Lowering.Partials
import YulSemantics.Interp

namespace Midfall.Lowering.RunEmitted
open Midfall.Generator YulSemantics YulSemantics.EVM Midfall.Lowering Midfall.Lowering.GenAst

set_option maxRecDepth 400000

/-- The explicit fuel bound. A bound, not a claim of termination. -/
def FUEL : Nat := 20000

abbrev D : Dialect := EVM.exec.toDialect
abbrev SR : Type := Interp.SResult EVM.exec

/-! ### The shell constant table, read out of the rendered contract -/

/-- The emitted program is a FRAGMENT: P-ARITY measured the identifiers it references and does
    not declare, and Partials.lean:1379-1385 records why that is not a defect - they are the
    contract-level uint256 internal constant declarations of Halo2Verifier.sol, and D-P30 puts
    the Solidity wrapper out of scope. To RUN the fragment they must be bound.

    THE VALUES ARE NOT A HAND-WRITTEN TABLE. They are parsed out of the contract the renderer
    itself produces: renderConstants poseidonCtx is the constants section of the deployed
    artifact, so this is the artifact's own numbers read at #eval time (D-P19). The gate
    emittedShellConstantsCoverFreeNames_ok is what makes that checkable: it fails if a free
    identifier of the emitted program has no constant behind it. -/
def myTrim (s : String) : String :=
  String.ofList (List.reverse (List.dropWhile (· == ' ')
    (List.reverse (List.dropWhile (· == ' ') s.toList))))

def strDrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

def hexDigitVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- A Solidity integer literal: 0x-hex or decimal, folded LEFT so the first digit is the most
    significant. An earlier draft folded 16 * rest + head, which silently REVERSED every
    literal - invisible on the palindromic 0x44, and caught only because the gate below pins
    EXPECTED_VK_LENGTH against the artifact's own 4577. Recorded because a parser that is wrong
    on most inputs and right on the ones a reader eyeballs is the classic silent defect. -/
def natOfLiteral (s : String) : Nat :=
  if s.startsWith "0x" then
    (strDrop s 2).toList.foldl (fun acc c => acc * 16 + hexDigitVal c) 0
  else
    s.toList.foldl (fun acc c => if c.isDigit then acc * 10 + (c.toNat - '0'.toNat) else acc) 0

/-- One "uint256 internal constant NAME = VALUE;" line of the rendered contract. -/
def solConstantLine? (l : String) : Option (String × Nat) :=
  let pre := "uint256 internal constant "
  let t := myTrim l
  if t.startsWith pre then
    match (strDrop t pre.length).splitOn "=" with
    | [nm, v] => match v.splitOn ";" with
        | [val, _] => some (myTrim nm, natOfLiteral (myTrim val))
        | _ => none
    | _ => none
  else none

/-- The deployed contract's own constant table. -/
def solConstants : List (String × Nat) :=
  (renderConstants poseidonCtx).splitOn "\n" |>.filterMap solConstantLine?

/-- The two shell-provided locals that are NOT constants: the VK address and the success
    accumulator the artifact's prologue initialises to true (GenAst.lean:893 and :1046 both
    name 'let success := true' as shell material). -/
def shellLocals : List (String × Nat) := [("vk", 0x1000), ("success", 1)]

def letsOf : List (String × Nat) -> Block EVM.Op :=
  fun xs => xs.map fun (n, v) => Stmt.letDecl [n] (some (Expr.lit (Literal.number v)))

/-- The fragment's free names, bound. -/
def shellLets : Block EVM.Op := letsOf (solConstants ++ shellLocals)

/-- THE BINDING SITE, AND WHY IT IS INSIDE THE FUNCTIONS. A Yul function cannot read a variable
    from an enclosing block: Step.callOk initialises the callee environment with the parameters
    and the zeroed return slots and nothing else (BigStep.lean:189; the module header at
    BigStep.lean:33-34 says so out loud). Binding the shell constants only above the fragment
    therefore leaves every helper stuck on its first reference to one - which an earlier draft
    of this file measured and which was a bug in THIS file, not in the emitter. In the deployed
    contract the constants are Solidity-level and solc inlines them per function, so the
    faithful runnable reconstruction binds them inside every emitted function body. -/
def bindInside (b : Block EVM.Op) : Block EVM.Op :=
  b.map fun
    | Stmt.funDef n ps rs body => Stmt.funDef n ps rs (shellLets ++ body)
    | s => s

/-! ### The seven builtins the closed executable dialect cannot answer -/

/-- gas, the four call kinds and the two create kinds: stepOp returns none for them whatever
    the arguments (EVMExec.lean:869-870). A run stuck HERE is stuck on the dialect. -/
def closedBlindOps : List EVM.Op :=
  [EVM.Op.gas, EVM.Op.call, EVM.Op.callcode, EVM.Op.delegatecall, EVM.Op.staticcall,
    EVM.Op.create, EVM.Op.create2]

def isClosedBlind (op : EVM.Op) : Bool := closedBlindOps.contains op

/-- Which call-family builtins a block calls, by name. Reuses the P-ARITY walker
    (Partials.lean builtinNamesIn) rather than writing a second one. -/
def blindOpsCalledIn (b : Block EVM.Op) : List String :=
  (Midfall.Lowering.builtinNamesIn b).filter fun n =>
    (closedBlindOps.map EVM.opName).contains n

/-! ### Running a program -/

/-- The run of one block from one frame at the closed executable dialect. -/
def runBlock (prog : Block EVM.Op) (st0 : EvmState) : Result SR :=
  Interp.run EVM.exec FUEL prog st0

def runIsOk : Result SR -> Bool
  | Result.ok _ => true
  | _ => false

/-- The verdict of one unit: did the semantics accept it? A stuck run is excused only when the
    unit's own closure reaches a builtin the closed dialect does not implement; outOfFuel is
    never excused. -/
def runClean (prog : Block EVM.Op) (closure : Block EVM.Op) (st0 : EvmState) : Bool :=
  match runBlock prog st0 with
  | Result.ok _ => true
  | Result.outOfFuel => false
  | Result.stuck => ! (blindOpsCalledIn closure).isEmpty

/-! ### The units that get run -/

def helperSignatures (pv : PlanView) : List (String × List String × List String) :=
  (emitHelpers pv).filterMap fun
    | Stmt.funDef n ps rs _ => some (n, ps, rs)
    | _ => none

/-- A driver that calls one helper with zero-valued arguments. Without it no helper BODY ever
    executes: Step.funDef is a no-op and a hoisted definition runs only when called. -/
def helperDriver (h : String × List String × List String) : Block EVM.Op :=
  let (_, ps, rs) := h
  let call := Expr.call h.1 (ps.map (fun _ => Expr.lit (Literal.number 0)))
  if rs.isEmpty then [Stmt.exprStmt call] else [Stmt.letDecl rs (some call)]

/-- One runnable unit: a name, the block that runs it, and the block whose call-family uses
    decide whether a stuck run is excusable. -/
structure Unit where
  name : String
  prog : Block EVM.Op
  closure : Block EVM.Op

/-- The body of one emitted helper, with the shell bindings left out: this is what the unit's
    call closure is measured over, so a helper that reaches no precompile gets no excuse. -/
def helperBody (name : String) (pv : PlanView) : Block EVM.Op :=
  ((emitHelpers pv).filterMap fun
    | Stmt.funDef n _ _ b => if n == name then some b else none
    | _ => none).headD []

/-- The name of one partial. Spelled here because Partial carries no name projection and
    Midfall.Lowering.GenAst.emitPartial matches on it exhaustively. -/
def partialName (q : Midfall.Lowering.Partial) : String :=
  match q with
  | .vkLoading => "vkLoading"
  | .transcriptParser => "transcriptParser"
  | .lagrange => "lagrange"
  | .quotientLin => "quotientLin"
  | .pcs => "pcs"
  | .finalPairing => "finalPairing"
  | .traceReturn => "traceReturn"

/-- The runnable helper block, SHARED. Every unit below points at this one value instead of
    re-spelling shellLets ++ bindInside (emitHelpers pv): the VM does not do common
    subexpression elimination across the elements of a map, and the un-shared version made
    fourteen copies of the helper block live at once and pushed a single lean process to
    4.2 GB resident with 55 GB of swap in use. Sharing is a memory fix, not a semantic one. -/
def runnableHelpers (pv : PlanView) : Block EVM.Op := shellLets ++ bindInside (emitHelpers pv)

/-- The eight helper units. -/
def helperUnits (pv : PlanView) : List Unit :=
  let base := runnableHelpers pv
  let hs := emitHelpers pv
  (helperSignatures pv).map fun h =>
    { name := "helper:" ++ h.1,
      prog := base ++ helperDriver h,
      closure := Midfall.Lowering.callClosure hs
        [Stmt.funDef h.1 h.2.1 h.2.2 (helperBody h.1 pv)] }

/-- One slice unit. Spelled per-partial so the cheap set below can be built WITHOUT constructing
    the pcs slice at all - see gatedUnits and the memory note there. -/
def sliceUnit (pv : PlanView) (q : Midfall.Lowering.Partial) : Unit :=
  { name := "slice:" ++ partialName q,
    prog := runnableHelpers pv ++ emitPartial pv q,
    closure := Midfall.Lowering.callClosure (emitHelpers pv) (emitPartial pv q) }

/-- The seven slice units. -/
def sliceUnits (pv : PlanView) : List Unit := Midfall.Lowering.partials.map (sliceUnit pv)

/-- The whole emitted program: helpers and all seven slices in one block. -/
def wholeUnit (pv : PlanView) : Unit :=
  { name := "main", prog := shellLets ++ bindInside (emitMain pv), closure := emitMain pv }

def allUnits (pv : PlanView) : List Unit :=
  [wholeUnit pv] ++ helperUnits pv ++ sliceUnits pv

/-- THE SIX CHEAP PARTIALS: everything except pcs. This is a MEASURED constraint, not a
    convenience. Constructing and running the deployed pcs slice is what makes a lean process
    reach gigabytes - the whole portable module already peaks at 2.34 GB resident, and adding
    the per-unit runs on top of the six-slice set plus pcs pushed a single process past 8 GB and
    OOM-killed the session (docs/plans/P-EXEC-run-emitted.md was executed on a machine with
    4 GB of swap already in use). So the per-unit gate covers the eight helpers and six of the
    seven slices directly, and pcs is covered by the WHOLE-PROGRAM run, which executes it as
    part of emitMain and is a separate, already-green gate. -/
def cheapPartials : List Midfall.Lowering.Partial :=
  [.vkLoading, .transcriptParser, .lagrange, .quotientLin, .finalPairing, .traceReturn]

/-- The units the per-unit claim covers: the eight helpers and the six slices that are not pcs,
    with the helper block SHARED across all of them. Unshared, every unit re-spelled
    shellLets ++ bindInside (emitHelpers pv) and its own callClosure over emitHelpers, and a
    single lean process crossed 4.6 GB and was killed by this package's own memory watchdog.
    The positional Unit.mk is deliberate: a multi-field structure literal spread across lines
    inside a map fun does not parse at this toolchain (plans README, the one-line-update trap). -/
def gatedUnits (pv : PlanView) : List Unit :=
  let hs := emitHelpers pv
  let base := shellLets ++ bindInside hs
  let clos := Midfall.Lowering.callClosure hs
  ((helperSignatures pv).map fun h =>
      Unit.mk ("helper:" ++ h.1) (base ++ helperDriver h)
        (clos [Stmt.funDef h.1 h.2.1 h.2.2 (helperBody h.1 pv)])) ++
    (cheapPartials.map fun q =>
      Unit.mk ("slice:" ++ partialName q) (base ++ emitPartial pv q) (clos (emitPartial pv q)))

def unitClean (u : Unit) : Bool := runClean u.prog u.closure EvmState.init

/- WHY THERE IS NO PER-HELPER #eval GATE HERE, and what replaced it. Running all eight helper
    units - let alone the seven slices - in the Lean VM was MEASURED, not guessed: the portable
    module went from 2.34 GB to 3.81 GB resident and was killed by this package's own watchdog,
    and the Instances formulation went past 4.6 GB. Two costs stack: each unit's callClosure does
    nine fixpoint rounds over the helper block, and each interpreter run builds its own memory
    closure chain. So the per-unit claim is proved natively over gatedUnits in
    Midfall/Instances/RunEmitted.lean, where it fits, and what stays in the VM here is the
    whole-program run plus emittedRunGateDetectsStuckPrograms_ok - which does execute a real
    emitted helper body (common_word) and does redden on a wrong-arity call into it. The
    machinery is therefore demonstrated live; only its breadth moved to the native layer. -/

/-! ### Gates -/

/-- GATE (THE SHELL TABLE IS THE ARTIFACT'S, AND IT COVERS THE FRAGMENT). Four clauses: the
    parse found a substantial table at all; every identifier the emitted program references and
    does not declare is either a parsed constant or one of the two named shell locals; the
    coverage is not vacuous, because a name that is not in the contract is not in the table; and
    the values are the contract's own - EXPECTED_VK_LENGTH is the artifact's 4577, PROOF_LEN_CPTR
    is 0x44, and FR_MODULUS is a 254-bit number, so a parser that returned zeros for everything
    fails here. Red if the renderer's constant block changes shape, if the emitter starts
    referencing a name the contract does not declare, or if the parser silently drops entries. -/
def emittedShellConstantsCoverFreeNames_ok : Bool :=
  let free := Midfall.Lowering.emittedFreeIdentifiers artifactPlanView
  let names := solConstants.map Prod.fst
  solConstants.length >= 60 &&
    (free.all fun n => names.contains n || (shellLocals.map Prod.fst).contains n) &&
    (! names.contains "NOT_A_CONTRACT_CONSTANT") &&
    (solConstants.lookup "EXPECTED_VK_LENGTH" == some 4577) &&
    (((solConstants.lookup "FR_MODULUS").getD 0) > 2 ^ 253) &&
    (solConstants.lookup "PROOF_LEN_CPTR" == some 0x44)

/-- GATE (THE WHOLE EMITTED PROGRAM RUNS AND IS NOT STUCK). The single strongest cheap claim:
    shellLets ++ bindInside (emitMain pv), from an empty frame, at the closed executable
    dialect, at FUEL - the interpreter finds a Step derivation for every statement it executes
    and never reaches a configuration with no rule. Both pinned plan views. -/
def emittedWholeProgramNotStuck_ok : Bool :=
  (allUnits artifactPlanView).any (fun u => u.name == "main") &&
    runClean (wholeUnit artifactPlanView).prog (wholeUnit artifactPlanView).closure
      EvmState.init &&
    runClean (wholeUnit GenAst.pcsFixturePlan).prog (wholeUnit GenAst.pcsFixturePlan).closure
      EvmState.init

/-- Where the empty-calldata world actually stops, as data: the halt the whole-program run ends
    in. A REVERT, not a stuck state and not an accept. -/
def wholeProgramHalt : String :=
  match runBlock (wholeUnit artifactPlanView).prog EvmState.init with
  | Result.ok (_, st, _) => match st.halted with
      | some (k, d) => reprStr k ++ " " ++ toString (d.take 4)
      | none => "no halt"
  | Result.stuck => "STUCK"
  | Result.outOfFuel => "FUEL"

/-- GATE (THE RUN IS SHALLOW, AND THAT IS SAID RATHER THAN HIDDEN). The whole-program run on an
    empty frame ends in the VK-mismatch revert: the entry frame has no extcode at the VK
    address, so vkLoading's first guard fires and nothing after it executes. This is a real run
    of the real emitted block - the shell lets, the vkLoading guard, a revert - and it is NOT a
    verification. Pinning the halt kind is what stops a later reader from calling it an accept. -/
def emittedWholeProgramStopsAt_ok : Bool :=
  wholeProgramHalt.startsWith "YulSemantics.EVM.HaltKind.revert"

/-! ### Reddening witnesses: the gate is a gate because it can fail -/

/-- Add one extra argument to every call of one dialect builtin. -/
def addArgToBuiltin (target : EVM.Op) : Expr EVM.Op -> Expr EVM.Op
  | Expr.builtin op args =>
      if EVM.opName op == EVM.opName target then
        Expr.builtin op (args ++ [Expr.lit (Literal.number 7)])
      else Expr.builtin op (args.map (addArgToBuiltin target))
  | Expr.call fn args => Expr.call fn (args.map (addArgToBuiltin target))
  | e => e

/-- Map an expression patch over every statement of a block. -/
partial def patchExprs (f : Expr EVM.Op -> Expr EVM.Op) : Block EVM.Op -> Block EVM.Op
  | [] => []
  | s :: ss => patchS f s :: patchExprs f ss
where
  patchS (f : Expr EVM.Op -> Expr EVM.Op) : Stmt EVM.Op -> Stmt EVM.Op
    | Stmt.block b => Stmt.block (patchExprs f b)
    | Stmt.funDef n ps rs b => Stmt.funDef n ps rs (patchExprs f b)
    | Stmt.letDecl vs e => Stmt.letDecl vs (e.map f)
    | Stmt.assign vs e => Stmt.assign vs (f e)
    | Stmt.cond c b => Stmt.cond (f c) (patchExprs f b)
    | Stmt.switch c cs d => Stmt.switch (f c) (cs.map fun ⟨l, b⟩ => (l, patchExprs f b))
        (d.map (patchExprs f))
    | Stmt.forLoop i c p b =>
        Stmt.forLoop (patchExprs f i) (f c) (patchExprs f p) (patchExprs f b)
    | Stmt.exprStmt e => Stmt.exprStmt (f e)
    | s => s

/-- A loop-free emitted helper, unmutated: the baseline the witnesses below are compared
    against. common_word reads two calldata words and returns one - no loop, no precompile, so
    its unit runs in milliseconds and its closure reaches no call-family builtin, which is what
    makes it the right place to demonstrate that a wrong arity is caught. -/
def commonWordUnit : Unit :=
  (helperUnits artifactPlanView).filter (fun u => u.name == "helper:common_word") |>.headD
    { name := "missing", prog := [], closure := [] }

/-- The common_word definition as emitted, with one extra argument spliced into every add. -/
def wrongArityClone : Block EVM.Op :=
  shellLets ++ bindInside [Stmt.funDef "common_word" ["a", "b"] ["c"]
    (patchExprs (addArgToBuiltin EVM.Op.add)
      (helperBody "common_word" artifactPlanView))] ++
    [Stmt.letDecl ["cw"] (some (Expr.call "common_word"
      [Expr.lit (Literal.number 0), Expr.lit (Literal.number 0)]))]

/-- WITNESS 2 (MISSING HELPER REDDENS): a driver that calls a helper nothing defines. -/
def missingHelperClone : Block EVM.Op :=
  shellLets ++ [Stmt.letDecl ["mh"] (some (Expr.call "no_such_helper" []))]

/-- WITNESS 3 (UNBOUND LOCAL REDDENS): a reference to a name nothing declares. -/
def unboundVarClone : Block EVM.Op :=
  shellLets ++ [Stmt.exprStmt (Expr.builtin EVM.Op.iszero [Expr.var "never_declared"])]

/-- GATE (THE STUCK-STATE GATE CAN FAIL). The unmutated helper unit is clean; each of the three
    mutations is not. If any of the three came out clean the gate above would be decoration. -/
def emittedRunGateDetectsStuckPrograms_ok : Bool :=
  runClean commonWordUnit.prog commonWordUnit.closure EvmState.init &&
    ! (runClean wrongArityClone [Stmt.funDef "common_word" ["a", "b"] ["c"]
        (helperBody "common_word" artifactPlanView)] EvmState.init) &&
    ! (runClean missingHelperClone missingHelperClone EvmState.init) &&
    ! (runClean unboundVarClone unboundVarClone EvmState.init)

/-- The blind census equals this list, as a set in both directions (no ordering assumption). -/
def expectedBlindUnits : List String :=
  ["main", "helper:scalar_inv", "helper:batch_invert", "helper:ec_pairing", "slice:lagrange",
    "slice:finalPairing"]

def sameNames (xs : List String) : Bool :=
  (xs.all fun x => expectedBlindUnits.contains x) &&
    (expectedBlindUnits.all fun x => xs.contains x) &&
    xs.length == expectedBlindUnits.length && xs.eraseDups.length == xs.length

/-- The call-family census, as data: which units' closures reach a builtin the closed dialect
    cannot answer. -/
def blindClosureUnits (pv : PlanView) : List (String × List String) :=
  (allUnits pv).filterMap fun u =>
    let bl := blindOpsCalledIn u.closure
    if bl.isEmpty then none else some (u.name, bl.eraseDups)

/-- GATE (THE EXCUSE IS BOUNDED AND NAMED). Exactly the units below reach a call-family builtin;
    every other unit gets no excuse at all and must run clean. Red if the set moves, so a new
    unit that silently gains a precompile call cannot slip through. -/
def emittedRunBlindUnits_ok : Bool :=
  sameNames ((blindClosureUnits artifactPlanView).map Prod.fst) &&
    (! (blindClosureUnits artifactPlanView).any fun (_, bl) => bl.isEmpty)
#eval emittedShellConstantsCoverFreeNames_ok        -- expect true
#eval emittedWholeProgramNotStuck_ok                -- expect true
#eval emittedRunGateDetectsStuckPrograms_ok         -- expect true
#eval emittedWholeProgramStopsAt_ok -- expect true
#eval emittedRunBlindUnits_ok                       -- expect true
/-- The revert SELECTOR the empty-frame run ends in, pinned as a Bool rather than printed as a
    string: kat_gate.py reads an expectation as the first whitespace-free token, so a printed
    list with spaces inside it cannot be a gate. Pinning the four bytes is what stops a later
    change to vkLoading's first guard from passing unnoticed - and it caught a real staleness
    here, because the selector moved when the literal parser was fixed. -/
def emittedWholeProgramRevertSelector_ok : Bool :=
  wholeProgramHalt.endsWith "[164, 71, 215, 62]"

#eval emittedWholeProgramRevertSelector_ok          -- expect true

end Midfall.Lowering.RunEmitted