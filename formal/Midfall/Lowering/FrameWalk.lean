/-
Midfall.Lowering.FrameWalk

P-FRAME (docs/plans/P-FRAME.md) STEP 1: MEASURE whether the emitted Yul program is actually
insensitive to the frame difference that makes 'ir_refines' false in general.

THE DIFFERENCE BEING MEASURED. 'ShellModel.prologue' is 'mstore(0x40, memoryguard(128))'. Running
it leaves the arm in a frame whose 'activeWords' is 3 and whose memory bytes [64, 96) spell 128,
while 'initState' and 'callState' have 'activeWords' 0 and those bytes zero. R-66 proved three
theorems about that ('arm_frame_active_words_nonzero', 'no_mem₀_reaches_the_arm_frame',
'prologue_write_is_observable') and concluded 'ObsEquiv (wrap S ...) (RunShell S ...)' is FALSE for
a GENERAL program. What R-66 did not do, and what this file does, is ask which channels can carry
that difference for a SPECIFIC program.

THE CHANNELS, and why they are exactly two. 'ObsView' (Midfall/Yul/Bridge.lean:373) carries the
outcome, the halt payload and the eleven world components. It carries NEITHER memory NOR
'activeWords'. So the frame difference reaches an observation only through

  (1) 'msize', the only reader of 'activeWords' in the vendored dialect ('EVMExec.lean:375'
      defines 'memorySize', ':765' is its only reader), or
  (2) a memory READ whose byte range overlaps [64, 96) - 'mload', the source of 'mcopy', the input
      region of 'keccak256', of the log family, of 'ret', of 'revert' and of the call family -
      because those are the only bytes the two frames disagree about.

A WRITE into the window is not a channel: 'mstore' is blind (EVMOp.lean:106, 'reads := false'), so
a write makes the frames agree from that point on. Gas is not a channel either: 'ir_refines' fixes
the oracle at 'ExternalGas.ofFun (fun _ => g₀)', a constant of the state.

WHAT THIS FILE COMPUTES. 'frameSites' walks a block and returns one 'Site' per memory read: the
operation name, the resolved base address, the resolved size. Resolution is constant propagation
through the contract-level literal bindings ('RunEmitted.solConstants' - the artifact's OWN
numbers, not a second hand-written table, D-P19) and through 'let' and assignment right-hand
sides, and it is INTERPROCEDURAL: a call inlines the callee with its parameters bound to the
caller's argument values, which is the only way 'mload(p)' inside 'scalar_inv' becomes resolvable
at all. A read whose address cannot be resolved is reported UNRESOLVED, and unresolved counts as
DIRTY - the conservative direction, the same rule 'Partials.staticcallAddr' applies to an
unreadable precompile target. 'mentionsMsize' is a separate whole-block walk that enters EVERY
function body whether it is called or not, so the "no msize anywhere" half is not reachability
scoped.

THE SCOPE OF THE READ WALK, STATED RATHER THAN HIDDEN. 'frameSites' is reachability-scoped: a read
inside a helper that no call site reaches is not walked, because at its definition site its
parameters are unbound and every parameter-addressed read would report as unresolved. At the
fixture plan exactly one emitted helper is uncalled; 'Instances/FrameWalkWitness.lean' names that
set as data instead of pretending it is empty. The 'msize' claim does not have this limit.

THE NEGATIVE CONTROLS ARE THE POINT. A walk that accepts everything is decoration, and this project
has measured 28 gate blind spots. The plants landed as theorems below are: a literal 'mload(64)'; a
'msize()'; a read through a LET-BOUND name whose value is 64, so constant propagation must bite and
not merely literal matching; a read through a CALL PARAMETER bound to 64 at the call site, so the
interprocedural resolution must bite; a range read that overlaps the window without starting at it;
a plant inside a function body; inside a for-loop body; inside a switch DEFAULT; inside a switch
CASE arm; and a plant whose address is unresolvable. Each is rejected. And the walk is shown NOT to
be vacuously rejecting: it accepts a clean block, it accepts a read ending exactly at the window
edge and one starting exactly above it, and it rejects the same clean block with the fuel starved.
-/
import Midfall.Lowering.GenAstDispatch
import Midfall.Lowering.RunEmitted
import YulSemantics.Syntax

namespace Midfall.Lowering.FrameWalk
open YulSemantics YulSemantics.EVM

/-! ### The window the two frames disagree about -/

/-- The free-memory-pointer byte the dispatcher prologue writes. The same number as
    'ShellModel.fmpAddr', restated here because this file sits below the Yul layer and must not
    reach up into it. -/
def frameLo : Nat := 0x40

/-- One past the last byte the prologue writes: 'memoryguard(128)' occupies [64, 96). -/
def frameHi : Nat := 0x40 + 32

/-- Does [base, base + size) meet the disagreement window [64, 96)? -/
def overlapsWindow (base size : Nat) : Bool :=
  !(base + size <= frameLo || base >= frameHi)

/-! ### The sites the walk reports -/

/-- One memory read the walk found. 'base' and 'size' are 'none' when constant propagation could not
    read them, which is DIRTY and never a pass. 'msize' carries no address. -/
structure Site where
  op : String
  base : Option Nat
  size : Option Nat
  deriving Inhabited, DecidableEq, Repr

/-- Can this site see the frame difference?

    * 'msize' always can - it is the only reader of 'activeWords'.
    * A read whose BASE is at or above 'frameHi' never can, whatever its size is, because every
      memory reader in the dialect reads the half-open range [base, base + size) and that range
      starts past the window. This is what makes the ten 'keccak256(TRANSCRIPT_MPTR,
      sub(buf_len, TRANSCRIPT_MPTR))' sites of the emitted transcript squeeze clean: the base is
      the literal 4096 and the length is a live cursor the walk cannot resolve, and the base alone
      settles it.
    * A read whose BASE cannot be resolved at all always can - unresolved is the conservative side,
      and 'plantUnresolvableRejects' is the control that shows it is not a free pass.
    * Otherwise the resolved range can exactly when it overlaps [64, 96). -/
def Site.frameVisible : Site -> Bool
  | ⟨op, base, size⟩ =>
      op == "msize" || op == "FUEL-EXHAUSTED" ||
        match base with
        | none => true
        | some b =>
            if frameHi <= b then false
            else match size with
              | some n => overlapsWindow b n
              | none => true

/-- The sites that can see the frame difference. -/
def frameVisibleSites : List Site -> List Site
  | ss => ss.filter fun s => s.frameVisible

/-! ### Constant resolution -/

/-- A name in scope, with the byte value it resolves to. 'none' means the walk cannot read it, which
    is reported as dirty rather than silently treated as a number. -/
abbrev Consts := List (String × Option Nat)

/-- THE PINNED CONSTANT TABLE, and why it is a literal here.

    The walk has to be discharged by 'decide', i.e. by the KERNEL, because that is the only discharge
    this project trusts for a headline fact: a KAT trusts the compiler, a 'decide' does not. And the
    kernel CANNOT reduce 'String.splitOn' or 'String.startsWith' - they are '@[extern]' C++ - so
    feeding the walk 'RunEmitted.solConstants', which is exactly those two functions applied to the
    rendered contract, makes every verdict about the real program undecidable in the kernel.
    Measured, not assumed: 'shellConsts.length = 92' FAILS 'decide' when 'shellConsts' is the parsed
    table, while the same walk over a literal table decides in about a second.

    THE FIX IS A PIN, NOT A SUBSTITUTION. 'pinnedConstants' is a transcription of the same table and
    'shellConsts_matches_artifact_ok' is the gate saying the transcription IS the artifact's own
    numbers, evaluated by 'kat_gate.py' at every gate run, so a regenerated or edited contract that
    moves a constant reddens the gate instead of silently desynchronising the two tables. That is the
    R-58 copy class handled the only way it can be handled here: a copy WITH a named pin between the
    two sides.
-/
def pinnedConstants : List (String × Nat) := [
  ("EXPECTED_VK_PAYLOAD_LENGTH", 4576),
  ("EXPECTED_VK_LENGTH", 4577),
  ("EXPECTED_VK_CODEHASH_WORD", 15933609736973938366157763540951553264596488184743928812768469146773639656731),
  ("PROOF_LEN_CPTR", 68),
  ("PROOF_CPTR", 100),
  ("NUM_INSTANCE_CPTR", 4420),
  ("INSTANCE_CPTR", 4452),
  ("TRANSCRIPT_MPTR", 4096),
  ("RETURN_MPTR", 4096),
  ("VK_MPTR", 10496),
  ("VK_DIGEST_MPTR", 10496),
  ("NUM_INSTANCES_MPTR", 10528),
  ("K_MPTR", 10560),
  ("N_INV_MPTR", 10592),
  ("OMEGA_MPTR", 10624),
  ("OMEGA_INV_MPTR", 10656),
  ("OMEGA_INV_TO_L_MPTR", 10688),
  ("HAS_ACCUMULATOR_MPTR", 10720),
  ("ACC_OFFSET_MPTR", 10752),
  ("NUM_ACC_LIMBS_MPTR", 10784),
  ("NUM_ACC_LIMB_BITS_MPTR", 10816),
  ("G1_BASE_MPTR", 10848),
  ("G2_BASE_MPTR", 10976),
  ("NEG_S_G2_BASE_MPTR", 11232),
  ("CHALLENGE_MPTR", 15072),
  ("THETA_MPTR", 15072),
  ("BETA_MPTR", 15104),
  ("GAMMA_MPTR", 15136),
  ("TRASH_CHALLENGE_MPTR", 15168),
  ("Y_MPTR", 15200),
  ("X_MPTR", 15232),
  ("X1_MPTR", 15264),
  ("X2_MPTR", 15296),
  ("X3_MPTR", 15328),
  ("X4_MPTR", 15360),
  ("F_COM_MPTR", 15392),
  ("PI_MPTR", 15520),
  ("ACC_LHS_MPTR", 15648),
  ("ACC_RHS_MPTR", 15776),
  ("X_N_MPTR", 15904),
  ("X_N_MINUS_1_INV_MPTR", 15936),
  ("L_LAST_MPTR", 15968),
  ("L_BLIND_MPTR", 16000),
  ("L_0_MPTR", 16032),
  ("INSTANCE_EVAL_MPTR", 16064),
  ("QUOTIENT_EVAL_MPTR", 16096),
  ("QUOTIENT_MPTR", 16128),
  ("F_EVAL_MPTR", 16288),
  ("V_MPTR", 16320),
  ("FINAL_COM_MPTR", 16352),
  ("PAIRING_LHS_MPTR", 16480),
  ("PAIRING_RHS_MPTR", 16608),
  ("ROT_POINTS_MPTR", 16736),
  ("X1_POWERS_MPTR", 17632),
  ("Q_COM_MPTR", 19712),
  ("Q_EVAL_SET_MPTR", 19712),
  ("Q_EVAL_CPTR_MPTR", 21504),
  ("G1_IDENTITY_MPTR", 21760),
  ("REVERSED_EVALS_MPTR", 22112),
  ("SELECTOR_ACC_MPTR", 26080),
  ("QUOTIENT_RETURN_MPTR", 4096),
  ("BATCH_INV_SCRATCH_MPTR", 26080),
  ("LAGRANGE_DENOMS_MPTR", 26560),
  ("TRACE_U256_MPTR", 33728),
  ("ADVICE_COMMS_MPTR_BASE", 23648),
  ("LOOKUP_M_COMMS_MPTR_BASE", 24672),
  ("PERM_Z_COMMS_MPTR_BASE", 24800),
  ("LOOKUP_HELPER_COMMS_MPTR_BASE", 25184),
  ("LOOKUP_Z_COMMS_MPTR_BASE", 25312),
  ("TRASHCAN_COMMS_MPTR_BASE", 25440),
  ("QUOTIENT_LIMB_COMMS_MPTR_BASE", 25568),
  ("G1ADD_GAS", 375),
  ("G1MSM_GAS_1PAIR", 12000),
  ("PAIRING_GAS_2PAIR", 102900),
  ("MODEXP_GAS", 4080),
  ("G1MSM_GAS_SMOKE", 337836),
  ("ERR_BAD_CALLDATA_SHAPE", 463070076),
  ("ERR_VK_MISMATCH", 2756171582),
  ("ERR_NON_CANONICAL_SCALAR", 2001928258),
  ("ERR_BAD_POINT_ENCODING", 4068017644),
  ("ERR_PRECOMPILE_FAILED", 2229802642),
  ("ERR_PROOF_REJECTED", 3283146957),
  ("ERR_QUOTIENT_PROGRAM_INVALID", 1019747209),
  ("ERR_MEMORY_LAYOUT_VIOLATED", 3381169443),
  ("FR_MODULUS", 52435875175126190479447740508185965837690552500527637822603658699938581184513),
  ("BLS_P_HI", 34565483545414906068789196026815425751),
  ("BLS_P_MINUS_ONE_LO", 45442060874369865957053122457065728162598490762543039060009208264153100167850),
  ("BLS_P_MINUS_ONE_PACKED_0", 25645630028331783532722944590531249665523018521732413678114874305194),
  ("BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG", 25645630028331783532722944590531249665523018521732485735708912233130),
  ("BLS_P_MINUS_ONE_PACKED_1", 148457621397983152316361523253305392630546779012),
  ("vk", 4096),
  ("success", 1)
]

/-- The walk's constant environment: the pinned table, every entry resolved. -/
def shellConsts : Consts := pinnedConstants.map fun n => (n.1, some n.2)

/-- **THE PIN.** The transcription above is the rendered contract's own constant section, in the same
    order, with the same values, plus the two shell locals. 'true' by computation over the artifact,
    and a gate at every 'checks.sh' run. -/
def shellConsts_matches_artifact_ok : Bool :=
  pinnedConstants == (Midfall.Lowering.RunEmitted.solConstants ++
    Midfall.Lowering.RunEmitted.shellLocals)

#eval shellConsts_matches_artifact_ok -- expect true

/-- Resolve a byte address or a byte length: a number, an in-scope name, or 'add', 'sub' or 'mul' of
    resolved values. Anything else is 'none'. -/
def resolve : Consts -> Expr Op -> Option Nat
  | env, Expr.lit (Literal.number n) => some n
  | env, Expr.var x => match env.lookup x with | some v => v | none => none
  | env, Expr.builtin Op.add [a, b] =>
      match resolve env a, resolve env b with
      | some x, some y => some (x + y)
      | _, _ => none
  | env, Expr.builtin Op.sub [a, b] =>
      match resolve env a, resolve env b with
      | some x, some y => some (x - y)
      | _, _ => none
  | env, Expr.builtin Op.mul [a, b] =>
      match resolve env a, resolve env b with
      | some x, some y => some (x * y)
      | _, _ => none
  | _, _ => none

/-- Which argument positions of a memory-reading builtin carry the base and the size, as
    (base index, CONSTANT size, size index) where a zero constant means 'take the size from the
    third component'. 'mload' reads a whole word, so its size is the literal 32 and NOT a second
    argument: a walk that read 'mload's size from 'args[1]' would score 'mload(64)' as a zero-byte
    read and call the program clean. That misreading is the blind spot this line exists to close,
    and 'plantLiteralMloadRejects' is the control that shows it is closed. -/
def readShape : Op -> Option (Nat × Nat × Nat)
  | Op.mload => some (0, 32, 0)
  | Op.mcopy => some (1, 0, 2)
  | Op.keccak256 | Op.log0 | Op.log1 | Op.log2 | Op.log3 | Op.log4
  | Op.ret | Op.revert => some (0, 0, 1)
  | Op.staticcall | Op.callcode | Op.delegatecall => some (2, 0, 3)
  | Op.call => some (3, 0, 4)
  | _ => none

/-- The term substituted for a missing argument, so a short argument list resolves to 'none' rather
    than crashing the walk. -/
def zeroLit : Expr Op := Expr.lit (Literal.number 0)

/-- One emitted function definition: name, parameters, body. -/
abbrev FnTable := List (String × List String × List (Stmt Op))

/-- The function definitions a block carries, in definition order. -/
def fnTable : List (Stmt Op) -> FnTable
  | b => b.filterMap fun
    | Stmt.funDef n ps _ body => some (n, ps, body)
    | _ => none

/-! ### The walk -/

/-- The positions the walk stands at, as ONE flat index type so the recursion is a single decreasing
    'Nat' the kernel can reduce. This is the 'Bridge.noWritersScan' pattern and the reason recorded
    there: mutual recursion compiles through 'WellFounded.fix', which the kernel cannot reduce, so no
    witness would be provable by 'decide'. The environment is threaded through the recursion rather
    than stored in the index, because a 'let' binds a name for the statements that FOLLOW it, which
    a purely local step function cannot express. -/
inductive Scan
  | e : Expr Op -> Scan
  | es : List (Expr Op) -> Scan
  | s : Stmt Op -> Scan
  | b : List (Stmt Op) -> Scan
  | cs : List (Literal × List (Stmt Op)) -> Scan

/-- The walk's answer at one position: the sites found, and the environment as it is AFTER the
    position, so a block threads its bindings forward. -/
structure Step where
  sites : List Site
  env : Consts

/-- One layer of the walk. A 'Stmt.funDef' is NOT walked at its definition site - its parameters are
    unbound there - but at every CALL SITE with the parameters bound to the caller's arguments. That
    is what makes this interprocedural rather than a literal scan, and 'plantViaParameterRejects' is
    the control that shows it bites. A 'switch' walks its condition, EVERY case arm and the default,
    over-approximating the reachable set, which is the sound direction for a no-dirty-reads claim. -/
def frameStep : FnTable -> (Consts -> Scan -> Step) -> Consts -> Scan -> Step
  | _fns, _rec, env, .e (Expr.builtin Op.msize _) =>
      { sites := [{ op := "msize", base := none, size := none }], env := env }
  | fns, rec, env, .e (Expr.builtin o args) =>
      let mine := match readShape o with
        | some (i, csize, j) =>
            let base := resolve env (args.getD i zeroLit)
            let size := if csize > 0 then some csize else resolve env (args.getD j zeroLit)
            [{ op := opName o, base := base, size := size }]
        | none => []
      let sub := rec env (.es args)
      { sites := mine ++ sub.sites, env := sub.env }
  | fns, rec, env, .e (Expr.call f args) =>
      let sub := rec env (.es args)
      match fns.find? (fun x => x.1 == f) with
      | some (_, ps, body) =>
          let env2 := (List.zip ps args).map (fun p => (p.1, resolve env p.2)) ++ env
          let inner := rec env2 (.b body)
          { sites := sub.sites ++ inner.sites, env := sub.env }
      | none => { sites := sub.sites, env := sub.env }
  | _fns, _rec, env, .e _ => { sites := [], env := env }
  | _fns, _rec, env, .es [] => { sites := [], env := env }
  | fns, rec, env, .es (e :: rest) =>
      let a := rec env (.e e)
      let b := rec a.env (.es rest)
      { sites := a.sites ++ b.sites, env := b.env }
  | _fns, rec, env, .s (Stmt.block body) => rec env (.b body)
  | _fns, rec, env, .s (Stmt.letDecl xs (some e)) =>
      let a := rec env (.e e)
      let v := resolve env e
      { a with env := a.env ++ xs.map (fun x => (x, v)) }
  | _fns, _rec, env, .s (Stmt.letDecl _ none) => { sites := [], env := env }
  | _fns, rec, env, .s (Stmt.assign xs e) =>
      let a := rec env (.e e)
      let v := resolve env e
      { a with env := a.env ++ xs.map (fun x => (x, v)) }
  | _fns, rec, env, .s (Stmt.cond c body) =>
      let a := rec env (.e c)
      let b := rec a.env (.b body)
      { sites := a.sites ++ b.sites, env := b.env }
  | _fns, rec, env, .s (Stmt.switch c cases dflt) =>
      let a := rec env (.e c)
      let b := rec a.env (.cs cases)
      match dflt with
      | some d =>
          let e2 := rec b.env (.b d)
          { sites := a.sites ++ b.sites ++ e2.sites, env := e2.env }
      | none => { sites := a.sites ++ b.sites, env := b.env }
  | _fns, rec, env, .s (Stmt.forLoop init c post body) =>
      let a := rec env (.b init)
      let b := rec a.env (.e c)
      let d := rec b.env (.b post)
      let e2 := rec d.env (.b body)
      { sites := a.sites ++ b.sites ++ d.sites ++ e2.sites, env := e2.env }
  | _fns, rec, env, .s (Stmt.exprStmt e) => rec env (.e e)
  | _fns, _rec, env, .s _ => { sites := [], env := env }
  | _fns, _rec, env, .b [] => { sites := [], env := env }
  | fns, rec, env, .b (s :: ss) =>
      let a := rec env (.s s)
      let b := rec a.env (.b ss)
      { sites := a.sites ++ b.sites, env := b.env }
  | _fns, _rec, env, .cs [] => { sites := [], env := env }
  | fns, rec, env, .cs ((_, body) :: rest) =>
      let a := rec env (.b body)
      let b := rec env (.cs rest)
      { sites := a.sites ++ b.sites, env := b.env }

/-- The walk, fuel-bounded. Exhaustion reports ITSELF as a site, so a program needing more fuel than
    it gets is DIRTY rather than clean (R-37, the same rule the writer scan follows). -/
def frameScan : Nat -> FnTable -> Consts -> Scan -> Step
  | 0, _fns, env, _sc =>
      { sites := [{ op := "FUEL-EXHAUSTED", base := none, size := none }], env := env }
  | n + 1, fns, env, sc => frameStep fns (frameScan n fns) env sc

/-- The memory-read sites of a block at an explicit constant table and fuel bound. -/
def frameSitesAt (consts : Consts) (fuel : Nat) (b : List (Stmt Op)) : List Site :=
  (frameScan fuel (fnTable b) consts (.b b)).sites

/-- The default fuel. A bound, not a claim of sufficiency: exhaustion is itself a dirty site, so a
    bound that is too small makes 'frameClean' answer false rather than falsely answer true. -/
def defaultFuel : Nat := 20000

/-- The sites of a block under the contract constant table at the default fuel. -/
def frameSites (b : List (Stmt Op)) : List Site := frameSitesAt shellConsts defaultFuel b

/-- The frame-visible sites of a block at an explicit table and fuel. -/
def frameDirtyAt (consts : Consts) (fuel : Nat) (b : List (Stmt Op)) : List Site :=
  frameVisibleSites (frameSitesAt consts fuel b)

/-- The frame-visible sites of a block. -/
def frameDirty (b : List (Stmt Op)) : List Site := frameVisibleSites (frameSites b)

/-- Is a block frame-insensitive? Every read resolves, no resolved read touches [64, 96), 'msize'
    does not appear, and the walk did not run out of fuel. -/
def frameClean (b : List (Stmt Op)) : Bool := (frameDirty b).isEmpty

/-! ### The whole-block msize walk -/

/-- The positions the 'msize' walk stands at. A SEPARATE flat index type from 'Scan', and the
    difference is the point: 'frameStep' deliberately does NOT enter a 'Stmt.funDef' at its
    definition site (its parameters are unbound there), while 'msizeStep' MUST, because the claim
    "no 'msize' occurs anywhere in the emitted AST" is not a reachability claim and must not inherit
    that scope. Exhaustion is again reported as dirty. -/
inductive MScan
  | e : Expr Op -> MScan
  | es : List (Expr Op) -> MScan
  | s : Stmt Op -> MScan
  | b : List (Stmt Op) -> MScan
  | cs : List (Literal × List (Stmt Op)) -> MScan

/-- One layer of the 'msize' walk. -/
def msizeStep : MScan -> (MScan -> Bool) -> Bool
  | .e (Expr.builtin Op.msize _), _rec => true
  | .e (Expr.builtin _ args), rec => rec (.es args)
  | .e (Expr.call _ args), rec => rec (.es args)
  | .e _, _rec => false
  | .es [], _rec => false
  | .es (e :: rest), rec => rec (.e e) || rec (.es rest)
  | .s (Stmt.block body), rec => rec (.b body)
  | .s (Stmt.funDef _ _ _ body), rec => rec (.b body)
  | .s (Stmt.letDecl _ (some e)), rec => rec (.e e)
  | .s (Stmt.letDecl _ none), _rec => false
  | .s (Stmt.assign _ e), rec => rec (.e e)
  | .s (Stmt.cond c body), rec => rec (.e c) || rec (.b body)
  | .s (Stmt.switch c cases dflt), rec =>
      rec (.e c) || rec (.cs cases) ||
        (match dflt with | some d => rec (.b d) | none => false)
  | .s (Stmt.forLoop init c post body), rec =>
      rec (.b init) || rec (.e c) || rec (.b post) || rec (.b body)
  | .s (Stmt.exprStmt e), rec => rec (.e e)
  | .s _, _rec => false
  | .b [], _rec => false
  | .b (s :: ss), rec => rec (.s s) || rec (.b ss)
  | .cs [], _rec => false
  | .cs ((_, body) :: rest), rec => rec (.b body) || rec (.cs rest)

/-- The 'msize' walk, fuel-bounded. Exhaustion answers TRUE, i.e. dirty: a walk that ran out of fuel
    has not established absence. -/
def msizeScan : Nat -> MScan -> Bool
  | 0, _sc => true
  | n + 1, sc => msizeStep sc (msizeScan n)

/-- Does 'msize' occur anywhere in a block, at an explicit fuel? -/
def mentionsMsizeAt : Nat -> List (Stmt Op) -> Bool := fun fuel b => msizeScan fuel (.b b)

/-- Does 'msize' occur ANYWHERE in a block - every function body entered, called or not? Separate
    from 'frameSites' precisely because that walk is reachability-scoped and this claim is not. -/
def mentionsMsize : List (Stmt Op) -> Bool := mentionsMsizeAt defaultFuel

/-- Is a block frame-insensitive at an explicit table and fuel? -/
def frameCleanAt (consts : Consts) (fuel : Nat) (b : List (Stmt Op)) : Bool :=
  (frameDirtyAt consts fuel b).isEmpty

/-! ### The negative controls, as theorems -/

/-- A planted literal read of the free-memory word. -/
def plantLiteral : List (Stmt Op) := yul% { sstore(0, mload(64)) }

/-- A planted 'msize'. -/
def plantMsize : List (Stmt Op) := yul% { sstore(0, msize()) }

/-- A planted read through a LET-BOUND name whose value is 64. This is the control that separates a
    constant-propagating walk from one that only pattern-matches the literal 64: the AST contains no
    'mload(64)' at all, only 'mload(fmp)'. -/
def plantViaLet : List (Stmt Op) := yul% { let fmp := 64 sstore(0, mload(fmp)) }

/-- A planted read through a CALL PARAMETER bound to 64 at the call site. This is the control that
    separates the interprocedural walk from a walk that stops at the function boundary: the read is
    'mload(p)' inside a definition, and only the call site says 'p' is 64. -/
def plantViaParameter : List (Stmt Op) := yul% { function h(p) { sstore(0, mload(p)) } h(64) }

/-- A planted range read that OVERLAPS the window without starting at it: 'keccak256(0x30, 0x40)'
    hashes bytes [48, 112), which contains [64, 96). A walk that tested only 'base == 64' would call
    this clean. -/
def plantOverlappingRange : List (Stmt Op) := yul% { sstore(0, keccak256(0x30, 0x40)) }

/-- A planted read inside a function body reached through a call. -/
def plantInsideFunction : List (Stmt Op) := yul% { function h() { sstore(0, mload(64)) } h() }

/-- A planted read inside a for-loop body - the shape a trace or batching emitter would use. -/
def plantInsideLoop : List (Stmt Op) :=
  yul% { for { let i := 0 } lt(i, 4) { i := add(i, 1) } { sstore(0, mload(64)) } }

/-- A planted read reachable only through a switch DEFAULT arm. -/
def plantInsideSwitchDefault : List (Stmt Op) :=
  yul% { switch 2 case 1 { stop() } default { sstore(0, mload(64)) } }

/-- A planted read reachable only through a switch CASE arm. -/
def plantInsideSwitchCase : List (Stmt Op) :=
  yul% { switch 2 case 1 { sstore(0, mload(64)) } default { stop() } }

/-- A planted read whose address the walk cannot resolve at all. Unresolved is dirty, never clean. -/
def plantUnresolvable : List (Stmt Op) := yul% { sstore(0, mload(NOT_A_BOUND_NAME)) }

/-- A block that reads memory well above the window: the walk must ACCEPT this, or every rejection
    above would be the walk answering false to everything. -/
def controlCleanAbove : List (Stmt Op) := yul% { let x := mload(0x1000) sstore(0, x) }

/-- A block that reads the word ending exactly at the window's lower edge: [32, 64) does not meet
    [64, 96), so this is clean, and a walk that used '<=' where it needed '<' would reject it. -/
def controlCleanEdgeBelow : List (Stmt Op) := yul% { sstore(0, mload(32)) }

/-- A block that reads starting exactly at the window's upper edge: [96, 128) is clean. -/
def controlCleanEdgeAbove : List (Stmt Op) := yul% { sstore(0, mload(96)) }

/-- **EVERY PLANT IS REJECTED.** Ten controls, each a kernel-checked 'decide', so the walk cannot be
    the constant 'true' wearing a different name. -/
theorem plantLiteralRejects : (frameSites plantLiteral).any Site.frameVisible = true := by decide
theorem plantMsizeRejects : (frameSites plantMsize).any Site.frameVisible = true := by decide
theorem plantViaLetRejects : (frameSites plantViaLet).any Site.frameVisible = true := by decide
theorem plantViaParameterRejects : (frameSites plantViaParameter).any Site.frameVisible = true := by decide
theorem plantOverlappingRangeRejects :
    (frameSites plantOverlappingRange).any Site.frameVisible = true := by decide
theorem plantInsideFunctionRejects :
    (frameSites plantInsideFunction).any Site.frameVisible = true := by decide
theorem plantInsideLoopRejects : (frameSites plantInsideLoop).any Site.frameVisible = true := by decide
theorem plantInsideSwitchDefaultRejects :
    (frameSites plantInsideSwitchDefault).any Site.frameVisible = true := by decide
theorem plantInsideSwitchCaseRejects :
    (frameSites plantInsideSwitchCase).any Site.frameVisible = true := by decide
theorem plantUnresolvableRejects :
    (frameSites plantUnresolvable).any Site.frameVisible = true := by decide

/-- **AND THE WALK IS NOT VACUOUSLY REJECTING.** The three clean controls are accepted, so the ten
    rejections above discriminate on the address and not on the mere presence of a memory read. -/
theorem controlAboveAccepted : frameClean controlCleanAbove = true := by decide
theorem controlEdgeBelowAccepted : frameClean controlCleanEdgeBelow = true := by decide
theorem controlEdgeAboveAccepted : frameClean controlCleanEdgeAbove = true := by decide

/-- **THE FUEL BOUND IS LOAD-BEARING.** Starved to one unit the walk reports exhaustion, and
    exhaustion is dirty, so a verdict of clean is a verdict that the walk actually finished. -/
theorem fuelExhaustionIsDirty :
    (frameSitesAt shellConsts 1 (plantLiteral)).any Site.frameVisible = true := by decide

/-- The 'msize' walk also rejects every plant that mentions 'msize', and it does so on the whole
    block rather than only on the reachable part. -/
theorem msizePlantsRejected :
    (mentionsMsize plantMsize && mentionsMsize (yul% { function h() { sstore(0, msize()) } }) &&
      mentionsMsize (yul% { for { let i := 0 } lt(i, 1) { i := add(i, 1) } { sstore(0, msize()) } }) &&
      ! (mentionsMsize plantLiteral) && ! (mentionsMsize controlCleanAbove)) = true := by
  decide

/-! ### Step 2, the part that is arithmetic rather than a run -/

/-- **THE HEAD GUARD CANNOT DISTINGUISH THE TWO FRAMES.** The arm's first statement is
    'if gt(mload(0x40), 0x1000) { revert(0,0) }'. The deployment frame reads 0 at that word and the
    arm frame reads 128 - 'ShellModel.arm_frame_reads_a_different_head_word' proves exactly that
    difference - and BOTH values fail 'gt · 0x1000'. So the guard takes the same branch from either
    frame, and the one window read the emitted program does have is the one that cannot matter.
    Stated at the model's own threshold rather than for an arbitrary one, because that is the fact
    the bridge needs; the general arithmetic form is '∀ V ≥ 128', and it is the same two 'decide's
    with a bound hypothesis that 'BitVec.toNat_ofNat' will not discharge without a mod-2^256 side
    condition. -/
theorem headGuard_indifferent_at_the_model_threshold :
    (((0 : BitVec 256) > BitVec.ofNat 256 0x1000) = false) ∧
      (((BitVec.ofNat 256 128 : BitVec 256) > BitVec.ofNat 256 0x1000) = false) :=
  ⟨by decide, by decide⟩

/-- The pointwise core of the frame-insensitivity argument, one read at a time. -/
theorem readBytes_congr (m₁ m₂ : Nat → UInt8) (p n : Nat)
    (h : ∀ i, i < n → m₁ (p + i) = m₂ (p + i)) :
    (List.range n).map (fun i => m₁ (p + i)) = (List.range n).map (fun i => m₂ (p + i)) :=
  List.map_eq_map_iff.mpr fun x hx => h x (List.mem_range.mp hx)

/-- **A READ THAT AVOIDS THE WINDOW CANNOT SEE THE DIFFERENCE.** Two memories that agree everywhere
    outside [64, 96) agree on every byte range that does not meet the window. This is the whole
    content of frame insensitivity at the level of ONE memory read, and it is where the syntactic
    property of this file earns its keep: 'frameClean' is exactly the statement that every read of
    the emitted program satisfies the side condition 'havoid'.

    WHAT IT DOES NOT BUY, stated because the brief asks for the honest scope. It is a per-read lemma,
    not a run lemma. Turning it into 'two runs from the two frames agree in 'ObsView'' needs an
    induction over the vendored 'Step' relation relabeling the environment and the memory together -
    the same 77-constructor cost class as the registered hole 'Bridge.Run_worldEq_of_noWriters', which
    is still an open hole in this tree. That is reported as remaining, not closed here. -/
theorem readBytes_avoids_window (m₁ m₂ : Nat → UInt8) (p n : Nat)
    (hagree : ∀ i, ¬ (frameLo ≤ i ∧ i < frameHi) → m₁ i = m₂ i)
    (havoid : p + n ≤ frameLo ∨ frameHi ≤ p) :
    YulSemantics.EVM.readBytes m₁ p n = YulSemantics.EVM.readBytes m₂ p n := by
  unfold YulSemantics.EVM.readBytes
  refine readBytes_congr m₁ m₂ p n fun i hi => ?_
  refine hagree (p + i) ?_
  intro hh
  cases havoid with
  | inl hv => omega
  | inr hv => omega

/-! ### The free identifiers of a block -/

/- The names a block BINDS: every 'let' and assignment target and every function parameter, read off
    the whole block rather than tracked through scope. Deliberately generous to the program - a name
    bound anywhere at all counts as bound - because the claim this feeds is 'this name is bound
    NOWHERE', and a conservative binder set is what makes that claim mean something. The shape is the
    'Partials.bundleWalk' shape: a 'mutual' block with one 'termination_by' per definition, which is
    what the kernel needs to reduce it. -/
mutual
def boundE : Expr Op -> List String := fun _ => []

def boundS : Stmt Op -> List String
  | Stmt.block body => boundSs body
  | Stmt.funDef _ ps _ body => ps ++ boundSs body
  | Stmt.letDecl xs (some e) => xs ++ boundE e
  | Stmt.letDecl xs none => xs
  | Stmt.assign xs e => xs ++ boundE e
  | Stmt.cond c body => boundE c ++ boundSs body
  | Stmt.switch c cases dflt =>
      boundE c ++ boundSC cases ++
        (match dflt with | some d => boundSs d | none => [])
  | Stmt.forLoop init c post body =>
      boundSs init ++ boundE c ++ boundSs post ++ boundSs body
  | Stmt.exprStmt e => boundE e
  | _ => []
termination_by s => sizeOf s

def boundSs : List (Stmt Op) -> List String
  | [] => []
  | s :: ss => boundS s ++ boundSs ss
termination_by ss => sizeOf ss

def boundSC : List (Literal × List (Stmt Op)) -> List String
  | [] => []
  | (_, body) :: rest => boundSs body ++ boundSC rest
termination_by cs => sizeOf cs
end

/-- The names a block BINDS. -/
def boundNames : List (Stmt Op) -> List String := boundSs

/- The names a block REFERENCES: every 'Expr.var' use, at any depth, inside a function body or not. -/
mutual
def refE : Expr Op -> List String
  | Expr.var x => [x]
  | Expr.builtin _ args => args.flatMap refE
  | Expr.call _ args => args.flatMap refE
  | _ => []

def refS : Stmt Op -> List String
  | Stmt.block body => refSs body
  | Stmt.funDef _ _ _ body => refSs body
  | Stmt.letDecl _ (some e) => refE e
  | Stmt.letDecl _ none => []
  | Stmt.assign _ e => refE e
  | Stmt.cond c body => refE c ++ refSs body
  | Stmt.switch c cases dflt =>
      refE c ++ refSC cases ++
        (match dflt with | some d => refSs d | none => [])
  | Stmt.forLoop init c post body =>
      refSs init ++ refE c ++ refSs post ++ refSs body
  | Stmt.exprStmt e => refE e
  | _ => []
termination_by s => sizeOf s

def refSs : List (Stmt Op) -> List String
  | [] => []
  | s :: ss => refS s ++ refSs ss
termination_by ss => sizeOf ss

def refSC : List (Literal × List (Stmt Op)) -> List String
  | [] => []
  | (_, body) :: rest => refSs body ++ refSC rest
termination_by cs => sizeOf cs
end

/-- The identifiers a block uses that it never binds anywhere inside itself. For the emitted program
    these are the contract-level 'uint256 internal constant' declarations of 'Halo2Verifier.sol' and
    the two shell locals - 'RunEmitted.lean:67-76' records exactly that, and D-P30 puts the Solidity
    wrapper out of scope. The relevance here is narrow and it is stated where it is used: a name that
    is free in the block is a name the big-step semantics has no value for at the top of the block,
    because 'YulSemantics.Run' starts the variable environment at '[]' (BigStep.lean:366-368) and
    'Step.var' needs 'VEnv.get V x = some v'. -/
def freeNames : List (Stmt Op) -> List String :=
  fun b => ((refSs b).filter fun n => !((boundSs b).contains n)).eraseDups

end Midfall.Lowering.FrameWalk
