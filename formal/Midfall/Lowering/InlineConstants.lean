/-
Midfall.Lowering.InlineConstants

P-INLINE (docs/plans/P-INLINE.md), implementing **D-P39** (docs/design.md D-P39).

WHY THIS FILE EXISTS. 'lowering_equivalence' is PROVED and VACUOUS at every Surface in the tree,
because the shell side has no runs at all. 'Midfall/Instances/RunShellInversion.lean' proved it:
'no_arm_run' shows the block 'RunShell' runs has NO 'Step' derivation from the shell's entry frame,
because the emitted Yul is a FRAGMENT - 61 identifiers it references and never declares - and
'curveSurface.bindLocals = []'. 'runShell_curveSurface_empty' lifts that to the run predicate, and
'ir_refines_refuted_at_curveSurface' turns it into a REFUTATION of a 'LoweringCorrect' field.

WHY THE OBVIOUS FIX IS NOT THE FIX, and it was measured rather than assumed (P-RUNSHELL step 2):
binding the fragment's free names at the ARM level is insufficient. A Yul function is not a
closure - 'Step.callOk' initialises the callee environment with the parameters and the zeroed
return slots and nothing else (BigStep.lean:189) - and six of the eight emitted helpers read names
their own signature cannot supply. So the embedding has to DESCEND INTO FUNCTION BODIES.

THE DECISION. In the real build, solc inlines the contract's 'uint256 internal constant'
declarations at every use site, INSIDE function bodies as well as at the top level. That embedding
is what this file specifies: 'inlineContractConstants' substitutes each constant's literal at every
USE SITE and threads the binders it passes so that a SHADOWING BINDER IS NEVER SUBSTITUTED.

NO NEW NUMBERS. The table is the one 'RunEmitted.shellLets' already reads: 'renderConstants
poseidonCtx' is the constants section of the deployed artifact, parsed at '#eval' time (D-P19). The
parser and the table MOVED here from 'RunEmitted.lean' rather than being copied, so there is still
exactly one copy of each number in the tree.

WHAT IS NOT IN THE TABLE, AND THAT IS THE POINT. 'shellLocals' - 'vk' and 'success' - are NOT
contract-level constants. They are locals the Solidity wrapper's own prologue declares ('let vk :=
loadimmutable("AUTHORIZED_VK")', 'let success := true'). A local must be BOUND, not substituted,
and the difference is not cosmetic: 'success' is ASSIGNMENT-ACCUMULATED at the top of 'main'
('success := and(success, ...)', eleven times) and is REUSED AS A PARAMETER NAME by two of the
emitted helpers ('batch_invert(success, ...)', 'ec_pairing(success, ...)'). Substituting it would
rewrite the accumulator chain into a constant and would substitute under a shadowing binder -
exactly the failure mode this package was warned about. So 'contractConstants' is the Solidity table
ONLY and 'shellLocalLets' is the block that binds the two locals.

THE FUEL, and why it is here rather than a structural recursion (R-37, RE-MEASURED here). Lean
4.35's structural estimator cannot drive recursion through 'Stmt.switch', whose case list is a
'List (Literal × Block Op)' - the goal is 'sizeOf b < sizeOf cs' for 'b ∈ Prod.snd '' cs', and the
mutual variants all fail the same way. 'Midfall/Generator/Render.lean:118-128' records the same
wall and the same answer, and 'Midfall/Lowering/FrameWalk.lean:300-391' is the second instance of
it. So the walk is a SINGLE function well-founded on an explicit fuel, with the recursion passed to
the layer function as a continuation - the 'frameStep'/'frameScan' shape.

WHAT THAT BUYS, MEASURED RATHER THAN ASSUMED, because an earlier draft of this header claimed
something stronger and wrong. Neither this shape nor a 'mutual' block is DEFINITIONALLY reducible:
'rfl' fails on 'inExpr (Expr.var "a") [("a", 3)] []' (nested recursion through a 'List' field is
compiled through 'brecOn', not 'casesOn'), and it fails on the fuel walk too. What the fuel shape
buys is that the EQUATION lemmas exist and 'simp' can run them, at a raised 'maxRecDepth' and
'maxHeartbeats' - which is how every shape fact about the inlined arm below and in
'Midfall/Instances/RunShellInversion.lean' is discharged. A 'mutual' block would give the same, so
the choice is forced by 'Stmt.switch' and not by reducibility. Fuel exhaustion REPORTS ITSELF
('inlineExhaustedAt'), so a too-small bound under-substitutes loudly rather than silently.
-/
import Midfall.Generator.VerifierPartials
import YulSemantics.Syntax
import YulSemantics.Dialect.EVM

/- The walk is fuel-bounded at 'inlineFuel' = 2000, and discharging one equation of it needs the
   simplifier to unfold that many layers, so the recursion and heartbeat bounds are raised for the
   whole file. -/
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Midfall.Lowering.Inline
open Midfall.Generator YulSemantics YulSemantics.EVM


/-! ### The shell constant table, read out of the rendered contract

    MOVED VERBATIM from 'Midfall/Lowering/RunEmitted.lean:77-125', which now cites these names.
    The reason it moved is a cycle: 'RunEmitted' imports 'Lowering/Partials.lean', which imports
    'Lowering/Surface.lean', and 'Surface.lean' is where 'RunShell' lives - so the table 'RunShell'
    needs cannot live in 'RunEmitted'. Moving, not copying, is what keeps one copy of each number. -/

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
    literal - invisible on the palindromic 0x44, and caught only because the gate in RunEmitted
    pins EXPECTED_VK_LENGTH against the artifact's own 4577. Recorded because a parser that is
    wrong on most inputs and right on the ones a reader eyeballs is the classic silent defect. -/
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

/-- **THE TABLE 'inlineContractConstants' IS APPLIED TO**: the contract's own 'uint256 internal
    constant' declarations and NOTHING ELSE, read off the pinned literal table above (so that a
    'decide' verdict about the inlined program is a kernel verdict). 'shellLocals' is deliberately
    excluded: those two are locals of the wrapper's assembly block, so they are BOUND
    ('shellLocalLets'), not substituted - 'inlining_a_local_rewrites_reads_but_not_writes' is the
    theorem that says what goes wrong otherwise, and 'contractConstantsShape_ok' is the gate that
    reddens if anyone puts them back in. -/
def contractConstants : List (String × Nat) :=
  pinnedConstants.filter fun n => n.1 != "vk" && n.1 != "success"

/-- A 'let x := <literal>' block for a constant table - the arm-level binding. -/
def letsOf : List (String × Nat) -> Block EVM.Op :=
  fun xs => xs.map fun (n, v) => Stmt.letDecl [n] (some (Expr.lit (Literal.number v)))

/-- The block that binds the two shell locals. This is the honest value of 'Surface.bindLocals':
    the field is documented as "the constant-substituted locals block", and what belongs in it is
    exactly the locals the wrapper declares, not the contract constants (which solc inlines). -/
def shellLocalLets : Block EVM.Op := letsOf shellLocals

/-! ### The inlining transform -/

abbrev Consts := List (String × Nat)
abbrev Cases := List (Literal × List (Stmt EVM.Op))

/-- The names one statement BINDS at its own site: a function's parameters and return slots, a
    'let' target, an assignment target. An assignment target counts because 'x := e' declares
    nothing but makes 'x' a LOCAL of the enclosing block, and a name the program assigns to is by
    that fact not a constant - 'success := and(success, ...)' is the case that matters. -/
def boundOf : Stmt EVM.Op -> List String
  | Stmt.funDef _ ps rs _ => ps ++ rs
  | Stmt.letDecl xs _ => xs
  | Stmt.assign xs _ => xs
  | _ => []

/-- Does an enclosing binder own 'x' at this position? Written as its own boolean rather than as
    'List.contains', because the equation compiler rewrites 'contains' into 'decide (x ∈ sh)' and
    that form is a nuisance to discharge. -/
def shadowed : List String -> String -> Bool
  | [], _ => false
  | y :: ys, x => if y == x then true else shadowed ys x

/-- **THE USE-SITE RULE.** A variable occurrence is replaced by the constant's literal unless the
    name is in the shadow list, i.e. unless an enclosing binder owns it at this position. The
    shadow list is what makes this a SUBSTITUTION rather than a find-and-replace, and
    'inExpr_keeps_shadowed' is the lemma saying so.

    FUEL-INDEXED, AND THAT IS LOAD-BEARING FOR EVIDENCE, not for termination: an expression walk
    written as a direct structural recursion over 'Expr' is compiled through 'brecOn' because the
    recursive occurrences sit inside a 'List' field, and 'rfl' then FAILS on it - measured here, and
    the reason 'FrameWalk'\'s 'refE'/'boundS' mutual block needs 'native_decide'. Indexing on an
    explicit fuel makes the same walk reduce in the kernel, so every shape fact below and in
    'Midfall/Instances/RunShellInversion.lean' is 'rfl' or 'decide' and not 'simp'. -/
def inExpr : Nat -> Expr EVM.Op -> Consts -> List String -> Expr EVM.Op
  | 0, e, _, _ => e
  | fuel+1, Expr.var x, consts, sh =>
      match shadowed sh x with
      | true => Expr.var x
      | false => match consts.lookup x with
        | some v => Expr.lit (Literal.number v)
        | none => Expr.var x
  | fuel+1, Expr.builtin op args, consts, sh =>
      Expr.builtin op (args.map fun a => inExpr fuel a consts sh)
  | fuel+1, Expr.call f args, consts, sh =>
      Expr.call f (args.map fun a => inExpr fuel a consts sh)
  | _, e, _, _ => e

/-- The expression fuel. Exhaustion here would silently under-substitute, and what rules it out is
    'inlineClosesTheArm_ok': a constant whose use site was skipped because the fuel ran out is
    still a free identifier of the result, and that gate says there are none. -/
def exprFuel : Nat := 64

/-- The walk's answer at one position: the rewritten block, and whether the fuel ran out on the
    way. Exhaustion is DATA rather than silence, so a too-small bound is detectable (R-37). -/
structure SRes where
  blks : List (Stmt EVM.Op)
  exhausted : Bool

def anyEx : List SRes -> Bool := fun rs => rs.any (fun r => r.exhausted)

/-- One statement, with the recursion supplied as a continuation so this function is not itself
    recursive - the 'FrameWalk.frameStep' shape, and the reason the walk stays kernel-reducible.
    Note what each case THREADS: a 'funDef' adds its parameters and return slots, a 'let'/'assign'
    adds its targets for the statements that follow it in the same block, a 'for' adds its 'init'
    bindings for the condition, the post block and the body (the vendored AST's own scoping note,
    Ast.lean:61-63), and a nested 'block' gets its own scope. -/
def inlineStmtStep (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    : List String -> Stmt EVM.Op -> Stmt EVM.Op × Bool
  | sh, Stmt.block b => let r := rec sh b; (Stmt.block r.blks, r.exhausted)
  | sh, Stmt.funDef n ps rs body =>
      let r := rec (sh ++ ps ++ rs) body
      (Stmt.funDef n ps rs r.blks, r.exhausted)
  | sh, Stmt.letDecl xs e => (Stmt.letDecl xs (e.map fun x => inExpr exprFuel x consts sh), false)
  | sh, Stmt.assign xs e => (Stmt.assign xs (inExpr exprFuel e consts sh), false)
  | sh, Stmt.cond c body => let r := rec sh body; (Stmt.cond (inExpr exprFuel c consts sh) r.blks, r.exhausted)
  | sh, Stmt.switch c cs d =>
      let cr := cs.map fun (_, b) => rec sh b
      let dr := match d with
        | none => (none, false)
        | some db => let r := rec sh db; (some r.blks, r.exhausted)
      (Stmt.switch (inExpr exprFuel c consts sh) ((cs.map Prod.fst).zip (cr.map (fun r => r.blks))) dr.1,
        anyEx cr || dr.2)
  | sh, Stmt.forLoop init c post body =>
      let i := rec sh init
      let sh' := sh ++ (i.blks.flatMap boundOf)
      let p := rec sh' post
      let b := rec sh' body
      (Stmt.forLoop i.blks (inExpr exprFuel c consts sh') p.blks b.blks,
        i.exhausted || p.exhausted || b.exhausted)
  | sh, Stmt.exprStmt e => (Stmt.exprStmt (inExpr exprFuel e consts sh), false)
  | _, s => (s, false)

/-- The block fold's accumulator: the rewritten statements so far, the shadow set as it stands
    AFTER them (Yul 'let' scope runs to the end of its block), and whether any descent ran out. -/
structure Acc where
  blks : List (Stmt EVM.Op)
  sh : List String
  exhausted : Bool

/-- One block: rewrite every statement, threading each statement's binders into the ones that follow
    it in the same block. Traversing the list itself costs NO fuel; only DESCENDING into a nested
    block - a function body, an if-body, a case arm, a loop body - costs one. So the bound is the
    statement-nesting depth and not the program length, which is the same choice
    'Midfall/Generator/Render.lean:118-128' records for the same reason, and it is what makes the
    kernel able to unfold the walk at all: with one level per statement, every 'rfl' about the
    inlined arm cost 600 unfoldings of a 50-statement program and this package measured 18 minutes
    and 8.7 GB of resident memory for one such lemma. -/
def inlineStep (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    : List String -> List (Stmt EVM.Op) -> SRes
  | sh, bl =>
      let a : Acc := bl.foldl (fun (acc : Acc) (s : Stmt EVM.Op) =>
        let r := inlineStmtStep rec consts acc.sh s
        { blks := acc.blks ++ [r.1], sh := acc.sh ++ boundOf s,
          exhausted := acc.exhausted || r.2 })
        { blks := [], sh := sh, exhausted := false }
      { blks := a.blks, exhausted := a.exhausted }

/-- The fuel-bounded walk. -/
def inlineScan : Nat -> Consts -> List String -> List (Stmt EVM.Op) -> SRes
  | 0, _, _, bl => { blks := bl, exhausted := true }
  | fuel+1, consts, sh, bl => inlineStep (inlineScan fuel consts) consts sh bl

/-- **A BOUND ON NESTING DEPTH, NOT ON PROGRAM LENGTH.** The walk spends a level only when it
    descends into a nested block, and the deepest statement nest measured in the emitted program is
    well under ten; 'inlineFuelIsEnough_ok' checks the bound on the real program and reports
    exhaustion as data rather than trusting it. -/
def inlineFuel : Nat := 64

/-- **D-P39's TRANSFORM.** 'inlineContractConstants consts b' substitutes each constant's literal
    at every use site of 'b', inside 'funDef' bodies included, and leaves a name alone wherever an
    enclosing binder owns it. -/
def inlineContractConstantsAt (fuel : Nat) (consts : Consts) :
    List (Stmt EVM.Op) -> List (Stmt EVM.Op) :=
  fun b => (inlineScan fuel consts [] b).blks

def inlineContractConstants (consts : Consts) : List (Stmt EVM.Op) -> List (Stmt EVM.Op) :=
  inlineContractConstantsAt inlineFuel consts

/-- Did the walk run out of fuel? 'false' is the honest answer for every program this package runs
    the transform on, and the gate below is what says so. -/
def inlineExhaustedAt (fuel : Nat) (consts : Consts) : List (Stmt EVM.Op) -> Bool :=
  fun b => (inlineScan fuel consts [] b).exhausted

/-! ### Shadowing: the lemma, and the planted tests

    THE FAILURE MODE THIS SECTION EXISTS TO KILL. A 'funDef' parameter or a 'let' binder may reuse a
    constant's name. Substituting there changes the program's MEANING while leaving every later
    theorem provable - the run relation does not care where a literal came from, so nothing
    downstream can tell that the transform rewrote a local into a constant. The test is therefore
    made against the transform itself, and against a deliberately WRONG transform next to it. -/

/-- **THE SHADOWING LEMMA, expression level.** At a position whose shadow list already carries a
    name, that name's occurrence survives: the transform leaves it alone whatever the table says. -/
theorem inExpr_keeps_shadowed (consts : Consts) (sh : List String) (x : String) (v : Nat)
    (fuel : Nat) (h : shadowed sh x = true) :
    inExpr (fuel + 1) (Expr.var x) ((x, v) :: consts) sh = Expr.var x := by
  cases h2 : ((x, v) :: consts).lookup x <;> simp [inExpr, h]


/-- And the positive half: with nothing shadowing it, the occurrence DOES become the literal.
    Without this the lemma above would be satisfied by a transform that never substitutes. -/
theorem inExpr_substitutes_unshadowed (consts : Consts) (x : String) (v : Nat) (fuel : Nat) :
    inExpr (fuel + 1) (Expr.var x) ((x, v) :: consts) [] = Expr.lit (Literal.number v) := by
  cases consts with
  | nil => simp [inExpr, shadowed, List.lookup]
  | cons c rest => simp [inExpr, shadowed, List.lookup]

/-- **PLANTED SHADOW 1 - a helper parameter literally named 'VK_MPTR'.** This is not a hypothetical
    shape: the emitted 'batch_invert' and 'ec_pairing' both take a parameter named 'success', and
    'success' is one of the two shell locals. -/
theorem planted_parameter_shadow_survives :
    inlineContractConstants [("VK_MPTR", 0x100)]
      [Stmt.funDef "helper" ["VK_MPTR"] ["out"]
        [Stmt.letDecl ["out"] (some (Expr.builtin Op.mload [Expr.var "VK_MPTR"]))]]
      = [Stmt.funDef "helper" ["VK_MPTR"] ["out"]
        [Stmt.letDecl ["out"] (some (Expr.builtin Op.mload [Expr.var "VK_MPTR"]))]] := by
  rfl

/-- **THE SAME BLOCK WITH THE PARAMETER RENAMED substitutes**, which is what makes the test above a
    test: the only difference between the two blocks is who owns the name. -/
theorem unshadowed_site_is_substituted :
    inlineContractConstants [("VK_MPTR", 0x100)]
      [Stmt.funDef "helper" ["mptr"] ["out"]
        [Stmt.letDecl ["out"] (some (Expr.builtin Op.mload [Expr.var "VK_MPTR"]))]]
      = [Stmt.funDef "helper" ["mptr"] ["out"]
        [Stmt.letDecl ["out"] (some (Expr.builtin Op.mload [Expr.lit (Literal.number 0x100)]))]] := rfl

/-- **PLANTED SHADOW 2 - a 'let' binder that reuses a constant name**, and the use AFTER it belongs
    to the local while the use BEFORE it belongs to the constant. Scope runs forward, not backward. -/
theorem planted_let_shadow_survives :
    inlineContractConstants [("X", 7)]
      [Stmt.exprStmt (Expr.var "X"), Stmt.letDecl ["X"] (some (Expr.lit (Literal.number 2))),
        Stmt.exprStmt (Expr.var "X")]
      = [Stmt.exprStmt (Expr.lit (Literal.number 7)),
        Stmt.letDecl ["X"] (some (Expr.lit (Literal.number 2))),
        Stmt.exprStmt (Expr.var "X")] := rfl

/-- **PLANTED SHADOW 3 - a 'switch' case body**, the position that forces the fuel (R-37): a
    transform that silently skipped case bodies would pass every other test in this section.
    Stated at an explicit fuel of 40 rather than at 'inlineFuel' only because 2000 makes the kernel
    unfold 2000 layers to answer a question about one case arm; shadowing does not depend on it. -/
theorem planted_switch_shadow_survives :
    inlineContractConstantsAt 40 [("X", 7)]
      [Stmt.switch (Expr.var "X") [(Literal.number 1, [Stmt.exprStmt (Expr.var "X")])]
        (some [Stmt.exprStmt (Expr.var "X")])]
      = [Stmt.switch (Expr.lit (Literal.number 7))
        [(Literal.number 1, [Stmt.exprStmt (Expr.lit (Literal.number 7))])]
        (some [Stmt.exprStmt (Expr.lit (Literal.number 7))])] := rfl

/-! ### The wrong transform, kept as evidence -/

/-- **THE WRONG VERSION, ON PURPOSE.** A find-and-replace that threads nothing: it substitutes under
    a shadowing binder. Kept so the difference is a THEOREM rather than a paragraph - D-P23's
    falsification half, and the only way to show the shadow list in 'inExpr' is load-bearing. -/
def naiveReplaceOne (x : String) (v : Nat) : Expr EVM.Op -> Expr EVM.Op
  | Expr.var y => if y == x then Expr.lit (Literal.number v) else Expr.var y
  | Expr.builtin op args => Expr.builtin op (args.map (naiveReplaceOne x v))
  | Expr.call f args => Expr.call f (args.map (naiveReplaceOne x v))
  | e => e

/-- The wrong version applied to one statement, at every depth. Fuel-indexed for the same reason
    the specified walk is (R-37), and so its equations are usable by 'simp' - a 'partial def' here
    would make the theorem below about a 'WF.fix' the simplifier cannot unfold. -/
def naiveReplaceStmt : Nat -> String -> Nat -> Stmt EVM.Op -> Stmt EVM.Op
  | 0, _, _, s => s
  | fuel+1, x, v, Stmt.block b => Stmt.block (b.map (naiveReplaceStmt fuel x v))
  | fuel+1, x, v, Stmt.funDef n ps rs body =>
      Stmt.funDef n ps rs (body.map (naiveReplaceStmt fuel x v))
  | _fuel+1, x, v, Stmt.letDecl xs e =>
      Stmt.letDecl xs (e.map fun e' => naiveReplaceOne x v e')
  | _fuel+1, x, v, Stmt.assign xs e => Stmt.assign xs (naiveReplaceOne x v e)
  | fuel+1, x, v, Stmt.cond c body =>
      Stmt.cond (naiveReplaceOne x v c) (body.map (naiveReplaceStmt fuel x v))
  | fuel+1, x, v, Stmt.switch c cs d =>
      Stmt.switch (naiveReplaceOne x v c)
        (cs.map fun (l, b) => (l, b.map (naiveReplaceStmt fuel x v)))
        (d.map fun b => b.map (naiveReplaceStmt fuel x v))
  | fuel+1, x, v, Stmt.forLoop init c post body =>
      Stmt.forLoop (init.map (naiveReplaceStmt fuel x v)) (naiveReplaceOne x v c)
        (post.map (naiveReplaceStmt fuel x v)) (body.map (naiveReplaceStmt fuel x v))
  | _, x, v, Stmt.exprStmt e => Stmt.exprStmt (naiveReplaceOne x v e)
  | _, _, _, s => s

/-- **THE SHADOWING DIFFERENCE, AS A THEOREM.** The correct transform does NOT produce the
    rewritten-under-the-shadow program that the naive one does, so the two differ on this block and
    the difference is the shadow threading. Nothing downstream can see this - the run relation only
    sees the literals - so it has to be seen HERE. -/
theorem shadowing_is_load_bearing :
    inlineContractConstants [("VK_MPTR", 0x100)]
        [Stmt.funDef "helper" ["VK_MPTR"] [] [Stmt.exprStmt (Expr.var "VK_MPTR")]]
      ≠ [Stmt.funDef "helper" ["VK_MPTR"] []
        [Stmt.exprStmt (Expr.lit (Literal.number 0x100))]] := by
  intro h
  -- a projection that can SEE the difference: is the helper's first body statement a literal?
  have h2 := congrArg (fun b : List (Stmt EVM.Op) =>
    match b.headD (Stmt.block []) with
    | Stmt.funDef _ _ _ body =>
        match body.headD (Stmt.exprStmt (Expr.lit (Literal.number 0))) with
        | Stmt.exprStmt (Expr.lit _) => true
        | _ => false
    | _ => false) h
  exact absurd h2 (by decide)

/-- ...and the wrong transform DOES produce that rewritten program, so the disagreement above is a
    disagreement about shadowing and not about something else. -/
theorem naive_transform_substitutes_under_the_shadow :
    (naiveReplaceStmt 20 "VK_MPTR" 0x100 (Stmt.funDef "helper" ["VK_MPTR"] []
      [Stmt.exprStmt (Expr.var "VK_MPTR")]))
      = Stmt.funDef "helper" ["VK_MPTR"] []
        [Stmt.exprStmt (Expr.lit (Literal.number 0x100))] := by
  simp [naiveReplaceStmt, naiveReplaceOne]

/-- **THE OTHER HALF OF THE BOUNDARY: THE TWO LOCALS MUST BE BOUND, NOT INLINED.** 'success' is
    assigned, and an assignment target is not a use site - so a transform that treats 'success' as a
    constant rewrites the READS of the accumulator chain into the literal 1 while leaving the WRITES
    as writes to a name nothing declares. Stated as a theorem because the resulting program is
    syntactically well-formed and only the run relation would notice, and the run relation does not
    notice: it just evaluates 'and(1, ...)' happily. 'inlineTheLocalsToo_stuck_ok' is the gate that
    says what the artifact does with it. -/
theorem inlining_a_local_rewrites_reads_but_not_writes :
    inlineContractConstants [("success", 1)]
      [Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success", Expr.lit (Literal.number 0)])]
      = [Stmt.assign ["success"]
        (Expr.builtin Op.and [Expr.lit (Literal.number 1), Expr.lit (Literal.number 0)])] := rfl

/-- ...and the specified table, which excludes the locals, leaves the chain alone. -/
theorem binding_a_local_leaves_the_chain :
    inlineContractConstants contractConstants
      [Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success", Expr.lit (Literal.number 0)])]
      = [Stmt.assign ["success"]
        (Expr.builtin Op.and [Expr.var "success", Expr.lit (Literal.number 0)])] := rfl

/-! ### Gates -/

/-- GATE (THE TABLE IS THE ARTIFACT'S AND IT IS SUBSTANTIAL). The parse found a real table, the
    three numbers the artifact is known by are its own, and the two locals are NOT in it - which is
    the D-P39 boundary stated as data. Red if the renderer's constant block changes shape, if the
    parser silently drops entries, or if someone moves 'shellLocals' into the inlined table. -/
def contractConstantsShape_ok : Bool :=
  contractConstants.length >= 55 &&
    (contractConstants.lookup "EXPECTED_VK_LENGTH" == some 4577) &&
    (((contractConstants.lookup "FR_MODULUS").getD 0) > 2 ^ 253) &&
    (contractConstants.lookup "PROOF_LEN_CPTR" == some 0x44) &&
    (! ((contractConstants.map Prod.fst).contains "vk")) &&
    (! ((contractConstants.map Prod.fst).contains "success")) &&
    (shellLocals.map Prod.fst == ["vk", "success"]) &&
    (SyntaxEq.stmtsBeq (Midfall.Lowering.Inline.letsOf contractConstants)
      (Midfall.Lowering.Inline.letsOf solConstants))

/-- GATE (THE TRANSFORM DOES SOMETHING). On a planted block with no shadowing, a constant use
    becomes a literal; on the same block with a shadowing parameter, it does not; and the fuel is
    not the reason anything survives. Red if the threading is dropped, if the substitution is
    dropped, or if 'inlineFuel' is set so small that the walk stops descending. -/
def inlineShadowingKats_ok : Bool :=
  (SyntaxEq.stmtsBeq (inlineContractConstants [("X", 7)] [Stmt.exprStmt (Expr.var "X")])
      [Stmt.exprStmt (Expr.lit (Literal.number 7))]) &&
    (SyntaxEq.stmtsBeq (inlineContractConstants [("X", 7)]
        [Stmt.funDef "h" ["X"] [] [Stmt.exprStmt (Expr.var "X")]])
      [Stmt.funDef "h" ["X"] [] [Stmt.exprStmt (Expr.var "X")]]) &&
    (SyntaxEq.stmtsBeq (inlineContractConstants [("X", 7)]
        [Stmt.letDecl ["X"] (some (Expr.var "X")), Stmt.exprStmt (Expr.var "X")])
      [Stmt.letDecl ["X"] (some (Expr.lit (Literal.number 7))), Stmt.exprStmt (Expr.var "X")]) &&
    (! (inlineExhaustedAt inlineFuel [("X", 7)]
      [Stmt.funDef "h" ["X"] [] [Stmt.exprStmt (Expr.var "X")]]))

/-- GATE (THE WRONG TRANSFORM IS WRONG). The naive version substitutes under the shadowing binder
    and the specified one does not. This is the falsification half for the shadowing claim. -/
def naiveTransformIsWrong_ok : Bool :=
  (SyntaxEq.stmtBeq (naiveReplaceStmt 20 "VK_MPTR" 0x100 (Stmt.funDef "helper" ["VK_MPTR"] []
      [Stmt.exprStmt (Expr.var "VK_MPTR")]))
      (Stmt.funDef "helper" ["VK_MPTR"] [] [Stmt.exprStmt (Expr.lit (Literal.number 0x100))])) &&
    (SyntaxEq.stmtsBeq (inlineContractConstants [("VK_MPTR", 0x100)]
        [Stmt.funDef "helper" ["VK_MPTR"] [] [Stmt.exprStmt (Expr.var "VK_MPTR")]])
      [Stmt.funDef "helper" ["VK_MPTR"] [] [Stmt.exprStmt (Expr.var "VK_MPTR")]])

#eval contractConstantsShape_ok        -- expect true
#eval inlineShadowingKats_ok           -- expect true
#eval naiveTransformIsWrong_ok         -- expect true

/-! ### GEN.4 - the inliner distributes over a concatenation

    TWO HALVES, NEITHER ABOUT A RENDER. (1) `inlineScan_append`: the walk is a `List.foldl`, so it
    splits over `a ++ b` with the left block's binders THREADED into the right scan's shadow list -
    `List.foldl_append` plus two accumulator facts about `stepAcc`. (2) `inlineScan_irrel`: a shadow
    list that names no constant of the table is inert, so under `inline_append`'s `topBinders`
    hypothesis the threaded scan collapses to the standalone one. `Midfall.LoweringV2.inline_append`
    (`LoweringV2/ProgramLemmas.lean`) is (1) + (2) at `inlineFuel`. Everything is stated at
    `fuel + 1` and the walk is NEVER unfolded at a literal fuel, which is what keeps each `rfl` here
    cheap; the two falsifiers below are `rfl` at fuel 1 for the same reason.
-/

/-- `List.map` congruence, stated locally: `List.congr`/`List.map_congr` are not available here,
    and the tree's own precedent is `LoweringV3/VkWindow.lean`'s `map_congr_of`. -/
theorem inline_map_congr {α β : Type} (f g : α -> β) (l : List α) (h : ∀ x, f x = g x) :
    List.map f l = List.map g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, h a]
      exact congrArg (List.cons (g a)) ih

/-- The `inlineStep` fold's starting accumulator: no statements yet, shadow list `sh`, nothing
    exhausted. Named so its projections are lemmas. -/
def initAcc (sh : List String) : Acc := { blks := [], sh := sh, exhausted := false }

theorem initAcc_blks (sh : List String) : (initAcc sh).blks = [] := rfl
theorem initAcc_sh (sh : List String) : (initAcc sh).sh = sh := rfl
theorem initAcc_exhausted (sh : List String) : (initAcc sh).exhausted = false := rfl

/-- The same shadow list, no accumulated statements, nothing exhausted. -/
def resetAcc (acc : Acc) : Acc := { blks := [], sh := acc.sh, exhausted := false }

theorem resetAcc_eq (acc : Acc) :
    resetAcc acc = { blks := [], sh := acc.sh, exhausted := false } := rfl
theorem resetAcc_blks (acc : Acc) : (resetAcc acc).blks = [] := rfl
theorem resetAcc_sh (acc : Acc) : (resetAcc acc).sh = acc.sh := rfl
theorem resetAcc_exhausted (acc : Acc) : (resetAcc acc).exhausted = false := rfl
theorem resetAcc_initAcc (sh : List String) : resetAcc (initAcc sh) = initAcc sh := rfl

/-- One step of the `inlineStep` fold, named so that the fold can be reasoned about: this is
    `inlineStep`'s own accumulator lambda verbatim, and `inlineStep_eq_foldl` is the bridge. -/
def stepAcc (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    (acc : Acc) (s : Stmt EVM.Op) : Acc :=
  { blks := acc.blks ++ [(inlineStmtStep rec consts acc.sh s).1],
    sh := acc.sh ++ boundOf s,
    exhausted := acc.exhausted || (inlineStmtStep rec consts acc.sh s).2 }

theorem stepAcc_blks (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    (acc : Acc) (s : Stmt EVM.Op) :
    (stepAcc rec consts acc s).blks = acc.blks ++ [(inlineStmtStep rec consts acc.sh s).1] := rfl

theorem stepAcc_sh (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    (acc : Acc) (s : Stmt EVM.Op) :
    (stepAcc rec consts acc s).sh = acc.sh ++ boundOf s := rfl

theorem stepAcc_exhausted (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    (acc : Acc) (s : Stmt EVM.Op) :
    (stepAcc rec consts acc s).exhausted =
      (acc.exhausted || (inlineStmtStep rec consts acc.sh s).2) := rfl

theorem resetAcc_stepAcc (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    (acc : Acc) (s : Stmt EVM.Op) :
    resetAcc (stepAcc rec consts acc s) = resetAcc (stepAcc rec consts (resetAcc acc) s) := by
  rw [resetAcc_eq, resetAcc_eq, stepAcc_sh, stepAcc_sh, resetAcc_sh]

theorem inlineStep_eq_foldl (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts)
    (sh : List String) (bl : List (Stmt EVM.Op)) :
    inlineStep rec consts sh bl =
      { blks := (bl.foldl (stepAcc rec consts) (initAcc sh)).blks,
        exhausted := (bl.foldl (stepAcc rec consts) (initAcc sh)).exhausted } := by
  unfold inlineStep stepAcc initAcc
  rfl

theorem foldl_stepAcc_sh (rec : List String -> List (Stmt EVM.Op) -> SRes) (consts : Consts) :
    ∀ (bl : List (Stmt EVM.Op)) (acc : Acc),
      (bl.foldl (stepAcc rec consts) acc).sh = acc.sh ++ bl.flatMap boundOf := by
  intro bl
  induction bl with
  | nil => intro acc; rw [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons s bl ih =>
      intro acc
      rw [List.foldl_cons, ih, stepAcc_sh, List.flatMap_cons, List.append_assoc]

theorem foldl_stepAcc_blks_split (rec : List String -> List (Stmt EVM.Op) -> SRes)
    (consts : Consts) :
    ∀ (bl : List (Stmt EVM.Op)) (acc : Acc),
      (bl.foldl (stepAcc rec consts) acc).blks =
        acc.blks ++ (bl.foldl (stepAcc rec consts) (resetAcc acc)).blks := by
  intro bl
  induction bl with
  | nil => intro acc; rw [List.foldl_nil, List.foldl_nil, resetAcc_blks, List.append_nil]
  | cons s bl ih =>
      intro acc
      have A : (s :: bl).foldl (stepAcc rec consts) acc
          = bl.foldl (stepAcc rec consts) (stepAcc rec consts acc s) := by rw [List.foldl_cons]
      have B : (s :: bl).foldl (stepAcc rec consts) (resetAcc acc)
          = bl.foldl (stepAcc rec consts) (stepAcc rec consts (resetAcc acc) s) :=
        by rw [List.foldl_cons]
      rw [A, ih (stepAcc rec consts acc s), B, ih (stepAcc rec consts (resetAcc acc) s)]
      rw [stepAcc_blks, stepAcc_blks, resetAcc_blks, resetAcc_sh, resetAcc_stepAcc]
      rw [List.nil_append, ← List.append_assoc]

/-- **GEN.4 STEP 2.** The scan of a concatenation is the scan of the left block followed by the scan
    of the right block AT THE SHADOW LIST THE LEFT BLOCK LEAVES BEHIND. The threading is not
    decoration: `inlineScan_append_is_threaded` below falsifies the unthreaded form. -/
theorem inlineScan_append (fuel : Nat) (consts : Consts) (sh : List String)
    (a b : List (Stmt EVM.Op)) :
    (inlineScan (fuel + 1) consts sh (a ++ b)).blks =
      (inlineScan (fuel + 1) consts sh a).blks ++
        (inlineScan (fuel + 1) consts (sh ++ a.flatMap boundOf) b).blks := by
  have h1 : ∀ (bl : List (Stmt EVM.Op)) (s : List String),
      (inlineScan (fuel + 1) consts s bl).blks =
        (bl.foldl (stepAcc (inlineScan fuel consts) consts) (initAcc s)).blks := by
    intro bl s
    rw [show (inlineScan (fuel + 1) consts s bl).blks =
          (inlineStep (inlineScan fuel consts) consts s bl).blks from rfl,
        inlineStep_eq_foldl]
  rw [h1, h1, h1, List.foldl_append, foldl_stepAcc_blks_split]
  rw [resetAcc_eq, foldl_stepAcc_sh, initAcc_sh]
  rw [show initAcc (sh ++ a.flatMap boundOf) =
        { blks := [], sh := sh ++ a.flatMap boundOf, exhausted := false } from rfl]

/-! #### A shadow list that names no constant is inert -/

theorem shadowed_append_or (sh t : List String) (x : String) :
    shadowed (sh ++ t) x = (shadowed sh x || shadowed t x) := by
  induction sh generalizing t with
  | nil => simp [shadowed]
  | cons y ys ih =>
      by_cases h : y == x
      · simp [shadowed, h, ih]
      · simp [shadowed, h, ih]

theorem shadowed_true_iff_mem (sh : List String) (x : String) :
    shadowed sh x = true ↔ x ∈ sh := by
  induction sh with
  | nil => simp [shadowed]
  | cons y ys ih =>
      by_cases h : y = x
      · subst h
        simp [shadowed]
      · have hb : ¬ (y == x) := fun hh => h (beq_iff_eq.mp hh)
        have hxy : ¬ (x = y) := fun hh => h hh.symm
        simp [shadowed, hb, ih, hxy]

theorem lookup_none_of_not_mem (consts : Consts) (x : String) (h : x ∉ consts.map Prod.fst) :
    consts.lookup x = none := by
  induction consts with
  | nil => rfl
  | cons c rest ih =>
      cases c with
      | mk k b =>
        have hcf : ¬ (x == k) := by
          intro heq
          exact h (by simp [beq_iff_eq.mp heq])
        have hrest : x ∉ rest.map Prod.fst := by
          intro hx
          exact h (by simp [hx])
        simp only [List.lookup_cons, hcf]
        exact ih hrest

theorem inExpr_irrel (consts : Consts) (sh : List String)
    (hsh : ∀ x ∈ sh, x ∉ consts.map Prod.fst) :
    ∀ (fuel : Nat) (t : List String) (e : Expr EVM.Op),
      inExpr fuel e consts (sh ++ t) = inExpr fuel e consts t := by
  intro fuel
  induction fuel with
  | zero => intro t e; rfl
  | succ F ih =>
      intro t e
      cases e with
      | lit l => rfl
      | var x =>
          by_cases h1 : shadowed t x
          · have h2 : shadowed (sh ++ t) x = true := by
              rw [shadowed_append_or, h1]
              simp
            simp [inExpr, h1, h2]
          · by_cases h2 : shadowed (sh ++ t) x
            · have h1f : shadowed t x = false := by
                cases hz : shadowed t x with
                | true => exact absurd hz h1
                | false => rfl
              have hx : x ∈ sh := by
                rw [shadowed_append_or] at h2
                rw [h1f, Bool.or_false] at h2
                rwa [shadowed_true_iff_mem] at h2
              have hl : consts.lookup x = none :=
                lookup_none_of_not_mem consts x (hsh x hx)
              simp [inExpr, h1, h2, hl]
            · simp [inExpr, h1, h2]
      | builtin op args =>
          simp only [inExpr]
          congr 1
          exact inline_map_congr (fun a => inExpr F a consts (sh ++ t))
            (fun a => inExpr F a consts t) args (fun a => ih t a)
      | call f args =>
          simp only [inExpr]
          congr 1
          exact inline_map_congr (fun a => inExpr F a consts (sh ++ t))
            (fun a => inExpr F a consts t) args (fun a => ih t a)

theorem inlineStmtStep_irrel (rec₁ rec₂ : List String -> List (Stmt EVM.Op) -> SRes)
    (consts : Consts) (sh : List String) (hsh : ∀ x ∈ sh, x ∉ consts.map Prod.fst)
    (hrec : ∀ (u : List String) (bl : List (Stmt EVM.Op)), rec₁ (sh ++ u) bl = rec₂ u bl) :
    ∀ (t : List String) (s : Stmt EVM.Op),
      inlineStmtStep rec₁ consts (sh ++ t) s = inlineStmtStep rec₂ consts t s := by
  intro t s
  have key : ∀ (u : List String) (e : Expr EVM.Op),
      inExpr exprFuel e consts (sh ++ u) = inExpr exprFuel e consts u :=
    inExpr_irrel consts sh hsh exprFuel
  cases s with
  | block b => simp only [inlineStmtStep, hrec]
  | funDef n ps rs body => simp only [inlineStmtStep, hrec, List.append_assoc]
  | letDecl xs e => simp only [inlineStmtStep, key]
  | assign xs e => simp only [inlineStmtStep, key]
  | cond c body => simp only [inlineStmtStep, hrec, key]
  | «switch» c cs d => simp only [inlineStmtStep, hrec, key]
  | forLoop init c post body => simp only [inlineStmtStep, hrec, key, List.append_assoc]
  | exprStmt e => simp only [inlineStmtStep, key]
  | «break» => rfl
  | «continue» => rfl
  | «leave» => rfl

theorem foldl_stepAcc_irrel (rec₁ rec₂ : List String -> List (Stmt EVM.Op) -> SRes)
    (consts : Consts) (sh : List String) (_hsh : ∀ x ∈ sh, x ∉ consts.map Prod.fst)
    (h : ∀ (t : List String) (s : Stmt EVM.Op),
        inlineStmtStep rec₁ consts (sh ++ t) s = inlineStmtStep rec₂ consts t s) :
    ∀ (bl : List (Stmt EVM.Op)) (acc₁ acc₂ : Acc),
      acc₁.blks = acc₂.blks → acc₁.exhausted = acc₂.exhausted → acc₁.sh = sh ++ acc₂.sh →
      (bl.foldl (stepAcc rec₁ consts) acc₁).blks = (bl.foldl (stepAcc rec₂ consts) acc₂).blks ∧
      (bl.foldl (stepAcc rec₁ consts) acc₁).sh = sh ++ (bl.foldl (stepAcc rec₂ consts) acc₂).sh ∧
      (bl.foldl (stepAcc rec₁ consts) acc₁).exhausted =
        (bl.foldl (stepAcc rec₂ consts) acc₂).exhausted := by
  intro bl
  induction bl with
  | nil => intro acc₁ acc₂ h1 h2 h3; rw [List.foldl_nil, List.foldl_nil]; exact ⟨h1, h3, h2⟩
  | cons s bl ih =>
      intro acc₁ acc₂ h1 h2 h3
      have hgs : inlineStmtStep rec₁ consts acc₁.sh s = inlineStmtStep rec₂ consts acc₂.sh s := by
        rw [h3]
        exact h acc₂.sh s
      have hbs : (stepAcc rec₁ consts acc₁ s).blks = (stepAcc rec₂ consts acc₂ s).blks := by
        rw [stepAcc_blks, stepAcc_blks, h1, hgs]
      have hes : (stepAcc rec₁ consts acc₁ s).exhausted =
          (stepAcc rec₂ consts acc₂ s).exhausted := by
        rw [stepAcc_exhausted, stepAcc_exhausted, h2, hgs]
      have hss : (stepAcc rec₁ consts acc₁ s).sh = sh ++ (stepAcc rec₂ consts acc₂ s).sh := by
        rw [stepAcc_sh, stepAcc_sh, h3, List.append_assoc]
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ hbs hes hss

theorem inlineStep_irrel (rec₁ rec₂ : List String -> List (Stmt EVM.Op) -> SRes)
    (consts : Consts) (sh : List String) (hsh : ∀ x ∈ sh, x ∉ consts.map Prod.fst)
    (hrec : ∀ (u : List String) (bl : List (Stmt EVM.Op)), rec₁ (sh ++ u) bl = rec₂ u bl) :
    ∀ (t : List String) (bl : List (Stmt EVM.Op)),
      inlineStep rec₁ consts (sh ++ t) bl = inlineStep rec₂ consts t bl := by
  have h := inlineStmtStep_irrel rec₁ rec₂ consts sh hsh hrec
  intro t bl
  rw [inlineStep_eq_foldl, inlineStep_eq_foldl]
  have hh := foldl_stepAcc_irrel rec₁ rec₂ consts sh hsh h bl
    (initAcc (sh ++ t)) (initAcc t) rfl rfl rfl
  rw [hh.1, hh.2.2]

theorem inlineScan_irrel (consts : Consts) :
    ∀ (fuel : Nat) (sh t : List String) (bl : List (Stmt EVM.Op)),
      (∀ x ∈ sh, x ∉ consts.map Prod.fst) →
      inlineScan fuel consts (sh ++ t) bl = inlineScan fuel consts t bl := by
  intro fuel
  induction fuel with
  | zero => intro sh t bl _; rfl
  | succ F ih =>
      intro sh t bl hsh
      refine inlineStep_irrel (inlineScan F consts) (inlineScan F consts) consts sh hsh ?_ t bl
      intro u bl
      exact ih sh u bl hsh

/-! #### The falsifier: the threading is load-bearing (GEN.4 step 4) -/

def inlineAppendFalsA : List (Stmt EVM.Op) :=
  [Stmt.letDecl ["X"] (some (Expr.lit (Literal.number 1)))]

def inlineAppendFalsB : List (Stmt EVM.Op) :=
  [Stmt.exprStmt (Expr.builtin EVM.Op.mstore [Expr.var "X", Expr.lit (Literal.number 0)])]

/-- Does the second statement of the block read `X` as a VARIABLE? A hand-written observation, used
    because `SyntaxEq.stmtsBeq` is compiled through `WellFounded.fix` and does not reduce in the
    kernel, so `decide` gets stuck on it (measured). -/
def readsX : List (Stmt EVM.Op) -> Bool
  | [_, Stmt.exprStmt (Expr.builtin _ (Expr.var "X" :: _))] => true
  | _ => false

/-- The UNTHREADED equation - second scan at the ORIGINAL shadow list - is FALSE: `a` binds `X`,
    `b` reads `X`, and `X` is a constant name, so threading leaves the read alone and not threading
    substitutes 7 into it. GEN.4 step 4's falsifier, and the reason `inline_append` carries a
    `topBinders` side condition at all. -/
theorem inlineScan_append_is_threaded :
    ¬ ((inlineScan 1 [("X", 7)] [] (inlineAppendFalsA ++ inlineAppendFalsB)).blks =
       (inlineScan 1 [("X", 7)] [] inlineAppendFalsA).blks ++
        (inlineScan 1 [("X", 7)] [] inlineAppendFalsB).blks) := by
  intro h
  have h1 : readsX ((inlineScan 1 [("X", 7)] []
      (inlineAppendFalsA ++ inlineAppendFalsB)).blks) = true := rfl
  have h2 : readsX ((inlineScan 1 [("X", 7)] [] inlineAppendFalsA).blks
      ++ (inlineScan 1 [("X", 7)] [] inlineAppendFalsB).blks) = false := rfl
  rw [h] at h1
  rw [h2] at h1
  exact absurd h1 Bool.false_ne_true

end Midfall.Lowering.Inline

-- GEN.4: the two new facts are sorry-free, and their axiom sets are the standard three minus
-- `Classical.choice` (the walk is computational).
#print axioms Midfall.Lowering.Inline.inlineScan_append
#print axioms Midfall.Lowering.Inline.inlineScan_append_is_threaded
