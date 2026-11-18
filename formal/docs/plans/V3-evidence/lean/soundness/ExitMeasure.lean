/- MEASUREMENT (scratch): the exit scan of SoundnessV3.lean §4, evaluated on the AST the theorem
   runs at HEAD (asmOf poseidonPv poseidonM 0 0). The scan is copied verbatim from SoundnessV3.lean
   because a scratch file cannot be imported.

   RECON.1b-i: ST.3 landed a scan of the same name in this file's open namespace
   (`Midfall.LoweringV2.exitScan`, Statements.lean:452), so the three measurements below are
   qualified to THIS file's copy - the §4 scan of the design, which is what is being measured.
   (They are not the same function: the landed one treats a `for` POST block as outside the loop,
   §4's copy as inside it, so `break` in a post block is flagged there and not here. The
   measurements start from `false false`, where the two agree.) -/
import Midfall.Instances.PoseidonValid
set_option autoImplicit false
open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Instances.PoseidonValid

def isCommitHalt : EVM.Op → Bool
  | .ret | .stop | .selfdestruct => true
  | _ => false

def exitScan : Nat → Bool → Bool → Scan → Bool
  | 0, _, _, _ => false
  | n + 1, lp, fn, sc =>
    match sc with
    | .e (.lit _) => true
    | .e (.var _) => true
    | .e (.builtin op args) => !isCommitHalt op && exitScan n lp fn (.es args)
    | .e (.call _ args) => exitScan n lp fn (.es args)
    | .es [] => true
    | .es (e :: rest) => exitScan n lp fn (.e e) && exitScan n lp fn (.es rest)
    | .s (.block body) => exitScan n lp fn (.b body)
    | .s (.funDef _ _ _ body) => exitScan n false true (.b body)
    | .s (.letDecl _ none) => true
    | .s (.letDecl _ (some e)) => exitScan n lp fn (.e e)
    | .s (.assign _ e) => exitScan n lp fn (.e e)
    | .s (.cond c body) => exitScan n lp fn (.e c) && exitScan n lp fn (.b body)
    | .s (.switch c cases dflt) =>
        exitScan n lp fn (.e c) && exitScan n lp fn (.cs cases) &&
          (match dflt with | none => true | some d => exitScan n lp fn (.b d))
    | .s (.forLoop init c post body) =>
        exitScan n lp fn (.b init) && exitScan n lp fn (.e c) &&
          exitScan n true fn (.b post) && exitScan n true fn (.b body)
    | .s (.exprStmt e) => exitScan n lp fn (.e e)
    | .s .break => lp
    | .s .continue => lp
    | .s .leave => fn
    | .b [] => true
    | .b (s :: ss) => exitScan n lp fn (.s s) && exitScan n lp fn (.b ss)
    | .cs [] => true
    | .cs ((_, b) :: rest) => exitScan n lp fn (.b b) && exitScan n lp fn (.cs rest)

def progHead : YulBlock := asmOf poseidonPv poseidonM 0 0
def sl (q : Partial) : YulBlock := sliceOf poseidonPv poseidonM q

-- number of top-level statements of the program, and of the seven slices
#eval (progHead.length,
  [Partial.vkLoading, .transcriptParser, .lagrange, .quotientLin, .pcs, .finalPairing, .traceReturn].map
    (fun q => (sl q).length))
-- whole program: must be FALSE (it contains the one `return`)
#eval _root_.exitScan 100000 false false (.b progHead)
-- program without its last statement (the `return` of TraceReturn): must be TRUE
#eval _root_.exitScan 100000 false false (.b progHead.dropLast)
-- the last statement is the `return`
#eval match progHead.getLast? with
  | some (Stmt.exprStmt (Expr.builtin Op.ret _)) => true
  | _ => false
-- everything before the TraceReturn slice (3 statements): must be TRUE
#eval _root_.exitScan 100000 false false (.b (progHead.take (progHead.length - 3)))
-- the TraceReturn slice is the last three statements of the program
#eval (sl .traceReturn).length == 3
