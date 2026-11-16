/-
  Midfall.LoweringV2.Shared

  VERBATIM copies of the v1 definitions the V2 statement surface needs, so that the V2 cone reaches
  none of the retired v1 lowering chain (EXECUTION-V2 section 6, ticket Q0.2). The originals stay
  where they are - v1 gates read them, so nothing was moved: these are copies, and each is
  character-for-character the definition it names. The only addition is a section variable that a
  copy needs and its source file supplied by 'variable'.

    Midfall/Lowering/Surface.lean     ptReadable (:512), initState (:728), ZeroAbove (:757)
    Midfall/Lowering/Partials.lean    revertedOf (:93), Reverted (:99)
    Midfall/Lowering/Accumulator.lean frOfWord? (:1401), instOfWords? (:1407)
    Midfall/Lowering/FrameWalk.lean   freeNames (:586) with boundE/boundS/boundSs/boundSC
                                      (:511-539) and refE/refS/refSs/refSC (:545-577)
-/
import Midfall.Common.Bytes
import Midfall.Common.Curve
import Midfall.Common.Word
import Midfall.Halo2.Exec.Native
import Midfall.Yul.Bridge
import Midfall.Yul.Externals
import YulSemantics.Syntax
import YulSemantics.ObjectRun

namespace Midfall.LoweringV2

open Midfall Midfall.Halo2 YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-! ### From Midfall/Lowering/Surface.lean
-/


/-- The codec-side readability of one embedded G1 point, factored out so the forall in
    vkPoints stays readable: the EIP-2537 bytes parse, and what they parse to is a
    point the MSM precompile accepts rather than a non-canonical word. Both halves are
    computable (Externals.lean:476, :512), so a gate can point at the one that fails. -/
def ptReadable (b : Bytes) : Prop :=
  ∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true

/-- A revert as the EVM state records it (EVMExec.lean:844-846): the halt kind is
    revert and the returned bytes are whatever the failing arm passed. Every
    fail(ERR_*) in a partial ends here, and the soundness post is a disjunction whose
    left arm is this - the right arm being the next checkpoint.

    Bool-valued with the Prop as the wrapper, the way stage 3 made Inv decidable: the
    gate below has to CHECK that a return record is not a revert, and a bare exists
    over a halt payload cannot be evaluated. -/
def revertedOf (h : Option (HaltKind × List UInt8)) : Bool :=
  match h with
  | some (.revert, _) => true
  | _ => false

/-- Reverted st: the frame halted by reverting. -/
def Reverted (st : EvmState) : Prop := revertedOf st.halted = true

/-- The assembly entry frame: arbitrary initial memory mem0 (verifier_sound is stated
    for ANY mem0, which is why the g1_identity window is an Inv clause rather than an
    assumption about zeroed memory), the calldata, the world W, the hash H, and the
    shell layout for the data and immutable maps. Every other field comes from W, so
    callvalue and static are deployment facts rather than frame facts, which is what
    makes DeploymentW the right home for them. -/
def initState (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes)
    (mem₀ : Nat → UInt8) : EvmState :=
  { EvmState.init with
    memory := mem₀
    env := { W with
      calldata := cd.data.toList
      code := Lyt.code
      dataOffset := Lyt.dataOffset
      dataSize := Lyt.dataSize
      immutable := Lyt.immutable
      keccakOf := hashOfBytes H } }


/-- Memory that is zero from 0x80 up: the attack FIX 1 hypothesis. The solc dispatcher
    writes only mem[0x00..0x80), so everything above is whatever the caller left, and
    the counterexample in attack.md is a caller that left a non-identity
    committed-instance commitment in the g1_identity window.

    R-58 F9 deleted the Bool-valued sampler that used to sit here
    (memoryZeroAbove, four addresses plus a KAT). Nothing consumed it: every theorem
    takes the Prop below, so the sample was decoration and its gate was a gate about
    the sample, not about the hypothesis. ZeroAbove stays a Prop because it IS the
    hypothesis, and a decidable stand-in for a forall over all memory would be a
    different and weaker claim, not a check of this one. -/
def ZeroAbove (mem₀ : Nat → UInt8) : Prop := ∀ a, 0x80 ≤ a → mem₀ a = 0


/-! ### From Midfall/Lowering/Accumulator.lean

    The source file supplies 'p' and its primality by 'variable'; the copy states them explicitly.
-/

variable {p : ℕ} [Fact (Nat.Prime p)]


/-- The contract's canonicality gate on one instance word
    (TranscriptProofParser.yul:63-68: lt(inst_be, r)). A word at or above p is
    none, not a reduction - that is the R-26.7 point. -/
def frOfWord? (w : Word256) : Option (Fr p) :=
  if w.toNat < p then some (Nat.cast w.toNat) else none

/-- The same gate lifted over the whole instance array. ContractRefAcceptsAcc below
    takes instW : Array Word256 rather than Array (Fr p) precisely so this rejection
    stays visible. -/
def instOfWords? (ws : Array Word256) : Option (Array (Fr p)) :=
  (ws.toList.mapM frOfWord?).map List.toArray


/-! ### From Midfall/Lowering/FrameWalk.lean
-/


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

end Midfall.LoweringV2
