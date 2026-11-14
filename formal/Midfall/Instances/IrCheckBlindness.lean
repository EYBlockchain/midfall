-- |
-- Midfall.Instances.IrCheckBlindness
--
-- P-CSURFACE STEP 2, THE PROBE: WHAT 'irCheck' CANNOT SEE, MADE INTO A GATE.
--
-- THE QUESTION THE BRIEF ASKS. 'Midfall/Yul/ImportSolcIR.lean' pins solc's 'ir' output -
-- the PRE-optimisation textual via-IR - while the DEPLOYED bytecode is the product of the
-- optimizer (the header there records 'memoryguard(128, 160)' in 'ir' against
-- 'memoryguard(0x08e0, 0xa0)' in 'irOptimized', and the shipped bytes agree with the
-- latter). So the model and the artifact already differ by everything the optimizer does.
-- 'LoweringCorrect.ir_refines' is stated under the single hypothesis 'S.irCheck ir = true',
-- and M8 is the package that would have to turn that hypothesis into a simulation. The
-- question this file answers by computation is: IS THAT HYPOTHESIS STRONG ENOUGH TO BE
-- WORTH SIMULATING FROM? Concretely - can 'irCheck' tell the pinned IR apart from an IR
-- that is NOT equivalent to it?
--
-- THE ANSWER, MEASURED: NO, AND NOT MARGINALLY. 'Surface.irCheck' (Lowering/Surface.lean)
-- is a projection of 'Surface.runtimeName' onto a two-clause test: the named runtime
-- sub-object EXISTS, and no TOP-LEVEL statement calls a user function the TOP LEVEL does
-- not declare. Everything below is a mutation of the real imported runtime that the
-- optimizer performs or undoes, that is NOT alpha-equivalent to the artifact, and that
-- 'irCheck' accepts unchanged:
--
--   * 'mutAlpha' - every helper renamed, call sites rewritten with it. Semantically the
--     identity; 'irCheck' cannot even see that it is a rename, in either direction.
--   * 'mutFold' - a top-level store address wrapped in 'add x 0', the inverse of a real
--     optimizer fold. Accepted.
--   * 'mutRevertLen' - a revert DATA LENGTH changed inside every helper body: 0 -> 32.
--     That is a different revert return data, i.e. a different observable, and 'irCheck'
--     accepts it because it never descends into a function body.
--   * 'mutDeleteInside' - the first statement of every helper body deleted. Accepted,
--     for the same reason.
--   * 'mutCreation' - the CREATION object's code mutated ('codecopy' size changed).
--     Accepted, because 'irCheck' looks only at the deployed sub-object, and the creation
--     code is what decides what gets deployed at all.
--
--   Against 'mutBroken' - the planted rename, a declaration renamed with its call sites
--   left alone - 'irCheck' does say false, and that is the whole of what it detects.
--
-- WHAT THIS BOUNDS, and this is the finding the scoping note carries into the ledger.
-- 'irCheck' is a LINKING sanity check on one object's top-level name resolution. It is not
-- an equivalence check, not even a partial one: there is no Prop it expresses, short of
-- 'this object has a runtime sub-object whose undeclared top-level calls are absent', from
-- which 'the IR refines the shell model' could be read. So M8 cannot be 'prove ir_refines
-- from irCheck'. Either the hypothesis is STRENGTHENED - to a real translation relation
-- between the imported object and the shell, which is a construction and not a check - or
-- the trusted hop is stated as what it is: an assumption about solc, discharged by
-- differential testing against the compiler and not by a theorem in this tree. The second
-- is the honest reading of PLAN section 7's 'irCheck validates the unoptimised IR'.
--
-- WHY THIS IS A GATE AND NOT ONLY A NOTE. Every claim above is a '#eval' line with an
-- 'expect', so 'scripts/kat_gate.py' runs it: if 'irCheck' is ever strengthened to see
-- into function bodies, or narrowed so it rejects the artifact, this gate goes red and the
-- scoping note has to be rewritten rather than left to rot. That is the R-41 discipline -
-- a finding that cannot fail is a finding that will be stale.
--
-- WHY IN Instances/. 'irCheck' is a projection of a 'Surface', and a Surface needs an
-- 'AdmissiblePairing', so the object whose check is being exercised has to come from a
-- Surface in this directory (D-P17). Nothing outside Instances/ cites this file.

import Midfall.Lowering.Surface
import Midfall.Instances.SurfaceFixture
import Midfall.Instances.ImportedIR
import Midfall.Yul.ImportSolcIR

namespace Midfall.Instances.IrCheckBlindness
open Midfall Midfall.Yul Midfall.Lowering Midfall.Yul.Bridge Midfall.Yul.Ir
open Midfall.Instances Midfall.Instances.SurfaceFixture Midfall.Instances.ImportedIR
open YulSemantics YulSemantics.EVM

/-- The imported deployed runtime, exactly as the artifact has it: 28 top-level
    statements, of which the first two run and the rest are definitions. -/
def irRt : YulBlock := verifierRuntime

/-- Replace the runtime sub-object of the imported object, leaving name, creation code,
    the other sub-objects and the data segments alone. -/
def withRuntime (b : YulBlock) : YulObject :=
  Object.mk verifierIr.name verifierIr.codeBlock
    (verifierIr.subObjects.map fun o =>
      if o.name == verifierRuntimeName then Object.mk o.name b o.subObjects o.dataSegs else o)
    verifierIr.dataSegs

/-- **M1, ACCEPTED AND NOT EQUIVALENT-BY-SYNTAX: a full alpha-rename.** Every declared
    helper gets a prefix and every call to it, at the top level and inside bodies, is
    rewritten with it. This is the one mutation that IS semantically the identity, and it
    is here to show the other direction of the blindness: 'irCheck' cannot confirm a
    rename either. -/
def mutAlpha : YulBlock :=
  let names := declaredTops irRt
  irRt.map fun s => match s with
    | Stmt.funDef n ps rs body =>
        Stmt.funDef ("solc_" ++ n) ps rs
          (body.map fun t => match t with
            | Stmt.exprStmt (Expr.call c args) =>
                Stmt.exprStmt (Expr.call (if names.contains c then "solc_" ++ c else c) args)
            | u => u)
    | Stmt.exprStmt (Expr.call c args) =>
        Stmt.exprStmt (Expr.call (if names.contains c then "solc_" ++ c else c) args)
    | _ => s

/-- **M2, ACCEPTED AND NOT EQUIVALENT: the inverse of a constant fold.** A top-level
    store's address becomes 'add addr 0', which the solc optimizer collapses. The call is
    NESTED inside the statement, and 'unresolvedTop' only looks at calls in statement
    position and let-initialisers, so a nested undeclared call is invisible to it. -/
def mutFold : YulBlock :=
  irRt.map fun s => match s with
    | Stmt.exprStmt (Expr.builtin Op.mstore [a, e]) =>
        Stmt.exprStmt (Expr.builtin Op.mstore
          [Expr.call "add" [a, Expr.lit (.number 0)], e])
    | _ => s

/-- **M3, ACCEPTED AND DIFFERENTLY OBSERVABLE: a revert return-data length.** Every
    'revert(p, 0)' inside a helper body becomes 'revert(p, 32)'. Return data is part of
    'ObsView', so this is a difference the headline theorems can SEE and the import check
    cannot. This is the sharpest of the five: it is not a layout detail, it is a
    different answer to the call. -/
def mutRevertLen : YulBlock :=
  irRt.map fun s => match s with
    | Stmt.funDef n ps rs body =>
        Stmt.funDef n ps rs (body.map fun t => match t with
          | Stmt.exprStmt (Expr.builtin Op.revert [a, Expr.lit (.number 0)]) =>
              Stmt.exprStmt (Expr.builtin Op.revert [a, Expr.lit (.number 32)])
          | u => u)
    | _ => s

/-- **M4, ACCEPTED AND DIFFERENTLY OBSERVABLE: a statement deleted from every helper
    body.** Dead-store elimination in reverse: the first statement of each body is
    dropped. 'irCheck' never descends into a body, so it cannot see a body change at all. -/
def mutDeleteInside : YulBlock :=
  irRt.map fun s => match s with
    | Stmt.funDef n ps rs body =>
        match body with
        | [] => s
        | _ :: rest => Stmt.funDef n ps rs rest
    | _ => s

/-- **M5, ACCEPTED AND DIFFERENT: the CREATION object mutated.** The 'codecopy' size in
    the constructor is changed. 'irCheck' reads only the deployed sub-object, so the code
    that decides what gets deployed is entirely outside its scope - and the deployment
    pins in 'DeploymentW' are about the runtime image, not about the constructor. -/
def mutCreation : YulObject :=
  Object.mk verifierIr.name
    (verifierIr.codeBlock.map fun s => match s with
      | Stmt.exprStmt (Expr.builtin Op.codecopy [a, b, _]) =>
          Stmt.exprStmt (Expr.builtin Op.codecopy [a, b, Expr.lit (.number 4096)])
      | _ => s)
    verifierIr.subObjects verifierIr.dataSegs

/-- **THE CONTROL: the planted rename, which 'irCheck' DOES reject.** Without this the
    five acceptances above could be read as 'irCheck always returns true on this object'.
    It does not: rename a declaration and leave its call site and the top-level scan sees
    an unresolved call. That is the whole of its power, and it is real. -/
def mutBroken : YulBlock :=
  irRt.map fun s => match s with
    | Stmt.funDef n ps rs body => Stmt.funDef ("solc_" ++ n) ps rs body
    | _ => s

/-- **THE PROBE, AS A GATE.** Five non-equivalent mutants accepted, the planted rename
    rejected, the artifact accepted, and each mutant PROVED-BY-COMPUTATION different from
    the artifact under the structural comparator the tree uses for AST equality. Every
    line is load-bearing: the 'irCheck' lines are the blindness, the 'stmtsBeq' lines are
    the non-equivalence, and the last block is the control. -/
def irCheckBlindness_ok : Bool :=
  -- the artifact itself, and the control
  irSurface.irCheck verifierIr &&
    ! irSurface.irCheck (withRuntime mutBroken) &&
    -- the five mutants, all accepted
    irSurface.irCheck (withRuntime mutAlpha) &&
    irSurface.irCheck (withRuntime mutFold) &&
    irSurface.irCheck (withRuntime mutRevertLen) &&
    irSurface.irCheck (withRuntime mutDeleteInside) &&
    irSurface.irCheck mutCreation &&
    -- and none of them is the artifact, under the tree's own structural comparator
    ! SyntaxEq.stmtsBeq mutAlpha irRt &&
    ! SyntaxEq.stmtsBeq mutFold irRt &&
    ! SyntaxEq.stmtsBeq mutRevertLen irRt &&
    ! SyntaxEq.stmtsBeq mutDeleteInside irRt &&
    ! SyntaxEq.stmtsBeq mutCreation.codeBlock verifierIr.codeBlock &&
    -- the shape facts that make the mutations non-trivial rather than vacuous
    irRt.length == 28 && mutAlpha.length == 28 && mutFold.length == 28 &&
    mutRevertLen.length == 28 && mutDeleteInside.length == 28 &&
    (declaredTops irRt).length > 0 &&
    -- the revert arm really is inside a body and not at the top level, which is WHY M3
    -- is invisible: the top level has no revert builtin at all
    (irRt.any fun s => match s with
      | Stmt.exprStmt (Expr.builtin Op.revert _) => true
      | _ => false) == false &&
    (mutRevertLen.any fun s => match s with
      | Stmt.funDef _ _ _ body =>
          body.any fun t => match t with
            | Stmt.exprStmt (Expr.builtin Op.revert [_, Expr.lit (.number 32)]) => true
            | _ => false
      | _ => false) == true

#eval irCheckBlindness_ok                  -- expect true

/-- **THE BLINDNESS IS A THEOREM ABOUT THE DEFINITION, NOT ONLY A TABLE OF CASES.**
    'Surface.irCheck' factors through 'unresolvedTop', and 'unresolvedTop' reads only the
    TOP-LEVEL statements of the runtime sub-object: a call in statement position, or a
    call in a let-initialiser, against the names the top level declares. So two runtime
    blocks whose top-level resolution agrees are INDISTINGUISHABLE to the check whatever
    their function bodies say. That is the general fact the five cases above instantiate,
    and it is what bounds M8: the hypothesis 'irCheck ir = true' constrains the top-level
    name resolution of one object and nothing else, so 'ir_refines' cannot be recovered
    from it by any amount of proof work. Stated as a theorem so the bound cannot be argued
    away as an artefact of the five mutations chosen. -/
theorem irCheck_eq_of_top_level_agreement (b₁ b₂ : YulBlock)
    (h : unresolvedTop b₁ = unresolvedTop b₂) :
    irSurface.irCheck (withRuntime b₁) = irSurface.irCheck (withRuntime b₂) := by
  have e₁ : irSurface.irCheck (withRuntime b₁) = ! unresolvedTop b₁ := rfl
  have e₂ : irSurface.irCheck (withRuntime b₂) = ! unresolvedTop b₂ := rfl
  rw [e₁, e₂, h]

/-- **AND THE FOUR RUNTIME MUTANTS DO AGREE WITH THE ARTIFACT ON EXACTLY THAT.** Each has
    no unresolved top-level call, which is the whole of why each passes. This is the
    hypothesis of the theorem above, discharged by computation rather than asserted, so
    the general statement and the five cases are the same fact and not two lists. -/
theorem five_cases_agree_on_what_irCheck_reads :
    unresolvedTop mutAlpha = unresolvedTop irRt ∧
      unresolvedTop mutFold = unresolvedTop irRt ∧
      unresolvedTop mutRevertLen = unresolvedTop irRt ∧
      unresolvedTop mutDeleteInside = unresolvedTop irRt ∧
      unresolvedTop irRt = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **THE CONSEQUENCE FOR M8, AS A DERIVED EQUALITY, NOT A PARAGRAPH.** The artifact and
    the revert-length mutant - which returns DIFFERENT DATA from the same call, an
    'ObsView' difference the headline theorems can observe - are indistinguishable to the
    only hypothesis 'ir_refines' carries. If 'ir_refines' is true of the artifact and the
    shell model, the same statement is NOT forced true of this mutant by 'irCheck', and
    that is the gap M8 has to close or widen the hypothesis to close. -/
theorem irCheck_cannot_separate_the_revert_length_mutant :
    irSurface.irCheck (withRuntime mutRevertLen) = irSurface.irCheck verifierIr :=
  irCheck_eq_of_top_level_agreement mutRevertLen irRt rfl

/-! ### The decisive case: two objects, one check, different observables -/

/-- **A RUNTIME BLOCK THAT RETURNS 32 BYTES.** One top-level statement, no unresolved
    call, so 'irCheck' says true. -/
def irRet : YulObject :=
  withRuntime [Stmt.exprStmt (Expr.builtin Op.ret
    [Expr.lit (.number 0), Expr.lit (.number 32)])]

/-- **A RUNTIME BLOCK THAT REVERTS 0 BYTES.** Also one top-level statement, also no
    unresolved call, also accepted. -/
def irRev : YulObject :=
  withRuntime [Stmt.exprStmt (Expr.builtin Op.revert
    [Expr.lit (.number 0), Expr.lit (.number 0)])]

/-- The runtime block of one of these objects, as a projection. -/
def runtimeOf (o : YulObject) : YulBlock :=
  match o.subObject verifierRuntimeName with
  | some s => s.codeBlock
  | none => []

/-- **THE HALT KIND THE FIRST STATEMENT OF EACH PRODUCES.** A one-line reader, used only
    to state the difference below as a decidable fact rather than as prose. -/
def firstHalt (b : YulBlock) : Option HaltKind := match b with
  | Stmt.exprStmt (Expr.builtin Op.ret _) :: _ => some HaltKind.ret
  | Stmt.exprStmt (Expr.builtin Op.revert _) :: _ => some HaltKind.revert
  | _ => none

/-- **BOTH PASS THE CHECK.** 'rfl' for each: the hypothesis 'ir_refines' takes is
    satisfied by a program that returns and by a program that reverts, with no other
    difference at all. -/
theorem irCheck_accepts_both_outcomes :
    irSurface.irCheck irRet = true ∧ irSurface.irCheck irRev = true := ⟨rfl, rfl⟩

/-- **AND THEY HAVE DIFFERENT OBSERVABLES.** One halts by returning 32 bytes, the other
    by reverting none. 'HaltKind.ret' and 'HaltKind.revert' are different constructors,
    and the halt kind is exactly what 'Obs.isRevertOrHalt' and 'Obs.returnData' read, so
    this is a difference at the level 'ObsEquiv' compares at - the level 'ir_refines' is
    stated at. -/
theorem irCheck_admits_different_observables :
    firstHalt (runtimeOf irRet) ≠ firstHalt (runtimeOf irRev) := by
  intro e
  exact HaltKind.noConfusion (Option.some.inj e)

/-- **THE GENERAL SHAPE, SO THE TWO CASES ABOVE CANNOT BE CALLED UNLUCKY.** 'irCheck'
    factors through 'unresolvedTop' on the runtime sub-object and nothing else, so ANY
    block whose top-level calls all resolve is accepted - whatever it computes, whatever
    it returns, and whether it mentions the verifier at all. That is the whole of the
    hypothesis 'LoweringCorrect.ir_refines' carries about the imported object, and it is
    why M8 cannot be 'prove ir_refines from irCheck': there is no content in irCheck to
    simulate FROM. -/
theorem irCheck_accepts_any_top_level_clean_block (b : YulBlock)
    (h : unresolvedTop b = false) : irSurface.irCheck (withRuntime b) = true := by
  have key : irSurface.irRuntime (withRuntime b) = some b := rfl
  show ! (unresolvedTop b = true) = true
  rw [h]
  rfl

/-- **AND THE ARTIFACT IS ONE OF THEM**, which is what makes the previous line a
    statement about the check's reach rather than about a broken check: it does accept the
    object it is supposed to accept, and it accepts everything else too. -/
theorem irCheck_accepts_the_artifact : unresolvedTop irRt = false := rfl

end Midfall.Instances.IrCheckBlindness
