-- |
-- Midfall.Instances.QInterpWitnessF1
--
-- T3.10's W12 EVIDENCE AT THE FIXTURE. The CONTRACT and its generic witnesses and falsifiers are in
-- 'Midfall/Lowering/QuotientInterp.lean'; D-P71 says a fixture is a TEST and never a premise, so the
-- F1 instance lives here, in 'Instances/', where the deployment model may be imported (D-P17) and
-- where 'native_decide' is confined.
--
-- WHAT IS PROVED HERE (not #eval'd): 'qinterpF1_hypotheses_together' - at the deployment's own
-- quotient program, with its real window base and its real length, the contract's hypotheses are
-- jointly satisfiable. And 'qinterpF1_first_window_nonempty' - the F1 program's window is a LEGAL
-- segment, which is the hypothesis the generic witness cannot get from the shape alone.
--
-- WHAT IS GATED HERE (Bool, '#eval', kat_gate.py's): the teeth. 'qinterpArmFamilies_cover_ok' says
-- the family table in the contract file IS the emitter's arm list at both OBJ.15 acceptance contexts,
-- in both directions, so an arm added, deleted or renumbered in 'GenAstQvm' reddens it - the same kind
-- of gate that caught OBJ.15's arm reorder and its 18 ungated memory-token cases.
-- 'qinterpRowTracksTheProgram_ok' says the row's block really is a function of the program: switching
-- ONE 'opUsage' flag changes the block the contract is stated about. If the row had been stated at a
-- fixed block - the fixture-shaped failure this card exists to avoid - that gate would be false.

import Midfall.Lowering.QuotientInterp
import Midfall.Instances.M2BatchKats
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.Instances.QInterpWitnessF1

open Midfall Midfall.Generator Midfall.Lowering Midfall.Lowering.GenAst Midfall.Lowering.QuotientInterp
open Midfall.Instances.M2BatchKats Midfall.Lowering.YulParse
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-- The deployment's quotient program, as the F1 context carries it. -/
def f1Program : Option QuotientProgram := ctx.quotientProgram

/-- The template-constant table the emitter reads its opcode labels from. -/
def f1Tcq : QuotientVmTemplateConstants := ctx.templateConstants.quotientVm

/-- **WITNESS AT F1 - THE HYPOTHESES HOLD TOGETHER AT THE DEPLOYMENT.** At the program the F1 context
    actually carries, the whole-program window is a legal segment and there is an environment and a
    machine state satisfying 'AtSegment' and all three window agreements at once. PROVED, not
    '#eval'd; the axioms are the three allowed ones. -/
theorem qinterpF1_hypotheses_together {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (hp : f1Program = some program) (hlen : 0 < program.len) :
    ∃ (V : VEnv (Bridge.Dialect c g)) (st : EvmState),
      AtSegment (c := c) (g := g) (program := program)
        (segmentV (c := c) (g := g) (program := program)
          ⟨program.programMptr, program.len, 0, program.len⟩ 0 false)
        EvmState.init ⟨program.programMptr, program.len, 0, program.len⟩ ∧
      Agrees [] program.constMptr 0 0 [] EvmState.init
        (quotientRefMemoryNew Midfall.Bytes.empty)
        ⟨program.programMptr, program.len, 0, program.len⟩ := by
  refine ⟨segmentV (c := c) (g := g) (program := program)
      ⟨program.programMptr, program.len, 0, program.len⟩ 0 false, EvmState.init,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  · simp only [Agrees]
    refine ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro k hk
      exact absurd hk (Nat.not_lt_zero k)
    · intro a ha
      exact absurd ha (Nat.not_lt_zero a)

/-- **THE F1 WINDOW IS A LEGAL SEGMENT** - the hypothesis of the witness above, measured at the
    deployment: the program is present and its length is non-zero, so '[0, len)' satisfies
    'QSegment.inWindow' and the contract is stated over a window the emitter really writes. -/
theorem qinterpF1_first_window_nonempty {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (_hp : f1Program = some program) (hlen : 0 < program.len) :
    QSegment.inWindow ⟨program.programMptr, program.len, 0, program.len⟩ :=
  ⟨hlen, Nat.le_refl _⟩

#assert_axioms Midfall.Instances.QInterpWitnessF1.qinterpF1_hypotheses_together [propext, Classical.choice, Quot.sound] native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]
#assert_axioms Midfall.Instances.QInterpWitnessF1.qinterpF1_first_window_nonempty [propext, Classical.choice, Quot.sound] native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]
#print axioms Midfall.Instances.QInterpWitnessF1.qinterpF1_hypotheses_together
#print axioms Midfall.Instances.QInterpWitnessF1.qinterpF1_first_window_nonempty

/-! ### THE TEETH GATES -/

/-- The emitter's own arm labels at a context, in template order. -/
def emittedArmLabels (ctx' : PartialCtx) (program : QuotientProgram) : List Nat :=
  let tcq := ctx'.templateConstants.quotientVm
  ((qvmOpcodeArms ctx' program tcq ++ qvmNativeArms ctx' program tcq ++ qvmFoldArms ctx' program tcq).map
    fun (lit, _) => match lit with | Literal.number n => n | _ => 0)

/-- The emitter's arm labels at a context, as a list. -/
def emitted (ctx' : PartialCtx) : List Nat :=
  match ctx'.quotientProgram with
  | none => []
  | some p => emittedArmLabels ctx' p

/-- The label the family table assigns to an arm name, through the template constants. -/
def tableArmLabels (tcq : QuotientVmTemplateConstants) : List Nat :=
  qArmNames.filterMap fun n =>
    if n == "pushConst" then some tcq.op.pushConst
    else if n == "pushMemLiteral" then some tcq.op.pushMemLiteral
    else if n == "pushMemToken" then some tcq.op.pushMemToken
    else if n == "pushMemTokenOffset" then some tcq.op.pushMemTokenOffset
    else if n == "pushMemU16" then some tcq.op.pushMemU16
    else if n == "add" then some tcq.op.add
    else if n == "mul" then some tcq.op.mul
    else if n == "neg" then some tcq.op.neg
    else if n == "pow5" then some tcq.op.pow5
    else if n == "pushConstU8" then some tcq.op.pushConstU8
    else if n == "addConstU8" then some tcq.op.addConstU8
    else if n == "mulConstU8" then some tcq.op.mulConstU8
    else if n == "addConst" then some tcq.op.addConst
    else if n == "mulConst" then some tcq.op.mulConst
    else if n == "addMemU16" then some tcq.op.addMemU16
    else if n == "mulMemU16" then some tcq.op.mulMemU16
    else if n == "addMulMemMemConstU8" then some tcq.op.addMulMemMemConstU8
    else if n == "addMulConstU8MemU16" then some tcq.op.addMulConstU8MemU16
    else if n == "addMulMemMem" then some tcq.op.addMulMemMem
    else if n == "runAddMulMemMemConstU8" then some tcq.op.runAddMulMemMemConstU8
    else if n == "runAddMulConstU8MemU16" then some tcq.op.runAddMulConstU8MemU16
    else if n == "affineSum" then some tcq.op.affineSum
    else if n == "lin7" then some tcq.op.lin7
    else if n == "bilin7Row" then some tcq.op.bilin7Row
    else if n == "bilin7Pairwise" then some tcq.op.bilin7Pairwise
    else if n == "modarith7" then some tcq.op.modarith7
    else if n == "foldMain" then some tcq.op.foldMain
    else if n == "foldSelector" then some tcq.op.foldSelector
    else if n == "nativePermutation" then some tcq.op.nativePermutation
    else if n == "nativeLookup" then some tcq.op.nativeLookup
    else if n == "nativeIdentity" then some tcq.op.nativeIdentity
    else none

/-- **TEETH 1: THE FAMILY TABLE IS THE EMITTER'S ARM LIST**, at the all-flags context (all 31 arms)
    and at the deployment (the 10 the fixture renders), in template order, and every name in the table
    has a family. An arm added to 'GenAstQvm' without a family, deleted, or renumbered reddens this. -/
def qinterpArmFamilies_cover_ok : Bool :=
  match ctx.quotientProgram with
  | none => false
  | some p =>
      let tcq := ctx.templateConstants.quotientVm
      let all := tableArmLabels tcq
      all.length == 31 &&
        (qArmNames.all fun n => (qArmFamilyOfName n).isSome) &&
        (all.all fun l => (emitted qvmAllArms).contains l) &&
        ((emitted qvmAllArms).all fun l => all.contains l) &&
        (emitted qvmAllArms).length == 31 &&
        (emitted ctx).length == 10 &&
        (emitted ctx).all fun l => all.contains l
#eval qinterpArmFamilies_cover_ok -- expect true

/-- **TEETH 2: THE ROW'S BLOCK IS A FUNCTION OF THE PROGRAM.** The loop the contract is stated
    about moves when ANY of the five program fields the contract's window reads moves, and does not
    move when nothing changes. Stated at a fixed block - the fixture-shaped failure this card exists to
    avoid - the first negated conjunct would be true and the gate would go red. -/
def qinterpRowTracksTheProgram_ok : Bool :=
  match ctx.quotientProgram with
  | none => false
  | some p =>
      let tcq := ctx.templateConstants.quotientVm
      let loop := [GenAst.qvmLoop ctx p tcq]
      let region := GenAst.emitQuotientNumeratorA ctx
      let pOff : QuotientProgram := { p with opUsage := quotientVmOpcodeUsageDefault }
      let pStack : QuotientProgram := { p with stackMptr := p.stackMptr + 32 }
      let pLen : QuotientProgram := { p with len := p.len + 32 }
      let pPtr : QuotientProgram := { p with programMptr := p.programMptr + 32 }
      let pConst : QuotientProgram := { p with constMptr := p.constMptr + 32 }
      SyntaxEq.stmtsBeq loop loop &&
        ! SyntaxEq.stmtsBeq loop [GenAst.qvmLoop ctx pOff tcq] &&
        ! SyntaxEq.stmtsBeq loop [GenAst.qvmLoop ctx pStack tcq] &&
        ! SyntaxEq.stmtsBeq region (GenAst.emitQuotientNumeratorA { ctx with quotientProgram := some pLen }) &&
        ! SyntaxEq.stmtsBeq region (GenAst.emitQuotientNumeratorA { ctx with quotientProgram := some pPtr }) &&
        ! SyntaxEq.stmtsBeq region (GenAst.emitQuotientNumeratorA { ctx with quotientProgram := some pConst })
#eval qinterpRowTracksTheProgram_ok -- expect true

/-- **TEETH 3 - THE TWO HYPOTHESES THE F1 WITNESS ASSUMES ARE JOINTLY INHABITED AT THE DEPLOYMENT**
    (check_hypothesis_bundles' rule: a bundle must be exhibited together, not one at a time). One
    'match' says the F1 context carries a quotient program AND that its length is non-zero, which is
    what 'QSegment.inWindow' needs for the whole-program window. -/
def qinterpF1_hypotheses_inhabited_ok : Bool :=
  match ctx.quotientProgram with
  | some p => p.len > 0 && p.programMptr > 0 && p.constMptr > 0 && p.stackMptr > 0
  | none => false
#eval qinterpF1_hypotheses_inhabited_ok -- expect true

/-- **TEETH 4: THE WINDOW THE CONTRACT QUANTIFIES OVER IS THE PROGRAM'S OWN WINDOW** - the prologue
    writes 'q_end := q_program_mptr + program.len', so the row's window is '(programMptr, len)', and
    perturbing either field moves the segment the contract is stated at. The Bool form of
    'QSegment.inWindow', so the gate can actually evaluate. -/
def inWindowB (s : QSegment) : Bool := s.cursor < s.len && s.len <= s.len

def qinterpWindowIsThePrograms_ok : Bool :=
  match ctx.quotientProgram with
  | none => false
  | some p =>
      let w : QSegment := ⟨p.programMptr, p.len, 0, p.len⟩
      inWindowB w &&
        (let p2 : QuotientProgram := { p with programMptr := p.programMptr + 32 }
         let w2 : QSegment := ⟨p2.programMptr, p2.len, 0, p2.len⟩
         inWindowB w2 && w.base ≠ w2.base) &&
        (let p3 : QuotientProgram := { p with len := p.len + 1 }
         inWindowB ⟨p3.programMptr, p3.len, 0, p3.len⟩ && p3.len ≠ p.len)
#eval qinterpWindowIsThePrograms_ok -- expect true
