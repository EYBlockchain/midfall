-- |
-- Midfall.Lowering.GenAstDispatch
--
-- P-PLANVIEW: the dispatch that sees all seven partials, and the pcs slice wired into it.
--
-- WHY THIS FILE EXISTS AT ALL, and it is an import direction and not a tidy-up. The
-- generator function the blk pin pins to is 'emitPartial : PlanView -> Partial -> Block Op',
-- and it has to reach EVERY partial's emitter. Six of them live in
-- Midfall/Lowering/GenAst.lean. The seventh - the Kzg multi-prepare body - lives in
-- Midfall/Lowering/GenAstPcs.lean, which IMPORTS GenAst (its own gates need the constructor
-- helpers, mapStmtExprs and stmtIsFor). So the dispatch cannot stay in GenAst: GenAst
-- importing GenAstPcs is a cycle, and the alternatives churn two other packages' files -
-- moving 550 lines of PCS definitions into GenAst, or moving the constructor helpers out to
-- a fourth module so the direction can flip - to relocate one arm of a match. A module that
-- sits ABOVE both and re-exports the dispatch under the SAME names is the smallest honest
-- move: Midfall.Lowering.GenAst.emitPartial, .emitMain, .emitSlices, .emittedPartials,
-- .placeholderPartials and .partialIsEmitted are unchanged as identifiers, because a Lean
-- namespace is not a file. Nothing downstream was renamed, and
-- scripts/check_statement_fingerprints.py's BlkIsEmitter fragments still match verbatim.
--
-- WHAT CHANGED IN THE DISPATCH ITSELF. 'emitPartial' used to end in a wildcard arm falling
-- through to emitPlaceholder, and the wildcard was load-bearing for exactly one partial:
-- pcs. The arm is now explicit and the match is exhaustive over the seven constructors, so
-- emitPlaceholder has NO caller inside the emitter. It survives as a def because the
-- falsification plants in Instances/SurfaceFixture.lean need a block to plant, and because
-- the other six placeholders are still what those plants compare against. D-P30 clause 4 is
-- satisfied in its stronger half: unreachable by the dispatcher, not merely documented as
-- wrong. 'placeholderPartials' is empty and placeholderPartials_nil PROVES it.
--
-- THE TWO INPUTS, AND THE RULE THAT GOVERNS THEM. computationsAst needs a
-- ConstraintSystemMeta and a Data, and PlanView carried neither; it carries both now
-- (Inv.lean, PlanView.meta_ and PlanView.dat). DERIVE, NEVER OBSERVE, applied honestly: the
-- meta and Data these gates run on are the Kzg FIXTURE's - Encoding.lean's metaFixture,
-- which is ConstraintSystemMeta.new over Protocol.lean's fixtureCs, and dataFixture, which
-- is Data.new over that meta - so they are a circuit the generator describes, not numbers
-- read off a dump. The DEPLOYED poseidon meta and Data are the opposite: observations of the
-- artifact, confined to Instances/DeployedProfile.lean, which this file must not import (the
-- Instances confinement gate greps the import, and this file states a theorem).
--
-- THE CIRCUIT-GAP FINDING, measured rather than asserted. Carrying the two fields does NOT
-- make the deployed PCS region emittable, and the reason is narrower than the previous
-- package thought: poseidonMeta's PROTOCOL field is the default, because
-- ProtocolPlan::from_constraint_system needs the halo2 ConstraintSystem of the circuit and
-- that is not in this tree. intermediateSets walks the protocol's query schedule, so an
-- empty protocol means no point set means the KZ:943-945 early return means the deployed
-- plan view emits NOTHING. Seven of seven partials are now emitted by a real AST function;
-- the further claim that the function reproduces the deployed bytes is owed by the circuit,
-- not by the generator. DeployedProfile.pcs_deployedGap_measured_ok is that sentence as a
-- computation.
--
-- WHAT THE TAGGING IS FOR. The vendored AST has no comment node, so the eight-block
-- partition the text emitter identified with leading comments survives only positionally.
-- pcsTaggedFromPlan re-derives the ROLE LIST from the plan (set count and x1-power count,
-- both read off the meta and the Data rather than passed in) and zips it onto the emitted
-- blocks; emitPcsTagging_ok pins that the zip is total, that flattening it gives back
-- exactly what the dispatcher returns, and that the block tagged pairingInputs is the one
-- that writes PAIRING_RHS_MPTR. That is the partition as an inductable structure with the
-- comment's values carried beside it.
--
-- NAMING NOTE FOR THE TAGGING: PcsBlockRole, pcsBlockRoles, pcsTaggedBlocks and writesTo are
-- declared inside GenAstPcs's Kats namespace (GenAstPcs.lean:1035-1072), i.e. in the gate
-- namespace rather than the definition namespace, because P-STR2AST wrote them as part of its
-- gate section. This file therefore spells them GenAstPcs.Kats.*. They are definitions and
-- belong one level up; moving them is a one-line-per-def edit to a file this package does not
-- own, so it is reported rather than done.

import Midfall.Lowering.GenAst
import Midfall.Lowering.GenAstPcs
import Midfall.Generator.Kzg
import Midfall.Generator.YulGolden
import YulSemantics.Syntax
import YulSemantics.PrettyPrint

namespace Midfall.Lowering.GenAst
open YulSemantics YulSemantics.EVM Midfall.Generator Midfall.Lowering

/-! ### The emitter, total over Partial -/

/-- THE PARTIALS THIS GENERATOR EMITS FOR REAL: all seven, since P-PLANVIEW wired pcs into
    the dispatch. The list is explicit rather than defined as Midfall.Lowering.partials so
    that "emitted" remains a claim that can be wrong - a gate compares it against the
    dispatcher's own arms (gate 23) and against the placeholder (gate 8), and an empty
    difference between an explicit list and the seven partials is evidence in a way that
    'partials' = 'partials' is not.

    What P-AST4 recorded about pcs was true then and is corrected here: the blocker was
    never the string machinery - P-STR2AST wrote the AST emitter (computationsAst) - it was
    that PlanView carried neither a ConstraintSystemMeta nor a Data, which are precisely the
    two inputs that emitter needs. Both fields exist now (Inv.lean). What still does NOT
    exist is a DERIVED deployed meta: poseidonMeta's protocol field is the default because
    ProtocolPlan::from_constraint_system needs the circuit, so the poseidon plan view emits
    nothing through this arm. That is the circuit gap, measured at
    DeployedProfile.pcs_deployedGap_measured_ok and not papered over here.
    transcriptParser was the second-to-last placeholder until P-AST4 supplied the four
    AssemblyHelpers definitions it calls and the six plan values it interpolates. -/
def emittedPartials : List Partial :=
  [.vkLoading, .transcriptParser, .lagrange, .quotientLin, .pcs, .finalPairing, .traceReturn]

/-- The partials still emitted as a placeholder. EMPTY since P-PLANVIEW, as data rather than
    as a paragraph, and derived from emittedPartials so the two lists cannot disagree.
    placeholderPartials_nil proves the equation below rather than gating it. -/
def placeholderPartials : List Partial :=
  Midfall.Lowering.partials.filter (fun q => !emittedPartials.contains q)

/-- Is this partial emitted for real, or is it a placeholder? Decidable, so that "one
    partial completely" is a computation in the tree and not a paragraph in a plan. -/
def partialIsEmitted (q : Partial) : Bool := emittedPartials.contains q

/-! ### The pcs arm -/

/-- THE PCS SLICE OF ONE PLAN VIEW: computationsAst applied to the plan's own meta, Data,
    memory and truncation flag, flattened into the single Block Op the pin expects.

    WHY FLATTENED: 'blk' returns a Block Op, i.e. a statement list, and the text emitter's
    block partition is a list of statement lists that the template concatenates inside one
    region - the braces the token gates add are the comparator's, not the artifact's. So the
    flattening is faithful to the render. The partition is NOT lost: it is recoverable
    through pcsTaggedFromPlan below, which is what the tagging is for.

    WHY THE ERROR ARM IS THE EMPTY BLOCK: computationsAst aborts where the Rust indexes a
    vector it assumes is long enough (KZ:1788 and KZ:1376, the selector-column reads) and at
    the two MSM-shape asserts. The reference's answer to a generator error is no contract at
    all, and an empty block is the closest this pure function can get: it falls off the end,
    which every PartialSound post refutes. It is NOT the placeholder - emitPcsFaultArm_ok
    pins both halves, including that the arm is reachable and that the witness plan's
    emptiness comes from the empty-plan guard and not from it.

    WHY trace IS FALSE HERE AND NOT A PLAN FIELD: the emitter is production-only (GenAst's
    header, and SupportedS.production on every *_spec theorem). A trace flag on PlanView
    would be a fifth input no render model supplies. -/
def emitPcsFromPlan (pv : PlanView) : Block Op :=
  match Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
      pv.truncatedChallenges false with
  | .ok blocks => blocks.flatten
  | .error _ => []

/-- The plan's own PCS shape: how many intermediate point sets and how many x1 powers the
    (meta, Data) pair implies. Re-derived here rather than passed in, because the role list
    has to be a FUNCTION OF THE PLAN - the same two numbers computationsAst computes
    internally at KZ:941 and KZ:946 - and a caller-supplied count is a count that can lie. -/
def pcsPlanShape (pv : PlanView) : Except Midfall.Halo2.Fault (Nat × Nat) := do
  let sets ← Midfall.Generator.intermediateSets pv.meta_ pv.dat
  let nSets := sets.pointSets.length
  if nSets == 0 then pure (0, 0)
  else
    let bySet ← Midfall.Generator.commitmentsBySet sets nSets
    pure (nSets, (bySet.map List.length).foldl max 0)

/-- THE TAGGED PARTITION OF ONE PLAN VIEW: the role list the plan implies, zipped onto the
    blocks the plan emits. This is the object a pcs_spec can induct over - "for every
    qEvalSet block, P" is a statement about this list and not about a comment string. -/
def pcsTaggedFromPlan (pv : PlanView) :
    Except Midfall.Halo2.Fault (List (GenAstPcs.Kats.PcsBlockRole × Block Op)) := do
  let (nSets, nbX1Powers) ← pcsPlanShape pv
  let blocks ← Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
    pv.truncatedChallenges false
  pure (GenAstPcs.Kats.pcsTaggedBlocks nSets nbX1Powers false blocks)

/-- The unique block carrying a role, or the empty block if the role is absent or doubled.
    Returning [] on a duplicate is deliberate: every caller below compares, and a duplicate
    role would make the comparison fail rather than pick a winner. -/
def roleBlock (tagged : List (GenAstPcs.Kats.PcsBlockRole × Block Op))
    (role : GenAstPcs.Kats.PcsBlockRole) : Block Op :=
  match (tagged.filter fun p => p.fst == role) with
  | [(_, b)] => b
  | _ => []

/-- An Except read as a block list, named so the gates below do not each re-spell a match.
    KzgKats.unFault is the same shape; this one is here because the dispatch does not open
    the Kats namespace at file scope. -/
def unF {alpha : Type} (e : Except Midfall.Halo2.Fault alpha) (d : alpha) : alpha :=
  match e with
  | .ok x => x
  | .error _ => d

/-- Is this Except an error? Named because Except.isError does not exist at this toolchain
    and a gate that wants to say 'the emitter aborted' should say it directly. -/
def isFault {alpha : Type} (e : Except Midfall.Halo2.Fault alpha) : Bool :=
  match e with
  | .error _ => true
  | .ok _ => false

/-- THE GENERATOR FUNCTION the blk pin pins to: the Yul block of one partial under one plan
    view. Total over Partial by construction, and since P-PLANVIEW EXHAUSTIVE over it
    without a wildcard arm - which is the difference between "the placeholder is documented
    as unreachable" and "the placeholder cannot be reached". Every one of the seven arms
    reads the plan view; none of them reads a fixture tuple. -/
def emitPartial (pv : PlanView) (q : Partial) : Block Op :=
  match q with
  | .vkLoading => emitVkLoading pv
  | .transcriptParser => emitTranscriptParser pv
  | .lagrange => emitLagrange pv
  | .quotientLin => emitQuotientLin pv
  | .pcs => emitPcsFromPlan pv
  | .finalPairing => emitFinalPairing pv
  | .traceReturn => emitTraceReturn pv

/-- The seven slices in include order (Halo2Verifier.sol:217-229), i.e. exactly the tail
    main_concat speaks about. -/
def emitSlices (pv : PlanView) : Block Op :=
  Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++ emitPartial pv q

/-- The whole main block the emitter produces: the helpers, then the seven slices. -/
def emitMain (pv : PlanView) : Block Op := emitHelpers pv ++ emitSlices pv
/-! ### The fixture plan view the pcs gates run on -/

/-- The plan view the pcs gates run on, and WHICH SOURCE it comes from: the Kzg fixture's own
    triple. metaF is ConstraintSystemMeta.new over Protocol.lean's fixtureCs and dataF is
    Data.new over (metaF, vkFixture, memFixture), i.e. a DERIVED circuit description reached
    through the reference's own constructors - not a transcription of the deployed dump. That
    is what makes the gates below circuit derivations and not observations.

    The parser facts are the empty-plan ones, and that is declared rather than hidden: this
    plan view exists to exercise the PCS slice, and emitPcsReadsOnlyFourFields_ok below proves
    that the two fields it does not derive (userPhases, lookupHPlusAcc) cannot reach the pcs
    emission at all. numNegLagranges is read off the meta the way ART:288 does. -/
def pcsFixturePlan : PlanView :=
  Midfall.Lowering.planViewWithAccumulator
    (vk := Midfall.Lowering.witnessVkPayload)
    (vkMptr := KzgKats.memF.vkMptr) (memory := KzgKats.memF)
    (proofLayout := KzgKats.proofLayoutF)
    (numInstances := 1) (k := 6)
    (numNegLagranges := KzgKats.metaF.rotationLast.natAbs)
    (acc := none) (facts := Midfall.Lowering.emptyParserFacts)
    (meta_ := KzgKats.metaF) (dat := KzgKats.dataF)

/-- Move one meta field or the Data of a plan view. Named because the gates below perturb one
    field at a time, and because a structure update whose fields are split across lines does
    NOT parse at this toolchain: '{ x with a := 1,' followed by the next field on the next
    line is rejected with "expected '}'" while the same update on one line builds. Measured
    twice in this package, and recorded because it will be hit again. -/
def withMeta (m : ConstraintSystemMeta) (pv : PlanView) : PlanView := { pv with meta_ := m }
def withDat (d : Midfall.Generator.Data) (pv : PlanView) : PlanView := { pv with dat := d }

/-- The same EcPoint list with every base advanced by one word: a perturbation of the Data
    that changes no LENGTH, so no count check can see it and only the emitted addresses move. -/
def shiftedFixedComms (ds : List EcPoint) : List EcPoint :=
  ds.map fun e => EcPoint.new (Ptr.add e.base 1)

/-! ### The two gate relations, the tagging, and the plan dependence -/

/-- GATE 45 (THE AUTHORITATIVE RELATION, at the dispatch). stmtsBeq between the block the
    DISPATCHER returns and the 'yul%' quotations that already exist in GenAstPcs - reached
    through the tagging rather than by index, which is the point: the quotation of the
    x1-power table is compared against the block TAGGED x1Powers, not against block 1. If the
    partition order ever changed, an index comparison would silently compare the wrong pair
    and this one would not. Line 3 is the negative control: at truncatedChallenges = false the
    x1Powers block is NOT the truncated quotation, so line 1 is not a quotation that matches
    anything. Line 4 says the role lookup and the positional index name the SAME block, so the
    tagging is a labelling of the emission and not a second emission. -/
def emitPcsDispatch_beq_ok : Bool :=
  let tagged := unF (pcsTaggedFromPlan pcsFixturePlan) []
  let raw := unF (Midfall.Lowering.GenAstPcs.computationsAst KzgKats.metaF KzgKats.dataF
    KzgKats.memF false false) []
  SyntaxEq.stmtsBeq (roleBlock tagged GenAstPcs.Kats.PcsBlockRole.x1Powers)
    GenAstPcs.Kats.pcsBlock2_quotation &&
    SyntaxEq.stmtsBeq (roleBlock tagged GenAstPcs.Kats.PcsBlockRole.pairingInputs)
    GenAstPcs.Kats.pcsBlock6_quotation &&
    ! SyntaxEq.stmtsBeq (roleBlock tagged GenAstPcs.Kats.PcsBlockRole.x1Powers)
      GenAstPcs.Kats.pcsBlock2_truncQuotation &&
    (match raw[1]? with
      | some b => SyntaxEq.stmtsBeq (roleBlock tagged
          GenAstPcs.Kats.PcsBlockRole.x1Powers) b
      | none => false) &&
    tagged.length == 10

/-- GATE 46 (THE TRIPWIRE, at the dispatch). The flattened emitted slice tokenises to the
    text port's flattened blocks - the same comparison computationsAst_tokens_ok makes per
    block, now made on the ONE block the dispatcher actually returns - and under all four
    combinations of the two booleans at the emitter level. The dispatch itself always takes
    the production arm (trace = false), so the trace rows are checked against the emitter and
    the no-trace row against the dispatch; saying which is which is the difference between a
    gate and a shrug. The last block is the relation gap at the dispatch: spelling every
    staticcall of the emitted slice as a USER call keeps the token stream and breaks
    stmtsBeq, and the count proves the rewrite reached the nested 'if success' scopes. -/
def emitPcsDispatch_tokens_ok : Bool :=
  let emitted := emitPartial pcsFixturePlan .pcs
  let txt := unF (Midfall.Generator.computations KzgKats.metaF KzgKats.dataF KzgKats.memF
    false false) []
  yulTokens ("{" ++ String.intercalate "\n" (txt.flatten) ++ "}") == yulTokens (EVM.print emitted) &&
    ([(false, false), (true, false), (false, true), (true, true)] : List (Bool × Bool)).all
      fun (tq, tr) =>
        let t := unF (Midfall.Generator.computations KzgKats.metaF KzgKats.dataF KzgKats.memF
          tq tr) []
        let a := unF (Midfall.Lowering.GenAstPcs.computationsAst KzgKats.metaF KzgKats.dataF
          KzgKats.memF tq tr) []
        yulTokens ("{" ++ String.intercalate "\n" (t.flatten) ++ "}") ==
          yulTokens (EVM.print (a.flatten)) &&
    (let good := emitted
      let bad := good.map (mapStmtExprs fun
        | Expr.builtin Op.staticcall args => Expr.call "staticcall" args
        | e => e)
      yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
        ! SyntaxEq.stmtsBeq good bad &&
        Midfall.Generator.VerifierPartialKats.occ (EVM.print bad) "staticcall(" ==
          Midfall.Generator.VerifierPartialKats.occ (EVM.print good) "staticcall(" &&
        Midfall.Generator.VerifierPartialKats.occ (EVM.print good) "staticcall(" > 4)

/-- A perturbation row, stated once: the emitter must NOT abort at the perturbed plan, and
    the emitted block must differ from the unperturbed one. The first half is the half a
    bare 'the output moved' check is missing - P-PLANVIEW measured that
    computationsAstDependsOnPlan_ok's simpleSelectorCols := [0,1,2] row passes because the
    emitter aborts and unFault turns the abort into [], which differs from the fixture's
    ten blocks. A row that cannot tell 'moved' from 'broke' is not a dependence gate. -/
def pcsRow (pv : PlanView) : Bool :=
  (Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
    pv.truncatedChallenges false).isOk &&
    ! SyntaxEq.stmtsBeq (emitPartial pcsFixturePlan .pcs) (emitPartial pv .pcs)

/-- GATE 47 (PLAN DEPENDENCE THROUGH THE PLAN VIEW). Every input the pcs slice reads,
    perturbed IN THE PLAN VIEW and not in the emitter's argument list, moves the emitted
    block WITHOUT aborting it - and the text port moves with it, which is the half that
    cannot be faked. This is the gate the standing note demands: hard-coding a value that
    matches the fixture reddens neither yulTokens nor stmtsBeq at the fixture, and a
    plan-view-level gate is the only thing that reaches a value the emitter reads off the
    record rather than off its arguments.

    WHAT THE ROWS MEASURED, and one of them is a finding. The meta rows are the quotient-limb
    count (both directions) and the selector columns. The Data rows are the fixed-commitment
    addresses (the selector pairs' mcopy sources), the permutation-Z commitment handles and
    the advice commitment handles - all three moved by advancing every base one word, which
    changes NO LENGTH and so is invisible to every count check in the tree. The memory rows
    are the three scratch bases. And numPermutationZs is NOT a row: perturbing it alone moves
    neither the AST nor the text port, because the point-set partition follows the Data's
    eval schedule (queries over data.permutationZEvals and friends) and not the meta's count.
    The two agree only when the Data was built by Data.new from that meta - which is how
    GenAstPcs's gate-10 note reads 'numPermutationZs = 3, which is what the point-set count
    follows'. True of a derived pair; false as a statement about the meta. Reported rather
    than quietly dropped. -/
def emitPcsDependsOnPlanView_ok : Bool :=
  let M := KzgKats.metaF
  let D := KzgKats.dataF
  let ME := KzgKats.memF
  -- the meta: quotient limbs (both directions) and the selector columns
  pcsRow (withMeta { M with numQuotients := 5 } pcsFixturePlan) &&
    pcsRow (withMeta { M with numQuotients := 1 } pcsFixturePlan) &&
    pcsRow (withMeta { M with simpleSelectorCols := [] } pcsFixturePlan) &&
    -- the Data: three commitment-handle lists, each moved by one word, none of them a
    -- length change. This is the row that proves 'dat' is not decoration: no other field of
    -- PlanView reaches any of them.
    pcsRow (withDat { D with fixedComms := shiftedFixedComms D.fixedComms } pcsFixturePlan) &&
    pcsRow (withDat { D with permutationZComms := shiftedFixedComms D.permutationZComms }
      pcsFixturePlan) &&
    pcsRow (withDat { D with adviceComms := shiftedFixedComms D.adviceComms } pcsFixturePlan) &&
    -- the memory: three scratch bases, one per block that reads them
    pcsRow { pcsFixturePlan with memory := { ME with pcsFinalMsmScratchMptr := 0x8300 } } &&
    pcsRow { pcsFixturePlan with memory := { ME with pcsQEvalSourceTableMptr := 0x8040 } } &&
    pcsRow { pcsFixturePlan with memory := { ME with pcsPairingScratchMptr := 0x9300 } } &&
    -- the truncation flag
    pcsRow { pcsFixturePlan with truncatedChallenges := true } &&
    -- the gate is live: the unperturbed plan is not a row (no movement, so pcsRow is false)
    ! pcsRow pcsFixturePlan &&
    -- CONTROL: the same perturbations move the TEXT port, and the perturbed AST still agrees
    -- token for token with the perturbed text.
    let txtBase := unF (Midfall.Generator.computations M D ME false false) []
    let txt (m : ConstraintSystemMeta) (d : Midfall.Generator.Data) :=
      unF (Midfall.Generator.computations m d ME false false) []
    txtBase != txt { M with numQuotients := 5 } D &&
      txtBase != txt { M with simpleSelectorCols := [] } D &&
      txtBase != txt M { D with fixedComms := [] } &&
      txtBase != txt M { D with adviceComms := shiftedFixedComms D.adviceComms } &&
      (let t := txt { M with numQuotients := 5 } D
        let a := unF (Midfall.Lowering.GenAstPcs.computationsAst { M with numQuotients := 5 }
          D ME false false) []
        t.length == a.length && (t.zip a).all fun (tb, ab) =>
          yulTokens ("{" ++ String.intercalate "\n" tb ++ "}") == yulTokens (EVM.print ab))

/-- GATE 48 (WHICH FIELDS THE SLICE READS, and which it cannot). The pcs emission depends on
    exactly four things: the meta, the Data, the memory and the truncation flag. Perturbing
    numInstances, k, numNegLagranges, userPhases, lookupHPlusAcc or vkMptr leaves it
    IDENTICAL - which is both a non-vacuity guard for gate 47 (a gate that reddened on every
    perturbation would be testing the comparator and not the emitter) and the declaration
    that pcsFixturePlan's empty-plan parser facts cannot contaminate a pcs claim. The last
    two lines say the trace region is unreachable through a plan view at all: the dispatch
    emits no log1, and the emitter does when asked. -/
def emitPcsReadsOnlyFourFields_ok : Bool :=
  let base := emitPartial pcsFixturePlan .pcs
  SyntaxEq.stmtsBeq base (emitPartial { pcsFixturePlan with numInstances := 9 } .pcs) &&
    SyntaxEq.stmtsBeq base (emitPartial { pcsFixturePlan with k := 3 } .pcs) &&
    SyntaxEq.stmtsBeq base (emitPartial { pcsFixturePlan with numNegLagranges := 0 } .pcs) &&
    SyntaxEq.stmtsBeq base (emitPartial { pcsFixturePlan with lookupHPlusAcc := 17 } .pcs) &&
    SyntaxEq.stmtsBeq base (emitPartial { pcsFixturePlan with userPhases := [] } .pcs) &&
    SyntaxEq.stmtsBeq base (emitPartial { pcsFixturePlan with vkMptr := pcsFixturePlan.memory.vkMptr } .pcs) &&
    !(EVM.print base).contains "log1(" &&
    (EVM.print ((unF (Midfall.Lowering.GenAstPcs.computationsAst KzgKats.metaF
      KzgKats.dataF KzgKats.memF false true) []).flatten)).contains "log1("

/-- GATE 49 (THE TAGGING IS THE PARTITION, and the partition is inductable). The role list
    the plan implies has the same length as the block list the plan emits, no block is empty,
    flattening the tagged list gives back EXACTLY what the dispatcher returns, and the three
    roles whose identity the comments used to carry are pinned by what their blocks WRITE:
    pairingInputs writes PAIRING_RHS_MPTR, fEval writes F_EVAL_MPTR, finalMsm writes V_MPTR.
    The deployed arithmetic is the last two lines: three sets and at least one x1 power give
    eight roles - the eight-block partition the artifact shows - and a plan with no circuit
    gives the four unconditional roles - rotationWalk, fEval, finalMsm, pairingInputs - and no
    per-set block at all, which is the guard structure doing what the guard says. -/
def emitPcsTagging_ok : Bool :=
  let tagged := unF (pcsTaggedFromPlan pcsFixturePlan) []
  let blocks := unF (Midfall.Lowering.GenAstPcs.computationsAst KzgKats.metaF KzgKats.dataF
    KzgKats.memF false false) []
  tagged.length == blocks.length &&
    tagged.length == 10 &&
    (tagged.all fun (_, b) => ! b.isEmpty) &&
    SyntaxEq.stmtsBeq ((tagged.map Prod.snd).flatten) (emitPartial pcsFixturePlan .pcs) &&
    (tagged.filter fun p => match p.fst with
      | GenAstPcs.Kats.PcsBlockRole.qEvalSet _ => true | _ => false).length == 5 &&
    GenAstPcs.Kats.writesTo tagged GenAstPcs.Kats.PcsBlockRole.pairingInputs "PAIRING_RHS_MPTR" &&
    GenAstPcs.Kats.writesTo tagged GenAstPcs.Kats.PcsBlockRole.fEval "F_EVAL_MPTR" &&
    GenAstPcs.Kats.writesTo tagged GenAstPcs.Kats.PcsBlockRole.finalMsm "V_MPTR" &&
    (GenAstPcs.Kats.pcsBlockRoles 3 33 false).length == 8 &&
    (match pcsPlanShape Midfall.Lowering.witnessPlanView with
      | .ok (n, _) => n == 0 && (GenAstPcs.Kats.pcsBlockRoles 0 0 false).length == 4
      | .error _ => false)

/-- GATE 50 (the fault arm and the empty-plan arm are DIFFERENT THINGS, and neither is the
    placeholder). Rows 1-3: a plan whose Data is too short for the meta's selector columns
    faults inside the emitter, the dispatch returns the empty block for it, and the emitter
    itself says .error - so the emptiness is attributable to the fault and not to a guard.
    Rows 4-5: the witness plan's emission is empty because its meta has no intermediate set
    (the KZ:943-945 early return) and the emitter says .ok [] - the same output, a different
    reason, and the two must not be conflated. Row 6: neither empty block is the placeholder,
    so a fall-through could never masquerade as either.

    WHY THIS GATE EXISTS: computationsAstDependsOnPlan_ok's simpleSelectorCols := [0,1,2] row
    reads its result through unFault, so it cannot tell "the perturbation moved the AST" from
    "the perturbation aborted the emitter". P-PLANVIEW measured that the second is what
    happens for that row - dataF.fixedComms has two entries, so the third selector index
    aborts at KZ:1788 - which does not invalidate the row (a constant emitter still fails it)
    but does mean the row is not evidence about three selectors. Row 7 states the measurement
    rather than leaving it in a report. -/
def emitPcsFaultArm_ok : Bool :=
  let broken := withDat { KzgKats.dataF with fixedComms := [] } pcsFixturePlan
  (emitPartial broken .pcs).isEmpty &&
    isFault (Midfall.Lowering.GenAstPcs.computationsAst broken.meta_ broken.dat KzgKats.memF
      false false) &&
    ! SyntaxEq.stmtsBeq (emitPartial broken .pcs) (emitPlaceholder .pcs) &&
    (emitPartial Midfall.Lowering.witnessPlanView .pcs).isEmpty &&
    (match Midfall.Lowering.GenAstPcs.computationsAst Midfall.Lowering.witnessPlanView.meta_
        Midfall.Lowering.witnessPlanView.dat Midfall.Lowering.witnessPlanView.memory false false with
      | .ok b => b.isEmpty
      | .error _ => false) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .pcs)
      (emitPlaceholder .pcs) &&
    isFault (Midfall.Lowering.GenAstPcs.computationsAst { KzgKats.metaF with
      simpleSelectorCols := [0, 1, 2] } KzgKats.dataF KzgKats.memF false false)

/-- The placeholder is unreachable from the dispatcher, as a THEOREM and not a gate: the list
    of partials the emitter does not emit for real is empty, so no arm can fall through to it.
    D-P30 clause 4's stronger half - the def is still there for the falsification plants, but
    nothing in the emitter can reach it. -/
theorem placeholderPartials_nil : placeholderPartials = [] := by
  -- The filter over the seven partials with the seven emitted names in it: every membership
  -- test is a DecidableEq on Partial (Checkpoint.lean:84), so the whole equation is a
  -- computation and not a proof.
  decide


/-- GATE 8 (what is real and what is a placeholder, as a computation). ALL SEVEN partials
    are emitted for real since P-PLANVIEW - vkLoading, transcriptParser, lagrange,
    quotientLin, finalPairing, traceReturn and pcs - and placeholderPartials is EMPTY, which
    is what D-P30 clause 4 asked for and what the theorem below proves. The last conjuncts are the R-62 clause: for each real slice, the
    placeholder that used to stand for it is NOT what the emitter returns, so the pin cannot
    be satisfied by a dummy for a partial that has a real body. Before P-AST2 the lagrange
    and traceReturn conjuncts were unfalsifiable in exactly this way, before P-AST3a the
    quotientLin one was, and before this package the vkLoading one was - the placeholder WAS
    the emitter's answer - which is what "emitPlaceholder must shrink toward unreachable"
    (D-P30 clause 4) is measuring. The quotientLin and vkLoading conjuncts earn their place
    in a way the others do not: placeholder and real slice are BOTH one statement, so the
    tail conjuncts below are the only way this gate can tell them apart - a length check
    cannot, and it says so rather than pretending otherwise. -/
def emitPlaceholderIsTotal_ok : Bool :=
  emittedPartials.length == 7 && emittedPartials.contains .finalPairing &&
    emittedPartials.contains .pcs &&
    emittedPartials.contains .lagrange && emittedPartials.contains .traceReturn &&
    emittedPartials.contains .quotientLin && emittedPartials.contains .vkLoading &&
    emittedPartials.contains .transcriptParser &&
    placeholderPartials.isEmpty && placeholderPartials == [] &&
    (Midfall.Lowering.partials.all fun q =>
      partialIsEmitted q ==
        (q == .finalPairing || q == .lagrange || q == .traceReturn ||
          q == .quotientLin || q == .vkLoading || q == .transcriptParser ||
          q == .pcs)) &&
    (Midfall.Lowering.partials.all fun q =>
      partialIsEmitted q || (emitPlaceholder q).length == 1) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .finalPairing)
      (emitFinalPairingArms false 0x1000) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .lagrange) (emitLagrangeAt 6 1 9) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .traceReturn) emitTraceReturnBlock &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .quotientLin) (emitQuotientLinAt 6) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .vkLoading)
      (emitVkLoadingArms false 1 6 0 0 0 0 0x10e0) &&
    -- P-AST4: the fifth and sixth placeholder-vs-real pairs. The transcriptParser one is the
    -- only case in the file where the real slice is LONGER than the dummy by more than one
    -- statement, so it is the pair a length check separates for free - and the pair that a
    -- length check alone would NOT have separated for vkLoading or quotientLin, which is why
    -- the conjuncts are stmtsBeq and not counts.
    ! SyntaxEq.stmtsBeq (emitPlaceholder .transcriptParser)
      (emitTranscriptParserDeployed) &&
    -- P-PLANVIEW: the seventh placeholder-vs-real pair, and the one the standing note is
    -- about. The pcs placeholder is ONE statement and the real slice is hundreds, so a
    -- length check separates them for free here - which is exactly why the conjunct is
    -- written as stmtsBeq and the length is asserted separately below rather than being
    -- the test.
    ! SyntaxEq.stmtsBeq (emitPlaceholder .pcs) (emitPcsFromPlan pcsFixturePlan) &&
    (emitPlaceholder .pcs).length == 1 && (emitPcsFromPlan pcsFixturePlan).length > 100 &&
    -- the shape fact that makes the previous two lines load-bearing: same top-level length,
    -- so nothing but stmtsBeq separates the dummy from the real scope.
    (emitPlaceholder .quotientLin).length == 1 && (emitQuotientLinAt 6).length == 1 &&
    (emitPlaceholder .vkLoading).length == 1 &&
    (emitVkLoadingArms false 1 6 0 0 0 0 0x10e0).length == 1 &&
    (emitPlaceholder .transcriptParser).length == 1 &&
    emitTranscriptParserDeployed.length == 44 &&
    (match emitQuotientLinAt 6 with
     | [Stmt.block body] => body.length == 9
     | _ => false) &&
    (match emitVkLoadingArms false 1 6 0 0 0 0 0x10e0 with
     | [Stmt.block body] => body.length == 13
     | _ => false)
/-- GATE 23 (the dispatch, not just the list). emittedPartials CLAIMS seven partials are
    real; gates 14-28 check the emitters themselves. Without this gate the file could grow a
    real emitLagrange, list it in emittedPartials, and still have emitPartial fall through to
    emitPlaceholder - the pin would then pin a placeholder while every other gate stayed
    green. That is the R-62 class one level up, so it is checked as a computation: the
    dispatch reaches the real body for all four, and the placeholder is NOT what the
    dispatcher returns for any of them. -/
def emitPartialRoutesRealSlices_ok : Bool :=
  SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .lagrange)
    (emitLagrange Midfall.Lowering.witnessPlanView) &&
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .traceReturn)
    emitTraceReturnBlock &&
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitQuotientLin Midfall.Lowering.witnessPlanView) &&
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .finalPairing)
      (emitFinalPairing Midfall.Lowering.witnessPlanView) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .lagrange)
      (emitPlaceholder .lagrange) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .traceReturn)
      (emitPlaceholder .traceReturn) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitPlaceholder .quotientLin) &&
    -- and the dispatch reads pv.k rather than a hard-coded 6: the fixture plan's k is 2,
    -- so routing to the deployed constant would still satisfy the line above and this one
    -- would catch it.
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitQuotientLinAt Midfall.Lowering.witnessPlanView.k) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitQuotientLinAt 6) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .finalPairing)
      (emitPlaceholder .finalPairing) &&
    -- P-AST3b: the fourth dispatch line, and the one that matters most here. The
    -- placeholder for vkLoading is one statement and the real slice is one statement too,
    -- so "the dispatcher reached the real body" cannot be read off any shape or length; it
    -- is read off stmtsBeq against the dummy.
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .vkLoading)
      (emitPlaceholder .vkLoading) &&
    -- and the vkLoading dispatch reads the PlanView fields and not the deployed profile:
    -- the witness plan is k = 2 with the default proof length, so routing to the artifact's
    -- 6 and 0x10e0 would satisfy the line above and fail these two.
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .vkLoading)
      (emitVkLoadingArms Midfall.Lowering.witnessPlanView.hasAccumulator
        Midfall.Lowering.witnessPlanView.numInstances Midfall.Lowering.witnessPlanView.k
        Midfall.Lowering.witnessPlanView.expectedHasAccumulatorWord
        Midfall.Lowering.witnessPlanView.expectedAccOffset
        Midfall.Lowering.witnessPlanView.expectedNumAccLimbs
        Midfall.Lowering.witnessPlanView.expectedNumAccLimbBits
        Midfall.Lowering.witnessPlanView.proofLayout.proofLen) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .vkLoading)
      (emitVkLoadingArms false 1 6 0 0 0 0 0x10e0) &&
    -- P-AST4: the fifth dispatch line. The transcriptParser placeholder is one statement and
    -- the real slice is forty-four, so 'the dispatcher reached the real body' is decidable by
    -- length here - but the line that matters is the second one, which says the dispatch reads
    -- the ELEVEN PlanView fields and not the deployed profile: the witness plan carries the
    -- empty parser facts, so routing to poseidonCtx's numbers would satisfy the first line and
    -- fail this one.
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .transcriptParser)
      (emitTranscriptParser Midfall.Lowering.witnessPlanView) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .transcriptParser)
      (emitPlaceholder .transcriptParser) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .transcriptParser)
      emitTranscriptParserDeployed &&
    SyntaxEq.stmtsBeq (emitPartial transcriptParserPoseidonPlan .transcriptParser)
      emitTranscriptParserDeployed &&
    -- P-PLANVIEW: the seventh dispatch line, and the one this package exists for. Three
    -- claims: the dispatcher reaches the real pcs body (not the placeholder), it reaches it
    -- THROUGH THE PLAN VIEW rather than through a fixture tuple, and the block it returns is
    -- the emitter's own answer at that plan view and at no other.
    SyntaxEq.stmtsBeq (emitPartial pcsFixturePlan .pcs) (emitPcsFromPlan pcsFixturePlan) &&
    ! SyntaxEq.stmtsBeq (emitPartial pcsFixturePlan .pcs) (emitPlaceholder .pcs) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .pcs)
      (emitPartial pcsFixturePlan .pcs) &&
    -- and the witness plan's pcs slice is empty because its meta has no circuit, NOT
    -- because the dispatcher fell through to something: the placeholder is one statement
    -- and the empty emission is none, so the two are distinguishable here.
    (emitPartial Midfall.Lowering.witnessPlanView .pcs).isEmpty &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .pcs)
      (emitPlaceholder .pcs)

/-! ### The artifact-facing plan view, and the helper region against the dump (P-SCRATCH)

THE GATE THIS SECTION ADDS, and why its absence was the real defect. P-SCRATCH found three
different numbers in the tree for memory.rs:437's scalar-inversion scratch slot: 0x2800 in the
text port's deployed context, 0x1f00 at the witness plan view and 0x3f00 at the poseidon KAT
layout. The arbiter is the Rust, and the Rust says all three are the SAME rule read at three
different vk_mptr inputs: memory.rs:672-677 registers the frame at
vk_start.saturating_sub(MODEXP_SCRATCH_BYTES) with MODEXP_SCRATCH_WORDS = 8 (mod.rs:92-93),
i.e. 0x100 bytes below the caller's VK base, and validate re-derives that expression as a
hard error at memory.rs:1038-1040. LayoutMemory.lean:193-195 ports the line verbatim. The
deployed artifact satisfies it: D:115 declares VK_MPTR = 0x2900 and D:650 prints
"let p := 0x2800", and 0x2900 - 0x100 = 0x2800. The 0x1f00 is the Rust's OWN test fixture
(MEM:1294-1299, asserted at MEM:1428-1429 as 0x2000 - MODEXP_SCRATCH_BYTES), and 0x3f00 is
the synthetic headline fixture's chosen base at LayoutMemory.lean:535-537.

SO NO DEPLOYED BYTE IS WRONG, and nothing in the port of memory.rs:437 is wrong either. What
was wrong is that the emitter's artifact-facing gates ran at a FIXTURE plan view and no gate
ever said which plan view an artifact claim belongs to. The emitter therefore put 0x1f00 into
main while every artifact-facing gate in the file reached the dump through the TEXT port's own
context (gates 52-53 compare the emitted helper at poseidonCtx's value and say so), and nothing
at all compared emitMain's helper region against the dump to notice. That comparison is gate 60,
and it runs at
artifactPlanView, the deployed plan view. Gate 61 is its falsification: the same predicate at
the pre-fix plan view, at a nudged deployed slot, and with the hex-versus-decimal spelling
control the standing note demands.

WHY THE COMPARISON IS A VALUE COMPARISON. Numeric spelling is invisible to every AST relation
in this tree - numericSpellingDivergence_ok (GenAst.lean) pins that the emitter prints 10240
where the artifact prints 0x2800, and yulTokens maps the two onto each other. A gate that
compared TEXT would therefore pass on a real mismatch or fail on an innocent one, so litValue?
parses both sides into a Nat and every address clause below compares numbers. -/

/-- THE ARTIFACT-FACING PLAN VIEW: the deployed poseidon profile reached through a PlanView,
    i.e. the only plan view at which an emitted claim can be compared against the tracked
    artifact. It is transcriptParserPoseidonPlan (GenAst.lean:1243), which P-AST4 built from
    poseidonCtx.memory - that is poseidonMemoryLayout, the transcribed deployed layout
    VerifierPartials' gate 77 checks three ways (against the dump's own *_MPTR lines,
    against Layout.lean's ported constants and MEM:1039's rule, and against the ported
    validate). It is NOT witnessPlanView, whose memory is the Rust's 0x2000 test fixture. -/
def artifactPlanView : PlanView := transcriptParserPoseidonPlan

/-- The HELPER REGION of emitMain: the maximal prefix of function definitions, which is what
    emitHelpers ++ emitSlices makes of it - the first slice is a Stmt.block, so the prefix
    stops exactly where main's definitions stop. Slicing emitMain rather than calling
    emitHelpers is the point: the gate is about what main actually carries. -/
def mainHelperRegion (pv : PlanView) : Block Op :=
  (emitMain pv).takeWhile fun | Stmt.funDef _ _ _ _ => true | _ => false

/-- The names of the definitions in a region, in order. -/
def regionHelperNames (b : Block Op) : List String :=
  b.filterMap fun | Stmt.funDef n _ _ _ => some n | _ => none

/-- One definition of a region by name, as a block of its own, or the empty block if the region
    does not define it. A list and not an Option because every caller compares it with
    EVM.print, and an absent helper prints as the empty string and so fails every comparison
    it appears in rather than short-circuiting one. -/
def regionHelper (b : Block Op) (nm : String) : Block Op :=
  b.filterMap fun s => match s with
    | Stmt.funDef n _ _ _ => if n == nm then some s else none
    | _ => none

/-- The value of a decimal literal body. -/
def decVal (t : String) : Nat :=
  t.foldl (fun (acc : Nat) (c : Char) => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- THE VALUE OF A YUL NUMBER LITERAL, however it is spelled: 0x2800, 0X2800 and 10240 all
    give 10240, and anything that is not a number gives none. This is the parser the standing
    note asks for - numeric spelling is invisible to yulTokens and to stmtsBeq, so a gate that
    compared text would pass on a real mismatch. -/
def litValue? (t : String) : Option Nat :=
  let s := trimWs t
  if s.startsWith "0x" || s.startsWith "0X" then
    let ds := ((s.drop 2).takeWhile Char.isHexDigit).toString
    if ds.isEmpty then none else some (hexVal ds)
  else
    let ds := (s.takeWhile (fun c => c >= '0' && c <= '9')).toString
    if ds.isEmpty then none else some (decVal ds)

/-- The value of the first "let NAME := <literal>" line of a rendered slice, parsed through
    litValue? so hex and decimal are the same question. None when the slice has no such line,
    which is what makes an absent helper a red and not a shrug. -/
def dumpLetValue (slice name : String) : Option Nat :=
  let needle := "let " ++ name ++ " := "
  match (slice.splitOn "\n").find? (fun l => (trimWs l).startsWith needle) with
  | some l => litValue? (((trimWs l).splitOn needle).drop 1 |>.headD "")
  | none => none

-- Every "let NAME := <number>" in an emitted block, at any nesting depth: the function
-- bodies, the if arms, the for init/post blocks and the switch cases are all walked, so a
-- literal the emitter buried inside a branch cannot hide from the comparison. A doc comment
-- cannot sit directly above `mutual` at this toolchain - the parser reads it as the header of
-- a declaration and then rejects `mutual` - hence the line comments.
mutual
partial def letNumsSs (ss : List (Stmt Op)) : List (String × Nat) :=
  ss.flatMap letNumsS

partial def letNumsS (s : Stmt Op) : List (String × Nat) :=
  match s with
  | Stmt.letDecl vs (some (Expr.lit (Literal.number n))) => vs.map (fun v => (v, n))
  | Stmt.letDecl _ _ => []
  | Stmt.block b => letNumsSs b
  | Stmt.funDef _ _ _ b => letNumsSs b
  | Stmt.cond _ b => letNumsSs b
  | Stmt.switch _ cases dflt =>
      letNumsSs (cases.map Prod.snd).flatten ++
        (match dflt with | some b => letNumsSs b | none => [])
  | Stmt.forLoop i _ p b => letNumsSs i ++ letNumsSs p ++ letNumsSs b
  | _ => []
end

/-- The value one "let NAME := <literal>" carries in an emitted AST, read off the AST and not
    off the printed text, so the printer's decimal habit cannot flatter the comparison. -/
def emittedLetValue (b : Block Op) (name : String) : Option Nat :=
  match (letNumsSs b).find? (fun p => p.fst == name) with
  | some p => some p.snd
  | none => none

/-- One helper of one plan view against the dump's own bytes for that helper, token for token.
    Split out so the falsification gate can name WHICH helper fails and not merely that one
    does. -/
def helperTokensMatch (sol : String) (pv : PlanView) (nm : String) : Bool :=
  yulTokens ("{" ++ renderFunction sol nm ++ "}") ==
    yulTokens (EVM.print (regionHelper (mainHelperRegion pv) nm))

/-- THE HELPER-REGION COMPARISON, as a function of the plan view so gate 61 can run the SAME
    predicate at the wrong one and report that it fails. Six clauses, none of them weaker than
    the mismatch it was written to catch:

    (1) the region is EXACTLY the eight helpers emitHelpers claims, in the template's order;
    (2) each of the eight is present in the dump and COMPLETE there - the brace test P-AST4
        had to repair on the slicer - and is emitted exactly once here;
    (3) each emitted definition equals the dump's bytes token for token;
    (4) the two addresses the helpers interpolate are the same NUMBER on both sides, read out
        of the AST on one side and out of the dump's hex on the other, and each occurs exactly
        once so "first match wins" cannot pick an unrelated line;
    (5) the plan view really carries those two numbers, i.e. the emitter read them from the
        plan and not from a constant the converter typed;
    (6) THE RUST RULE ITSELF, against the artifact: memory.rs:674 puts the frame at
        vk_mptr - MODEXP_SCRATCH_BYTES, and the input is the dump's own VK_MPTR line rather
        than a Lean constant, so the expected side never touches the emitter. -/
def helperRegionMatchesArtifact (sol : String) (pv : PlanView) : Bool :=
  let hr := mainHelperRegion pv
  let sInv := regionHelper hr "scalar_inv"
  let pair := regionHelper hr "ec_pairing"
  let dumpInv := renderFunction sol "scalar_inv"
  let dumpPair := renderFunction sol "ec_pairing"
  regionHelperNames hr == emittedHelperNames &&
    emittedHelperNames.length == 8 &&
    (emittedHelperNames.all fun nm =>
      sliceIsComplete (renderFunction sol nm) && (regionHelper hr nm).length == 1) &&
    (emittedHelperNames.all fun nm => helperTokensMatch sol pv nm) &&
    dumpLetValue dumpInv "p" == emittedLetValue sInv "p" &&
    dumpLetValue dumpPair "scratch" == emittedLetValue pair "scratch" &&
    VerifierPartialKats.occ dumpInv "let p := " == 1 &&
    VerifierPartialKats.occ dumpPair "let scratch := " == 1 &&
    ((letNumsSs sInv).filter (fun p => p.fst == "p")).length == 1 &&
    ((letNumsSs pair).filter (fun p => p.fst == "scratch")).length == 1 &&
    some pv.memory.scalarInvScratchMptr == emittedLetValue sInv "p" &&
    some pv.memory.finalPairingScratchMptr == emittedLetValue pair "scratch" &&
    (match EvmKats.solConstant sol "VK_MPTR" with
      | some vk =>
          dumpLetValue dumpInv "p" == some (vk - modexpScratchBytes) &&
            pv.memory.scalarInvScratchMptr == vk - modexpScratchBytes &&
            vk == poseidonCtx.vkMptr
      | none => false)

/-- GATE 60 (THE MISSING GATE, P-SCRATCH). emitMain's helper region against the tracked
    artifact, at the artifact-facing plan view. This is the check whose absence P-SCRATCH names
    as the real bug: the value mismatch is only what its absence revealed. Two things beyond
    helperRegionMatchesArtifact are pinned here. The reachability first (D-P19: a moved dump is
    a named red, never a vacuous needle match), and the shape of the slice - main continues past
    the eighth definition with a Stmt.block, so the prefix really is the helper region and
    mainHelperRegion has neither swallowed a slice nor stopped short of a helper. The two line
    counts are the witness that the dump slices the gate compares against are whole functions
    and not the truncated fragments P-AST4 found once before. -/
def emitMainHelperRegion_matchesArtifact_ok : IO Bool :=
  VerifierPartialKats.readDump >>= fun sol =>
  let m := emitMain artifactPlanView
  pure (EvmKats.generatedReadOk sol &&
    helperRegionMatchesArtifact sol artifactPlanView &&
    m.length > 8 &&
    (match m.drop 8 with
      | [] => false
      | Stmt.funDef _ _ _ _ :: _ => false
      | _ :: _ => true) &&
    VerifierPartialKats.lineCount (renderFunction sol "scalar_inv") == 23 &&
    VerifierPartialKats.lineCount (renderFunction sol "ec_pairing") == 36)

/-- GATE 61 (D-P23 / R-41: THE GATE MUST BE ABLE TO FAIL, AND THE FAILURE MODE IS NAMED). Six
    clauses. (1) THE PRE-FIX STATE ITSELF: the emitter fed the witness fixture's layout, which
    is exactly what the tree did when P-HELPERS recorded the divergence, reddens the gate.
    (2) It reddens on ONE helper and not on the eight, so the gate localises the defect to the
    slot instead of drowning it - the measurement that made this diagnosable at all. (3) The
    number that moved, as a number. (4) A one-word nudge of the DEPLOYED slot reddens it too,
    so an emitter that hard-coded 0x2800 instead of reading the plan would not pass gate 60.
    (5) The SPELLING CONTROL: litValue? maps 0x2800, 0X2800 and 10240 onto one number and
    0x1f00 onto another, which is what makes the address clauses value comparisons rather than
    text comparisons. (6) The same control at the bytes: the printed AST spells the deployed
    address in DECIMAL, the dump spells it in HEX, and the two still match - so the gate is not
    a string comparison wearing a hat. -/
def emitMainHelperRegion_detectsWrongScratch_ok : IO Bool :=
  VerifierPartialKats.readDump >>= fun sol =>
  let witnessMem := Midfall.Lowering.witnessPlanView.memory
  let badPV := { artifactPlanView with memory := witnessMem }
  let nudgedPV := { artifactPlanView with memory :=
    { poseidonMemoryLayout with scalarInvScratchMptr := 0x2820 } }
  pure (EvmKats.generatedReadOk sol &&
    ! helperRegionMatchesArtifact sol badPV &&
    emittedHelperNames.filter (fun nm => ! helperTokensMatch sol badPV nm) ==
      ["scalar_inv"] &&
    emittedHelperNames.filter (fun nm => ! helperTokensMatch sol nudgedPV nm) ==
      ["scalar_inv"] &&
    emittedLetValue (regionHelper (mainHelperRegion badPV) "scalar_inv") "p" ==
      some witnessMem.scalarInvScratchMptr &&
    witnessMem.scalarInvScratchMptr == 0x1f00 &&
    ! helperRegionMatchesArtifact sol nudgedPV &&
    litValue? "0x2800" == litValue? "10240" &&
      litValue? "0X2800" == litValue? "0x2800" &&
      litValue? "0x2800" == some 10240 &&
      litValue? "0x1f00" == some 7936 &&
      litValue? "0x1f00" != litValue? "0x2800" &&
      litValue? "not a number" == none &&
    (EVM.print (regionHelper (mainHelperRegion artifactPlanView) "scalar_inv")).contains
      "10240" &&
      (renderFunction sol "scalar_inv").contains "0x2800" &&
      ! (renderFunction sol "scalar_inv").contains "10240")

end Midfall.Lowering.GenAst

#eval Midfall.Lowering.GenAst.emitPlaceholderIsTotal_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPartialRoutesRealSlices_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPcsDispatch_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPcsDispatch_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPcsDependsOnPlanView_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPcsReadsOnlyFourFields_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPcsTagging_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPcsFaultArm_ok -- expect true
#eval Midfall.Lowering.GenAst.emitMainHelperRegion_matchesArtifact_ok -- expect true
#eval Midfall.Lowering.GenAst.emitMainHelperRegion_detectsWrongScratch_ok -- expect true
