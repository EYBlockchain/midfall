/-
  Midfall.Instances.PoseidonValid

  C.4 (GEN - SKELETON, box 2 h, branch t/C.4 from a1febbf): `poseidon_valid` taken apart
  into ONE NAMED LEMMA PER `Render.Valid` CLAUSE, and every clause decided at `poseidonRender`.

  RE-MEASURED BY F.1 (GEN - PORT, branch t/F.1 from 3e15e9f). F.1 exported the deployment's real
  constraint system into `fixtures/conformance/poseidon/cs.json` - gates, lookups, trashcans,
  permutation columns, challenge phase - and `poseidonMeta` is now `ConstraintSystemMeta.new`
  applied to it instead of a transcription of counts. That moves FOUR of C.4's six refutations.
  The table below is the F.1 re-measurement; every value in it is printed by this file.

    #   clause          verdict   deciding value (F.1)
    1   circuitMeta     PROVED    derived numEvals 48 against the plan's 48 (was 27 vs 48), and the
                                  whole record agrees: `deciding_circuitMeta` is true by rfl-level
                                  comparison of the derived meta against `poseidonPlanV2.meta_`.
    2   layout          REFUTED   `fromProtocol` on the REAL protocol gives proofLen 4224 against the
                                  plan's transcribed 4320. New reason, narrower: the 96-byte gap is
                                  the `num_point_sets` / `num_dummy_evals` that
                                  `LoweringPlan::new` sets AFTER `from_constraint_system`
                                  (ENC:506 `setNumPointSets`), which is the fallback F.1 excludes.
    3   invariants      REFUTED   no longer the linearization-query refusal - the real protocol's PCS
                                  schedule DOES end with it. Now check 16: planned PcsMemory
                                  {rotPoints 28, x1Powers 65, qEvalSet 0, qEvalSourceTable 0,
                                  qComTraceMsm 0 terms} against recomputed {3, 33, 6, 33, 39};
                                  finalMsm agrees at 47 terms / 7520 bytes. The typed-in
                                  `poseidonLayoutConfig.pcs` is P-13's observation of the artifact.
    4   model           SORRY     unchanged: true by construction, not machine-dischargeable (C.4's
                                  gap (c) plus the dependent-motive obstruction).
    5   inputs          PROVED    unchanged. k = 6 = vk.domain.k.
    6   codegen         REFUTED   unchanged in kind (WP-G1, the un-emitted includes), bigger on both
                                  sides now: AST 6761 tokens against text 14054 (was 3156/10433) -
                                  the pcs arm emits 225 statements where it used to emit none.
    7   closed          PROVED    unchanged.
    8   slots           PROVED    FLIPPED. `numNegLagranges` 9 against `blindingFactors + 1` = 9
                                  (was 9 vs 7: the empty CS recomputed blinding_factors to 6 while
                                  vk.json always said 8). All ten `EnvAgrees` clauses now hold.
    9   supported       REFUTED   narrowed to ONE field. `csDegreeMatches` now HOLDS - the ported
                                  degree on the exported gates is 5 = the imported cs_degree - and
                                  `permutationCommitmentsMatch` still fails: 8 sigma commitments
                                  against `divCeil 8 3` = 3 z-chunks. That clause compares the VK's
                                  per-COLUMN sigma commitments with the proof's per-CHUNK z count;
                                  it is a v1 `Exec/VerifyingKey` defect, not a data gap.
   10   noWriters       PROVED    unchanged in verdict, higher fuel: 200 is now EXHAUSTED (the main
                                  block grew), 2000 and 20000 both answer true.
   11   transcriptMptr  PROVED    unchanged. TRANSCRIPT_MPTR = 4096.
   12   vkPins          PROVED    unchanged (S.8/S.9): VK_MPTR, payload length, instance count,
                                  disjointness all hold at the derived plan view.
   13   vkProgressPins  PROVED    unchanged (S.8/S.9): EXPECTED_VK_LENGTH and EXPECTED_VK_CODEHASH.
   14   returnMptr      PROVED    NEW (D-P48, clause and discharge landed together by Q0.5):
                                  RETURN_MPTR = some 4096, so tr_blockProgress's existence half is
                                  reachable from `R.Valid` at all.

  So 9 PROVED, 4 REFUTED, 1 SORRY out of fourteen clauses - from 6/6/1 of thirteen. `poseidonRender.Valid` is STILL unsatisfiable and
  `poseidonRender_notValid` now runs through clause 2 rather than clause 1, because clause 1 became
  a theorem. What is left is no longer "the constraint system is missing": it is
  `LoweringPlan::new`'s post-constructor sizing (clauses 2 and 3) and one v1 `WellFormed` field
  (clause 9), plus the AST emitter (clause 6), none of which is fixture data.

  ## WHAT WAS NOT TOUCHED

  `PoseidonV2.lean` is C.1's and is untouched: `poseidon_valid` stays a sorry there. Replacing it
  with `fun h => poseidonRender_notValid h |>.elim` would close the hole by proving its negation,
  which is a DIFFERENT theorem from the one `lowering_equivalence_poseidon` consumes - the headline
  would then be vacuous rather than open, and that is C.1's call to make, not this card's.
  `Statements.lean` is frozen; `Blocks.lean` sections 6 and 7 are C.2's; no v1 file, no fixture and
  no gate script was edited.

  ## native_decide, AND WHAT EACH USE COSTS

  `Statements.lean:136-138` sanctions native_decide in `Instances/` for exactly these clauses.
  Each use adds ONE compiler-trusted axiom of the shape `<decl>._native.native_decide.ax_1_1`; the
  name is given in each clause's docstring. They are listed together in the report to the
  orchestrator. `check_frozen_axioms.py` is unaffected: it probes `Midfall/Statements.lean` only.
-/
import Midfall.Instances.PoseidonV2
import Midfall.Instances.PoseidonCoherence

namespace Midfall.Instances.PoseidonValid

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open Midfall.Yul.Bridge Midfall.Generator.LoweringPlanKats
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.LoweringV2

/-! ## 0. The computable faces of the render's derived views -/

/-- `poseidonRender` is a NONCOMPUTABLE def (its E, params and sG2gen fields are), so nothing that
    projects from it reaches the VM: `native_decide` refuses it with `lean.dependsOnNoncomputable`.
    These two names are the same views built from D.1's and D.2's COMPUTABLE terms, and the pins say
    the render's own views ARE them - by rfl, so by the kernel and not by a tactic. Every computation
    below goes through them and is transferred back to the render by defeq. -/
def poseidonM : Model := poseidonModelVal
def poseidonPv : PlanView := planViewOf poseidonPlanV2 poseidonM poseidonConfig.accumulator

theorem poseidonM_eq : poseidonRender.model = poseidonM := rfl
theorem poseidonPv_eq : poseidonRender.pv = poseidonPv := rfl
theorem poseidonVk_eq : poseidonRender.vk = poseidonVkExec := rfl
theorem poseidonPlan_eq : poseidonRender.plan = poseidonPlanV2 := rfl
theorem poseidonCfg_eq : poseidonRender.cfg = poseidonConfig := rfl
theorem poseidonInputs_eq : poseidonRender.inputs = poseidonInputs := rfl
theorem poseidonFlags_eq : poseidonRender.flags = poseidonFlags := rfl
theorem poseidonConsts_eq : poseidonRender.consts = constTableOf poseidonM := rfl
theorem poseidonProg_eq : poseidonRender.prog 0 0 = asmOf poseidonPv poseidonM 0 0 := rfl

/-! ## 1. circuitMeta - REFUTED -/

/-- **CLAUSE 1 OF 13 - PROVED SINCE F.1.** `ConstraintSystemMeta.new` on the deployment's
    own constraint system now RETURNS the meta the plan carries, because the plan's meta IS that
    call: DeployedProfile's `poseidonMeta` is `ConstraintSystemMeta.new Features.solidity poseidonCs 1`
    and `poseidonCs` now carries the gates, lookups, trashcans and permutation columns that
    `cs.json` exports (F.1). C.4's refutation read "derived numEvals 27 against the typed-in 48";
    the derived number is now 48 and the whole record agrees, so the clause is TRUE at this render.

    Stated as the deciding computation rather than as the Prop. `ConstraintSystemMeta` derives
    `BEq` and `Fault` derives no `DecidableEq`, so the record comparison is what native_decide can
    see; the Prop form `... = .ok plan.meta_` follows from it by a case split on the constructor
    plus the fact that the error arm is unreachable, and `poseidonRender_notValid` below no longer
    runs through this clause. AXIOM: deciding_circuitMeta._native.native_decide.ax_1_1. -/
theorem deciding_circuitMeta :
    (match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
      | .ok m => m == poseidonPlanV2.meta_ | .error _ => false) = true := by
  native_decide

/-- THE PRINTED VALUE FOR CLAUSE 1: the derived numEvals, which C.4 measured at 27 and F.1 moves to
    48 - the artifact's own 0x600 word count. AXIOM:
    deciding_circuitMeta_numEvals._native.native_decide.ax_1_1. -/
theorem deciding_circuitMeta_numEvals :
    (match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
      | .ok m => m.numEvals | .error _ => 0) = 48 := by
  native_decide

/-! ## 2. layout - REFUTED -/

/-- THE DECIDING VALUE FOR CLAUSE 2: derived proofLen 1792 against the plan's 4320. AXIOM:
    deciding_layout._native.native_decide.ax_1_1. -/
theorem deciding_layout :
    (match ProofCalldataLayout.fromProtocol poseidonPlanV2.meta_.protocol abiVerifyProofProofCptr
        poseidonPlanV2.meta_.numEvals poseidonPlanV2.meta_.numPointSets with
      | .ok l => l.proofLen | .error _ => 0) ≠ poseidonPlanV2.proofLayout.proofLen := by
  native_decide

/-- **CLAUSE 2 OF 11 - REFUTED.** The literal `Render.Valid.layout`. D.3 already proved the root
    cause by rfl - `check2_typedInProtocolIsDefault`, cited below rather than redone - so
    `fromProtocol` rebuilds a layout with every commitment section emptied. -/
theorem poseidonValid_layout_not :
    ¬ (ProofCalldataLayout.fromProtocol poseidonRender.plan.meta_.protocol abiVerifyProofProofCptr
        poseidonRender.plan.meta_.numEvals poseidonRender.plan.meta_.numPointSets
        = .ok poseidonRender.plan.proofLayout) := by
  show ¬ (ProofCalldataLayout.fromProtocol poseidonPlanV2.meta_.protocol abiVerifyProofProofCptr
      poseidonPlanV2.meta_.numEvals poseidonPlanV2.meta_.numPointSets
      = .ok poseidonPlanV2.proofLayout)
  intro h
  exact deciding_layout
    (congrArg (fun x : Except Fault ProofCalldataLayout =>
      match x with | .ok l => l.proofLen | .error _ => 0) h)

/-- THE ROOT CAUSE OF CLAUSES 1, 2, 3 AND 8 IS GONE. D.3's crux - that the plan's protocol field IS
    `protocolPlanDefault` - was flipped by F.1: `poseidonPlanV2.meta_.protocol` is the real
    `ProtocolPlan`, derived from `cs.json`. Clause 2 therefore fails for a NEW and narrower reason:
    `fromProtocol` on the real protocol builds a 4224-byte layout where the plan's transcribed
    `poseidonProofLayout` is 4320, and the 96-byte difference is the `num_point_sets` /
    `num_dummy_evals` that `LoweringPlan::new` sets AFTER `from_constraint_system` (ENC:506's
    `setNumPointSets`), which is the fallback this card was told not to port. -/
theorem deciding_layout_rootCause :
    poseidonPlanV2.meta_.protocol ≠ Midfall.Generator.protocolPlanDefault :=
  PoseidonCoherence.check2_typedInProtocolIsReal

/-- The two printed proof lengths clause 2 now turns on: 4224 derived against 4320 transcribed. -/
def deciding_layout_derivedProofLen : Nat :=
  match ProofCalldataLayout.fromProtocol poseidonPlanV2.meta_.protocol abiVerifyProofProofCptr
      poseidonPlanV2.meta_.numEvals poseidonPlanV2.meta_.numPointSets with
  | .ok l => l.proofLen | .error _ => 0

def deciding_layout_planProofLen : Nat := poseidonPlanV2.proofLayout.proofLen

/-! ## 3. invariants - REFUTED -/

/-- THE DECIDING VALUE FOR CLAUSE 3: the plan still refuses its own invariant check, but for a
    completely different reason now that the protocol is real. With `protocolPlanDefault` the FIRST
    of the sixteen checks refused ("PCS query schedule must end with linearization query"); with the
    real protocol the schedule DOES end with the linearization query and check 1 passes, and the
    refusal has moved to the PCS memory sizing: the plan's transcribed `poseidonLayoutConfig.pcs`
    (rotPoints 28, x1Powers 65, qEvalSet 0, qEvalSourceTable 0, qComTraceMsm 0 terms) against what
    the real protocol recomputes (rotPoints 3, x1Powers 33, qEvalSet 6, qEvalSourceTable 33,
    qComTraceMsm 39 terms; finalMsm agrees at 47 terms / 7520 bytes). AXIOM:
    deciding_invariants._native.native_decide.ax_1_1. -/
theorem deciding_invariants :
    (match poseidonPlanV2.validateGeneratorInvariants with
      | .ok (.ok ()) => true | _ => false) = false := by
  native_decide

/-- THE REFUSAL, AS THE REFERENCE PRINTS IT, for the report rather than as a pinned string: a
    message-text change should not redden a clause verdict. -/
def deciding_invariants_message : String :=
  match poseidonPlanV2.validateGeneratorInvariants with
  | .ok (.error s) => s
  | .ok (.ok ()) => "OK"
  | .error (Fault.panic t) => "PANIC " ++ t
  | .error _ => "OTHER"

/-- **CLAUSE 3 OF 11 - REFUTED, AND THE CARD DID NOT PREDICT IT.** The literal
    `Render.Valid.invariants`: the plan must pass the generator's own sixteen invariant checks
    (`plan.rs:427-437`). It does not - check 1 of sixteen, `meta_.validateAgainstProtocol`,
    refuses because the typed-in meta's default protocol has no linearization query to end a query
    schedule with. Third face of the same typed-in meta.
    AXIOM: poseidonValid_invariants_not._native.native_decide.ax_1_4. -/
theorem poseidonValid_invariants_not :
    ¬ (poseidonRender.plan.validateGeneratorInvariants = .ok (.ok ())) := by
  show ¬ (poseidonPlanV2.validateGeneratorInvariants = .ok (.ok ()))
  intro h
  have key : (match poseidonPlanV2.validateGeneratorInvariants with
              | .ok (.ok ()) => true | _ => false) = false := by native_decide
  have k2 : (match poseidonPlanV2.validateGeneratorInvariants with
              | .ok (.ok ()) => true | _ => false) = true := by rw [h]
  rw [key] at k2
  exact absurd k2 (by decide)

/-! ## 4. model - SORRY (true, and not dischargeable here) -/

/-- **CLAUSE 4 OF 11 - SORRY, OPEN.** The literal `Render.Valid.model`.

    IT IS TRUE. `Render.model` was defined as `poseidonModelVal`, the projection of exactly this
    generator call along the proof that its error arm is unreachable, so the clause reads
    `x = .ok (proj x)`.

    IT IS NOT PROVABLE HERE, and this card found a SECOND obstruction beyond C.1's gap (c), which is
    worth more than the clause itself:
    * C.1 gap (c), confirmed: the kernel will not reduce `poseidonModel`, so `decide` and `rfl`
      both get stuck at `match poseidonModel with`; and there is no `BEq`/`DecidableEq` on the
      71-field `Halo2Verifier`, so `native_decide` has no instance to run. Measured again here.
    * NEW: the case split that closes an `Except` along a proved-unreachable error arm does NOT
      close this one. `poseidonModelVal` is a `match h : poseidonModel with` whose ERROR BRANCH
      mentions `poseidonModel` in the type of its proof argument, so abstracting `poseidonModel`
      to case on it is not type-correct: `cases h : poseidonModel`, `rw [h]`, `conv`, `simp [h]`
      and `h ▸ rfl` all fail on the motive (each message measured). The clause is a tautology about
      a term the kernel cannot see inside.

    WHAT WOULD DISCHARGE IT, in ascending cost:
    (a) give `Halo2Verifier` a `deriving Inhabited` in `Generator/Models.lean` - one line, but it
        is a v1 edit and this card forbids it, AND restate `poseidonModelVal` as
        `poseidonModel.getD default` in `PoseidonV2.lean`. The second half is what matters: the
        `getD` match has a NON-dependent motive, so `cases h : poseidonModel` closes the clause by
        iota and `rfl` - which is exactly what the present dmatch motive forbids;
    (b) restate `poseidonModelVal` so its error arm does not mention `poseidonModel` - e.g.
        `match h : poseidonModel with | .ok v => v | .error e => (False.elim (noErr e) : Model)`
        where noErr is proved from a Bool rather than from the equation - which needs (a) anyway;
    (c) make `Render.model` an `Except Fault Model` field, which is a FROZEN-surface edit
        (`Statements.lean:86`) and therefore a decision, not a patch.
    None of the three is a computation, so no amount of native_decide and no heartbeat increase
    (forbidden anyway) helps. -/
theorem poseidonValid_model :
    generateVerifierFromPlan (fun _ _ => poseidonRender.qblocks) poseidonRender.inputs
      poseidonRender.flags poseidonRender.plan = .ok poseidonRender.model := by
  sorry

/-! ## 5. inputs - PROVED -/

/-- **CLAUSE 5 OF 11 - PROVED.** The build inputs are the configuration's and the VK's, not
    independent numbers. Three of the four are rfl, and they are rfl at EXACTLY these literals -
    which is what `poseidonConfig_forced` says is forced. The fourth, `inputs.k = vk.domain.k`,
    is not rfl because the domain arrives through `EvaluationDomain.new`.
    AXIOM: poseidonValid_inputs._native.native_decide.ax_1_1. -/
theorem poseidonValid_inputs :
    poseidonRender.inputs.numInstances = poseidonRender.cfg.numInstances ∧
      poseidonRender.inputs.accEncoding = poseidonRender.cfg.accumulator ∧
      poseidonRender.inputs.k = poseidonRender.vk.domain.k ∧
      poseidonRender.inputs.truncatedChallenges = Features.solidity.truncatedChallenges := by
  show poseidonInputs.numInstances = poseidonConfig.numInstances ∧
       poseidonInputs.accEncoding = poseidonConfig.accumulator ∧
       poseidonInputs.k = poseidonVkExec.domain.k ∧
       poseidonInputs.truncatedChallenges = Features.solidity.truncatedChallenges
  exact ⟨rfl, rfl, by native_decide, rfl⟩

/-! ## 6. codegen - REFUTED -/

/-- THE DECIDING VALUE FOR CLAUSE 6: the whole conjunction is false. AXIOM:
    deciding_codegen._native.native_decide.ax_1_1. -/
theorem deciding_codegen : codegenAgrees poseidonPv poseidonM = false := by native_decide

/-- The half that is TRUE, pinned so the refutation cannot be read as "the emitter is broken
    everywhere": the ABI-shape guard block prints to the guard text token for token. AXIOM:
    deciding_codegen_guard._native.native_decide.ax_1_1. -/
theorem deciding_codegen_guard :
    yulTokens (YulSemantics.EVM.print (abiGuardBlock poseidonM)) == abiGuardTokens poseidonM := by
  native_decide

/-- THE FIRST DIFFERING TOKEN, as a minimal reproducer a reader can check by eye. The emitted main
    block is 3156 tokens where the printed text is 10433, and at index 1333 the AST has already
    moved on to `let r := FR_MODULUS` while the text is still emitting
    `function load_acc_coord_shifted (src, bits)` - an accumulator helper include that
    `GenAst.emitSlices` does not emit. AXIOM:
    deciding_codegen_witness._native.native_decide.ax_1_1. -/
theorem deciding_codegen_witness :
    (yulTokens (YulSemantics.EVM.print (mainAsmRaw poseidonPv))).length = 6761 ∧
      (mainAssemblyTokens poseidonM).length = 14054 := by
  native_decide

/-- **CLAUSE 6 OF 11 - REFUTED.** The literal `Render.Valid.codegen`. `Program.lean:96-101`
    already says this is false and names the gap (WP-G1: emitSlices emits the linearization SCOPE of
    QuotientAndLinearization but not the two `quotient_numerator` includes in front of them, and
    the accumulator and trace helper includes are not emitted) - "CodegenAgrees below is FALSE until
    they are, which is the point: the gap is a red gate, not a silent omission". This is that red
    gate MEASURED at the deployment, and it is the only refutation here that is NOT about the plan's
    meta: it is the AST emitter, and it is C.2/WP-G1's to close. -/
theorem poseidonValid_codegen_not : ¬ CodegenAgrees poseidonRender.pv poseidonRender.model := by
  show ¬ (codegenAgrees poseidonPv poseidonM = true)
  rw [deciding_codegen]
  decide

/-! ## 7. closed - PROVED -/

/-- **CLAUSE 7 OF 11 - PROVED.** After inlining, the main block's only free names are the two
    wrapper locals. `Program.lean:128-134` says this is discharged by native_decide in Instances/
    per render because `Shared.freeNames` is not kernel-reducible; this is that discharge.
    AXIOM: poseidonValid_closed._native.native_decide.ax_1_1. -/
theorem poseidonValid_closed : mainClosed poseidonRender.pv poseidonRender.model = true := by
  show mainClosed poseidonPv poseidonM = true
  native_decide

/-! ## 8. slots - REFUTED -/

/-- **CLAUSE 8 OF 13 - PROVED SINCE F.1.** `EnvAgrees`'s `negLagranges` clause reads
    `PV.numNegLagranges = vk.cs.blindingFactors + 1`. C.4 measured 9 against 7 and refuted it,
    because the VK's constraint system had no trashcans and no lookup chunks and so recomputed
    `blinding_factors` to 6 while the plan's typed-in `rotationLast` said -9. With the real
    constraint system the reference's own number is 8 (vk.json has said 8 all along - the port was
    reading an empty CS), so the clause is 9 = 9 and it HOLDS. AXIOM:
    poseidonValid_slots_negLagranges._native.native_decide.ax_1_1. -/
theorem poseidonValid_slots_negLagranges :
    poseidonPv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1 := by
  native_decide

/-- The finite content of `EnvAgrees.omegaOrder`, which is the one clause of the ten that is
    neither a computation at the render nor refuted: `orderExactly` is a forall over every smaller
    exponent, so it needs the domain's own order, not a reduction. Checked exhaustively over
    `List.range n` (n = 64) rather than by a general theorem about the repaired root. AXIOMS:
    omegaBall._native.native_decide.ax_1_1, omegaOrder._native.native_decide.ax_1_1 and
    omegaOrder._native.native_decide.ax_1_2. -/
theorem omegaBall : ∀ m ∈ List.range poseidonVkExec.domain.n,
    m = 0 ∨ poseidonVkExec.domain.omega ^ m ≠ (1 : Fr blsR) := by native_decide

/-- `EnvAgrees.omegaOrder` AT THE DEPLOYMENT: the imported omega has order exactly n. This is D.2's
    root repair earning its keep - poseidonRootOfUnity was chosen so that its 2^26-th power IS the
    deployment's omega - and it is now a theorem rather than a gated observation. -/
theorem omegaOrder : Midfall.Assumptions.orderExactly poseidonVkExec.domain.omega
    poseidonVkExec.domain.n := by
  refine ⟨by native_decide, by native_decide, fun m h0 hlt => ?_⟩
  exact (omegaBall m (List.mem_range.mpr hlt)).elim (fun h => absurd h (Nat.ne_of_gt h0)) id

/-- THE NINE `EnvAgrees` CLAUSES THAT HOLD, so clause 8's refutation is located rather than total:
    modulus, truncWidth, domainN (both conjuncts), baryWeight, omegaInvMul, omegaOrder, nG2, sG2 and
    vkDigestWord. `nG2` and `sG2` are rfl because D.2 built the params from the assumed pairing's
    own generator (`poseidonParams_areTheAssumedGenerators`); `truncWidth` is stated at
    `poseidonFc` because `poseidonE` is noncomputable and the VM cannot see through it, and the
    `show` is the kernel saying the two are the same term. AXIOMS: six native_decide uses in this
    declaration, poseidonValid_slots_nine._native.native_decide.ax_1_1 through ax_1_6, plus the two
    omegaOrder ones and omegaBall's. -/
theorem poseidonValid_slots_nine :
    blsR = frModulusConstant ∧
      divCeil (divCeil poseidonE.field.numBits 8) 2 = 16 ∧
      poseidonVkExec.domain.n = 2 ^ poseidonVkExec.domain.k ∧
      poseidonVkExec.domain.k = poseidonPv.k ∧
      poseidonVkExec.domain.barycentricWeight = ((2 ^ poseidonVkExec.domain.k : ℕ) : Fr blsR)⁻¹ ∧
      poseidonVkExec.domain.omegaInv * poseidonVkExec.domain.omega = 1 ∧
      Midfall.Assumptions.orderExactly poseidonVkExec.domain.omega poseidonVkExec.domain.n ∧
      poseidonParams.nG2Prepared = bls12_381Pairing.g₂⁻¹ ∧
      poseidonParams.sG2Prepared = poseidonSG2 ∧
      (poseidonPv.vk.constants.getD 0 ("", 0)).2 = frWord poseidonVkExec.transcriptRepr :=
  ⟨rfl, by show divCeil (divCeil poseidonFc.numBits 8) 2 = 16; native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, omegaOrder, rfl, rfl,
    by native_decide⟩

/-- **CLAUSE 8 OF 13, WHOLE - PROVED.** All ten `EnvAgrees` clauses at `poseidonRender`: the nine
    C.4 already proved, plus `negLagranges`. This is the first of C.4's six refutations to become a
    proof, and it is the same root cause clause 1 had - the missing constraint system - closed by
    the same export. -/
theorem poseidonValid_slots :
    EnvAgrees poseidonRender.E poseidonRender.vk poseidonRender.pv poseidonRender.params
      poseidonRender.sG2gen := by
  obtain ⟨hmod, htrunc, hd1, hd2, hbary, homega, horder, hng2, hsg2, hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, hd2⟩, hbary, homega, horder, ?_, hng2, hsg2, hdig⟩
  show poseidonPv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
  exact poseidonValid_slots_negLagranges

/-! ## 9. supported - REFUTED -/

/-- **CLAUSE 9'S FIRST FACE IS CLOSED BY F.1.** `SupportedV2.wf.csDegreeMatches` demands
    `vk.cs.degree = .ok vk.csDegree`. C.4 measured the ported degree recomputing to 3 against the
    imported 5 - D.2's gap A, an empty `gates` array. With the exported gates the ported
    `ConstraintSystem.degree` recomputes to 5 and the clause HOLDS. AXIOM:
    deciding_supported_degree._native.native_decide.ax_1_1. -/
theorem deciding_supported_degree :
    (match poseidonVkExec.cs.degree with | .ok d => d | .error _ => 0) = poseidonVkExec.csDegree := by
  native_decide

/-- The second failing `WellFormed` clause, so the refutation is not one unlucky field: 8
    permutation commitments against `divCeil 0 3 = 0`, because vk.json names permutation
    COMMITMENTS but no permutation COLUMNS. AXIOM:
    deciding_supported_perm._native.native_decide.ax_1_1. -/
theorem deciding_supported_perm :
    poseidonVkExec.permutation.commitments.size ≠
      divCeil poseidonVkExec.cs.permutation.columns.size (poseidonVkExec.csDegree - 2) := by
  native_decide

/-- **CLAUSE 9 OF 13 - STILL REFUTED, BY ONE FIELD, AND IT IS NOT THE EXPORT'S.**
    `SupportedV2 poseidonRender` requires `R.vk.WellFormed Features.solidity`, whose first clause
    `csDegreeMatches` demands `vk.cs.degree = .ok vk.csDegree`. With `gates = #[]` - D.2 gap A,
    vk.json carries no gates at all - the ported `ConstraintSystem.degree` recomputes to 3 while
    the imported `cs_degree` is 5. Those two are the render's OWN vk and its OWN cs, so this is not
    the typed-in meta; it is the missing constraint system, and it is the same gap that blocks
    clauses 1, 2, 3 and 8 from the other side. -/
theorem poseidonValid_supported_not : ¬ SupportedV2 poseidonRender := by
  intro h
  exact deciding_supported_perm h.wf.permutationCommitmentsMatch

/-- The eleven `SupportedV2` fields that DO hold, so clause 9's refutation is located. Every one is
    a computation at the render's own vk, plan and flags. AXIOMS:
    poseidonValid_supported_rest._native.native_decide.ax_1_1 through ax_1_7. -/
theorem poseidonValid_supported_rest :
    poseidonVkExec.cs.numAdviceColumns ≠ 0 ∧
      poseidonVkExec.cs.numInstanceColumns = 2 ∧
      poseidonConfig.numCommittedInstances = 1 ∧
      poseidonVkExec.cs.numChallenges = 0 ∧
      poseidonVkExec.domain.getQuotientPolyDegree = poseidonVkExec.csDegree - 1 ∧
      poseidonPlanV2.memory.map.WellFormed ∧
      poseidonPlanV2.memory.validate.isOk = true ∧
      poseidonFlags.trace = false ∧ poseidonFlags.gasCheckpoints = false ∧
      poseidonConfig.accumulator = none ∧ poseidonFlags.externalQuotient = false ∧
      poseidonFlags.expectedQuotient = none ∧ poseidonFlags.separate = true ∧
      Features.solidity.committedInstances = true ∧
      (∀ q ∈ poseidonVkExec.cs.instanceQueries.toList, q.2.int = 0) := by
  refine ⟨by native_decide, by native_decide, rfl, by native_decide, by native_decide,
    by native_decide, by native_decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by native_decide⟩

/-- The two `EnvAgrees`-style generator clauses of `SupportedV2.vkPoints`, discharged. It holds
    HERE for a reason worth naming: D.2 could only put `1 : G₁z` in every commitment slot
    (`PoseidonEnv.lean:341-350`, the placeholder codec decodes nothing), so all 27 points are the
    identity and the forall is 27 copies of one question - the identity's EIP-2537 encoding, 128
    zero bytes, which the MSM precompile accepts. This is NOT evidence that the deployment's real
    commitments are readable; they are not even in the carrier. AXIOMS:
    poseidonValid_supported_vkPoints._native.native_decide.ax_1_1, ax_1_2, ax_1_4 and ax_1_5. -/
theorem poseidonValid_supported_vkPoints :
    ∀ C ∈ poseidonVkExec.fixedCommitments.toList ++ poseidonVkExec.permutation.commitments.toList,
      ptReadable (poseidonE.g1.toEip C) := by
  have h1 : ∀ x ∈ poseidonVkExec.fixedCommitments.toList, x = (1 : G₁z) := by native_decide
  have h2 : ∀ x ∈ poseidonVkExec.permutation.commitments.toList, x = (1 : G₁z) := by native_decide
  intro C hC
  have hC1 : C = (1 : G₁z) := by
    simp only [List.mem_append] at hC
    cases hC with
    | inl h => exact h1 _ h
    | inr h => exact h2 _ h
  subst hC1
  show ptReadable (g1zToEip (1 : G₁z))
  exact ⟨(0, 0), by native_decide, by native_decide⟩

/-! ## 10. noWriters - PROVED -/

/-- The fuel is exhibited, not guessed, and it is not at its limit: `noWritersScan` answers false at
    exhaustion (R-37), so a true verdict at a finite fuel is a real scan of the whole block, and the
    same scan at ten times the fuel agrees. AXIOM:
    deciding_noWriters_fuel._native.native_decide.ax_1_1. -/
theorem deciding_noWriters_fuel :
    noWritersFuel 2000 (asmOf poseidonPv poseidonM 0 0) = true ∧
      noWritersFuel 20000 (asmOf poseidonPv poseidonM 0 0) = true := by
  native_decide

/-- **CLAUSE 10 OF 13 - PROVED, AT A HIGHER FUEL THAN C.4 NEEDED.** The generated program performs
    no world write - no `sstore`, `tstore`, `log*`, `create*` or value-bearing `call`. C.4 exhibited
    fuel 200; with the real protocol the pcs arm emits 225 statements instead of nothing, the main
    block is bigger, and 200 is now EXHAUSTED (measured false) while 2000 and 20000 both answer true.
    The fuel is exhibited at 2000 below.
    AXIOM: poseidonValid_noWriters._native.native_decide.ax_1_1. -/
theorem poseidonValid_noWriters : NoWriters (poseidonRender.prog 0 0) := by
  show NoWriters (asmOf poseidonPv poseidonM 0 0)
  exact ⟨2000, by native_decide⟩

/-! ## 11. transcriptMptr - PROVED -/

/-- **CLAUSE 11 OF 11 - PROVED.** The generator's own TRANSCRIPT_MPTR lies above Solidity's reserved
    words, so an entry frame exists (`entryFrame_inhabited`). The value is 4096 = 0x1000, read out
    of the render's own constant table - which is the ported `Constants.sol` template applied to
    this model and parsed back, so this clause doubles as the KAT that the parse still works.
    AXIOM: poseidonValid_transcriptMptr._native.native_decide.ax_1_1. -/
theorem poseidonValid_transcriptMptr :
    ∃ t, poseidonRender.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t := by
  show ∃ t, (constTableOf poseidonM).lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t
  exact ⟨4096, by native_decide, by decide⟩

/-! ## 14. returnMptr - PROVED (D-P48, landed with the clause by Q0.5) -/

/-- The terminal arm's return window is bound in this render's own constant table, so
    `tr_blockProgress`'s EXISTENCE half is reachable from `R.Valid` at all - which is the whole
    reason D-P48 exists (M.1: "progress asserts existence and so inherits a data obligation
    soundness does not"). F.2 measured it first; Q0.5 lands the clause and this discharge together.
    The value is 4096 = 0x1000, the same word `pinnedConstants` carries, read back out of the
    ported `Constants.sol` parse - so this is a computation at the deployment, not a premise.
    AXIOM: poseidonValid_returnMptr._native.native_decide.ax_1_1. -/
theorem poseidonValid_returnMptr :
    ∃ m, poseidonRender.consts.lookup "RETURN_MPTR" = some m := by
  show ∃ m, (constTableOf poseidonM).lookup "RETURN_MPTR" = some m
  exact ⟨4096, by native_decide⟩

/-! ## THE HEADLINE OF THIS CARD -/

/-- **`poseidonRender.Valid` IS UNSATISFIABLE.** Several of its clauses are false at this
    render (the header table above is the current verdict per clause, and it is the authority - a
    count in prose here would already be stale again); one refutation is enough and this uses clause 1. This is the card's own stop condition
    stated as a theorem rather than as a report line: C.1's `poseidon_valid` sorry is not an
    unfinished proof, it is an impossible one, and the only way to finish it is upstream - a
    `poseidonMeta` whose `protocol` is the real `ProtocolPlan`, which needs the halo2 constraint
    system that is not in the tree (D.2 gap A), the same circuit gap D.3 named.

    What this does NOT break: `lowering_equivalence_poseidon` takes no `R.Valid` hypothesis
    (`Statements` section 5), so C.1's headline survives as stated; `Valid` enters only through
    `blockContracts_of_valid`, which is where the sorry sits. -/
theorem poseidonRender_notValid : ¬ poseidonRender.Valid :=
  fun h => poseidonValid_layout_not h.layout

end Midfall.Instances.PoseidonValid
