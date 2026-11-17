/-
  Midfall.Instances.PoseidonValid

  C.4 (GEN - SKELETON, box 2 h, branch t/C.4 from a1febbf): `poseidon_valid` taken apart into ONE
  NAMED LEMMA PER `Render.Valid` CLAUSE, and every clause decided at `poseidonRender`.

  ## THE STOP CONDITION FIRED. SIX TIMES.

  `Render.Valid` (`Midfall/LoweringV2/Statements.lean:139`, FROZEN) has eleven clauses. At
  `poseidonRender`: 4 PROVED, 6 REFUTED, 1 SORRY.

    #   clause          verdict   deciding evidence
    1   circuitMeta     REFUTED   derived numEvals 27 against the typed-in 48 (D.3 check 2). The
                                  full field attribution is `PoseidonCoherence`'s
                                  check2_failureAttribution_ok - cited, not redone.
    2   layout          REFUTED   fromProtocol on the DEFAULT protocol gives proofLen 1792 against
                                  the plan's 4320 (D.3 check 1). Root: check2_typedInProtocolIsDefault.
    3   invariants      REFUTED   NOT PREDICTED BY THE CARD. validateGeneratorInvariants returns
                                  .ok (.error "protocol invariant failed: PCS query schedule must
                                  end with linearization query") - the FIRST of the sixteen checks,
                                  meta_.validateAgainstProtocol, refuses, because a default protocol
                                  describes no query schedule. Same root cause, third face.
    4   model           SORRY     true, and NOT machine-dischargeable - and, NEW, not dischargeable
                                  by case split either. See the clause's own docstring.
    5   inputs          PROVED    three rfl and one native_decide (k = 6 = vk.domain.k, not rfl
                                  because the domain arrives through EvaluationDomain.new).
    6   codegen         REFUTED   the documented WP-G1 gap, MEASURED here: the guard block agrees
                                  token for token; the main block prints 3156 tokens where the
                                  ported codegen prints 10433, first difference at index 1333,
                                  where the AST says `let` and the text says `function`
                                  (load_acc_coord_shifted - an accumulator helper include).
    7   closed          PROVED    mainClosed = true; every free name of the inlined main block is
                                  vk or quotientEvaluator.
    8   slots           REFUTED   EnvAgrees.negLagranges reads 9 = 7: the plan view carries
                                  numNegLagranges 9 (typed-in meta rotationLast := -9) while the
                                  VK's own cs.blindingFactors is 6. The other NINE clauses of
                                  EnvAgrees hold and are proved below, including omegaOrder.
    9   supported       REFUTED   a DIFFERENT root cause: SupportedV2.wf.csDegreeMatches demands
                                  vk.cs.degree = .ok vk.csDegree, and the ported degree recomputes
                                  to 3 against the imported cs_degree 5 (D.2 gap A: vk.json has no
                                  gates). wf.permutationCommitmentsMatch fails too, 8 against 0.
                                  The other eleven SupportedV2 fields hold and are proved below.
   10   noWriters       PROVED    noWritersFuel 200 on the closed program at (0, 0); 2000 agrees.
   11   transcriptMptr  PROVED    TRANSCRIPT_MPTR = 4096 >= 0x80.

  So `poseidonRender.Valid` is UNSATISFIABLE, and `poseidonRender_notValid` proves that from
  clause 1 alone. C.1's `poseidon_valid` sorry is not an unfinished proof; it is an impossible one
  at this render. Four of the six refutations - clauses 1, 2, 3, 8 - are ONE finding with four
  faces: `DeployedProfile.poseidonMeta` is typed in over `constraintSystemMetaDefault`, so every
  clause that compares the plan's meta against the VK's constraint system fails. Clause 9 is D.2's
  gap A (a constraint system with no gates), and clause 6 is WP-G1 (the AST emitter), unrelated to
  either. The card asked for the per-clause map rather than a green build; this is that map.

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

/-- THE DECIDING VALUE FOR CLAUSE 1: the ported constructor on the deployment's own constraint system
    yields 27 evals; the typed-in meta the plan carries says 48. One number refutes an equality of
    records. AXIOM: deciding_circuitMeta._native.native_decide.ax_1_1. -/
theorem deciding_circuitMeta :
    (match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
      | .ok m => m.numEvals | .error _ => 0) ≠ poseidonPlanV2.meta_.numEvals := by
  native_decide

/-- The refutation at the whole record, as a Bool: the constructor SUCCEEDS (D.3's
    check2_constructor_isOk) and the two metas are simply not the same meta. -/
theorem deciding_circuitMeta_record :
    (match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
      | .ok m => m == poseidonPlanV2.meta_ | .error _ => true) = false := by
  native_decide

/-- **CLAUSE 1 OF 11 - REFUTED.** The literal `Render.Valid.circuitMeta` at `poseidonRender`,
    and nothing weaker. D.3's `check2_circuitMeta_holds` is false; this is that fact as a
    kernel-checked theorem (the kernel checks the SHAPE; the deciding value is native_decide). -/
theorem poseidonValid_circuitMeta_not :
    ¬ (ConstraintSystemMeta.new Features.solidity poseidonRender.vk.cs
        poseidonRender.cfg.numCommittedInstances = .ok poseidonRender.plan.meta_) := by
  show ¬ (ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 = .ok poseidonPlanV2.meta_)
  intro h
  exact deciding_circuitMeta
    (congrArg (fun x : Except Fault ConstraintSystemMeta =>
      match x with | .ok m => m.numEvals | .error _ => 0) h)

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

/-- THE ROOT CAUSE OF CLAUSES 1, 2, 3 AND 8, cited from D.3 rather than restated: the typed-in meta's
    protocol field IS the default protocol plan. -/
theorem deciding_layout_rootCause :
    poseidonPlanV2.meta_.protocol = Midfall.Generator.protocolPlanDefault :=
  PoseidonCoherence.check2_typedInProtocolIsDefault

/-! ## 3. invariants - REFUTED -/

/-- THE DECIDING VALUE FOR CLAUSE 3, as the reference's own message string, so a change in the
    invariant checker's text reddens this rather than passing silently. AXIOM:
    deciding_invariants._native.native_decide.ax_1_1. -/
theorem deciding_invariants :
    (match poseidonPlanV2.validateGeneratorInvariants with
      | .ok (.error s) => s
      | .ok (.ok ()) => "OK"
      | .error (Fault.panic t) => "PANIC " ++ t
      | .error (Fault.error _) => "OTHER") =
      "protocol invariant failed: PCS query schedule must end with linearization query" := by
  native_decide

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
    ((yulTokens (YulSemantics.EVM.print (mainAsmRaw poseidonPv))).drop 1333).head? = some "let" ∧
      ((mainAssemblyTokens poseidonM).drop 1333).head? = some "function" ∧
      (yulTokens (YulSemantics.EVM.print (mainAsmRaw poseidonPv))).length = 3156 ∧
      (mainAssemblyTokens poseidonM).length = 10433 := by
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

/-- THE DECIDING VALUE FOR CLAUSE 8: 9 against 7. AXIOM:
    deciding_slots._native.native_decide.ax_1_1. -/
theorem deciding_slots :
    poseidonPv.numNegLagranges ≠ poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1 := by
  native_decide

/-- **CLAUSE 8 OF 11 - REFUTED.** The literal `Render.Valid.slots`, i.e. `EnvAgrees`'s ten
    clauses. Nine hold and are proved in `poseidonValid_slots_nine`; `negLagranges` does not: it
    demands `PV.numNegLagranges = vk.cs.blindingFactors + 1`, and the plan view carries 9 (it comes
    from the typed-in meta's `rotationLast := -9`) while the VK's own constraint system says
    blindingFactors = 6, so the clause reads 9 = 7. Fourth face of the typed-in meta. -/
theorem poseidonValid_slots_not :
    ¬ EnvAgrees poseidonRender.E poseidonRender.vk poseidonRender.pv poseidonRender.params
        poseidonRender.sG2gen := by
  intro h
  exact deciding_slots h.negLagranges

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

/-! ## 9. supported - REFUTED -/

/-- THE DECIDING VALUES FOR CLAUSE 9: the ported degree recomputes to 3 against the imported
    cs_degree 5. AXIOM: deciding_supported._native.native_decide.ax_1_1. -/
theorem deciding_supported :
    (match poseidonVkExec.cs.degree with | .ok d => d | .error _ => 0) ≠
      poseidonVkExec.csDegree := by
  native_decide

/-- The second failing `WellFormed` clause, so the refutation is not one unlucky field: 8
    permutation commitments against `divCeil 0 3 = 0`, because vk.json names permutation
    COMMITMENTS but no permutation COLUMNS. AXIOM:
    deciding_supported_perm._native.native_decide.ax_1_1. -/
theorem deciding_supported_perm :
    poseidonVkExec.permutation.commitments.size ≠
      divCeil poseidonVkExec.cs.permutation.columns.size (poseidonVkExec.csDegree - 2) := by
  native_decide

/-- **CLAUSE 9 OF 11 - REFUTED, BY A DIFFERENT ROOT CAUSE FROM 1, 2, 3 AND 8.**
    `SupportedV2 poseidonRender` requires `R.vk.WellFormed Features.solidity`, whose first clause
    `csDegreeMatches` demands `vk.cs.degree = .ok vk.csDegree`. With `gates = #[]` - D.2 gap A,
    vk.json carries no gates at all - the ported `ConstraintSystem.degree` recomputes to 3 while
    the imported `cs_degree` is 5. Those two are the render's OWN vk and its OWN cs, so this is not
    the typed-in meta; it is the missing constraint system, and it is the same gap that blocks
    clauses 1, 2, 3 and 8 from the other side. -/
theorem poseidonValid_supported_not : ¬ SupportedV2 poseidonRender := by
  intro h
  exact deciding_supported
    (congrArg (fun x : Except Fault Nat => match x with | .ok d => d | .error _ => 0)
      h.wf.csDegreeMatches)

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
    noWritersFuel 200 (asmOf poseidonPv poseidonM 0 0) = true ∧
      noWritersFuel 2000 (asmOf poseidonPv poseidonM 0 0) = true := by
  native_decide

/-- **CLAUSE 10 OF 11 - PROVED.** The generated program performs no world write - no `sstore`,
    `tstore`, `log*`, `create*` or value-bearing `call`.
    AXIOM: poseidonValid_noWriters._native.native_decide.ax_1_1. -/
theorem poseidonValid_noWriters : NoWriters (poseidonRender.prog 0 0) := by
  show NoWriters (asmOf poseidonPv poseidonM 0 0)
  exact ⟨200, by native_decide⟩

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

/-! ## THE HEADLINE OF THIS CARD -/

/-- **`poseidonRender.Valid` IS UNSATISFIABLE.** Six of its eleven clauses are false at this
    render; one refutation is enough and this uses clause 1. This is the card's own stop condition
    stated as a theorem rather than as a report line: C.1's `poseidon_valid` sorry is not an
    unfinished proof, it is an impossible one, and the only way to finish it is upstream - a
    `poseidonMeta` whose `protocol` is the real `ProtocolPlan`, which needs the halo2 constraint
    system that is not in the tree (D.2 gap A), the same circuit gap D.3 named.

    What this does NOT break: `lowering_equivalence_poseidon` takes no `R.Valid` hypothesis
    (`Statements` section 5), so C.1's headline survives as stated; `Valid` enters only through
    `blockContracts_of_valid`, which is where the sorry sits. -/
theorem poseidonRender_notValid : ¬ poseidonRender.Valid :=
  fun h => poseidonValid_circuitMeta_not h.circuitMeta

end Midfall.Instances.PoseidonValid
