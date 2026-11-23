/-
  Midfall.Instances.PoseidonValid

  C.4 (GEN - SKELETON, box 2 h, branch t/C.4 from a1febbf): the `Render.Valid` obligation
  (C.1's `poseidon_valid`, deleted by PL.1/W13) taken apart into ONE NAMED LEMMA PER CLAUSE, and
  every clause decided at `poseidonRender`.

  RE-MEASURED BY F.1 (GEN - PORT, branch t/F.1 from 3e15e9f). F.1 exported the deployment's real
  constraint system into `fixtures/conformance/poseidon/cs.json` - gates, lookups, trashcans,
  permutation columns, challenge phase - and `poseidonMeta` is now `ConstraintSystemMeta.new`
  applied to it instead of a transcription of counts. That moves FOUR of C.4's six refutations.
  The table below is the F.1 re-measurement; every value in it is printed by this file.

  ## THE SEVEN-CLAUSE TABLE (OBJ.8 step 5 - THE AUTHORITY FOR `Render.Valid` AT F1)

  ST.6 (D-P67) cut the frozen `Render.Valid` over to the seven V3 clauses, and OBJ.8 re-measured
  every one of them at `poseidonRender`. The fourteen-row table C.4/F.1 kept is retired below this
  block; the per-clause lemmas it cites still exist and are still what decides each verdict, but the
  VERDICTS are these seven, and every cell is what was MEASURED at this commit, not what the card
  predicted. `#check` lines and the deciding lemmas are in the sections that follow.

    #  frozen clause    verdict    deciding evidence at `poseidonRender`
    1  generated        REFUTED    NOT for the reason the card predicted. OBJ.8 step 2 replaced
                                   `poseidonE.delta := 2` with the field constant, which killed the
                                   delta refutation OBJ.7 gate 9 measured. What is left is bigger:
                                   `Render.generated` reads the payload from `R.plan.vk`, and the
                                   render's plan carries the PARSED artifact payload, which
                                   `generateAll` REFUSES at quotient.rs:202 ("VK must carry
                                   quotient constants") - OBJ.7 gate 11. Measured sorry-free as
                                   `poseidonValid_generated_not`. Step 3 (the render rebuilt from
                                   `generateAll`) is the card's own split; see section V3.
                                   **B4 (t/BOXe) LANDED THE MEASUREMENT §V3 CALLED FOR**: the exact
                                   sub-condition is `poseidonRender.plan.vk.quotientConstOffsetWords
                                   = none` (`ValidV3InhabitationF1.f1_payload_constOffset_none`),
                                   the generator ACCEPTS this circuit once the four reservation
                                   fields are filled (`genFilledRun_isOk`), the filled payload is a
                                   FIXED POINT of the projection `generated` reads through
                                   (`genFilledOut_plan_vk_is_the_payload_it_was_given`), and the
                                   clause is therefore SATISFIABLE
                                   (`f1GeneratedRender_generated`) - so this is a data-sourcing
                                   defect (OBJ.10 + OBJ.8 step 3/4), NOT a frozen edit. See §V3.
    2  inputs           PROVED     `poseidonValid_inputs`, unchanged: three `rfl` and one
                                   `native_decide` (k = 6 = vk.domain.k).
    3  program          PROVED     MOVED OPEN -> PROVED BY OBJ.9 STEP 3: `poseidonValid_program`.
                                   All three halves are now THEOREMS at the render: the decidable
                                   bundle `programOkB poseidonRender = true` (`deciding_programOkB`,
                                   fourteen conjuncts, ~11 s of COMPILED evaluation - the card's
                                   five-conjunct split was NOT needed and was NOT taken), plus
                                   `GasCallOk` and `ExitDiscipline`, each witnessed at fuel 20000.
                                   Before this card the bundle existed only as a VM `def`
                                   (`StatementsV3Deploy.recon1_programOkB_ok`), never as a theorem.
    4  noWriters        PROVED     `poseidonValid_noWriters`, fuel 20000 exhibited (OBJ.9 step 4:
                                   C.4 needed 200, F.1 exhibited 2000, this card raises the exhibit to
                                   the fuel the two program scans use, and 20000 is proved true at
                                   `deciding_noWriters_fuel`, so the exhibit is not at its limit).
    5  env              PROVED     `poseidonValid_slots` - all ten `EnvAgrees` clauses, unchanged
                                   ("env as before" in the card's Accept line).
    6  payload          HALF       STILL HALF, AND NOW WITH THEOREMS WHERE IT HAD `#eval`S: OBJ.9
                                   step 5 lands `poseidonValid_payload_scalars`, the EIGHT codec-free
                                   facts (`digest`, `numInstances`, `k`, `nInv`, `omega`,
                                   `omegaInv`, `omegaInvToL`, `accWords`) as ONE theorem at the
                                   render, where before they existed only as the VM booleans
                                   `recon1_payload_scalars_ok` and `recon1_payload_digest_ok`. The
                                   five point fields (`g1Base`, `g2Base`, `negSG2`, `fixedComms`,
                                   `permutationComms`) are OPEN - `toEip` is noncomputable at the
                                   placeholder codec, exactly the card's "point half OPEN". NOT a
                                   PROVED cell: eight of fourteen fields is a half, and it is
                                   reported as a half.
    7  supported        PROVED     REPAIRED AND DISCHARGED BY R.7 (D-P59). The field
                                   `wf.permutationCommitmentsMatch` compared the VK's sigma commitments
                                   against `divCeil columns (csDegree - 2)` - the count the PROOF
                                   carries, one product commitment per chunk - and now compares them
                                   against the permutation COLUMNS: 8 = 8 at `poseidonVkExec`
                                   (`deciding_supported_perm`), and `poseidonValid_supported` proves
                                   all twelve fields. FALSIFIER: `f7_mutantNotWellFormed`.

  SO, RE-MEASURED BY OBJ.9 (GEN/PROOF, branch t/OBJ.9 from 2f3f39d): **5 PROVED, 1 HALF-PROVED,
  0 OPEN, 1 REFUTED out of seven.** OBJ.9 moved exactly ONE cell - `program` OPEN -> PROVED - and
  strengthened the evidence behind `payload`'s half without moving its verdict. `inputs`,
  `noWriters`, `env` and `supported` were already PROVED at 2f3f39d and are re-measured, not
  re-claimed. `poseidonRender_notValid` still holds and still runs through `generated` ALONE,
  because R.7 CLOSED the `supported` refutation: the old route is gone, not merely unused.
  `Render.Valid` - the frozen name of the one text `Midfall.LoweringV3.ValidV3` - is therefore
  STILL NOT INHABITED at the fixture, and the single clause that stops it is `generated`: OBJ.9
  step 1 was ATTEMPTED AND REFUTED, not skipped (exact goal state at section V3). Reporting it as
  inhabited would be the lie the brief warns about. Nothing here was weakened to make F1 fit: the
  clause now compares what the Rust VK actually holds.

  OBJ.9's own finding, recorded rather than fixed: the PLAN ORDERS THIS WRONG. PLAN-V3 section 5 puts
  OBJ.9 in M3 ("the clause table at F1") and OBJ.10 in M4 ("the artifact" pair), so M3 is expected to
  close `generated` at the fixture BEFORE M4 lands the data-level base payload `generateVkFromBase`
  that `generated` needs. Step 1 cannot succeed in that order. See section V3 for the two exits.

  ## THE RETIRED FOURTEEN-ROW TABLE (F.1's measurement of the pre-ST.6 text; kept for provenance)

    #   clause          verdict   deciding value (F.1)
    1   circuitMeta     PROVED    derived numEvals 48 against the plan's 48.
    2   layout          REFUTED   `fromProtocol` on the REAL protocol gives proofLen 4224 against
                                  the plan's transcribed 4320. Now a conjunct of `generated`.
    3   invariants      REFUTED   check 16: planned PcsMemory against recomputed. Now `generated`.
    4   model           SORRY     true by construction, not machine-dischargeable. Now `generated`.
    5   inputs          PROVED    unchanged; it is the inputs clause of the seven.
    6   codegen         PROVED    FLIPPED BY M2 (G1.1 + G1.2 + OBJ.2): AST 14054 tokens / 74
                                  statements against text 14054 (was 6779/66). Now `program`.
    7   closed          PROVED    unchanged. Now `program` (`mainClosed`).
    8   slots           PROVED    all ten `EnvAgrees` clauses. Now `env`.
    9   supported       REFUTED   narrowed to ONE field: `permutationCommitmentsMatch`. Still a
                                  clause, and still the refutation.
    10  noWriters       PROVED    fuel 2000/20000 true; 200 EXHAUSTED. Still a clause.
    11  transcriptMptr  PROVED    TRANSCRIPT_MPTR = 4096. Now a theorem of `program`.
    12  vkPins          PROVED    VK_MPTR, payload length, instance count, disjointness. NOT a
                                  clause; four of the six are theorems of `program` and the
                                  structures themselves left the frozen surface in OBJ.8 step 4.
    13  vkProgressPins  PROVED    EXPECTED_VK_LENGTH and EXPECTED_VK_CODEHASH. Same fate.
    14  returnMptr      PROVED    RETURN_MPTR = some 4096. A THEOREM of `program`.

  So 10 PROVED, 3 REFUTED, 1 SORRY out of the retired fourteen.

  ## WHAT WAS NOT TOUCHED

  `PoseidonV2.lean` is C.1's. At this card's landing `poseidon_valid` was still a sorry there;
  PL.1/W13 has since DELETED it and the unconditional headline that consumed it, because the
  negation below is PROVED. Restating either with `(hR : poseidonRender.Valid)` would be the trap
  D-P54 rejects: a hypothesis refuted in the tree proves anything. The conditional
  `poseidon_block_contracts` keeps `hR` as a binder and is not applied at this render.
  `Statements.lean` is frozen; `Blocks.lean` sections 6 and 7 are C.2's. R.7 (D-P59) edited TWO
  v1 files under its recorded exception - `Halo2/Exec/VerifyingKey.lean` (the clause, its docstring
  bullet and the in-file KAT, line count unchanged) and `Halo2/Spec/Degrees.lean:101-103` (docstring
  only, line count unchanged) - plus `scripts/kat_gate.py`'s KAT pins; no fixture was touched.

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

/-- **THE CIRCUIT-META CLAUSE - PROVED SINCE F.1.** `ConstraintSystemMeta.new` on the deployment's
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

/-- THE PRINTED VALUE FOR THE CIRCUIT-META CLAUSE: the derived numEvals, which C.4 measured at 27 and F.1 moves to
    48 - the artifact's own 0x600 word count. AXIOM:
    deciding_circuitMeta_numEvals._native.native_decide.ax_1_1. -/
theorem deciding_circuitMeta_numEvals :
    (match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
      | .ok m => m.numEvals | .error _ => 0) = 48 := by
  native_decide

/-! ## 2. layout - REFUTED -/

/-- THE DECIDING VALUE FOR THE LAYOUT CLAUSE: derived proofLen 4224 against the plan's 4320. AXIOM:
    deciding_layout._native.native_decide.ax_1_1. -/
theorem deciding_layout :
    (match ProofCalldataLayout.fromProtocol poseidonPlanV2.meta_.protocol abiVerifyProofProofCptr
        poseidonPlanV2.meta_.numEvals poseidonPlanV2.meta_.numPointSets with
      | .ok l => l.proofLen | .error _ => 0) ≠ poseidonPlanV2.proofLayout.proofLen := by
  native_decide

/-- **THE LAYOUT CLAUSE - REFUTED.** The literal `Render.Valid.layout`. D.3 already proved the root
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

/-- The two printed proof lengths the layout clause now turns on: 4224 derived against 4320
    transcribed. -/
def deciding_layout_derivedProofLen : Nat :=
  match ProofCalldataLayout.fromProtocol poseidonPlanV2.meta_.protocol abiVerifyProofProofCptr
      poseidonPlanV2.meta_.numEvals poseidonPlanV2.meta_.numPointSets with
  | .ok l => l.proofLen | .error _ => 0

def deciding_layout_planProofLen : Nat := poseidonPlanV2.proofLayout.proofLen

/-! ## 3. invariants - REFUTED -/

/-- THE DECIDING VALUE FOR THE INVARIANTS CLAUSE: the plan still refuses its own invariant check, but for a
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

/-- **THE INVARIANTS CLAUSE - REFUTED, AND THE CARD DID NOT PREDICT IT.** The literal
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

/-- **THE MODEL CLAUSE - SORRY, OPEN.** The literal `Render.Valid.model`.

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

/-- **THE INPUTS CLAUSE - PROVED.** The build inputs are the configuration's and the VK's, not
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

/-! ## 6. codegen - PROVED (M2: G1.1 + G1.2 + OBJ.2 + ST.3) -/

/-- THE DECIDING VALUE FOR THE CODEGEN CLAUSE: the whole conjunction is TRUE. It was false at every commit
    before this batch - `mainAsmRaw` emitted 6,779 of the generator's 14,054 tokens, and the codegen
    clause was the one refutation here that was about the AST emitter rather than about typed-in plan meta.
    WP-G1 closed it: the five accumulator-codec definitions and `q_program_fail` / `q_pow5` as
    structured trees (G1.1, G1.2) and the 6,384-token quotient numerator as the parse of the model's
    own lines (OBJ.2). AXIOM: deciding_codegen._native.native_decide.ax_1_1. -/
theorem deciding_codegen : codegenAgrees poseidonPv poseidonM = true := by native_decide

/-- The half that is TRUE, pinned so the refutation cannot be read as "the emitter is broken
    everywhere": the ABI-shape guard block prints to the guard text token for token. AXIOM:
    deciding_codegen_guard._native.native_decide.ax_1_1. -/
theorem deciding_codegen_guard :
    yulTokens (YulSemantics.EVM.print (abiGuardBlock poseidonM)) == abiGuardTokens poseidonM := by
  native_decide

/-- THE WITNESS FOR THE CODEGEN CLAUSE, as the numbers a reader can check by eye: the emitted main block is
    the generator's main block - 74 statements and 14,054 tokens on both sides, where the emitter
    reached 66 statements / 6,779 tokens before this batch. The three regions the gap was made of
    are 823 (accumulator codecs) + 68 (quotient helpers) + 6,384 (numerator) = 7,275 tokens, and
    6,779 + 7,275 = 14,054 exactly: nothing was padded and nothing is left un-emitted at this
    render. AXIOM: deciding_codegen_witness._native.native_decide.ax_1_1. -/
theorem deciding_codegen_witness :
    (mainAsmRaw poseidonPv poseidonM).length = 74 ∧
      (yulTokens (YulSemantics.EVM.print (mainAsmRaw poseidonPv poseidonM))).length = 14054 ∧
      (mainAssemblyTokens poseidonM).length = 14054 := by
  native_decide

/-- **THE CODEGEN CLAUSE - PROVED.** The literal `Render.Valid.codegen`, and the only `Valid` clause this
    repository has ever been able to close by building the missing emitter instead of narrowing the
    claim. `Program.lean` kept the gap as a RED GATE on purpose ("`CodegenAgrees` below is FALSE
    until they are, which is the point: the gap is a red gate, not a silent omission") and the gate
    is now green at the deployment. What is still NOT claimed, and is what the un-emitted arms named
    in `mainAsmRaw` and `emitQuotientHelpersAt` are for: a render with an accumulator, or with the
    `q_limb7` / `q_widelimb7` helper flags set, makes this clause FALSE again rather than quietly
    skipping a region. This is a statement about ONE render, discharged by computation on it. -/
theorem poseidonValid_codegen : CodegenAgrees poseidonRender.pv poseidonRender.model := by
  show codegenAgrees poseidonPv poseidonM = true
  exact deciding_codegen

/-- THE STRUCTURAL TIE AT THE DEPLOYMENT (OBJ.2): the emitter's AST is `stmtsBeq`-equal to the
    parse of the generator text, for both assembly blocks. Stronger than the codegen clause, which only
    compares token streams and cannot see builtin-versus-call (RV-27). The parsed numerator half
    agrees by construction - see `codegenStruct`'s docstring for what is and is not being trusted
    here - and the structured half is what the per-region mutation falsifiers in
    `M2BatchKats.lean` put teeth into. AXIOM:
    deciding_codegenStruct._native.native_decide.ax_1_1. -/
theorem deciding_codegenStruct :
    codegenStruct (mainAsmRaw poseidonPv poseidonM) poseidonM = true := by native_decide

/-! ## 7. closed - PROVED -/

/-- **THE CLOSED-PROGRAM CLAUSE - PROVED.** After inlining, the main block's only free names are the two
    wrapper locals. `Program.lean:128-134` says this is discharged by native_decide in Instances/
    per render because `Shared.freeNames` is not kernel-reducible; this is that discharge.
    AXIOM: poseidonValid_closed._native.native_decide.ax_1_1. -/
theorem poseidonValid_closed : mainClosed poseidonRender.pv poseidonRender.model = true := by
  show mainClosed poseidonPv poseidonM = true
  native_decide

/-! ## 8. slots - REFUTED -/

/-- **THE ENV CLAUSE - PROVED SINCE F.1.** `EnvAgrees`'s `negLagranges` clause reads
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

/-- THE NINE `EnvAgrees` CLAUSES THAT HOLD, so the env clause's refutation is located rather than total:
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

/-- **THE ENV CLAUSE, WHOLE - PROVED.** All ten `EnvAgrees` clauses at `poseidonRender`: the nine
    C.4 already proved, plus `negLagranges`. This is the first of C.4's six refutations to become a
    proof, and it is the same root cause the circuit-meta clause had - the missing constraint system - closed by
    the same export. -/
theorem poseidonValid_slots :
    EnvAgrees poseidonRender.E poseidonRender.vk poseidonRender.pv poseidonRender.params
      poseidonRender.sG2gen := by
  obtain ⟨hmod, htrunc, hd1, hd2, hbary, homega, horder, hng2, hsg2, hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, hd2⟩, hbary, homega, horder, ?_, hng2, hsg2, hdig⟩
  show poseidonPv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
  exact poseidonValid_slots_negLagranges

/-! ## 9. supported - PROVED (R.7, D-P59) -/

/-- **CLAUSE 9'S FIRST FACE IS CLOSED BY F.1.** `SupportedV2.wf.csDegreeMatches` demands
    `vk.cs.degree = .ok vk.csDegree`. C.4 measured the ported degree recomputing to 3 against the
    imported 5 - D.2's gap A, an empty `gates` array. With the exported gates the ported
    `ConstraintSystem.degree` recomputes to 5 and the clause HOLDS. AXIOM:
    deciding_supported_degree._native.native_decide.ax_1_1. -/
theorem deciding_supported_degree :
    (match poseidonVkExec.cs.degree with | .ok d => d | .error _ => 0) = poseidonVkExec.csDegree := by
  native_decide

/-- **THE REPAIRED CLAUSE, DECIDED AT F1 (R.7 / D-P59).** `WellFormed.permutationCommitmentsMatch`
    now compares the VK's sigma commitments with the permutation COLUMNS - one per column, which is
    what the reference builds: `proofs/src/plonk/permutation.rs:123` reads
    `(0..argument.columns.len())` and `permutation/keygen.rs:244-250` commits
    `Vec::with_capacity(p.columns.len())`, one push per permutation polynomial. The `divCeil` that
    used to sit here is the count the PROOF carries (one product commitment per chunk,
    `permutation/verifier.rs:41-45`, ported as `Permutation.readProductCommitments`), never the VK's.
    WITNESS: both sides are 8 at `poseidonVkExec` - vk.json lists 8
    `permutation_commitments_compressed_hex` (PoseidonEnv gate 1) and F.1's cs.json names 8
    `permutation.columns` (gate 13). AXIOM:
    deciding_supported_perm._native.native_decide.ax_1_1. -/
theorem deciding_supported_perm :
    poseidonVkExec.permutation.commitments.size =
      poseidonVkExec.cs.permutation.columns.size := by native_decide

/-- `csDegreeMatches` in the shape the clause states it: `deciding_supported_degree` decides the
    match, and the `.error` arm is the one the fixture does not take (`csDegree` is vk.json's 5).
    AXIOMS: deciding_supported_degree_eq._native.native_decide.ax_1_1, ax_1_2. -/
theorem deciding_supported_degree_eq :
    poseidonVkExec.cs.degree = .ok poseidonVkExec.csDegree := by
  cases h' : poseidonVkExec.cs.degree with
  | ok d =>
      have h := deciding_supported_degree
      simp only [h'] at h
      exact congrArg Except.ok h
  | error e =>
      have h := deciding_supported_degree
      simp only [h'] at h
      exact absurd h (by native_decide)

/-- **ALL SEVEN `WellFormed` FIELDS AT THE FIXTURE KEY (R.7 step 5).** Six are computations on the
    imported key; `permutationCommitmentsMatch` is the repaired one above. AXIOMS:
    deciding_supported_wf._native.native_decide.ax_1_1 through ax_1_4, plus the ones named above. -/
theorem deciding_supported_wf : poseidonVkExec.WellFormed Features.solidity :=
  { csDegreeMatches := deciding_supported_degree_eq,
    chunkLenPositive := by native_decide,
    domainConsistent := by native_decide,
    permutationCommitmentsMatch := deciding_supported_perm,
    fixedCommitmentsMatch := by native_decide,
    singlePhase := by native_decide,
    committedInstancesOn := rfl,
    advicePhaseTotal := by native_decide,
    challengePhaseTotal := by native_decide }

/- **THE SUPPORTED CLAUSE WAS REFUTED HERE UNTIL R.7.** The refutation `poseidonValid_supported_not` ran
    through `wf.permutationCommitmentsMatch` - the mis-ported field D-P59 repairs. At the fixture the
    VK's 8 sigma commitments ARE the 8 permutation COLUMNS (`deciding_supported_perm`), and the
    `divCeil 8 3` = 3 that used to refute the clause is the number of product commitments the PROOF
    carries, not the number the VK holds. The whole clause is proved below, once the twelve fields it
    needs are in scope. -/

/-- The `SupportedV2` fields that hold independently of `wf`, so the supported clause's proof is
    located. Every one is a computation at the render's own vk, plan and flags. AXIOMS:
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

/-- **THE SUPPORTED CLAUSE - PROVED (R.7 step 5, D-P59).** All twelve `SupportedV2` fields at
    `poseidonRender`: the computations of `poseidonValid_supported_rest`, `vkPoints` from the
    generator clauses above, and `wf` from `deciding_supported_wf` - whose repaired field is
    `deciding_supported_perm`. Nothing was weakened to get here: the clause text is D-P59's
    `vk.permutation.commitments.size = vk.cs.permutation.columns.size`, and the FALSIFIER that shows
    the repaired clause still has teeth is `Instances/StatementsV3Falsifiers.f7_mutantNotWellFormed`
    (one sigma commitment dropped: 7 against 8, refused). NO new axiom beyond the native_decide ones
    named above: `#print axioms poseidonValid_supported`. -/
theorem poseidonValid_supported : SupportedV2 poseidonRender := by
  obtain ⟨hadvice, hinst1, hinst2, hsphase, hlimbs, hlay1, hlay2, hprod1, hprod2, hnoacc,
    hemb1, hemb2, hsep, _hci, hnorot⟩ := poseidonValid_supported_rest
  refine ⟨hadvice, ⟨hinst1, hinst2⟩, hnorot, hsphase, hlimbs, poseidonValid_supported_vkPoints,
    ⟨hlay1, hlay2⟩, ⟨hprod1, hprod2⟩, deciding_supported_wf, hnoacc, ⟨hemb1, hemb2⟩, hsep⟩

/-! ## 10. noWriters - PROVED -/

/-- The fuel is exhibited, not guessed, and it is not at its limit: `noWritersScan` answers false at
    exhaustion (R-37), so a true verdict at a finite fuel is a real scan of the whole block, and the
    same scan at ten times the fuel agrees. AXIOM:
    deciding_noWriters_fuel._native.native_decide.ax_1_1. -/
theorem deciding_noWriters_fuel :
    noWritersFuel 2000 (asmOf poseidonPv poseidonM 0 0) = true ∧
      noWritersFuel 20000 (asmOf poseidonPv poseidonM 0 0) = true := by
  native_decide

/-- **THE NO-WRITERS CLAUSE - PROVED, AND RE-EXHIBITED AT FUEL 20000 BY OBJ.9 STEP 4.** The
    generated program performs no world write - no `sstore`, `tstore`, `log*`, `create*` or
    value-bearing `call`. C.4 exhibited fuel 200; with the real protocol the pcs arm emits 225
    statements instead of nothing, the main block is bigger, and 200 is now EXHAUSTED (measured
    false) while 2000 and 20000 both answer true (`deciding_noWriters_fuel`). OBJ.9 step 4 raises
    the exhibited witness to 20000, the SAME fuel the two program scans and `ExitDiscipline` are
    witnessed at, so the four fuel-bounded clauses of the text are all read at one fuel and none of
    them is at its limit. The statement is unchanged - `NoWriters` pins no fuel - and only the
    witness moved. AXIOM: poseidonValid_noWriters._native.native_decide.ax_1_1. -/
theorem poseidonValid_noWriters : NoWriters (poseidonRender.prog 0 0) := by
  show NoWriters (asmOf poseidonPv poseidonM 0 0)
  exact ⟨20000, by native_decide⟩

/-! ## 11. transcriptMptr - PROVED -/

/-- **THE TRANSCRIPT-MPTR CLAUSE - PROVED.** The generator's own TRANSCRIPT_MPTR lies above Solidity's reserved
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

/-! ## 15. program - PROVED (OBJ.9 step 3) -/

/-- **THE DECIDABLE BUNDLE OF THE `program` CLAUSE, AS A THEOREM (OBJ.9 STEP 3).** Before this card
    `programOkB poseidonRender = true` existed only as a VM `def` plus a `#eval`
    (`StatementsV3Deploy.recon1_programOkB_ok`, seven facts printed as one 7-tuple). Here it is the
    whole fourteen-conjunct bundle proved at the render: `codegenStruct`, `codegenAgrees`,
    `constsCoherent`, `callsResolved`, `noShadowProg`, `noShadowCore`, `mainClosed`, the
    `TRANSCRIPT_MPTR` floor, `cdBoundB`, `hasMultiPointSet`, `transcriptRegionOk`,
    `g1IdentityFloor`, `negLagrangesFloor` and `permCommMatchRepaired`.

    THE RENDER IS NONCOMPUTABLE, so the decision runs on the computable faces and is transferred back
    by `show` - that is, by the kernel: `poseidonPv_eq`, `poseidonM_eq`, `poseidonCfg_eq` and
    `poseidonVk_eq` are all `rfl`. COST, MEASURED: ~11 s of compiled evaluation at the default
    `maxRecDepth` and default heartbeats. NOTHING WAS RAISED. The card's Stop-if named a
    five-conjunct split if this exceeded 60 s; it did not, so the Bool is landed whole and the split
    was not taken. AXIOM: deciding_programOkB._native.native_decide.ax_1_1. -/
theorem deciding_programOkB : programOkB poseidonRender = true := by
  show programOkCore poseidonPv poseidonM poseidonConfig.numInstances poseidonVkExec = true
  native_decide

/-- **PG-GAS AT THE FIXTURE, AS A THEOREM (OBJ.9 step 3).** `recon1_gas_ok` measured
    `gasScan 20000 (.b (asmOf poseidonPv poseidonM 0 0)) = true` in the VM; this is the same fact as
    a proposition, at the render's own program. F1 is the EASY case for this scan - the main block
    contains no `gas` token at all (`StatementsV3Deploy.mainBlockTokenCounts_ok`) - so the witness
    costs ~2 s and the clause's teeth are for the external-evaluator render. AXIOM:
    deciding_gasCallOk._native.native_decide.ax_1_1. -/
theorem deciding_gasCallOk : GasCallOk (poseidonRender.prog 0 0) := by
  show GasCallOk (asmOf poseidonPv poseidonM 0 0)
  exact ⟨20000, by native_decide⟩

/-- **THE ONE EXIT SCAN AT THE FIXTURE, AS A THEOREM (OBJ.9 step 3).** `exitDisciplineAtDeploy_ok`
    measured the triple (tail found, passes at 20000, FAILS at 200) in the VM; the fuel is therefore
    exhibited above its measured threshold of 299 and not at its limit, so the verdict is a real scan
    of the block and not an exhaustion answer. Same transfer by `show`, same cost class. AXIOM:
    deciding_exitDiscipline._native.native_decide.ax_1_1. -/
theorem deciding_exitDiscipline : ExitDiscipline (poseidonRender.prog 0 0) := by
  show ExitDiscipline (asmOf poseidonPv poseidonM 0 0)
  exact ⟨20000, by native_decide⟩

/-- **THE PROGRAM CLAUSE - PROVED BY OBJ.9 STEP 3.** `programOk poseidonRender`: the decidable
    bundle plus the two scans, all three halves theorems at the render. This is the ONE cell of the
    seven-clause table this card moved: OPEN -> PROVED. Nothing was weakened to get it - the clause
    text is RECON.1's, the bundle is the fourteen conjuncts `programOkCore` computes, and the two
    scans are the `∃ n` forms the text states, each witnessed at fuel 20000 rather than at a fuel
    pinned in the statement. AXIOMS: deciding_programOkB / deciding_gasCallOk /
    deciding_exitDiscipline, one `._native.native_decide.ax_1_1` each. -/
theorem poseidonValid_program : programOk poseidonRender :=
  ⟨deciding_programOkB, deciding_gasCallOk, deciding_exitDiscipline⟩

/-! ## 16. payload - the scalar half, landed as THEOREMS (OBJ.9 step 5) -/

/-- **THE EIGHT CODEC-FREE FIELDS OF `PayloadAgrees poseidonRender`, AS ONE THEOREM (OBJ.9 STEP 5).**
    `digest`, `numInstances`, `k`, `nInv`, `omega`, `omegaInv`, `omegaInvToL` and `accWords`:
    every field of the clause that mentions no codec and no group element. Before this card these
    existed only as two VM booleans (`recon1_payload_scalars_ok`, seven facts, and
    `recon1_payload_digest_ok`). The five that remain OPEN - `g1Base`, `g2Base`, `negSG2`,
    `fixedComms`, `permutationComms` - compare payload bytes with `toEip` of a group element, and
    `toEip` is noncomputable at the placeholder codec (`g1CodecZ`), so they are neither proved nor
    refuted here: `payload` STAYS HALF, eight of fourteen fields.

    Each conjunct is verbatim the corresponding field type at `R := poseidonRender`; the `show` is
    the kernel transferring from the render to D.1's and D.2's computable terms, and
    `poseidonValid_payload_scalars_are_fields` below is the machine-checked tie that says these eight
    equations ARE eight fields of the structure and not eight equations that merely look like them.
    AXIOM: poseidonValid_payload_scalars._native.native_decide.ax_1_1. -/
theorem poseidonValid_payload_scalars :
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.vkDigest
      = frWord poseidonRender.vk.transcriptRepr ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.numInstances
      = BitVec.ofNat 256 poseidonRender.cfg.numInstances ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.k
      = BitVec.ofNat 256 poseidonRender.vk.domain.k ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.nInv
      = frWord (((2 ^ poseidonRender.vk.domain.k : ℕ) : Fr blsR))⁻¹ ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.omega
      = frWord poseidonRender.vk.domain.omega ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.omegaInv
      = frWord poseidonRender.vk.domain.omegaInv ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.omegaInvToL
      = frWord (poseidonRender.vk.domain.omegaInv
        ^ poseidonRender.plan.meta_.rotationLast.natAbs) ∧
    ((payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
      accWordsOfEncoding poseidonRender.cfg.accumulator := by
  show payloadWord poseidonPv vkHeaderTemplateSlotsDefault.vkDigest
        = frWord poseidonVkExec.transcriptRepr ∧
      payloadWord poseidonPv vkHeaderTemplateSlotsDefault.numInstances
        = BitVec.ofNat 256 poseidonConfig.numInstances ∧
      payloadWord poseidonPv vkHeaderTemplateSlotsDefault.k
        = BitVec.ofNat 256 poseidonVkExec.domain.k ∧
      payloadWord poseidonPv vkHeaderTemplateSlotsDefault.nInv
        = frWord (((2 ^ poseidonVkExec.domain.k : ℕ) : Fr blsR))⁻¹ ∧
      payloadWord poseidonPv vkHeaderTemplateSlotsDefault.omega
        = frWord poseidonVkExec.domain.omega ∧
      payloadWord poseidonPv vkHeaderTemplateSlotsDefault.omegaInv
        = frWord poseidonVkExec.domain.omegaInv ∧
      payloadWord poseidonPv vkHeaderTemplateSlotsDefault.omegaInvToL
        = frWord (poseidonVkExec.domain.omegaInv ^ poseidonPlanV2.meta_.rotationLast.natAbs) ∧
      ((payloadWord poseidonPv vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
        (payloadWord poseidonPv vkHeaderTemplateSlotsDefault.accOffset).toNat,
        (payloadWord poseidonPv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
        (payloadWord poseidonPv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
        accWordsOfEncoding poseidonConfig.accumulator
  native_decide

/-- **THE TIE, CHECKED AND NOT PROSE.** The eight conjuncts above are the eight FIELD TYPES of
    `PayloadAgrees poseidonRender`, in field order: this term typechecks only if each projection has
    exactly the conjunct claimed, so the conjunction is a sub-list of the clause and not an imitation
    of it. No axiom: it is eight structure projections. -/
theorem poseidonValid_payload_scalars_are_fields (P : PayloadAgrees poseidonRender) :
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.vkDigest
      = frWord poseidonRender.vk.transcriptRepr ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.numInstances
      = BitVec.ofNat 256 poseidonRender.cfg.numInstances ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.k
      = BitVec.ofNat 256 poseidonRender.vk.domain.k ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.nInv
      = frWord (((2 ^ poseidonRender.vk.domain.k : ℕ) : Fr blsR))⁻¹ ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.omega
      = frWord poseidonRender.vk.domain.omega ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.omegaInv
      = frWord poseidonRender.vk.domain.omegaInv ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.omegaInvToL
      = frWord (poseidonRender.vk.domain.omegaInv
        ^ poseidonRender.plan.meta_.rotationLast.natAbs) ∧
    ((payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
      accWordsOfEncoding poseidonRender.cfg.accumulator :=
  ⟨P.digest, P.numInstances, P.k, P.nInv, P.omega, P.omegaInv, P.omegaInvToL, P.accWords⟩

/-- **D-GATE1's NEW `PayloadAgrees` FIELD, BY COMPUTATION.** The parsed artifact payload carries 35
    constants, so the eleven-header window (`vkHeaderTemplateSlotsDefault` slots 0-10) is present
    with room to spare. `native_decide` is in `Instances/`, as D-P71 requires; the render's own
    view is the same object by `rfl` (`poseidonRender_plan_isD1`). -/
theorem poseidon_payload_constantsLength : 11 ≤ poseidonPv.vk.constants.length := by
  native_decide

theorem poseidonRender_payload_constantsLength :
    11 ≤ poseidonRender.pv.vk.constants.length := by
  show 11 ≤ poseidonPv.vk.constants.length
  exact poseidon_payload_constantsLength

/-- **THE DECIDABLE HALF OF `ValidV3 poseidonRender`, IN ONE DECLARATION (OBJ.9's deliverable).**
    Five of the seven clauses - `inputs`, `program`, `noWriters`, `env`, `supported` - plus the
    eight scalar facts of `payload`. What is NOT here is the whole of `payload` (five point fields,
    OPEN at the placeholder codec) and `generated` (REFUTED, section V3), and the absence of
    `generated` from this conjunction is exactly why `ValidV3 poseidonRender` is still uninhabited.
    No new axiom: every conjunct is one of the theorems above. -/
theorem poseidonValid_decidableHalf :
    (poseidonRender.inputs.numInstances = poseidonRender.cfg.numInstances ∧
      poseidonRender.inputs.accEncoding = poseidonRender.cfg.accumulator ∧
      poseidonRender.inputs.k = poseidonRender.vk.domain.k ∧
      poseidonRender.inputs.truncatedChallenges = Features.solidity.truncatedChallenges) ∧
    programOk poseidonRender ∧ NoWriters (poseidonRender.prog 0 0) ∧
      EnvAgrees poseidonRender.E poseidonRender.vk poseidonRender.pv poseidonRender.params
        poseidonRender.sG2gen ∧
    SupportedV2 poseidonRender ∧
    payloadWord poseidonRender.pv vkHeaderTemplateSlotsDefault.vkDigest
      = frWord poseidonRender.vk.transcriptRepr :=
  ⟨poseidonValid_inputs, poseidonValid_program, poseidonValid_noWriters, poseidonValid_slots,
    poseidonValid_supported, poseidonValid_payload_scalars.1⟩

/-! ## V3. THE SEVEN FROZEN CLAUSES, AND THE ONE ROW THIS CARD COULD NOT CLOSE (OBJ.8 step 3/5)

  The table in the header is the verdict. This section is the EVIDENCE for the two cells the card
  expected to flip and did not, and the exact goal state of the row OBJ.8 records instead of forcing.

  **OBJ.9 ATTEMPTED STEP 1 AND STOPPED ON THIS WALL - THE EXACT GOAL STATE.** OBJ.9's step 1 names a
  route, `Except.eq_ok_getOk` (`Midfall/Common/Except.lean`, landed by OBJ.8 for exactly this), and
  the route was run, not assumed. `GeneratedBy poseidonRender` needs an `out` with
  `generated poseidonRender = .ok out`, and `eq_ok_getOk` supplies it from ONE hypothesis:

    h : (generated poseidonRender).isOk = true

  `poseidonRender` is noncomputable, so the VM cannot run `generated poseidonRender` itself; every
  argument it reads unfolds by `rfl` (`poseidonGenRender_eq_generated`), so the hypothesis is the
  same proposition at the computable face `poseidonGenRender`. Measured there, at this commit, by
  `native_decide`:

    Tactic `native_decide` evaluated that the proposition
      poseidonGenRender.isOk = true
    is false

  That is the wall, stated as a goal state and not as an opinion: the hypothesis `eq_ok_getOk` needs
  is FALSE, and its negation is the sorry-free `poseidon_generated_notOk` above. Step 1 is therefore
  not hard, not slow and not heartbeat-bound - it is IMPOSSIBLE at this commit, and any attempt to
  force it would be a proof of `False` from `poseidonValid_generated_not`. The clause was NOT
  weakened, NOT restated, and NOT bypassed; steps 2-5 landed and this row is recorded.

  **THE PLAN-ORDERING DEFECT THIS EXPOSES, AND THE TWO EXITS (OBJ.9's finding, named and not fixed).**
  PLAN-V3 section 5 places OBJ.9 in **M3** (line "M3 | ... ST.6 with OBJ.8, REF.7, ST.15, OBJ.9, ST.7
  ...", the clause table at F1) and OBJ.10 in **M4** ("M4 | ... OBJ.10, OBJ.12", the artifact pair).
  But `generated` reads the payload from `R.plan.vk`, and the only thing that can put a
  `generateAll`-acceptable payload there is OBJ.10's `generateVkFromBase` / `baseVkOfKeyData` - an
  M4 deliverable. **M3 as written cannot close `generated` before M4 exists.** The two exits, each of
  which needs a signature this card does not hold:
    (i) REORDER: pull OBJ.10 (and OBJ.11's G2 exports) forward into M3, or move the `generated` row
        of the clause table out of M3 and into M4, so the table is complete only after the artifact
        pair lands; or
    (ii) WIDEN: give `Render` a frozen `payload : Halo2VerifyingKey` field and read `generated`
        from it instead of from `R.plan.vk`, which cuts the circle without waiting for the port - a
        FROZEN-surface edit (W15: a sixth re-hash and a signature). This is exactly the first of the
        two frozen ways out listed a few lines below ("WHY STEP 3 CANNOT LAND WITHOUT A FROZEN
        DECISION", option (i)), and it is the only exit that does not wait on M4.
  This card names the defect and takes neither exit.

  **B4 (t/BOXe, `Midfall/Instances/ValidV3InhabitationF1.lean`) MEASURED BOTH EXITS AND NEITHER IS
  NEEDED.** The circle is cut WITHOUT a frozen edit: `generateAll` run on the payload with the four
  reservation fields filled (`PlanNewKats.vkFilled`, 31 / 1 / 32 / 3) returns `.ok`, and the plan
  it returns carries that very payload back out - `genFilledOut_plan_vk_is_the_payload_it_was_given`,
  proved field-wise through an injective ten-field signature, so exit (ii)'s `DecidableEq` is NOT
  required. `f1GeneratedRender` is the render of exit (i) built without touching `Render`: F1 with
  `plan`/`qblocks`/`model` re-sourced from the run, and `f1GeneratedRender_generated` is the
  clause holding of it. **So `generated` is satisfiable and the F1 refutation is a data-sourcing
  defect, not a spec defect.** What it does NOT change: `poseidonRender_notValid` stands, and
  `f1_plan_isNotTheGeneratorsPlan` shows a SECOND, payload-independent refutation - the generator's
  plan has `meta_.numPointSets = 3` against this render's raw 0, so re-sourcing the payload alone
  cannot close the clause; the render has to carry the generated plan, which re-points the DERIVED
  `pv` and therefore every `native_decide` clause in this file. That is a card, not an edit. And
  `generated` is the sole REFUTED clause but not the sole BLOCKER: `payload`'s five point fields are
  OPEN at the placeholder codec (B3's ticket), so no inhabitant of `ValidV3 poseidonRender` exists
  today even with `generated` closed.

  **WHY STEP 3 CANNOT LAND WITHOUT A FROZEN DECISION.** `Render.generated` reads the generator
  payload from `R.plan.vk` - the payload is smuggled in through the plan, because `Render` has no
  payload field and OBJ.7 forbade porting `generateVk` (OBJ.10 owns it). So the clause says
  "the plan is what `generateAll` returns when you feed it THIS plan's own payload". At the fixture
  that is a CIRCLE with no fixed point in the current record: the render's plan carries the PARSED
  artifact payload (`poseidonVkGen`, four reservation fields absent), `generateAll` refuses that
  payload at quotient.rs:202 (OBJ.7 gate 11), and so `generated poseidonRender` is not merely
  unproved - it is FALSE, and the delta fix cannot touch it. The two ways out are both frozen edits
  and neither is this card's to make unilaterally:
    (i) give `Render` a `payload : Halo2VerifyingKey` field and read `generated` from it, or
    (ii) set `poseidonRender.plan := poseidonGen.getOk h` and prove `(poseidonGen.getOk h).vk =
        poseidonVkFilled`, which needs a `DecidableEq Halo2VerifyingKey` that `Models.lean` does
        not derive (a v1 edit, forbidden here).
  Either way the render's `plan`/`model` stop unfolding by `rfl` to `poseidonPlanV2`/`poseidonM`,
  and every `show ... at poseidonPv` transfer in this file, in `PoseidonCoherence.lean` and in
  `PoseidonPins.lean` has to be re-pointed and re-decided - which is why the card's own split note
  (steps 1-3 separable from step 4) is the honest shape and step 3 is the row recorded here.

  WHAT THE GENERATOR DOES REPRODUCE, MEASURED. Run at the fixture on the FILLED payload and the
  field constant, `generateAll` agrees with this render on 16 of the 18 cheap faces you can compare
  without a `DecidableEq`: `meta_.numEvals` 48, `numDummyEvals`, `rotationLast`, `proofLayout`
  proofLen 4320 / proofEnd, `vk.len` 4576, `vk.runtimeBytes.size`, `vk.constants.length`,
  `memory.validate.isOk`, `memory.map.WellFormed`, and on the model `frDelta`, `numInstances`,
  `buildId`, `vkLen`, `proofLen`, `expectedVkCodehash`. It DISAGREES on two, and both are findings:
  `meta_.numPointSets` (the converged meta versus the raw `ConstraintSystemMeta.new` this render
  carries - `Generated.lean`'s own header predicts exactly this) and `qblocks`. So even with the
  payload circle cut, `generated` needs OBJ.6/OBJ.7's converged-meta question settled first.

  THE THREE RESIDUALS OF STEP 4, MEASURED AT THE FIXTURE (the brief's (a), (b), (c)). None of the
  three is a clause of `ValidV3` and none is a table fact (OBJ.4 proved the last two are not); each
  is a premise of `vk_blockRow`. At `poseidonRender` all three are TRUE and are proved here by
  computation, which is what makes them rows and not blockers:
    (a) `poseidon_residual_numInst`  - `pv.numInstances = cfg.numInstances` (1 = 1). Its GENERIC
        source is a `generateAll` lemma `out.model.numInstances = cfg.numInstances`; the model
        field is `inputs.numInstances` (ART:280) and the `inputs` clause gives `inputs.numInstances
        = cfg.numInstances`, so the generic lemma is one unfolding of `generateVerifierFromPlan`
        away - OWNER: OBJ.9/OBJ.12, file `LoweringV2/Generated.lean` (refinable).
    (b) `poseidon_residual_disjoint` - the g1_identity / VK window inequality. Its generic source is
        a layout lemma `memory.map.WellFormed -> disjointness` - OWNER: the WellFormed repair area
        (R.7's neighbours); `supported.layout` already carries the hypothesis at the render.
    (c) `poseidon_residual_codehashArm` - `expectedVkCodehash.IsSome`. Its generic source is a
        `generateAll` lemma `flags.separate = true -> (out.model).expectedVkCodehash.IsSome`;
        `Artifacts.lean:524` is that `if` - OWNER: OBJ.9, one unfolding away.
  No hypothesis was added to `ValidV3` to make any of them close, and no pin bundle was left
  silently free: the two structures moved to `Consts.lean` §5 and the three premises are on the row.
-/

/-- **THE COMPUTABLE FACE OF `Render.generated poseidonRender`.** `poseidonRender` is noncomputable,
    so the VM cannot run `generated poseidonRender` itself - but every argument it reads unfolds by
    `rfl` (`poseidonVk_eq`, `poseidonCfg_eq`, `poseidonPlan_eq`, `poseidonInputs_eq`,
    `poseidonFlags_eq`, `poseidonRender_E_isD2`), so this IS the same term, and the verdict below is
    the clause's. -/
def poseidonGenRender : Except Fault GenOut :=
  generateAll Features.solidity poseidonDelta poseidonVkExec poseidonConfig poseidonPlanV2.vk
    poseidonInputs poseidonFlags

theorem poseidonGenRender_eq_generated : generated poseidonRender = poseidonGenRender := rfl

/-- **THE MEASURED REFUTATION OF THE `generated` CLAUSE, AND ITS SITE.** The generator refuses the
    payload this render's plan carries: quotient.rs:202, "VK must carry quotient constants".
    WITNESS of the refutation and FALSIFIER of the clause in one line. AXIOM:
    poseidon_generated_notOk._native.native_decide.ax_1_1. -/
theorem poseidon_generated_notOk : poseidonGenRender.isOk = false := by native_decide

/-- The refusal is at the PAYLOAD and not at the delta: the same run with the four reservation fields
    filled is `.ok` (`GeneratedKats.generateAll_textIsTheArtifactButForBuildId_ok`, gate 4). Stated as
    a Bool because `GenOut` has no `DecidableEq`; the site string is what the gate reads. AXIOM:
    poseidon_generated_panicsAtQuotient202._native.native_decide.ax_1_1. -/
theorem poseidon_generated_panicsAtQuotient202 :
    (match poseidonGenRender with
      | .error (Fault.panic s) => s.contains "quotient.rs:202"
      | _ => false) = true := by native_decide

/-- **THE GENERATED CLAUSE - REFUTED, AND NOW THE ONLY REFUTATION.** `GeneratedBy poseidonRender`
    does not hold. It was the second refutation of `poseidonRender.Valid`, INDEPENDENT of
    `supported`: OBJ.8 step 2 killed the DELTA reason (`poseidonDelta_isArtifactLiteral_ok`) and this
    replaces it with the PAYLOAD reason. R.7 then closed the `supported` one, so `poseidonRender_notValid`
    below runs through THIS theorem and no other. -/
theorem poseidonValid_generated_not : ¬ GeneratedBy poseidonRender := by
  rintro ⟨out, ho, _, _, _⟩
  have h1 : poseidonGenRender.isOk = true := by rw [← poseidonGenRender_eq_generated, ho]; rfl
  have h2 := poseidon_generated_notOk
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- **RESIDUAL (a) AT THE FIXTURE.** `vk_blockRow`'s `hnum`. True here by computation; generic only
    once `Generated.lean` states `out.model.numInstances = cfg.numInstances`. AXIOM:
    poseidon_residual_numInst._native.native_decide.ax_1_1. -/
theorem poseidon_residual_numInst :
    poseidonRender.pv.numInstances = poseidonRender.cfg.numInstances := by
  show poseidonPv.numInstances = poseidonConfig.numInstances
  native_decide

/-- **RESIDUAL (b) AT THE FIXTURE.** `vk_blockRow`'s `hdisj`. The hypothesis its generic source needs
    (`supported.layout`, i.e. `memory.map.WellFormed`) is PROVED at this render already
    (`poseidonValid_supported_rest`), which is what makes this a row and not a blocker. AXIOM:
    poseidon_residual_disjoint._native.native_decide.ax_1_1. -/
theorem poseidon_residual_disjoint :
    ptrAddr poseidonRender.pv.memory.g1IdentityMptr + 128
      ≤ ptrAddr poseidonRender.pv.memory.vkMptr ∨
    ptrAddr poseidonRender.pv.memory.vkMptr + poseidonRender.pv.vk.len
      ≤ ptrAddr poseidonRender.pv.memory.g1IdentityMptr := by
  show ptrAddr poseidonPv.memory.g1IdentityMptr + 128 ≤ ptrAddr poseidonPv.memory.vkMptr ∨
    ptrAddr poseidonPv.memory.vkMptr + poseidonPv.vk.len ≤ ptrAddr poseidonPv.memory.g1IdentityMptr
  native_decide

/-- **RESIDUAL (c) AT THE FIXTURE.** `vk_blockRow`'s `hcode`. `flags.separate = true` is proved at
    `poseidonValid_supported_rest`; the generic step from it to the `IsSome` is the `if` at
    `Artifacts.lean:524`, i.e. one unfolding of `generateVerifierFromPlan`. AXIOM:
    poseidon_residual_codehashArm._native.native_decide.ax_1_1. -/
theorem poseidon_residual_codehashArm : ∃ x, poseidonRender.model.expectedVkCodehash = some x := by
  show ∃ x, poseidonM.expectedVkCodehash = some x
  -- The witness is the option's own `getD`: the arm is `some` exactly when the match reduces to
  -- `some` of its own default, which is what the VM decides here. AXIOM:
  -- poseidon_residual_codehashArm._native.native_decide.ax_1_1.
  exact ⟨poseidonM.expectedVkCodehash.getD 0, by native_decide⟩

/-- THE SEVEN CLAUSES AS ONE HONEST CONJUNCTION, so no cell of the table above is prose only:
    `inputs`, `noWriters`, `env` and - since R.7 - `supported` hold; `generated` is refuted by a
    sorry-free theorem above. -/
theorem poseidonValid_seven_summary :
    (¬ GeneratedBy poseidonRender) ∧ SupportedV2 poseidonRender ∧
      (poseidonRender.inputs.numInstances = poseidonRender.cfg.numInstances) ∧
      NoWriters (poseidonRender.prog 0 0) ∧
      EnvAgrees poseidonRender.E poseidonRender.vk poseidonRender.pv poseidonRender.params
        poseidonRender.sG2gen :=
  ⟨poseidonValid_generated_not, poseidonValid_supported, poseidonValid_inputs.1,
    poseidonValid_noWriters, poseidonValid_slots⟩


#print axioms Midfall.Instances.PoseidonValid.poseidon_generated_notOk
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_generated_not
#print axioms Midfall.Instances.PoseidonValid.poseidon_residual_numInst
#print axioms Midfall.Instances.PoseidonValid.poseidon_residual_disjoint
#print axioms Midfall.Instances.PoseidonValid.poseidon_residual_codehashArm
#print axioms Midfall.Instances.PoseidonValid.deciding_supported_degree_eq
#print axioms Midfall.Instances.PoseidonValid.deciding_supported_perm
#print axioms Midfall.Instances.PoseidonValid.deciding_supported_wf
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_supported
-- OBJ.9: the five clause theorems this card lands or re-measures. STEP 2 and STEP 4 already
-- existed and are re-printed here because the card names them; STEPS 3 and 5 are new.
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_inputs
#print axioms Midfall.Instances.PoseidonValid.deciding_programOkB
#print axioms Midfall.Instances.PoseidonValid.deciding_gasCallOk
#print axioms Midfall.Instances.PoseidonValid.deciding_exitDiscipline
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_program
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_noWriters
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_payload_scalars
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_payload_scalars_are_fields
#print axioms Midfall.Instances.PoseidonValid.poseidonValid_decidableHalf
/-! ## THE HEADLINE OF THIS CARD -/

/-- **`poseidonRender.Valid` IS UNSATISFIABLE.** Several of its clauses are false at this
    render (the header table above is the current verdict per clause, and it is the authority - a
    count in prose here would already be stale again). **R.7 (D-P59) CLOSED THE `supported`
    REFUTATION:** `wf.permutationCommitmentsMatch` now compares the VK's sigma commitments with the
    permutation COLUMNS - 8 against 8 at this key - and `poseidonValid_supported` proves the whole
    clause sorry-free, so `Valid` is no longer refutable through `supported` at all. THE ROUTE IS NOW
    `generated` ALONE: `poseidonValid_generated_not`, sorry-free, because the generator refuses the
    payload this render's plan carries at quotient.rs:202. OBJ.8 step 2 killed the older DELTA
    refutation (`poseidonDelta_isArtifactLiteral_ok`) by replacing `poseidonE.delta := 2` with the
    field constant, and the payload took its place. One clause, one owner: `generated` is OBJ.8
    step 3, and closing it needs a decision this card does not own - a frozen `Render.payload` field
    or a v1 `DecidableEq` (recorded at §V3, not attempted here).

    **OBJ.9 RE-MEASURED ALL SEVEN ON 2f3f39d AND DID NOT CHANGE THIS.** Step 1 was attempted through
    the route the card names (`Except.eq_ok_getOk`) and the ONE hypothesis it needs was DECIDED FALSE
    by the VM - section V3 prints the exact goal state and the exact tactic message - so `generated`
    is still REFUTED, still sorry-free, and still the ONLY refutation. Steps 2-5 landed: `program`
    moved OPEN -> PROVED (`poseidonValid_program`); `noWriters` was re-exhibited at fuel 20000;
    `inputs` was re-measured unchanged; and the eight scalar facts of `payload` are now theorems
    (`poseidonValid_payload_scalars`) instead of VM `def`s. SIX of the seven clauses are now decided
    at the fixture - five PROVED and one HALF - and `ValidV3 poseidonRender` is STILL UNINHABITED, by
    exactly one clause. `poseidonRender_notValid` below is unchanged, still routes through
    `h.generated` alone, and is PROVED rather than dangling: that is the invariant this card had to
    preserve, and it is preserved.

    What the retired clauses became: `circuitMeta`, `layout`, `invariants` and `model` collapsed
    into `generated`; `codegen`, `closed`, `transcriptMptr` and the two `vkLoading` pin bundles into
    `program` (`codegenAgrees`, `mainClosed`, `constsCoherent` are conjuncts of `programOkB`);
    `returnMptr` is a THEOREM of `constsCoherent` (`returnMptr_of_valid`); `slots` is `env`, same
    text, new name; `noWriters` and `inputs` and `supported` are unchanged.

    This is the card's own stop condition
    stated as a theorem rather than as a report line: C.1's `poseidon_valid` sorry WAS not an
    unfinished proof, it was an impossible one, and the only way to finish it is upstream - a
    `poseidonMeta` whose `protocol` is the real `ProtocolPlan`, which needs the halo2 constraint
    system that is not in the tree (D.2 gap A), the same circuit gap D.3 named. PL.1/W13 therefore
    DELETED `poseidon_valid` and the unconditional headline that consumed it.

    What this does NOT break: the conditional `poseidon_block_contracts` still states the block
    gluing with `hR : poseidonRender.Valid` as its binder, and `Valid` enters the V2 composition
    only through `blockContracts_of_valid`; no theorem is restated without that binder. -/
theorem poseidonRender_notValid : ¬ poseidonRender.Valid :=
  fun h => poseidonValid_generated_not h.generated

#print axioms Midfall.Instances.PoseidonValid.poseidonRender_notValid

end Midfall.Instances.PoseidonValid
