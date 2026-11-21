/-
  Midfall.LoweringV3.GeneratorTheorem

  PL.H0 (D-P74) - **THE ROOT, WIRED.** `lowering_correct` is the objective's theorem, stated with the
  objective's EXACT signature (PLAN-V3 §0:48, §5 M7:971, §6:1193; D-P71), and its proof now runs
  **through PROVED glue to named leaves and nothing else**:

      lowering_correct
        = lowering_equivalenceV3_of_rows R product hR (sim_rows R product) (prog_rows R product)
            ├─ twoOutcomesV3_of_valid      PROVED  → the scan leaves (ST.10, ST.12)
            ├─ rejectsV3_of_sims           PROVED  → sim_rows, prefix_sim, run_split
            │     sim_rows                  PROVED  → 7 BlockSim leaves, one per block
            ├─ completeV3_of_progs         PROVED  → prog_rows, prefix_prog, run_split/join
            │     prog_rows                 PROVED  → 7 BlockProgS leaves, one per block
            └─ totalV3_correct             PROVED  → 4 totality leaves (TOT.1, TOT.1.a)

  **THE ROUTE D-P74 SIGNS, AND WHAT IT REPLACED.** LH (`c1bb557`) had to route the root through
  `Midfall.LoweringW.lowering_correct_of_W` because `lowering_equivalenceV3_of_rows` needed
  `SimRowsV3` + `ProgRowsV3` as hypotheses beyond `ValidV3`, and the tree had no way to supply them.
  D-P74 makes those two bundles this card's deliverable as LEAVES: the bundles are re-pointed at
  SIM.2's `BlockSim`/`BlockProgS` over `StageInv` - the shape every ROW card proves - and
  `sim_rows`/`prog_rows` discharge them from fourteen named row leaves. `lowering_correct_of_W`
  STAYS in the tree (WideningStages.lean:717) and the root no longer uses it; M9 reaches it later
  through `blockSimW_iff_blockSim` plus WID's accumulator arms (D-P74 item 1). **The statement of
  `lowering_correct` did not move**: no hypothesis was added, moved or dropped, and no `ValidV3`
  clause was relaxed.

  THE FIRST MILESTONE. `lowering_sound` (conjuncts 1 and 3 plus `RejectsV3`) is reported BESIDE the
  root (D-P74 item 3): its cone is the simulation rows, `prefix_sim` and the scan leaves only, so
  WP A1/A3/A4/A6/A9/A10/A11 lower it before the progress side closes.

  THE V2 HEADLINE WAS DELETED BY PL.1/W13. `Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon`
  is gone, together with its refuted `poseidon_valid` input; the surviving V2 root is the generic
  `Midfall.LoweringV2.lowering_equivalence_of_blocks`. The register's ROOT column, `#cone_report` and
  `verify.sh` are keyed to THIS declaration.

  W12. FALSIFIER, LANDED AND PROVED: `lowering_correct_needs_valid`
  (`Instances/StatementsV3Falsifiers.lean` §F10) - the root with `hR : ValidV3 R` DROPPED is false at
  `bumpInst R`. WITNESS, BLOCKED AND NAMED: `ValidV3` has no inhabitant the tree can name, so none was
  invented; D-P75 item 5 allows the gap below as the witness of a statement over `ValidV3`.

  D-P71: generic in `R`, no fixture in the statement, and **no `native_decide` in the cone** -
  `#assert_axioms ... native []` below passes with an EMPTY native list, which is the objective's own
  gate. No frozen file was edited.
-/
import Midfall.LoweringV3.Composition
import Midfall.LoweringV3.Rows
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **THE GENERATOR THEOREM - D-P71'S DELIVERABLE.** For every render the Lean port of the generator
    emits for a circuit in the supported class (`hR : ValidV3 R`: the seven clauses of the ONE text,
    Statements.lean:1116), and for every pairing answer `product`, the four conjuncts of the V3
    headline hold. **The signature is the objective's, verbatim** - see the `#check` in §2. The proof
    is one line of proved glue to the row bundles; its cone is the leaf list §2 prints. -/
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product :=
  lowering_equivalenceV3_of_rows R product hR (sim_rows R product) (prog_rows R product)

/-- **THE FIRST MILESTONE (D-P74 item 3): THE SOUNDNESS HALF.** Conjuncts 1 and 3 (`TwoOutcomes`)
    plus the soundness obligation (`RejectsV3`), reported beside the root. PROVED glue: its cone is
    the seven simulation rows, `prefix_sim`, the run decomposition and the scan leaves - it does NOT
    read the progress rows or the totality leaves. -/
theorem lowering_sound (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    TwoOutcomes R ∧ RejectsV3 R product :=
  ⟨twoOutcomesV3_of_valid R hR, rejectsV3_of_sims R product hR (sim_rows R product)⟩

/-- **THE WITNESS BLOCKER, AS A NAMED RECORD (rule W12; the repo's `gap_*` convention).** The root
    needs a render whose `ValidV3` holds. There is none, and the blocking clause is named, with its
    cause and its owner, rather than left for a reader to notice:

    * `ValidV3 poseidonRender` - the only render the tree can name - is **UNINHABITED**, because
      clause 1 of the seven, `generated : GeneratedBy poseidonRender`, is **REFUTED** by
      `poseidonValid_generated_not` (`Instances/PoseidonValid.lean:893`, sorry-free).
    * THE CAUSE, measured not asserted: the ported generator refuses this render's payload.
      `poseidonGenRender` (:867) reads the payload the clause demands out of the render's own
      `plan.vk`, and it is not `.ok` (`poseidon_generated_notOk`, :877) with the panic at
      **`quotient.rs:202`**, "VK must carry quotient constants"
      (`poseidon_generated_panicsAtQuotient202`, :883). The refusal is at the PAYLOAD, not the delta.
    * THE OTHER CLAUSES ARE NOT THE BLOCKER: `poseidonValid_decidableHalf` (:757) exhibits
      `inputs`, `program`, `noWriters`, `env`, `supported` and the eight scalar facts of `payload`
      at the same render; what is missing there is `generated` and the five point fields of `payload`
      (OPEN at the placeholder codec). OWNER: WP B4 (OBJ.8 step 3, R.3, ST.15).
    * NOT BOUGHT WITH A WEAKENING: no clause of `ValidV3` was dropped, relaxed or restated to get an
      inhabitant, and `ValidV3` still has exactly ONE declaration in the tree. -/
def gap_lowering_correct_witness_unexhibited : String :=
  "ValidV3 has no named inhabitant in the tree, so lowering_correct has no W12 witness. Blocker: "
    ++ "clause 1 of the seven, GeneratedBy poseidonRender, REFUTED by poseidonValid_generated_not "
    ++ "(Instances/PoseidonValid.lean:893, proved with no hole). Cause: the ported generateAll "
    ++ "refuses this "
    ++ "render's payload - poseidonGenRender.isOk = false (poseidon_generated_notOk, :877) with the "
    ++ "panic at quotient.rs:202, 'VK must carry quotient constants' "
    ++ "(poseidon_generated_panicsAtQuotient202, :883) - and the payload the clause demands is read "
    ++ "out of R.plan.vk. Not the blocker: inputs, program, noWriters, env, supported and the "
    ++ "payload scalars, all exhibited at the same render by poseidonValid_decidableHalf (:757). "
    ++ "Owner: WP B4 - the OBJ/GEN route that makes generateAll accept the parsed form "
    ++ "(PoseidonValid:840 notes that even with the payload circle cut, generated still needs "
    ++ "OBJ.6/OBJ.7's converged-meta question). ValidV3 was NOT weakened to buy inhabitation, and no "
    ++ "fixture was substituted into the statement."

/-! ## §2. THE MEASUREMENTS - the root, its signature, and the axiom gate -/

-- THE OBJECTIVE'S SIGNATURE, AS THE TYPECHEKER READS IT, and the glue it now runs through.
#check @Midfall.LoweringV3.lowering_correct
#check @Midfall.LoweringV3.lowering_sound
#check @Midfall.LoweringV3.lowering_equivalenceV3_of_rows
#check @Midfall.LoweringV3.sim_rows
#check @Midfall.LoweringV3.prog_rows

-- **THE DELIVERABLE: THE ROOT'S LEAF LIST.** This is the tree D-P74 exists to produce.
#cone_sorries Midfall.LoweringV3.lowering_correct

-- **THE FIRST MILESTONE, BESIDE IT** (D-P74 item 3).
#cone_sorries Midfall.LoweringV3.lowering_sound

-- The root adds NO sorry of its own: every leaf above is a registered ROW, PREFIX, TOTALITY or SCAN
--    hole, and the axiom set is the standard three plus sorryAx - no user axiom, no native_decide.
#print axioms Midfall.LoweringV3.lowering_correct
#print axioms Midfall.LoweringV3.lowering_sound
#print axioms Midfall.LoweringV3.sim_rows
#print axioms Midfall.LoweringV3.prog_rows

/-! **D-P71'S AXIOM GATE, IN THE SKELETON FORM.** The plan's DONE gate is
    `#assert_axioms Midfall.LoweringV3.lowering_correct [propext, Classical.choice, Quot.sound]
    native []` (PLAN-V3 §5 M7:973, §6:1227). `sorryAx` is in the allow-list HERE because the leaves
    are still open: the honest version of the gate while they are open must name sorryAx or the build is
    red on every honest version of this file. **The native list is EMPTY**, which is the half of the
    gate D-P71 exists for: no fixture computation reaches the root. The surviving V2 root's cone, by
    contrast, is asserted in `Midfall/Tools/ConeReport.lean` with an EMPTY native list too, after
    PL.1/W13 re-pointed it from the deleted deployment headline to the generic composition. Deleting
    `sorryAx` from the list below is the commit that
    closes the objective (PL.H, WP A13). -/
open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.lowering_correct
  [propext, Classical.choice, Quot.sound, sorryAx] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.lowering_sound
  [propext, Classical.choice, Quot.sound, sorryAx] native []

end Midfall.LoweringV3
