/-
  Midfall.LoweringV3.GeneratorTheorem

  LH - **THE ROOT EXISTS.** `lowering_correct` is declared with the objective's EXACT signature
  (PLAN-V3 §0:48, §5 M7:971, §6:1193; D-P71), so the cone measure finally reads a V3 theorem.
  SIM.6 (ef19950) found the gap this card closes: the headline cone's ten ROOT rows are all V2-era
  names and RECON.2's three V3 obligations are cone `-`, because there was no V3 root to walk.
  Nothing is proved here. This is assembly, and it adds **zero** sorries.

  ================================================================================================
  1. WHAT THE BRIEF ASKED FOR, AND THE STOP CONDITION THAT FIRED (reported, not worked around)
  ================================================================================================

  The brief: compose RECON.2's `lowering_equivalenceV3_of_rows` under the objective's signature,
  with the three sorried obligations as leaves; STOP if a NEW sorry is needed. It fired.

    lowering_equivalenceV3_of_rows (R) (product) (hR : ValidV3 R)
      (hsim : SimRowsV3 R product) (hprog : ProgRowsV3 R product)
        : LoweringEquivalenceV3 R product

  The glue's CONCLUSION is exactly the objective's - `LoweringEquivalenceV3 R product`, nothing
  dropped inside it, `Eip2537.Holds` and `SoundSide` untouched (both `#check`s are printed in §4
  below, and they are the machine-checked form of this claim). The mismatch is on the LEFT: the glue
  needs TWO hypotheses beyond `ValidV3 R`, the row bundles `SimRowsV3 R product` and
  `ProgRowsV3 R product`. Those are M6's deliverable - PLAN-V3 §5 M6's exit gate is
  `rows_correct (R) (product) (hR : ValidV3 R) : R.ExitOk /\ R.SimContracts product /\
  R.ProgContracts product` - and it is NOT in the tree: SIM.2 and SIM.6 are the cards that owe
  them. So the RECON.2 route could only have been landed by

    (a) two NEW sorries for the bundles - the brief's own STOP condition, register 79 -> 81, or
    (b) the two bundles as hypotheses of `lowering_correct` - the forbidden weakening: a root with
        two extra premises is EASIER to prove than the objective's, which is this project's named
        failure mode (buying a green gate by editing the expectation).

  NEITHER WAS DONE. No hypothesis of the objective's statement was added, moved or dropped; no new
  `sorry` was written anywhere in this card.

  ================================================================================================
  2. WHAT LANDED INSTEAD: THE SAME THEOREM, BY THE ROUTE D-P72 SIGNS
  ================================================================================================

  `Midfall.LoweringW.lowering_correct_of_W` (WideningStages.lean:717) ALREADY HAS THE OBJECTIVE'S
  EXACT SIGNATURE - `(R) (product) (hR : ValidV3 R) : LoweringEquivalenceV3 R product` - and is
  PROVED, with no `sorry` of its own, from the widened target. That is not a second composition
  beside RECON.2's; it is the shape the signed decision prescribes. PLAN-V3 §5:1210: "With M9
  (D-P72) the headline is `lowering_correctW`, `lowering_correct` is its corollary", and
  WideningStages §7 already titles it "THE WIDENING SUBSUMES D-P71'S DELIVERABLE". This card
  REFERENCES it. It restates no obligation and composes nothing a second time (RECON.2's Goal).

  ================================================================================================
  3. WHAT THE NEW CONE DOES AND DOES NOT MEASURE - READ THIS BEFORE QUOTING THE NUMBER
  ================================================================================================

  `#cone_sorries Midfall.LoweringV3.lowering_correct` prints TWO leaves:

    Midfall.LoweringW.lowering_correctW      - the widened target (D-P72), 1 sorry
    Midfall.LoweringW.model_quotientMode     - the model's quotient-mode fact, 1 sorry

  It does NOT print RECON.2's three row obligations, because the route taken does not pass through
  them. Stated plainly, so nobody has to guess:

    * the cone is now a V3 measurement, which was the point of the card, but it measures the
      WIDENING obligations, not the ROW obligations;
    * closing SIM.2 / SIM.6's rows will therefore NOT move this cone. Until M6 lands, the number
      the ROW cards should be measured against is RECON.2's own glue, printed in §4 below:
      `#cone_sorries lowering_equivalenceV3_of_rows` = 5 leaves (rejectsV3_of_sims,
      completeV3_of_progs, totalV3_of_stages, plus the two scan leaves twoOutcomesV3_of_valid
      rests on: scans_prog_addr_indep, twoOutcomes_of_exitDiscipline);
    * when M6's `rows_correct` lands the root's BODY becomes
      `lowering_equivalenceV3_of_rows R product hR hsim hprog` - one line, statement untouched -
      and the cone becomes the row leaves. If instead `lowering_correctW` is decomposed through
      RECON.3's `lowering_equivalence_of_stagesW`, the row leaves arrive on this side of the cone.
      Either way THE STATEMENT BELOW DOES NOT MOVE, and that is the only thing the objective's
      DONE gate depends on.

  The cone is NOT empty, which was the brief's red flag: the root does depend on sorried leaves, and
  on nothing else - `#print axioms` shows exactly `[propext, sorryAx, Classical.choice, Quot.sound]`.

  ================================================================================================
  4. W12: THE FALSIFIER LANDED, THE WITNESS IS BLOCKED (and NOT faked)
  ================================================================================================

  FALSIFIER, LANDED: `lowering_correct_needs_valid`, in `Midfall/Instances/StatementsV3Falsifiers.lean`
  section F10 - PROVED, no `sorry`. The weakening it exhibits false is the root with `hR : ValidV3 R`
  DROPPED: at `bumpInst R` - the same render with one more public instance configured, whose program,
  constants and runs are `R`'s by `rfl` - the same returning run exists while the Lean verifier
  rejects (`leanAccepts_bump_false`), so conjunct 1 of the headline is false there and the
  fixture-free universal claim ("every render, no validity hypothesis") is refuted. It lives in
  `Instances/` because the theorem-bearing file may not import a fixture: checks.sh's Instances
  import-confinement gate is what keeps `lowering_correct` itself D-P71-clean.

  WITNESS, BLOCKED: see `gap_lowering_correct_witness_unexhibited` below. `ValidV3 R` has NO
  inhabitant the tree can name today, so no render satisfies the root's hypothesis and none was
  invented. `ValidV3` was not weakened to get one - it still has exactly ONE declaration in the tree
  (Statements.lean:1116, seven clauses), and this card touches neither it nor `ValidW`.

  ================================================================================================
  5. RULES THIS CARD OBSERVED
  ================================================================================================

  D-P71: generic in `R`; no fixture, no `poseidonRender`, no `native_decide` in the statement or in
  the cone (`#assert_axioms ... native []` passes with an EMPTY native list - unlike the V2 root
  `lowering_equivalence_poseidon`, whose cone carries
  `native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]`; ConeReport.lean:89-93).
  No frozen file was edited (Statements.sha256 / LoweringV2/Frozen.sha256 are untouched). No v1
  module is imported: this file imports LoweringV3.Statements (via Composition), Lowering.Stage,
  LoweringV3.Widening and LoweringV2.Stages - none of the AVOID-14 - which is also why the cone
  prints live HERE and not in `Midfall/Tools/ConeReport.lean`: ConeReport's own
  `#imports_avoid` gate would redden on `Midfall.Lowering.Accumulator`, which
  `LoweringV3/Widening.lean:43` imports.
-/
import Midfall.LoweringV3.Composition
import Midfall.LoweringV3.WideningStages
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

/-- **THE GENERATOR THEOREM - D-P71'S DELIVERABLE, STATED.** For every render the Lean port of the
    generator emits for a circuit in the supported class (`hR : ValidV3 R`: the seven clauses of
    the ONE text, Statements.lean:1116), and for every pairing answer `product`, the four conjuncts
    of the V3 headline hold. **No fixture occurs in the statement** (D-P71), and the cone below
    contains **no `native_decide` axiom** (D-P71's own gate).

    THE SIGNATURE IS THE OBJECTIVE'S, VERBATIM: PLAN-V3 §0:48, §5 M7:971, §6:1193 and the
    orchestrator's goal text (PLAN-V3 §10.3) all state
    `lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product`, and the `#check` in §4 is the machine-checked proof that this
    is that type. Nothing was added to make the proof fit; see the header §1 for the two routes the
    tree offers and why this one needs no new `sorry`.

    SKELETON, NOT PROVED: its cone has two sorried leaves (`lowering_correctW`,
    `model_quotientMode`). The objective's DONE gate is `0 sorried leaves` on this declaration;
    today the gate is measurable for the first time. -/
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product :=
  Midfall.LoweringW.lowering_correct_of_W R product hR

/-- **THE WITNESS BLOCKER, AS A NAMED RECORD (rule W12; the repo's `gap_*` convention).** The root
    needs a render whose `ValidV3` holds. There is none, and the blocking clause is named, with its
    cause and its owner, rather than left for a reader to notice:

    * `ValidV3 poseidonRender` - the only render the tree can name - is **UNINHABITED**, because
      clause 1 of the seven, `generated : GeneratedBy poseidonRender`, is **REFUTED** by
      `poseidonValid_generated_not` (`Instances/PoseidonValid.lean:893`, sorry-free).
    * THE CAUSE, measured not asserted: the ported generator refuses this render's payload.
      `poseidonGenRender` (:867) is `generateAll Features.solidity poseidonDelta poseidonVkExec
      poseidonConfig poseidonPlanV2.vk poseidonInputs poseidonFlags` - the payload the clause
      demands is read out of the render's own `plan.vk` - and it is not `.ok`
      (`poseidon_generated_notOk`, :877) with the panic at **`quotient.rs:202`**, "VK must carry
      quotient constants" (`poseidon_generated_panicsAtQuotient202`, :883). The refusal is at the
      PAYLOAD, not at the delta.
    * THE OTHER CLAUSES ARE NOT THE BLOCKER: `poseidonValid_decidableHalf` (:757) exhibits
      `inputs`, `program`, `noWriters`, `env`, `supported` and the eight scalar facts of
      `payload` holding at the same render; what is missing there is `generated` and the five point
      fields of `payload` (OPEN at the placeholder codec). Per PoseidonValid's own note (:840),
      even with the payload circle cut `generated` still needs OBJ.6/OBJ.7's converged-meta
      question settled. OWNER: the OBJ/GEN route that makes `generateAll` accept the parsed form.
    * NOT BOUGHT WITH A WEAKENING: no clause of `ValidV3` was dropped, relaxed or restated to get an
      inhabitant, and `ValidV3` still has exactly ONE declaration in the tree. The `example` in
      `Instances/StatementsV3Falsifiers.lean` F10 is a **typecheck** witness only - it takes
      `hR : ValidV3 poseidonRender` as a hypothesis, so it says the root instantiates at the
      fixture and says NOTHING about that hypothesis having a witness. -/
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
    ++ "Owner: the OBJ/GEN route that makes generateAll accept the parsed form (PoseidonValid:840 "
    ++ "notes that even with the payload circle cut, generated still needs OBJ.6/OBJ.7's "
    ++ "converged-meta question). ValidV3 was NOT weakened to buy inhabitation, and no fixture was "
    ++ "substituted into the statement."

/-! ## §4. THE MEASUREMENTS - the root, the two routes, and the axiom gate -/

-- THE OBJECTIVE'S SIGNATURE, AS THE TYPECHEKER READS IT. Compare with the two routes below: the
--    first is RECON.2's glue (two extra hypotheses - see header §1), the second is the corollary
--    this card actually references (identical type, WideningStages.lean:717).
#check @Midfall.LoweringV3.lowering_correct
#check @Midfall.LoweringV3.lowering_equivalenceV3_of_rows
#check @Midfall.LoweringW.lowering_correct_of_W

-- THE DELIVERABLE: the real V3 leaf list, and RECON.2's row leaf list beside it.
#cone_sorries Midfall.LoweringV3.lowering_correct
#cone_sorries Midfall.LoweringV3.lowering_equivalenceV3_of_rows

-- The root adds NO sorry of its own: the two leaves above are RECON.2/WID's registered holes, and
--    the axiom set is the standard three plus sorryAx - no user axiom, no native_decide axiom.
#print axioms Midfall.LoweringV3.lowering_correct

/-! **D-P71'S AXIOM GATE, IN THE SKELETON FORM.** The plan's DONE gate is
    `#assert_axioms Midfall.LoweringV3.lowering_correct [propext, Classical.choice, Quot.sound]
    native []` (PLAN-V3 §5 M7:973, §6:1227). `sorryAx` is added to the allow-list HERE because this
    is a declared skeleton, not a proof: the objective's gate is 0 sorried leaves, and the honest
    version of the gate while the two leaves are open must name sorryAx or the build is red on every
    honest version of this file. **The native list is EMPTY**, which is the half of the gate D-P71
    exists for: no fixture computation reaches the root. The V2 headline's cone, by contrast, is
    asserted with `native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]`
    (`Midfall/Tools/ConeReport.lean:89-93`). Deleting `sorryAx` from the list below is the commit
    that closes the objective. -/
open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.lowering_correct
  [propext, Classical.choice, Quot.sound, sorryAx] native []

end Midfall.LoweringV3
