/-
  StatementsV3Deploy — **RETIRED** (card RECON.1b-iii, 2026-11-18).

  THIS FILE WAS THE PRE-LANDING SCRATCH COPY OF `Midfall/Instances/StatementsV3Deploy.lean`. The
  content LANDED: ST.1c put the deployment measurements in the tree on the post-M2 baseline, ST.1b
  turned every print into an annotated gate, and RECON.1 added the clause table at F1. The tree
  module is gated by `scripts/kat_gate.py` (its ST.1c note counts **19** annotated
  `#eval ... -- expect ...` gates in it), so the landed copy is machine-checked harder than this
  scratch original ever was. This file stopped elaborating when ST.4/ST.6 cut the frozen surface
  over: its four errors were all ONE cause — `metaDataForStableStaticLayout` became
  `metaDataForStableStaticLayoutInputs` in the tree, taking a `ConstraintSystemMeta` where this
  file passed a `VerifierBuildInputs` and returning a different four-tuple (this file's old 69-77).

  WHERE EACH SECTION LANDED (tree module `Midfall/Instances/StatementsV3Deploy.lean`):
    (b) circuitMeta / layout at the two plans -> planToday, planFaithful, derivedProofLen,
        planTupleB, todayTuple_ok, faithfulTuple_ok, faithfulTuple_detectsPerturbation_ok,
        rustDerivationB, rustDerivation_ok, layoutBasesB, layoutBasesAgree_ok, dataConjunct_ok,
        wellFormedPermCounts_ok
    (c) the payload at the deployment -> poseidonE_delta, poseidon_delta_not,
        frDeltaIsGeneratorPow_ok, recon1_payload_scalars_ok, recon1_payload_digest_ok,
        recon1_payload_digest_falsifier_ok, recon1_payload_flipOmega_ok, commitmentCounts_ok,
        identityFixedCommIndices_ok, identityPermCommCount_ok, baseSlotWidths_ok
    (d), (i), (e) the decidable clauses at the deployment AST -> recon1_programOkB_ok,
        recon1_scans_ok, recon1_gas_ok, recon1_supported_gap_ok, exitDisciplineAtDeploy_ok,
        mainBlockTokenCounts_ok, cdBound_ok, recon1_cdBound_falsifier_ok, transcriptMptrPin_ok,
        recon1_tpbuf_numbers_ok, recon1_tpbuf_falsifier_ok, recon1_g1Identity_falsifier_ok,
        recon1_negLagranges_falsifier_ok, recon1_multiPoint_ok, recon1_permComm_falsifier_ok,
        recon1_constsCoherent_falsifier_ok
    (g), (j) the codec laws and WellFormedV3 at the deployment codec -> g1CodecZ_not_headlineLaws,
        poseidon_notInhabitedV3, exists_injective_comp, lawsV3_satisfiable_at_G1z
  Every `#eval` print this file made survives in the tree as a gated `*_ok` Bool against the SAME
  literal — `("today", true, false, false, 4224, 4320)`, `("faithful", false, true, true, 4320,
  4320)`, `(10496, 10496, 3, 48, 0, true, false)`, the ten layout bases all true, `(19, 19, 8, 8)`,
  `[8, 10, 11, 12, 14, 16]`, `0`, `(128, 256, 256, false)`, `(8, 8, 3)`, `(true, true, false)`,
  `[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]`, `(4484, true)`, `(some 4096, 21760)`. The prints had to
  become Bools because kat_gate.py:40 reads an expectation as [^\s,]+, so a tuple or list print
  cannot carry one (ST.1b's note at section (b)). Nothing measured here was dropped for being
  inconvenient.

  WHAT THIS FILE HELD THAT THE TREE DOES NOT — ONE THEOREM, KEPT LIVE BELOW, NOT DELETED.
  `poseidon_payloadAgrees_not` is the only declaration here with no counterpart in the landed
  module. It refutes the `PayloadAgrees` of the D-P67 EIGHTEEN-CLAUSE fallback text kept in
  `StatementsV3.lean` beside this file, which still has a `delta` field; the single `ValidV3`
  (`Midfall/LoweringV3/Statements.lean:1116`) DROPPED that field on purpose at RECON.1 step 3, so
  the statement is NOT EXPRESSIBLE against the landed text — the drop is recorded at
  `Midfall/LoweringV3/Statements.lean:424` ("`delta` IS DROPPED (card step 3)"),
  `Midfall/Instances/StatementsV3Falsifiers.lean:285-293` says of its twin `payloadAgrees_pins_delta`
  "the old theorem is deleted rather than restated", and
  `Midfall/Instances/StatementsV3Deploy.lean:306-311` says the refutation "is GONE with that field, and the F1 refutation of the single text now sits
  in `generated`". It is still CITED: `PLAN-V3-cards.md:753` (ST.1's acceptance: "Falsifier of the
  ticket: `PayloadAgrees poseidonRender` is refuted by `poseidon_payloadAgrees_not`"),
  `PLAN-V3-cards.md:1716` (the `Done` card proves `not_done_today` from it) and
  `design/statements.md:138). Cited, so kept. Under the single text the delta refutation lives in
  `GeneratedKats.generateAll_falsifierDeltaAndOmega_ok`, which the tree module pins.

  WHY THE FILE IS STILL IN THE GATE AND NOT REMOVED: `check.sh` names it in the `statements` area
  (line 44). Retiring it from the gate would mean editing `check.sh`, which is a gate change under
  D-P69 and not this card's to make. So the file stays, and now carries only what is still its own.
  NOTE FOR THE ORCHESTRATOR, OUT OF THIS CARD'S REACH TO FIX: `docs/plans/V3-evidence/README.md:24`
  still says "`statements/StatementsV3Deploy.log` is the clause table at the fixture". The clause
  table is in the tree module now; the log of this file no longer prints it.
-/
import StatementsV3
import Midfall.Instances.PoseidonValid
import Midfall.Instances.CurveSurface
import Midfall.Generator.Vk
set_option autoImplicit false

namespace Midfall.LoweringV3.Deploy

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid
open Midfall.LoweringV2 Midfall.LoweringV3

/-- The `delta` field is FALSE at today's render. Concrete deployment fact. Carried verbatim from
    the pre-landing copy; the same statement is landed at
    `Midfall/Instances/StatementsV3Deploy.lean`, but this file cannot import that module — Lean
    refuses the fallback text and the single text in one environment ("environment already contains
    'Midfall.LoweringV3.withCompressed'"), which is exactly why the theorem below has to stay on
    this side of the line. -/
theorem poseidon_delta_not :
    ¬ (poseidonRender.E.delta.val = Inline.natOfLiteral poseidonRender.inputs.frDelta) := by
  show ¬ ((2 : Fr Yul.blsR).val = Inline.natOfLiteral poseidonInputs.frDelta)
  native_decide

/-- So `PayloadAgrees poseidonRender` is refuted, by its `delta` field alone. **AT THE FALLBACK
    TEXT**: `PayloadAgrees` resolves to the eighteen-clause copy in `StatementsV3.lean` (D-P67),
    the only `PayloadAgrees` that still pins `frDelta`. The single text has no such field, so
    this refutation belongs to the fallback and cannot move into the tree. -/
theorem poseidon_payloadAgrees_not : ¬ PayloadAgrees poseidonRender :=
  fun h => poseidon_delta_not h.delta

#print axioms poseidon_payloadAgrees_not

end Midfall.LoweringV3.Deploy
