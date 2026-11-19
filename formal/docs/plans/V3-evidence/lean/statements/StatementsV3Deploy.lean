/-
  StatementsV3Deploy — **RETIRED** (card RECON.1b-iii, 2026-11-18), then **HOLLOWED** (card FALS2,
  2026-11-19).

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
    (c) the payload at the deployment -> poseidonE_delta, frDeltaIsGeneratorPow_ok,
        recon1_payload_scalars_ok, recon1_payload_digest_ok, recon1_payload_digest_falsifier_ok,
        recon1_payload_flipOmega_ok, commitmentCounts_ok, identityFixedCommIndices_ok,
        identityPermCommCount_ok, baseSlotWidths_ok
    (d), (i), (e) the decidable clauses at the deployment AST -> recon1_programOkB_ok,
        recon1_scans_ok, recon1_gas_ok, recon1_supported_gap_ok, exitDisciplineAtDeploy_ok,
        mainBlockTokenCounts_ok, cdBound_ok, recon1_cdBound_falsifier_ok, transcriptMptrPin_ok,
        recon1_tpbuf_numbers_ok, recon1_tpbuf_falsifier_ok, recon1_g1Identity_falsifier_ok,
        recon1_negLagranges_falsifier_ok, recon1_multiPoint_ok, recon1_permComm_falsifier_ok,
        recon1_constsCoherent_falsifier_ok
    (g), (j) the codec laws and WellFormedV3 at the deployment codec -> g1CodecZ_not_headlineLaws,
        poseidon_notInhabitedV3, exists_injective_comp, lawsV3_satisfiable_at_G1z
  Every `#eval` print this file made survives in the tree as a gated `*_ok` Bool against the SAME
  literal. Nothing measured here was dropped for being inconvenient.

  ================================ FALS2 (2026-11-19) ================================
  RECON.1b-iii kept TWO theorems live below: `poseidon_delta_not` and `poseidon_payloadAgrees_not`.
  Card FALS2 was briefed on the premise that OBJ.8 step 2 refuted BOTH. Re-checked against THIS tree
  (base cd736ff, which carries RECON.1b-iv b62e29e), they are in DIFFERENT cases. W13 bites on one
  of them only.

  **1. `poseidon_delta_not` — GENUINELY FALSE. RETIRED BELOW.**
  It asserted `¬ (poseidonRender.E.delta.val = Inline.natOfLiteral poseidonRender.inputs.frDelta)`.
  OBJ.8 step 2 moved the fixture's DELTA off the placeholder `2` and onto the field constant
  `poseidonDelta` (`Midfall/Instances/PoseidonEnv.lean:239`, `:264`, `:268`), so the tree now
  PROVES THE NEGATION: `Midfall/Instances/StatementsV3Deploy.lean:173-176`, headed "THE REFUTATION
  THAT DIED", is `poseidon_delta_is` — the same equation, unnegated, by `native_decide`. That is
  exactly W13's trigger: a cited statement whose negation is proved. Note this theorem mentioned NO
  fallback-only symbol — `poseidonRender`, `poseidonInputs` and `Fr Yul.blsR` are all tree terms —
  so it was not "false of the landed text but true of the fallback". It is false of BOTH, and the
  fallback cannot rescue it. The corrected fact is proved on this side of the line below as
  `poseidon_delta_is_at_fallback`, so the file still carries a live truth about the delta and not
  merely a tombstone.

  **2. `poseidon_payloadAgrees_not` — NOT FALSE. ITS PROOF DIED; ITS TRUTH IS OPEN. KEPT AS A
  STATEMENT, DEMOTED FROM THEOREM.**
  It asserted `¬ PayloadAgrees poseidonRender`, where `PayloadAgrees` resolves to the D-P67
  eighteen-clause fallback copy in `StatementsV3.lean:453` — the only `PayloadAgrees` that still
  has a `delta` field (`:507`). Its whole proof was `fun h => poseidon_delta_not h.delta`: the
  delta clause was the ONE clause that failed, "carried by the delta field alone"
  (`Midfall/Instances/StatementsV3Deploy.lean:322-324`). With delta now satisfied that route is
  dead — but the statement was NOT refuted, and it cannot be kept as a theorem either. The fallback
  `PayloadAgrees` has thirteen fields. Eight are codec-free and all eight now HOLD at F1: seven by
  `recon1_payload_scalars_ok` plus `delta` by `poseidon_delta_is`. The verdict therefore rests on
  the five point fields (`g1Base`, `g2Base`, `negSG2`, `fixedComms`, `permutationComms`), and
  those are UNDECIDABLE here: `g1CodecZ` is itself `noncomputable`
  (`Midfall/Instances/G1Agreement.lean:2002` — `ofEip?` is a `Classical.choose` over the codec's
  image), so `native_decide` refuses them. Verified on this tree, not taken on the card's word:
  every one of the five fails with "failed to compile definition ... depends on 'g1CodecZ', which is
  'noncomputable'". The tree says the same of its own payload row: HALF, "eight of thirteen fields
  is a half" (`Midfall/Instances/PoseidonValid.lean:48-57`, `:674`), and NO witness of
  `PayloadAgrees poseidonRender` exists anywhere in `Midfall/` (grep). So neither
  `PayloadAgrees poseidonRender` nor its negation is provable at the current tree.
  Deleting a cited statement whose negation is NOT proved is the failure mode this card exists to
  avoid, so the statement is kept live below as a `Prop` under its cited name. It is a CLAIM now,
  not a proof: any card that writes `poseidon_payloadAgrees_not h.delta` gets a type error, loudly,
  instead of a stale green.
  WHAT WOULD CLOSE IT: a decision about the placeholder codec, i.e. making `toEip` computable at
  `G₁z` or pinning the five point fields by hand. That is OBJ.8 step 5's "point half OPEN", not a
  documentation fix, and it is outside this card.

  STILL CITED, STILL OUTSIDE THIS FENCE (reported, not edited — see the card's fence):
    `docs/plans/PLAN-V3-cards.md:753`  "Falsifier of the ticket: `PayloadAgrees poseidonRender` is
        refuted by `poseidon_payloadAgrees_not`" — now false as written for BOTH names.
    `docs/plans/PLAN-V3-cards.md:1716`  the `Done` card proves `not_done_today` "from
        `poseidon_payloadAgrees_not`" — that route no longer has a proof term behind it.
    `docs/plans/PLAN-V3-cards.md:656`  "`native_decide` appears only in the Deploy file, for
        `poseidon_delta_not`" — the name is gone from the evidence file; the tree's own
        `poseidon_delta_is` is the native_decide use now.
    `docs/plans/V3-evidence/design/statements.md:138`  lists `poseidon_payloadAgrees_not` under
        "Falsifiers, proved". It is no longer proved.
    `docs/plans/PLAN-V3.md:203`  says this file "keeps only `poseidon_payloadAgrees_not`, which
        refutes the D-P67 fallback" — it keeps the claim, not a refutation.
  `docs/plans/V3-evidence/design/statements.md` is OUTSIDE this card's fence (the fence is
  `V3-evidence/lean/statements/` only), so it is reported here rather than edited.

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

/-- **FALS2: `poseidon_delta_not` IS RETIRED HERE — IT WAS FALSE.** It asserted that the render's
    DELTA was NOT the field literal. OBJ.8 step 2 put the field constant on the render, so the tree
    proves the opposite at `Midfall/Instances/StatementsV3Deploy.lean:173-176` (`poseidon_delta_is`,
    "THE REFUTATION THAT DIED"). W13: a cited statement whose negation is proved goes in the same
    commit as the refutation. What replaces it is the corrected fact, proved on THIS side of the line
    — this file cannot import the tree module, because Lean refuses the fallback text and the single
    text in one environment ("environment already contains 'Midfall.LoweringV3.withCompressed'"),
    which is also why the claim below has to stay here and not move into the tree. -/
theorem poseidon_delta_is_at_fallback :
    poseidonRender.E.delta.val = Inline.natOfLiteral poseidonRender.inputs.frDelta := by
  show poseidonDelta.val = Inline.natOfLiteral poseidonInputs.frDelta
  native_decide

/-- **FALS2: A CLAIM, NOT A PROOF.** `poseidon_payloadAgrees_not` used to be a theorem refuting the
    fallback's `PayloadAgrees poseidonRender` through its `delta` field. OBJ.8 step 2 satisfied
    that field, so the proof died — but nothing replaced it, and nothing refutes the negation either:
    the five point fields are undecidable at the noncomputable placeholder codec `g1CodecZ`, and the
    tree records its own payload row as HALF (see the header). The statement is kept live under its
    cited name so the citations still resolve and so the record says "open" instead of "false".
    It is a `Prop`, so it cannot be applied like a proof. -/
def poseidon_payloadAgrees_not : Prop := ¬ PayloadAgrees poseidonRender

-- Machine-checked here, not asserted: the claim still elaborates against the fallback text, and the
-- delta clause it used to refute now holds (poseidon_delta_is_at_fallback above).
#check poseidon_payloadAgrees_not
#print axioms poseidon_delta_is_at_fallback

end Midfall.LoweringV3.Deploy
