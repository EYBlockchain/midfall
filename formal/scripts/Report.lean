import Midfall

/-!
THE PROGRESS REPORT AND THE WHOLE-TREE SWEEPS, IN ONE COMMAND: `lake env lean scripts/Report.lean`
(DG.2, PLAN-V3 section 5). It imports ALL of Midfall, so a refutation landed anywhere is seen.

PROVENANCE. This is `docs/plans/V3-evidence/lean/tooling/Report.lean` from `end
Midfall.Tools.Done` onward - the part of that prototype that is NOT `Midfall/Tools/Done.lean`, which
DG.1 landed as the namespace. The prototype carries the namespace inline and it is byte-identical to
the landed file for those 660 lines, so copying it whole here would redeclare every helper: `import
Midfall` already brings them in. The file lives under `scripts/`, not `Midfall/`, on purpose: it
imports all of Midfall, and `lake build` must never compile it (same reason as DoneTest.lean).

OUTPUT CONTRACT, shared with the gates. Lines starting `SORRY ` feed the register - via
`scripts/sorries.sh --env`, hence SORRY.md and the checks.sh sorry section. Lines starting `DECL `
will feed Closure.manifest (DG.3, not landed yet). Everything else is the STATUS.md header verbatim
(DG.8). A verdict that is a GATE is logged as a Lean error, so it exits non-zero and `sorries.sh
--env` fails with it; a verdict that is a REPORT is info.

`#assert_no_refuted_sorry` is deliberately NOT run here yet: that is DG.6, and today it errors on
`Midfall.Instances.PoseidonV2.poseidon_valid`, which PL.1 has not removed yet.
-/
open Midfall.Tools.Done
open Midfall Midfall.Lowering Midfall.LoweringV2 Midfall.Generator
open Midfall.Instances.PoseidonValid

-- (i) THE PROGRESS ROOT (D-P74 item 3): the V3 generator theorem, leaf by leaf, and beside it the
--    first milestone (the soundness half). The V2 fixture headline is reported as RETIRED until PL.H
--    deletes it; it is no longer what the register's ROOT column or this report measures.
#cone_report Midfall.LoweringV3.lowering_correct under [Midfall]
#cone_report Midfall.LoweringV3.lowering_sound under [Midfall]
#eval IO.println "RETIRED (D-P74 item 3): Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon - the V2 fixture headline; reported here as retired, deleted by PL.H (WP A13). Its cone is not the progress measure."
#cone_sorries Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon

-- (ii) executable exhibits (names fixed by PLAN-V3; none exists at this commit)
#exhibits [Midfall.Instances.PoseidonExhibit.fixture_returns_abiTrue_ok,
           Midfall.Instances.PoseidonExhibit.fixture_leanAccepts_ok,
           Midfall.Instances.PoseidonExhibit.mutants_revert_ok,
           Midfall.Instances.PoseidonExhibit.mutants_leanRejects_ok]

-- (iii) block coverage at the deployment, and the weights
#block_coverage Midfall.LoweringV2.BlockRow Midfall.Lowering.Partial at Midfall.Instances.PoseidonV2.poseidonRender under [Midfall]
#eval IO.println s!"slice_tokens {partials.map fun q => (reprStr q, (yulTokens (YulSemantics.EVM.print (sliceOf poseidonPv poseidonM q))).length)}"
#eval IO.println s!"program_tokens ast_main {(yulTokens (YulSemantics.EVM.print (mainAsmRaw poseidonPv poseidonM))).length} generator_text_main {(mainAssemblyTokens poseidonM).length} codegenAgrees {codegenAgrees poseidonPv poseidonM}"

-- (iv) the axiom allow-list over the whole tree
#axiom_sweep [Midfall, YulSemantics] allow [Midfall.Assumptions.blsGT, Midfall.Assumptions.blsGT_group,
   Midfall.Assumptions.blsGT_primeOrder, Midfall.Assumptions.blsGT_module,
   Midfall.Assumptions.bls12_381Pairing] nativeModules [Midfall.Instances]

-- the register and the closure manifest
#sorry_sweep [Midfall] root Midfall.LoweringV3.lowering_correct
#closure_fingerprint [Midfall.LoweringV2.LoweringEquivalence, Midfall.LoweringV2.Render.Valid,
  Midfall.LoweringV2.HypothesesInhabited, Midfall.LoweringV2.EndToEnd,
  Midfall.LoweringV2.EntryFrameInhabited] under [Midfall, YulSemantics]
