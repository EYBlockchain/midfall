import ObjectV3Full
import StatementsV3
set_option autoImplicit false

/-! MEASUREMENT (T2 sanity): each decidable section-3 / section-5 lemma conclusion of
    GeneratorCertified.lean, evaluated with TODAY's `mainAsmRaw` at the generator-derived
    fixture render (`Fixture.gen`; payload = the Rust payload as input, ObjectV3Full 7). -/

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open Midfall.Lowering.YulParse YulSemantics YulSemantics.EVM

#eval Fixture.report Fixture.gen fun o =>
  let m := o.model
  let pv := planViewOf o.plan o.model none
  let main := mainAsmRaw pv
  let P2a := m.quotientDirect.isNone
  let P2b := constLinesLiteral m
  let P2c := constTableOf m == expectedConsts pv m
  let P2d := decide (((expectedConsts pv m).map Prod.fst).Nodup)
  let P2e := ((freeNames (abiGuardBlock m ++ main)).filter
      fun x => x != "vk" && x != "quotientEvaluator").all
      fun x => ((expectedConsts pv m).map Prod.fst).contains x
  let P3 := callsResolved main
  let P4 := noShadow (constTableOf m) (abiGuardBlock m ++ wrapperLocals m 0 0 ++ main)
  let P5 := (freeNames (Inline.inlineContractConstants (constTableOf m) (abiGuardBlock m ++ main))).all
      (fun x => x == "vk" || x == "quotientEvaluator")
  let P6 := decide (0x80 ≤ pv.memory.transcriptMptr)
  let NW := Midfall.Yul.Bridge.noWritersFuel 20000 (asmOf pv m 0 0)
  let XD := Midfall.LoweringV3.exitDisciplineFuel 20000 (asmOf pv m 0 0)
  let NS := Midfall.LoweringV3.noShadowCore pv m
  let MC := mainClosed pv m
  let CB := decide (o.plan.proofLayout.proofEnd + 32 + 32 * 1 < 2 ^ 256)
  let LY := match ProofCalldataLayout.fromProtocol o.plan.meta_.protocol abiVerifyProofProofCptr
      o.plan.meta_.numEvals o.plan.meta_.numPointSets with
    | .ok l => l.proofLen == o.plan.proofLayout.proofLen | .error _ => false
  let INV := match o.plan.validateGeneratorInvariants with | .ok (.ok ()) => true | _ => false
  let LAY := decide o.plan.memory.map.WellFormed && o.plan.memory.validate.isOk
  let K := pv.k == (Midfall.Instances.PoseidonEnv.poseidonVkExec).domain.k
  s!"with mainAsmRaw: P2a={P2a} P2b={P2b} P2c={P2c} P2d={P2d} P2e={P2e} P3={P3} P4={P4} P5={P5} P6={P6} noWriters={NW} exitDiscipline={XD} noShadowB={NS} mainClosed={MC} cdBound={CB} layoutV3={LY} invariants={INV} supported.layout={LAY} env_k={K}; vk.domain.k={(Midfall.Instances.PoseidonEnv.poseidonVkExec).domain.k} pv.numNegLagranges={pv.numNegLagranges} blinding+1={(((Midfall.Instances.PoseidonEnv.poseidonVkExec).cs.blindingFactors.toOption.getD 0)) + 1}"
