import RunLib
set_option autoImplicit false
/-! The TREE's own top-level composition (Exec/Native.lean `prepare`, the body of `verifyNative`)
    at the real codec, real delta and real commitments - unpatched Exec. -/
namespace RefRun
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2 RefModel
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv Midfall.Conformance

def envReal : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecC, field := poseidonFc, delta := deltaReal, fewerPointSetsRuntime := false }

def topLevel (label : String) (cs : ConstraintSystem (Fr blsR)) : IO Unit := do
  let (proof, _, _, publicHex) ← loadBundle
  let some vk := mkVk cs | IO.println "vk"
  let inst : List (Fr blsR) := (publicHex[0]?.getD #[]).toList.map fun b => ((bytesToNatBE b : Nat) : Fr blsR)
  let m := Midfall.Halo2.prepare (Gₜ := G₁z) envReal Features.solidity vk [[1]] [[inst]]
  match StateT.run m (Transcript.initFromBytes proof) with
  | .ok (_, t) => IO.println s!"{label}: prepare ok, pos={t.pos}"
  | .error f => IO.println s!"{label}: prepare = {faultStr f}"

end RefRun
#eval RefRun.topLevel "tree prepare, raw imported cs" Midfall.Instances.PoseidonFixture.poseidonCs
#eval RefRun.topLevel "tree prepare, canonical rotations" RefRun.csCanon
