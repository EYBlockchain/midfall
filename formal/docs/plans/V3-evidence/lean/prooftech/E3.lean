import P1_Exec
set_option autoImplicit false
open Midfall Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge Midfall.Scratch.ProofTech

/-! E3: the WHOLE closed deployment program under the fuel interpreter at the open honest dialect. -/
abbrev E := honestExec (fun _ => true)

def cdSyn : List UInt8 := (List.range 4484).map fun i =>
  if i == 35 then 0x40 else if i == 66 then 0x11 else if i == 67 then 0x40
  else if i == 98 then 0x10 else if i == 99 then 0xe0 else if i == 4451 then 1 else 0

def env0 : ExecEnv :=
  { calldata := cdSyn
    keccakOf := hashOfBytes Midfall.keccak256
    extCodeOf := fun _ => poseidonPlanV2.vk.runtimeBytes.data.toList }

def stEntry : EvmState :=
  { EvmState.init with env := env0, memory := storeWord (fun _ => 0) 0x40 (0x80 : U256) }

def summ (r : Result (Interp.SResult E)) : String :=
  match r with
  | .ok (V, st, o) =>
      s!"ok outcome={repr o} halted={repr (st.halted.map fun h => (h.1, h.2))} " ++
      s!"vars={V.map (·.1)} activeWords={st.activeWords.toNat}"
  | .stuck => "STUCK"
  | .outOfFuel => "OUT-OF-FUEL"

def prog : Block EVM.Op := asmOf poseidonPv poseidonM 7 0
#eval prog.length
#eval (yulTokens (YulSemantics.EVM.print prog)).length
def timed : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := summ (Interp.run E 10000000 prog stEntry)
  IO.println r
  let t1 ← IO.monoMsNow
  IO.println s!"whole-program interpreter time: {t1 - t0} ms"
#eval timed
