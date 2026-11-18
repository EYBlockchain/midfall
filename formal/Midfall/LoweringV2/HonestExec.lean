/-
  Midfall.LoweringV2.HonestExec

  THE HONEST EXECUTABLE DIALECT (T3.1, PLAN-V3): `Midfall.Yul.WpBridge`'s lawful executable dialect
  instantiated at the honest call relation of conjunct 2. Ported VERBATIM from the proved scratch
  source `docs/plans/V3-evidence/lean/prooftech/P1_Exec.lean` (lines 146-166: `callsOf_graph`,
  `honestExec`, `honestExec_lawful`, `honest_adequacy`); only the namespace, the imports and this
  header changed.

  WHY A LoweringV2 FILE AND NOT Midfall/Yul/WpBridge.lean: `callsOf` lives in
  `Midfall/LoweringV2/Statements.lean` (frozen), and `Midfall/Yul` is the lower layer - it must not
  reach up into `LoweringV2`. The card decides this by imports, not by taste (Do 2, "placement
  decided by imports"; Stop-if). No cycle arises in either direction.

  WHY IT MATTERS. `Bridge.RunCommitted` and the block rows are stated over the RELATIONAL open
  dialect `Bridge.Dialect (callsOf product) (ofFun fun _ => 0)`, which has no executable
  interpreter because an arbitrary relation is not a function. `honest_adequacy` is the bridge
  across: at the honest oracles the relation IS a function graph (`callsOf_graph`), so the vendored
  interpreter runs it and `Interp.adequacy` identifies the two. This is the statement
  `Midfall/Lowering/RunEmitted.lean:33` records as attempted and not landed, and it is what T3.11
  (the W14 executable exhibit) consumes.

  AXIOMS: `execOf_lawful` is the only nontrivial dependency and it rests on `[propext, Quot.sound]`;
  no `sorryAx`, no `native_decide` (D-P71).
-/
import YulSemantics
import Midfall.LoweringV2.Statements
import Midfall.Yul.WpBridge
set_option autoImplicit false

namespace Midfall.LoweringV2
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Yul.WpBridge

/-- The honest dialect of conjunct 2 is a function graph. -/
theorem callsOf_graph (product : PairingProduct) (req : EVM.CallRequest) (st : EvmState)
    (resp : CallResponse) :
    (Midfall.LoweringV2.callsOf product).Call req st resp ↔
      honestOf (honestRelations product) req st = some resp := by
  simp [Midfall.LoweringV2.callsOf, honestCalls]

/-- The honest executable dialect: `toDialect` IS the dialect of `BlockProgress` / conjunct 2. -/
@[reducible] def honestExec (product : PairingProduct) : ExecDialect :=
  execOf (Midfall.LoweringV2.callsOf product) (ExternalGas.ofFun fun _ => 0)
    (honestOf (honestRelations product)) (fun _ => 0)

theorem honestExec_lawful (product : PairingProduct) : (honestExec product).Lawful :=
  execOf_lawful (callsOf_graph product) (fun _ _ => Iff.rfl)

/-- Adequacy at the OPEN honest dialect: this is the statement `run_adequacy` could not give. -/
theorem honest_adequacy (product : PairingProduct) {funs V st code res} :
    Step (Bridge.Dialect (Midfall.LoweringV2.callsOf product) (ExternalGas.ofFun fun _ => 0))
        funs V st code res ↔
      ∃ n, Interp.InterpOk (honestExec product) n funs V st code res :=
  Interp.adequacy (honestExec_lawful product)

end Midfall.LoweringV2
