/-
  Midfall.Instances.PoseidonPins

  S.9 (INFRA / PORT): **D-P50's deployment discharge**, transplanted verbatim from S.8's
  orchestrator-verified probes at 24762c3 and landed next to the clauses it feeds.

  WHAT IS IN HERE. `Statements.lean` section 2 gained two `Valid` clauses under D-P50 - `vkPins R` (four
  constant-table facts the `.vkLoading` block needs) and `vkProgressPins R` (the two more its
  PROGRESS half needs). A clause of `Valid` is supposed to be "a fact about the render that is
  decided by computation at a deployment", and this file is that computation for the six new ones:
  `pins_at_render : vkPins poseidonRender` and `progress_at_render : vkProgressPins poseidonRender`, both
  SORRY-FREE (S.8 printed both sides of all six; the values are VK_MPTR = 10496 = 0x2900,
  EXPECTED_VK_PAYLOAD_LENGTH = 4576, numInstances = 1, the VK window 10496..15072 lying BELOW
  g1_identity at 21760 - so `disjoint`'s RIGHT arm is the one that holds and its left arm is FALSE
  here, which is why the disjunction is stated rather than one side proved - and EXPECTED_VK_LENGTH =
  4577, and EXPECTED_VK_CODEHASH_WORD = 15933609736973938366157763540951553264596488184743928812768469146773639656731).

  THE ROUTE, AND WHY IT IS THE ONLY ONE (S.8 measured all of this; do not re-derive it).
  * `#eval`/`native_decide` straight at `poseidonRender` fails with `dependsOnNoncomputable`. The culprit is
    `Assumptions.instGroupBlsGT` - the CARRIER instance, not the render's own fields - so it is not
    something a later edit to the render can fix.
  * Plain `decide`/`rfl` fail even at the COMPUTABLE proxies, stuck at `List.lookup "VK_MPTR"`
    `(constTableOf poseidonM)`; `set_option maxRecDepth 20000` does not help and `vm_decide` is unavailable in
    this toolchain.
  * So: `native_decide` on `poseidonM`/`poseidonPv`/`poseidonPlanV2`/`poseidonConfig` - D.1's and D.2's computable
    terms, `Instances/PoseidonValid.lean` section 0 - and transfer the verdict to the render by defeq.
    The transfer is `rfl` every time, i.e. the kernel checks it and no tactic is trusted for it:
    `poseidonConsts_eq`, `poseidonPv_eq`, `poseidonPlan_eq`, `poseidonCfg_eq` are all `rfl` (PoseidonValid.lean:91-97).

  TRUSTED BASE, STATED PLAINLY (D-P50's accepted cost). Each of the six decisions contributes one
  generated `native_decide` axiom, `poseidonPins_proxy_*._native.native_decide.ax_1_1`. The seventh is
  `poseidonModel_isOk`'s, which is not a pin at all: `poseidonM` IS `poseidonModelVal`, whose
  projection already carries that axiom, so it arrives in every list here whether a pin needs it or
  not. The two terms below therefore depend on SEVEN `native_decide`
  axioms between them - the deployment path goes from 1 to 7 - on top of the standing
  `Assumptions.bls12_381Pairing / blsGT / blsGT_group / blsGT_module / blsGT_primeOrder` carrier axioms.
  No `sorryAx`. `native_decide` stays confined to `Midfall/Instances/`, which is where `checks.sh` requires it.

  WHAT THIS DOES NOT BUY. `poseidonRender.Valid` is still UNSATISFIABLE: C.4 refutes six of the original
  eleven clauses (`circuitMeta`, `layout`, `invariants`, `codegen`, `slots`, `supported`) at this plan, and
  `poseidonRender_notValid` (PoseidonValid.lean:468) is the theorem that says so. Adding clauses only
  strengthens `Valid`, so nothing here makes a false headline true; what it does is let the hinge
  `blockContracts_of_valid` ask for the pins from its OWN hypothesis `hR` instead of from free
  premises. `vk_blockRow` still carries three `sorry` - the clean walk, the poisoned walk, the exhibited
  run - and `cone_sorries vk_blockRow` is still 3.
-/
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.Instances.PoseidonValid

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonValid Midfall.Instances.PoseidonV2
open Midfall.Instances Midfall.Instances.PoseidonInputs
open Midfall.LoweringV2.Blocks.VkLoading

namespace Midfall.Instances.PoseidonPins

/-! ## 1. THE SIX DECISIONS AT THE COMPUTABLE PROXIES -/

/-- Pin 1 at the proxy: the table's VK window address. AXIOM: `poseidonPins_proxy_vkMptr._native.native_decide.ax_1_1`. -/
theorem poseidonPins_proxy_vkMptr :
    (constTableOf poseidonM).lookup "VK_MPTR" = some (ptrAddr poseidonPv.memory.vkMptr) := by
  native_decide

/-- Pin 2 at the proxy: the payload length the table binds. AXIOM:
    `poseidonPins_proxy_payloadLen._native.native_decide.ax_1_1`. -/
theorem poseidonPins_proxy_payloadLen :
    (constTableOf poseidonM).lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some poseidonPv.vk.len := by
  native_decide

/-- Pin 3 at the proxy: the plan view's instance count is the configuration's. AXIOM:
    `poseidonPins_proxy_numInst._native.native_decide.ax_1_1`. -/
theorem poseidonPins_proxy_numInst : poseidonPv.numInstances = poseidonConfig.numInstances := by
  native_decide

/-- Pin 4 at the proxy: the VK window does not clobber the g1_identity window. The RIGHT arm is the
    one that holds (10496 + 4576 = 15072 <= 21760); the left arm is false here, which is why the
    disjunction is stated the way `Statements` section 2 states it. AXIOM:
    `poseidonPins_proxy_disjoint._native.native_decide.ax_1_1`. -/
theorem poseidonPins_proxy_disjoint :
    ptrAddr poseidonPv.memory.g1IdentityMptr + 128 ≤ ptrAddr poseidonPv.memory.vkMptr
      ∨ ptrAddr poseidonPv.memory.vkMptr + poseidonPv.vk.len ≤ ptrAddr poseidonPv.memory.g1IdentityMptr := by
  native_decide

/-- The progress pin on the runtime length. AXIOM:
    `poseidonPins_proxy_vkLen._native.native_decide.ax_1_1`. -/
theorem poseidonPins_proxy_vkLen :
    (constTableOf poseidonM).lookup "EXPECTED_VK_LENGTH" = some poseidonPlanV2.vk.runtimeBytes.size := by
  native_decide

/-- The progress pin on the runtime codehash word - the heaviest decision here (keccak256 over 4577
    bytes). AXIOM: `poseidonPins_proxy_vkHash._native.native_decide.ax_1_1`. -/
theorem poseidonPins_proxy_vkHash : (constTableOf poseidonM).lookup "EXPECTED_VK_CODEHASH_WORD"
    = some (keccak256 poseidonPlanV2.vk.runtimeBytes).toNat := by
  native_decide

/-! ## 2. THE SAME SIX AT THE RENDER, BY DEFEQ TRANSFER (no tactic trusted for the transfer) -/

/-- `poseidonRender.consts` IS `constTableOf poseidonM` and `poseidonRender.pv` IS `poseidonPv`, both by `rfl`
    (`poseidonConsts_eq`, `poseidonPv_eq`), so the proxy decision IS the render fact. Every lemma in this
    section is discharged by `rfl` against the section-1 lemma above it - the kernel checks it. -/
theorem poseidonPins_vkMptr :
    ∃ m, poseidonRender.consts.lookup "VK_MPTR" = some m ∧ m = ptrAddr poseidonRender.pv.memory.vkMptr :=
  ⟨_, poseidonPins_proxy_vkMptr, rfl⟩

/-- Pin 2 at the render. -/
theorem poseidonPins_payloadLen :
    ∃ m, poseidonRender.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some m ∧
      m = poseidonRender.pv.vk.len :=
  ⟨_, poseidonPins_proxy_payloadLen, rfl⟩

/-- Pin 3 at the render. -/
theorem poseidonPins_numInst :
    poseidonRender.pv.numInstances = poseidonRender.cfg.numInstances :=
  poseidonPins_proxy_numInst

/-- Pin 4 at the render. -/
theorem poseidonPins_disjoint :
    ptrAddr poseidonRender.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr poseidonRender.pv.memory.vkMptr
      ∨ ptrAddr poseidonRender.pv.memory.vkMptr + poseidonRender.pv.vk.len
        ≤ ptrAddr poseidonRender.pv.memory.g1IdentityMptr :=
  poseidonPins_proxy_disjoint

/-- The runtime-length pin at the render. -/
theorem poseidonPins_vkLen :
    ∃ m, poseidonRender.consts.lookup "EXPECTED_VK_LENGTH" = some m ∧
      m = poseidonRender.plan.vk.runtimeBytes.size :=
  ⟨_, poseidonPins_proxy_vkLen, rfl⟩

/-- The codehash pin at the render. -/
theorem poseidonPins_vkHash :
    ∃ m, poseidonRender.consts.lookup "EXPECTED_VK_CODEHASH_WORD" = some m ∧
      m = (keccak256 poseidonRender.plan.vk.runtimeBytes).toNat :=
  ⟨_, poseidonPins_proxy_vkHash, rfl⟩

/-! ## 3. THE TWO STRUCTURE TERMS - THE DISCHARGE D-P50 NEEDED -/

/-- **`Render.Valid` CLAUSE 12, PROVED AT THE DEPLOYMENT.** S.8's `pins_at_render`, transplanted
    unchanged: the four `vkPins` fields are the four section-2 lemmas, and nothing in the
    conjunction is left as a hypothesis. `vk_blockRow` now reaches this through `hR.vkPins`. -/
theorem pins_at_render : vkPins poseidonRender :=
  ⟨poseidonPins_vkMptr, poseidonPins_payloadLen, poseidonPins_numInst, poseidonPins_disjoint⟩

/-- **`Render.Valid` CLAUSE 13, PROVED AT THE DEPLOYMENT.** S.8's `progress_at_render`, transplanted
    unchanged. `vk_blockRow` now reaches this through `hR.vkProgressPins`. -/
theorem progress_at_render : vkProgressPins poseidonRender :=
  ⟨poseidonPins_vkLen, poseidonPins_vkHash⟩

end Midfall.Instances.PoseidonPins

#print axioms Midfall.Instances.PoseidonPins.pins_at_render
#print axioms Midfall.Instances.PoseidonPins.progress_at_render
