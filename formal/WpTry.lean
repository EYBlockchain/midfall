import Midfall.LoweringV3.Totality
set_option autoImplicit false

namespace Midfall.LoweringV2.Blocks.EcPairing

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage
open Midfall.LoweringV2.Blocks.TraceReturn
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac Midfall.Yul.VKP

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

example (product : PairingProduct) {g : ExternalGas} (funs : FunEnv (Bridge.Dialect (callsOf product) g))
    (st : EvmState) (LA GB LB GN : Bytes) (lhsW rhsW : U256) (scratch g2 neg : Nat)
    (cf : EVM.CallRequest → EvmState → Option EVM.CallResponse)
    (hcf : cf { kind := .staticcall, gas := 100, target := 0x0f, value := 0,
                input := readBytes st.memory scratch 768 } st = none)
    (hvalid : pairingValidInput (pairingFrame [(LA, GB), (LB, GN)]) = true)
    (hans : product (pairingFrame [(LA, GB), (LB, GN)]) = true)
    (hfail : ∃ cenv, lookupFun funs "fail" = some (failFDecl, cenv))
    (hsrc1 : bytesAt st lhsW.toNat 128 = LA)
    (hsrc2 : bytesAt st (g2 % 2^256) 256 = GB)
    (hsrc3 : bytesAt st rhsW.toNat 128 = LB)
    (hsrc4 : bytesAt st (neg % 2^256) 256 = GN)
    (hdisj1 : (scratch % 2^256) + 768 ≤ lhsW.toNat ∨ lhsW.toNat + 128 ≤ (scratch % 2^256))
    (hdisj2 : (scratch % 2^256) + 768 ≤ (g2 % 2^256) ∨ (g2 % 2^256) + 256 ≤ (scratch % 2^256))
    (hdisj3 : (scratch % 2^256) + 768 ≤ rhsW.toNat ∨ rhsW.toNat + 128 ≤ (scratch % 2^256))
    (hdisj4 : (scratch % 2^256) + 768 ≤ (neg % 2^256) ∨ (neg % 2^256) + 256 ≤ (scratch % 2^256))
    (hg2 : g2 < 2^256) (hneg : neg < 2^256) (hscratchWin : scratch + 768 < 2^256) :
    wpSS (Bridge.Dialect (callsOf product) g)
      (Bfun (callsOf product) g cf (fun _ => 0))
      (Cfail (callsOf product) g) 100
      (hoist (Bridge.Dialect (callsOf product) g)
        (ecPairingBodyLit scratch g2 neg 100 0x0f 768 32 0x84e81692 0xc3b0d8cd) :: funs)
      [("ret", (0 : U256)), ("success", (1 : U256)),
       ("lhs_mptr", lhsW), ("rhs_mptr", rhsW)] st
      (ecPairingBodyLit scratch g2 neg 100 0x0f 768 32 0x84e81692 0xc3b0d8cd)
      (fun _ _ _ => True) := by
  wp_run
  · exact ⟨_, hfail⟩
  · rename_i st4
    trace_state
    sorry

end Midfall.LoweringV2.Blocks.EcPairing
