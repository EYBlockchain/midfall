/-
  StatementsV3Falsifiers — **RETIRED** (card RECON.1b-iii, 2026-11-18).

  THIS FILE WAS THE PRE-LANDING SCRATCH COPY OF `Midfall/Instances/StatementsV3Falsifiers.lean`.
  Sections F1-F9 LANDED: ST.1c put them in the tree and ST.1b converted every measurement to an
  annotated gate, so the tree module carries **7** `#eval ... -- expect ...` gates
  (`scripts/kat_gate.py`, its ST.1c note). The landed header repeats this file's F1-F9 list
  verbatim. This file stopped elaborating at ST.4/ST.6, and all three of its errors were the frozen
  surface moving under it:
    :95  `h.circuitMeta` — ST.6 deleted `Render.Valid.circuitMeta`; the tree pins the pre-ST.6
         clause as `ValidPreST6_circuitMeta` (and `ValidPreST6_layout`) and states
         `frozenValid_numPointSets_zero` against the pin, so the `setNumPointSets` falsifier
         survives with its teeth.
    :188 `entryFrame_inhabited` no longer yields `∃ st₀, EntryFrame ... (padBytes cd N) st₀` — the
         tree pins the pre-ST.4 frame as `EntryFramePreST4` and exhibits F3 there.
    :326 `EntryFrame.mk` gained a sixth explicit field (`cdSize`) at ST.4 — same pin, same fix.

  WHERE EACH SECTION LANDED (tree module `Midfall/Instances/StatementsV3Falsifiers.lean`):
    F1 the double repack -> frozenCalldata_isOk, calldataOfV3_witness_ok, firstRepackLengths_ok,
       secondRepackError_ok  (the `frozenCalldata` pin the brief names: `(416, 416, 176)` and
       "lengthMismatch expected 176 actual 416" are gated Bools there, same literals)
    F2 circuitMeta forces numPointSets = 0 -> new_numPointSets_zero, ValidPreST6_circuitMeta,
       ValidPreST6_layout, frozenValid_numPointSets_zero, f2DeployMeasurement_ok
    F3 calldatasize wraps -> EntryFramePreST4, entryFrameV3_refuses_padded, leanAccepts_pad_false
    F4 EnvAgrees pins neither delta nor commitments -> envAgrees_delta_free,
       envAgrees_commitments_free
    F5 the frozen codec bundle -> the F5 examples at `g1CodecZ_laws`
    F6 the hoist breaks fail_lookup := rfl -> the F6 example
    F7 WellFormed.permutationCommitmentsMatch -> f7WellFormedCounts_ok, `(8, 8, 3)` pinned
    F8 the frozen gate does not ask for LeanAccepts -> leanAccepts_bump_false
    F9 rejects_of_not_accepts contradicts an accepted returning run ->
       rejects_of_not_accepts_contradiction (still cites the tree's sorried lemma, so its
       `#print axioms` still shows `sorryAx` — the finding, not a hole)
    plus the deploy-side repack lengths -> deployRepackLengths_ok, `(2640, 4320, 4320)` pinned.

  WHAT THIS FILE HELD THAT THE TREE DOES NOT — ONE THEOREM, KEPT LIVE BELOW, NOT DELETED.
  `payloadAgrees_pins_delta` has no counterpart in the landed module, and that deletion is
  deliberate and documented: the tree says at lines 285-293 "**`PayloadAgrees` IS BLIND TO `delta`
  NOW, ON PURPOSE (RECON.1 step 3)** ... The single text drops that field because the `generated`
  clause pins `E.delta` against the PROGRAM instead ... so the old theorem is deleted rather than
  restated." The theorem below therefore lives at the D-P67 EIGHTEEN-CLAUSE fallback text in
  `StatementsV3.lean` beside this file — the only `PayloadAgrees` that still has a `delta` field —
  and it cannot be stated against the landed module at all (Lean refuses both texts in one
  environment: "environment already contains 'Midfall.LoweringV3.withCompressed'"). It is CITED by
  `design/statements.md:138`, so it is kept, not deleted. Its replacement under the single text is
  `GeneratedKats.generateAll_falsifierDeltaAndOmega_ok`.

  WHY THE FILE IS STILL IN THE GATE AND NOT REMOVED: `check.sh` names it twice — line 44 in the
  `statements` area and line 58 as a precompiled dependency of the `object` area. Retiring it from
  the gate would mean editing `check.sh`, which is a gate change under D-P69 and not this card's to
  make. Nothing in `lean/object/` imports this module by name (`GeneratorCertified.lean` imports
  `ObjectV3Full` and `GeneratorTheorem`; `GeneratorTheorem` imports the LANDED
  `Midfall.Instances.StatementsV3Falsifiers`), so line 58 is satisfied by any file that elaborates.
-/
import StatementsV3
import Midfall.Instances.PoseidonValid
import Midfall.Instances.CurveSurface
set_option autoImplicit false

namespace Midfall.LoweringV3.Falsifiers

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- `PayloadAgrees` is NOT blind to `delta`: two renders that differ only there cannot both
    satisfy it. **AT THE FALLBACK TEXT** — see the header: this is the eighteen-clause
    `PayloadAgrees` of `StatementsV3.lean` (D-P67), whose `delta` field the single text dropped
    on purpose. PROVED, no `sorry`. -/
theorem payloadAgrees_pins_delta (R : Render p G₁ G₂ Gₜ) (d : Fr p)
    (h : PayloadAgrees R) (h' : PayloadAgrees { R with E := { R.E with delta := d } }) :
    d = R.E.delta := by
  have h1 : R.E.delta.val = Inline.natOfLiteral R.inputs.frDelta := h.delta
  have h2 : d.val = Inline.natOfLiteral R.inputs.frDelta := h'.delta
  exact ZMod.val_injective p (h2.trans h1.symm)

#print axioms payloadAgrees_pins_delta

end Midfall.LoweringV3.Falsifiers
