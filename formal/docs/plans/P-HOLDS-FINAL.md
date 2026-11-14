# P-HOLDS-FINAL - install D-P36a and land a single unconditional Holds term.

Status: READY, and **this is the last step on the G1/G2 track.** P-G2B staged it: holds_staged
exhibits all six Holds clauses given an AdmissiblePairing on the exhibited groups. What remains is
to install that hypothesis as a **named, gate-enforced assumption** per **D-P36a** and discharge
Holds unconditionally.

## Steps, in order

1. **State the named hypothesis** in Assumptions/ - that an AdmissiblePairing G1z G2fold Gt exists
   with the required Group/PrimeOrderWith/Module instances on Gt. **Named, documented,
   gate-enforced** - not a bare sorry, per the project's standing policy.
2. **Derive the unconditional Holds** from holds_staged. Should be a few lines.
3. **Register the assumption** so it cannot silently widen: a record naming exactly what is
   assumed, plus a gate token - the same mechanism that now protects the gap records.
4. **Update gap_holds_unexhibited** to CLOSED, with registry tokens changed **in the same commit**.
   **Keep bundle_holds_empty if it is still true at the fixture** - P-G2B's caveat (b) says the
   fixture wall is a separate fact about which codec the Surface installs, **not** a seventh
   clause. **Verify before deleting anything.**
5. **State what Holds buys**: which of the ten *_spec theorems and which LoweringCorrect fields
   become non-vacuous. finalPairing_spec takes Holds as a binder - is it now provable, or does it
   still need the Bridge/Partials work?

## Constraints

* **Do not weaken Holds to make it dischargeable.** If a clause resists, report it. The value of
  this package is that the exhibit is *honest*.
* **Enumerate the trusted base.** Add the new assumption to the list alongside the EIP-2537
  semantics, p = r, the pairing, and the solc hop - docs/PLAN.md's trusted-base section.
* **Instances/ confinement (D-P17)**; **D-P23 both halves as theorems** (falsification-deletion
  gap measured **thirteen** times - claim no coverage for falsifications).
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **Label prescriptions tried or guessed** - new rule from ledger R6. Do not record a tactic fix
  you have not tested.
* **RAM (D-P31)**: ram_guard.sh --selftest first and read it; --proc-limit 6G --limit 24G.
* **checks.sh is ~476 s** - do not add heavy #evals to #eval-bearing files.
* Do NOT edit Statements.lean, Statements.sha256, Rust, or vendor/. Do NOT git add or commit.
  Leave no scratch. Report back even if stuck.

## Environment

Repo /Users/julian/midfall, branch formal/baseline, tag formal-baseline-v1 at df7e607.
Build green at **5208 jobs**, 118 modules; checks.sh green: **57 tracked sorries**, 1302 KATs
across 90 files, 158 fragments, 12 fact families, 8 bundles with 4 gap defs, 30 pins, Statements
hash OK. **D-P32**: Rust pinned to 2d52f24.

Read first: Midfall/Instances/HoldsStaging.lean (holds_staged, frameLaws_g2fold,
holds_staged_needs_a_real_g2_encoder), Midfall/Assumptions/Pairing.lean, Midfall/Common/Curve.lean
(AdmissiblePairing), Midfall/Instances/ObligationsGates.lean (gap_holds_unexhibited,
bundle_holds_empty, gapHoldsBlockers_ok), docs/design.md D-P36.

## Acceptance

- lake build and bash scripts/checks.sh green.
- A single unconditional Holds exhibit, with the assumption named and gate-enforced.
- **Required finding**: with Holds landed, what is the honest remaining distance to
  lowering_equivalence - is it now purely the LoweringCorrect fields and the Bridge step lemmas,
  with no model-construction left?
