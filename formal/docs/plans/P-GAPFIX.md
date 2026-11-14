# P-GAPFIX - the gap records still name closed blockers. Re-pin them and the gate tokens together.

Status: READY, small, and **required for honesty.** P-POINTCOUNT landed four-of-four on the G1
side, but two gap records still claim otherwise. Leaving them is exactly the failure this project
keeps hitting — a stale claim that reads as current.

## What is stale

| site | what it says | truth |
|---|---|---|
| `Instances/ObligationsGates.lean` `gap_holds_unexhibited` (~:475) | blocker tokens name `g1Valid`, `Nat.Prime pBase`, `Nat.card G1Frame = r` | **all three closed** — `g1Valid` by P-CURVE, `Nat.Prime pBase` by `BasePrime`, the count by P-POINTCOUNT |
| `Instances/Bls12_381G1.lean` `gap_g1_prime_order` (~:306) | names the r-torsion count as an open blocker | **closed** by `torsion_eq_zpowers_gen` |
| `scripts/check_hypothesis_bundles.py` | registry enforces those body-only tokens | **must be edited in the same commit** or the bundle gate reddens |

P-POINTCOUNT deliberately left these untouched rather than redden the gate. That was correct
delegation — it is the orchestrator's registry to change.

## Deliverable

1. **Rewrite both gap records** to name what is *actually* still open. Per P-POINTCOUNT's
   required finding, the remaining blockers before a single `Holds` term are:
   * **`g2Valid`** — needs an Fp2 model (`Fp[u]/(u²+1)` is buildable; `p ≡ 3 [MOD 4]` is already
     pinned), then the G2 curve, codec, group-law agreement and **its own r-torsion argument —
     and the `2p+1 < r²` pigeonhole FAILS over Fp2**, since `r² ~ p^{4/3} < 2p²+1`. That last
     point must be recorded, or the next package will re-derive it.
   * **`pairing2` at real points** — needs an `AdmissiblePairing` on the curve groups; currently
     discharged only at the exponent model, whose `toEip` is not a curve point. D-P36 stands:
     assume or construct; construction is larger than this project.
2. **Update the registry tokens in the same commit** so the bundle gate stays green and keeps
   enforcing the *new* blocker names. The point of the token mechanism is that a gap cannot
   silently revert to a stale blame — so the new tokens must be as specific as the old ones.
3. **Add a `gap_g2_no_fp2_model` record** if one does not exist, so the G2 blocker is named in the
   registry rather than only in prose.
4. **Verify the four-of-four exhibit is actually reachable from the gate**: `g1CodecZ_g1_four`
   exists — is anything in the bundle registry still claiming no G1 codec satisfies `Holds`?
   `expG1Codec_not_holds` is about the *exponent* codec and stays valid; do not delete it.

## Constraints

* **`gap_holds_unexhibited` must NOT be deleted** — `Holds` is still not exhibited as a single term
  (two clauses remain). It must be *re-pointed*, not removed. Deleting it reddens the gate and
  would be false.
* **Keep `gap_holdsOld_empty` and the `HoldsOld` refutations** — they pin the repaired defect, per
  the standing rule that fixed defects stay as failing terms.
* **After any scripted insert, assert the file grew** — a splice last round deleted 44 KB of proofs
  and the build stayed green.
* **D-P23**: the rewritten gap records need a demonstrated failure mode — show the bundle gate
  reddens if a new token is dropped, as P-CURVE did for the old ones.
* **RAM (D-P31)**: `ram_guard.sh --selftest` FIRST and read its output before VM work.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. Report back even if stuck.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5202 jobs**, 113 modules; `checks.sh` green: **57 tracked sorries**, 1298 KATs
across 88 files, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements hash OK.

Read first: `Midfall/Instances/ObligationsGates.lean` (`gap_holds_unexhibited`,
`gap_holdsOld_empty`, `bundle_holds_empty`), `Midfall/Instances/Bls12_381G1.lean`
(`gap_g1_prime_order`, `gap_g1_no_group_law`), `scripts/check_hypothesis_bundles.py` (the
body-only token registry), `Midfall/Instances/G1PointCount.lean` (what is now proved),
`docs/design.md` D-P34/D-P36.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green, with the bundle gate enforcing the NEW tokens.
- Both stale records re-pointed to the real remaining blockers; nothing deleted that pins a
  repaired defect.
- **Required finding**: with the gap records accurate, what is the honest count of clauses
  discharged at a real-curve codec versus at the exponent model — and is there now a path to a
  single `Holds` term that does not require constructing Fp12?
