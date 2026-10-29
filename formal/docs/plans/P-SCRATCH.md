# P-SCRATCH - the converged layout disagrees with the deployed artifact on one slot. Diagnose and fix.

Status: READY. Found and measured by P-HELPERS, deliberately left for its owner.
**This is a correctness bug in the port, not a cosmetic mismatch.**

## The defect

For `scalarInvScratchMptr` there are **three different values in the tree**:

| source | value | note |
|---|---|---|
| text port `poseidonCtx` | **`0x2800`** | what the **deployed artifact prints** |
| converged Lean layout, witness plan view | **`0x1f00`** | what `PlanView.memory` carries |
| converged Lean layout, poseidon layout | **`0x3f00`** | also derived |

The other two helper slots the emitted helpers read (`finalPairingScratchMptr` 4672,
`accumulatorPairingBatchMptr` 4096) **agree** between ctx and plan. So this is **one slot**,
not a general split - which makes it diagnosable rather than architectural.

Pinned as data by `emitScalarInvScratchSourcesDiffer_ok`. **Nothing catches it**, because no
gate has ever compared `emitMain`'s helper region against the dump.

## Deliverable

1. **Determine which spelling is correct** by reading the Rust: `memory.rs:437` and the
   surrounding arena allocation order. The artifact is what is **deployed**, so if the
   converged layout derives a different address, either the port of `memory.rs:437` is wrong,
   or the text port's `0x2800` is a hard-coded observation that happens to match a different
   profile. **Say which, with the Rust cited.**
2. **Fix the wrong one.** If the converged layout is wrong, correct `LayoutMemory.lean` and
   re-check every gate that reads a derived address - the arena is computed sequentially, so
   one wrong slot may shift later ones. If the text port is wrong, correct `poseidonCtx` and
   re-pin whatever byte-exact gates move.
3. **Add the missing gate**: compare `emitMain`'s emitted helper region against the artifact
   dump. That is the check that would have caught this, and its absence is the actual bug -
   the value mismatch is just what it revealed.
4. **Update `emitScalarInvScratchSourcesDiffer_ok`** to assert agreement once fixed, or to
   record a justified divergence if the three values are legitimately different views.

## Constraints

* **Do not paper over it by making the gate compare fewer things.** If the fix is "delete the
  mismatching pin", stop and report instead.
* **Numeric spelling is invisible to every AST relation** - an address mismatch in decimal vs
  hex will not be caught by `stmtsBeq` or `yulTokens`. Compare **values**, not text.
* **`/-! ---- -/` does not close** (standing note). **`yul%` cannot write `end`.**
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp, verify `git diff --numstat`.
* **D-P23 / R-41**: witness AND failure mode. The new gate must be shown to redden - revert
  the fix on a copy and confirm it catches the mismatch.
* Keep all 12 gate sections green. `SORRY.md` delta should be zero.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5153 jobs**; `checks.sh` green: 64 tracked sorries, **1272 KATs across 84
files**, 111 statement fragments, 12 fact families, 23 spec-theorem bundles, 30 baseline
pins, Statements hash OK.

Read first: `Midfall/Generator/LayoutMemory.lean:193` and `:326`, `:357` (the derivation),
`Midfall/Generator/VerifierPartials.lean` (`poseidonCtx`), the artifact dump under
`proofs/solidity-verifier/target/poseidon-fixture-dump/`, and the Rust
`proofs/src/.../memory.rs:437`. Also `Midfall/Lowering/Partials.lean`
(`emitScalarInvScratchSourcesDiffer_ok`).

## Acceptance

- The three values reconciled, with the Rust cited as the arbiter.
- A gate exists that compares the emitted helper region against the artifact, and is shown to
  redden if the mismatch returns.
- **Required finding**: does the wrong address change any **deployed byte**? If the artifact
  is correct and only the Lean derivation was wrong, the deployment is fine and this is a
  port bug. If the reverse, the deployed contract has a scratch collision - say so loudly,
  because that would be a security-relevant finding about the real artifact.
