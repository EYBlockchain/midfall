# P-BR - Midfall.Yul.Bridge.Run (D-P10), independent of the port chain

Status: READY any time - depends only on the vendored dialect and
`Midfall/Yul/Externals.lean`, both already landed. It is **not** downstream of P-06..P-14,
so it can be fired in any gap in the port queue. It is a hard prerequisite for
`finalPairing_spec` and therefore for every semantic-equivalence result.

## What is actually there, measured

Checked against `formal/vendor/yul-semantics` rather than assumed:

| item | where | generic? |
|---|---|---|
| `BigStep.Run (D : Dialect) [DecidableEq D.Value] (prog : Block D.Op) (st0 : D.State) ...` | `BigStep.lean:366` | **yes** - fully dialect-parameterised |
| determinism of whole-program runs, given `∀ op, D.Deterministic op` | `Determinism.lean:410` | yes |
| `EVM.evm_deterministic (op : EVM.Op) : EVM.evm.Deterministic op` | `Determinism.lean:419` | the closed dialect only |
| `evmWithExternal (calls : ExternalCalls) (creates : ExternalCreates) (gasOracle)` | `Dialect/EVM.lean:135-164` (used by `effects_sound_withExternal`) | exists |
| `EVM.ExternalCalls` | a **structure**, not a predicate (finding Y-1, recorded in `Midfall/Yul/Externals.lean:16-21`) | - |
| `RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm) (stObs) (o)` | `Observation.lean:39-41` | **NO - hard-wired to `EVM.Op` and to `VEnv EVM.evm`** |
| `RunCommitted.det` | `Observation.lean:45-51` | proved via `EVM.run_det`, i.e. the closed dialect |
| `RunObject (o : Object EVM.Op) (L : Layout)` | `ObjectRun.lean:68` | also EVM.Op-specific |

**So Y-3 is real and precisely located.** `Run` is generic; the *committed* layer is not.
`RunCommitted` exists only for the closed `EVM.evm` dialect, and PLAN 9.5's
`RunVerifier` / `RunContractIR` need a committed run over
`evmWithExternal (calls L W) noCreates` with a configurable keccak oracle. That is why
D-P10 chose to define our own rather than wait on upstream.

## Deliverable

`formal/Midfall/Yul/Bridge.lean` providing:

1. `Bridge.Run` - `Run (evmWithExternal calls creates gasOracle) prog st0 V st' o`, or
   the closest honest wrapper; state in the header exactly what it adds over `Run` and
   do not invent a second semantics.
2. `Bridge.RunCommitted` - the same shape as `Observation.lean:39` but at the external
   dialect: `∃ st', Bridge.Run calls ... ∧ stObs = EVM.committedState st0 st'`. Confirm
   `committedState` is state-typed (not op-typed); if it is op-typed, that is a finding
   and the wrapper needs its own commit map.
3. **The determinism condition D-P10 demands.** Not "assume determinism": name the
   hypothesis on `calls` that actually gives it - functionality (at most one response per
   request) plus whatever the gas oracle needs - and prove
   `Bridge.RunCommitted.det` from it. D-P10's own words: an external-call relation is
   *not* automatically deterministic, so the layer needs explicit conditions that preserve
   determinism. If the vendored `Determinism.lean:410` theorem can be applied directly
   once `calls` is functional, say so and cite it; if it cannot, the obstruction is the
   finding.
4. The keccak-oracle hook: PLAN 9.5 wants `(keccak := H)` for arbitrary `H`. Check
   whether the vendored dialect fixes keccak or takes it as a parameter. If it is fixed,
   the hash-agnostic claim in PLAN 10.3 ("all lowering proofs are hash-agnostic") is
   **not achievable at this layer** and that must be reported, not worked around.

## Acceptance

- `lake build` and `scripts/checks.sh` green; no sorry; nothing outside `Midfall/Yul/`.
- A `#print axioms` check on `Bridge.RunCommitted.det` reported in the output.
- At least one gate showing the determinism hypothesis is *used*: construct a
  non-functional `calls` (two responses to one request) and show the determinism
  conclusion fails for it. A lemma whose hypothesis is decorative is the R-30/R-32
  pattern, and `dualMsm_scale_check`'s `hc` in `Spec/Lemmas.lean` is the in-repo example
  of doing this right - it ships a counterexample showing the hypothesis is necessary.
- Report, as a finding, whether `finalPairing_spec` can be stated against this layer
  with no further upstream gaps. That is the question the whole package exists to answer.
