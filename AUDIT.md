# Audit Report: PoseidonVerifier

This document outlines the findings and architectural observations from an audit of the Solidity Halo2 Verifier implementation (`PoseidonVerifier.sol`).

## 1. Missing `returndatasize` Check in Precompile Calls (High / Medium)

**Description:**
The verifier relies heavily on EIP-2537 precompiles (`0x0f` for Pairing, `0x0c` for G1MSM, `0x05` for ModExp). In `_pairingCheck()`, the `staticcall` is performed via inline assembly, but it does not check the `returndatasize`.

```solidity
        assembly {
            let ptr := add(pairs, 32)
            let sz  := mload(pairs)
            let ok0 := staticcall(gasCap, precompile, ptr, sz, 0, 32)
            ok := ok0
            result := mload(0)
        }
        if (!ok) return false;
        return uint256(result) == 1;
```

**Impact:**
If the contract is deployed on a chain where EIP-2537 is not activated (e.g., an L2 that does not support it, or an Ethereum fork pre-Prague), the precompile address is just an "empty account". A `staticcall` to an empty account returns `success = true` (i.e., `ok = true`) but returns `0` bytes of data.
Because the `returndatasize` is not checked, `result := mload(0)` will simply read whatever data was already present in the EVM scratch space at memory offset `0x00`. If an attacker can somehow control the scratch space to hold the value `1` prior to this call, the verifier will incorrectly assume the pairing check passed, leading to a critical proof forgery vulnerability.

**Recommendation:**
Explicitly check the return data size using the `returndatasize()` opcode:
```solidity
        assembly {
            // ...
            let ok0 := staticcall(gasCap, precompile, ptr, sz, 0, 32)
            if iszero(eq(returndatasize(), 32)) {
                ok0 := 0
            }
            ok := ok0
            // ...
        }
```

## 2. Unreachable Dead Code in `verify()` (Medium)

**Description:**
At the end of the main `verify()` function, inside the Phase D8 block, there is an unconditional `return true;` statement after the pairing check:
```solidity
                bool pOk = _pairingCheck(pairs);
                // ...
                if (!pOk) return false;
                return true;
            }
        }

        // --- Final pairing check ---
        gStart = gasleft();
        bool ok = _finalPairing(vkBlob, vk, pi, fCom);
        // ...
        return ok;
```

**Impact:**
The `_finalPairing()` call and the surrounding code are completely unreachable. Additionally, examining `_finalPairing()`, it appears to perform a dummy/structural pairing check (`e(pi, sG2) == e(pi, G2)`) which would trivially fail for any valid non-trivial proof because `s != 1`. This indicates leftover scaffolding or debugging code that was abandoned.

**Recommendation:**
Remove the dead code block and the `_finalPairing()` function entirely to save deployment cost and improve code clarity.

## 3. Acceptance of Unreduced Scalars (Low / Informational)

**Description:**
The Solidity verifier reads public inputs and transcript challenges directly as 32-byte words (e.g., `_readScalarLE32`) without checking if the value is strictly less than the scalar field modulus (`FR_MODULUS`).

```solidity
        assembly { le := mload(add(add(mload(r), 32), p)) }
```

In contrast, the Rust verifier (`midnight_curves::Fq::read`) uses `from_repr()`, which strictly rejects any 32-byte sequence that is `>= FR_MODULUS`.

**Impact:**
If an attacker modifies a valid proof by adding `FR_MODULUS` to one of the scalar evaluations, the Rust verifier will reject it, but the Solidity verifier will successfully parse it. 
However, this does **not** lead to a proof forgery because the unreduced bytes are absorbed exactly as-is into the Fiat-Shamir Keccak256 transcript. This causes the subsequent transcript challenges (like `x4`) to diverge. Because the attacker cannot compute a valid KZG opening proof (`pi`) for the new pseudo-random challenges without the witness polynomials, the final pairing check will fail.
Thus, while it prevents forgery, it is a behavioral divergence between the Rust and Solidity implementations.

**Recommendation:**
Consider adding an explicit `< FR_MODULUS` check when reading scalars in `_readScalarLE32` to strictly align with the Rust verifier's strict parsing rules and prevent potential consensus-split issues if used in cross-chain scenarios.

## 4. Gas Griefing via EIP-2537 Precompile Gas Consumption (Informational)

**Description:**
In `_pairingCheck`, the verifier passes a hardcoded `gasCap = 2_000_000` to the pairing precompile. Per EIP-2537, if the precompile is provided with invalid inputs (e.g., points not in the correct subgroup, off-curve points), it penalizes the caller by consuming **all** forwarded gas.

**Impact:**
An attacker submitting a proof with maliciously crafted off-curve points will cause the `staticcall` to consume the entire 2 million gas cap. If the outer transaction did not provide enough gas to cover this plus the baseline execution costs, the entire transaction will revert with an out-of-gas error instead of gracefully returning `false` from the verifier.

**Recommendation:**
Ensure that off-chain infrastructure supplying proofs is aware of this behavior, or perform an on-chain subgroup/curve check before calling the precompile (though this is typically too gas-expensive to do manually).

---

# Evaluation — Solidity PLONK verifier

Scope reviewed: `proofs/solidity-verifier/contracts/PoseidonVerifier.sol` (4,407 LOC) + `PoseidonVerifyingKey.sol`, against `proofs/src/plonk/verifier.rs` (+ `linearization/verifier.rs`, `poly/kzg/mod.rs`) and the associated docs (`ARCHITECTURE.md`, `OPTIMISATIONS.md`, `TODO.md`, `AUDIT.md`).

---

## 1. Soundness

### Strengths
- **Faithful algebraic port.** Every phase in Rust `prepare` → `parse_trace` → `verify_algebraic_constraints` → `multi_prepare` has a bracketed counterpart in `verify()` (Phases 0–E). Transcript ordering, challenge squeezing (θ, β, γ, trash, y, x, x1, x2, x3, x4) and point/scalar reads match one-for-one.
- **The load-bearing soundness checks are genuine.** `test_verify_poseidon_proof` runs the real prover against the Solidity `verify()` and requires `true`; `tests/forge.rs::rust_and_solidity_traces_match` diffs the Fiat–Shamir trace byte-for-byte with the real `CircuitTranscript<Keccak256>`. These are not replica-vs-replica comparisons — the Rust side is the actual `midnight-proofs`.
- **Rejection coverage is broad.** 25 forge tests + 8 PBT (bit-flips in proof, VK blob mutation, source-level VK mutation, instance delta, malformed calldata, adversarial matrix).
- **Subgroup safety.** G1 decompression checks curve membership; subgroup check is deferred to EIP-2537 `PAIRING`, which is spec-compliant.

### Soundness concerns (in priority order)

1. **`_pairingCheck` omits `returndatasize` check** (AUDIT.md §1 — rated High/Medium by the audit, correctly). On a chain without EIP-2537 activated (pre-Prague fork or an L2), `staticcall` to an empty account returns `ok = true` with 0 bytes of return data, and `mload(0)` reads leftover scratch. If an attacker can prime scratch to `0x…01` before this call, `verify()` returns `true` unconditionally — full forgery. On a correctly-configured mainnet/Prague this is latent, but "latent" is not the acceptable bar for a verifier. **Must fix before mainnet.**

2. **Unreduced-scalar parsing divergence** (AUDIT.md §3). `_readScalarLE32` accepts any 32-byte word; Rust `Fq::read` rejects `≥ FR_MODULUS`. The author correctly argues this does not enable forgery (the bytes are absorbed as-is into keccak, challenges diverge, KZG fails) — but it is a **real behavioral divergence** and could enable a consensus split between bridged systems. Low risk, should be aligned.

3. **Dead `_finalPairing` path** (AUDIT.md §2) after the Phase D8 `return true`. `_finalPairing` does `e(π, s·G2) == e(π, G2)` — a trivially-wrong check. It is unreachable today, but any future refactor that accidentally falls through into it would silently reject every valid proof (livness bug, not soundness) or — worse if it were reordered — accept wrong proofs. Delete it.

4. **Pairing gas cap burns all gas on invalid inputs.** EIP-2537 consumes all forwarded gas on malformed points; the 2M cap prevents DoS of the outer tx but makes malicious-input liveness a cliff. Soundness is preserved (cap-exceeded ⇒ `false`). Informational.

5. **Residual "check-without-trace-event" gap** (TODO.md §4). If the Rust verifier has a structural `assert!`/`debug_assert!` that doesn't touch the transcript and doesn't feed the pairing MSM, neither the trace-diff nor the end-to-end pairing test would notice a missing Solidity equivalent. Defense-in-depth only; probability low but not zero. The proposed `testing-api` visibility widening (TODO.md §3 Option 3) is the right long-term fix.

---

## 2. Equivalence with `proofs/src/plonk/verifier.rs`

### What matches (verified)
- Transcript construction (`CircuitTranscript<Keccak256>`) byte-for-byte via `rust_and_solidity_traces_match`.
- All 11 phases of `verify_algebraic_constraints` have line-referenced counterparts; the architecture document explicitly quotes Rust line numbers next to each Solidity helper.
- Query iterator order in `_buildQueryList` mirrors the `iter::empty().chain(...)` chain in Rust `verifier.rs:305-365`.
- Committed-instance branching (`column.index() < nb_committed_instances`) is replicated in `_buildPartialEvalEnv` (see ARCHITECTURE.md §4).
- Keccak absorb sequence for VK hash, committed-instance commitments, instance length (`u128 → Fq LE`), and instance values matches Rust `parse_trace` lines 60–77.

### What does not match — documented specialisations (ARCHITECTURE.md §7)
These are **not** equivalence bugs; they are deliberate narrowings of the Rust verifier's generic surface to the specific poseidon configuration. But they mean the answer to "is this equivalent to `proofs/src/plonk/verifier.rs`" is **"equivalent only on the poseidon configuration of `zk_stdlib::verify`"**:

| Rust generic | Solidity assumption | Location |
|---|---|---|
| arbitrary `num_lookups` | `require(numLookups == 1)` | line 2071 |
| `Σ instance_i · L_i(x)` | `instance · l_0` collapse | `_buildPartialEvalEnv` |
| arbitrary committed-instance commitment | hard-coded `G1::identity()` | verify() line ~3460 |
| `num_challenges` arbitrary | treated as 0 | `_buildPartialEvalEnv` |
| `fixed_queries[i]` by `(col, rot)` | indexed by `i` | `_buildFixedEvalsFull` |
| `num_proofs` batched | 1 proof only | public ABI |

### What does not match — feature-flag scope (ARCHITECTURE.md §7.3)
Only `keccak-transcript` is fully supported. `committed-instances` is partial (no ABI surface), and `truncated-challenges` / `single-h-commitment` / `fewer-point-sets` would break byte-level equivalence. For a prover built with any of those, the Solidity verifier reads off the end of the transcript or misaligns squeeze widths.

### Equivalence risk: Category B replicas (TODO.md §1)
Six fixtures (`perm_expressions`, `lookup_expressions`, `trashcan_expressions`, `partial_eval`, `linearization`, `feval_fold`) are **re-implementations** of `pub(in crate::plonk)` functions because they are not reachable via the public API. Drift between the replica and real algorithm wouldn't show up in the component-level tests. Two end-to-end tests (pairing identity + trace-diff) would still catch it — but only a divergence that affects the final pairing MSM or the transcript byte stream. The author acknowledges this and proposes a `testing-api` visibility feature upstream as the clean fix. This is the most important open structural risk for soundness confidence.

---

## 3. Production-readiness

**Verdict: not production-ready as-is.** The blockers are small in LOC but real.

### Hard blockers
1. **`returndatasize`-check fix in `_pairingCheck`** (AUDIT.md §1). ~5 lines of assembly.
2. **Delete dead `_finalPairing` + unreachable `verify()` tail** (AUDIT.md §2). Removes an accident-prone booby trap.
3. **Strip instrumentation for release** (OPTIMISATIONS.md §3 row 1). `Trace*`, `PhaseGas`, `TraceIntermediate` events are development affordances that leak intermediate state (informationally harmless for a soundness argument but undesirable on mainnet, plus ~1M gas overhead). Needs a build-time flag that the test harness can still enable.

### Soft blockers (should-fix)
4. **Align scalar parsing with `Fq::read`** (AUDIT.md §3). Add explicit `< FR_MODULUS` guards in `_readScalarLE32` and the q_eval loop.
5. **Contract size ≈ 47 KB > EIP-170's 24 KB.** Works in forge/revm with `limit_contract_code_size` raised to 1 MB, but mainnet deployment today requires either EIP-7907 (not live), splitting the verifier across libraries/delegatecall, or collapsing the RPN interpreter via template codegen (OPTIMISATIONS.md §3 row 4 — also fixes the size problem).
6. **Close replica-drift risk** (TODO.md §5 action items). Land a `testing-api` feature on `midnight-proofs` so the six Category B replicas collapse into direct calls.

### Non-blockers / roadmap items
7. **Gas is 40× halo2-solidity-verifier** (~11.25 M). Fully explained by OPTIMISATIONS.md §2. Acceptable for an L2/rollup setting; for L1 mainnet a template-generated + Yul-assembly + BN254 port is the obvious endgame (OPTIMISATIONS.md §3 table).
8. **Single-circuit scope.** `PoseidonVerifier.sol` is hand-maintained; `codegen.rs` has `render_verifying_key` but no `render_verifier`. Generalising beyond poseidon is the §9 roadmap and requires lifting the six specialisations in §7.2.
9. **Operational hardening.** The ABI is `verify(bytes32 instance, bytes proof)`; a production integration would want a structured error surface (currently `bool` only), explicit domain separation for the instance, and perhaps a view-function equivalent for off-chain pre-flight.

---

## Summary

| Axis | Verdict | Summary |
|---|---|---|
| Soundness (on-path) | Strong | Real-prover E2E + byte-for-byte trace-diff + adversarial matrix + PBT all pass |
| Soundness (off-path) | Has gaps | Missing `returndatasize` check (High) + dead `_finalPairing` + unreduced scalars |
| Equivalence (poseidon) | Faithful | Phases, transcript, query order, committed-instance split all match |
| Equivalence (generic) | Not a 1:1 port | 6 poseidon specialisations + 4 unsupported feature flags (ARCHITECTURE.md §7.2/§7.3) |
| Replica drift risk | Residual | 6 `pub(in crate::plonk)` functions re-implemented; `testing-api` upstream fix proposed |
| Production-ready | Not yet | Fix pairing `returndatasize`, strip events, address EIP-170 size, delete dead code |
| Gas | 11.25 M | Explainable, not fundamental; −10 M reachable with codegen + Yul + BN254 |

**Bottom line:** The design is architecturally sound and the equivalence story against the poseidon configuration of the Rust verifier is well-evidenced (end-to-end real-prover test + byte-for-byte trace diff is genuinely strong). The crate is **not production-ready** primarily because of the missing `returndatasize` check in `_pairingCheck` (latent forgery on non-Prague deployments), the unreachable-but-toxic `_finalPairing` tail, dev-instrumentation events leaking onto the hot path, and the 47 KB contract size exceeding EIP-170. None of these are architectural problems — all are local fixes. The larger, non-blocking story is that "equivalent to `proofs/src/plonk/verifier.rs`" should be read as "equivalent on the poseidon specialisation of the public `zk_stdlib::verify` surface"; a strict generic port requires the §7.2/§7.3/§9 workstreams.
