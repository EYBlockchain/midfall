# Halo2Verifier Static Audit Notes

I reviewed the pasted `Halo2Verifier` and `Halo2VerifyingKey` as a static, best-effort audit of the on-chain verifier surface. I did **not** run the verifier against the Rust generator, a live EIP-2537 implementation, or sample valid/invalid proofs, so the main remaining risk is generator/native-verifier equivalence. That said, I did not see an obvious "accept invalid proof" bug in the pasted verifier logic. The largest risks are deployment/precompile assumptions, production trace instrumentation, and integration misuse.

Prior verifier/precompile audits consistently focus on exactly these areas: verifier correctness, misuse, smart-contract vulnerabilities, privacy/integrity, and precompile semantics. For example, the Worldcoin Groth16 verifier audit lists correctness, misuse/gaming, smart-contract vulnerabilities, malicious attacks, data privacy, and information integrity as audit concerns, and prior precompile audits have found issues such as pairing return-length mismatches and missing subgroup checks.

## Executive summary

**No critical verifier-bypass issue found from static review.**

The code has several strong properties: exact ABI shape checks, exact proof and instance lengths, canonical Fr checks for instances/evaluations, canonical Fp coordinate checks for proof G1 points, codehash pinning of the VK runtime, rechecking the VK codehash on every proof, and return-length checks after precompile calls.

The main findings are:

| ID | Severity | Finding |
| --- | ---: | --- |
| M-01 | Medium | Production verifier contains active `gas_checkpoint` `LOG1` instrumentation |
| M-02 | Medium | Deployment smoke test does not prove MCOPY support or full EIP-2537 semantic compatibility |
| M-03 | Medium / High on custom chains | Proof-point validation relies on generated "all absorbed points are later consumed by precompiles" invariant |
| M-04 | Medium | Resolved: generated EIP-2537 calls forward `gas()` and constructor smoke covers full-size precompile shapes |
| H-INT | High integration risk | Raw verifier does not bind proof meaning to an application, chain, contract, user, nullifier, or program domain |
| L-01 | Low | Resolved: non-canonical public instances now revert immediately after the instance loop |
| L-02 | Low | Resolved: loaded VK header values are cross-checked against verifier constants |
| L-03 | Low | Resolved: quotient VM asserts exact bytecode termination and empty final stack |
| I-01 | Informational | VK codehash/length should be continuously tested from deployed bytecode |
| I-02 | Informational | Accumulator encoding logic needs extensive negative tests |
| I-03 | Informational | Terminal absolute-memory Yul strategy is acceptable but brittle |

## Findings

### M-01: Production verifier contains active `gas_checkpoint` instrumentation

The verifier defines:

```solidity
function gas_checkpoint(id) {
    log1(0, 0, or(shl(248, id), gas()))
}
```

and calls it throughout `verifyProof`.

This means every successful proof emits many anonymous logs. More importantly, the verifier cannot be safely called through `STATICCALL`, because EVM logs are state-changing side effects in a static context. Many verifier integrations expect proof verifiers to be `view`-like and call them with `staticcall` for safety. This contract documents that it is success-or-revert and uses terminal assembly, but active trace logging still makes it behave differently from a conventional verifier.

**Impact:** Integrations that use `staticcall` will fail even for valid proofs. Valid proofs also pay extra gas and emit unexpected logs.

**Recommendation:** Remove `gas_checkpoint` from production builds. Keep it only behind a separate trace/gas build artifact. Once removed, make `verifyProof` `external view returns (bool)` if the target precompile calls are all `staticcall`.

### M-02: Deployment smoke test does not prove MCOPY support or full EIP-2537 semantic compatibility

The constructor smoke-tests EIP-2537 with identity inputs for `G1ADD`, `G1MSM`, and `PAIRING_CHECK`. That is useful, but incomplete.

The runtime verifier later uses `mcopy`, which requires Cancun-compatible execution. The constructor does not execute an `mcopy` probe, so the verifier can be deployed on a chain/fork where construction succeeds but `verifyProof` later hits an invalid opcode.

The identity-only EIP-2537 smoke test also does not prove that the target chain correctly validates non-identity points, subgroup membership, scalar handling, or nontrivial pairings. This matters because previous precompile audits have found high-severity subgroup-check and return-shape issues in precompile implementations.

**Impact:** On an incompatible chain, the verifier may be permanently unusable after deployment. On a nonconforming EIP-2537 implementation, proof soundness assumptions may not hold.

**Recommendation:** Add deployment or deployment-script checks for:

```solidity
// Constructor-level MCOPY probe idea:
mstore(0x80, 0x1234)
mcopy(0xa0, 0x80, 0x20)
if iszero(eq(mload(0xa0), 0x1234)) { revert(0, 0) }
```

Also test non-identity EIP-2537 behavior in CI/deployment scripts: known valid generator operations, known off-curve points, known out-of-field coordinates, invalid subgroup points when applicable, and pairing positive/negative vectors.

### M-03: Proof-point validation relies on generated consumption invariants

`common_uncompressed_g1` checks only that the padded BLS12-381 coordinates are canonical Fp elements. It intentionally does **not** check curve or subgroup membership:

```solidity
// This helper does not run an independent curve/subgroup check.
// Instead, ProtocolPlan::validate rejects generated plans where an
// absorbed proof commitment would not later be consumed by an EIP-2537
// G1MSM or pairing path...
```

This is a reasonable optimization if all of the following stay true:

1. Every absorbed proof G1 point is later consumed by an EIP-2537 operation.
2. The relevant EIP-2537 implementation validates curve and subgroup membership for every point.
3. The implementation does not skip validation for zero-scalar MSM pairs.
4. Future codegen changes cannot introduce an absorbed-but-unused point.

From a static pass, the current pasted plan appears to route proof G1 material into final MSM/pairing paths. But this is a **generator invariant**, not a runtime assertion.

**Impact:** If a future generator emits an absorbed point that is not consumed, or if the target precompile implementation skips validation in some cases, invalid curve/subgroup points can enter the Fiat-Shamir transcript and undermine assumptions. Severity is Medium on canonical audited EIP-2537 implementations, but High on custom or immature chains.

**Recommendation:** Add a generated manifest and CI assertion: every `common_uncompressed_g1` call site must map to a later validation/consumption site. For extra hardening, consider an explicit validation MSM with scalar `1` for any proof G1 whose later scalar may be zero. At minimum, add target-chain conformance tests for "zero scalar with invalid point" behavior.

### M-04: Hard-coded precompile gas caps are brittle

Status: Fixed in the generator. EIP-2537 calls now forward `gas()` instead of
rendering EIP-2537 gas-schedule literals, and the constructor smoke test
exercises the largest generated G1MSM input and the runtime two-pair pairing
shape with identity data.

Previously, the verifier used fixed gas caps such as:

```solidity
staticcall(575096, 0x0c, 0xa300, 0x30c0, FINAL_COM_MPTR, 0x80)
staticcall(170000, 0x0f, scratch, 0x0300, scratch, 0x20)
staticcall(62000, 0x0c, ..., 0xa0, ..., 0x80)
staticcall(50000, 0x0b, ..., 0x0100, ..., 0x80)
```

Those caps were tuned for a specific EIP-2537 gas schedule. If such verifier
bytecode is deployed to a chain with a different gas schedule, modified
precompile pricing, or less favorable implementation, valid proofs can revert.

**Impact:** Availability failure for valid proofs on target chains/forks with different precompile gas costs.

**Recommendation:** Prefer forwarding `gas()` where safe, or leave a larger safety margin and enforce target-chain gas compatibility through deployment tests. The deployment smoke test should include worst-case-sized calls, not only one-pair identity calls.

### H-INT: Raw verifier does not bind proof meaning to an application domain

The verifier proves only:

> "This proof verifies for this VK and these public instances."

It does not enforce application meaning: expected state root, chain ID, contract address, user address, nullifier, epoch, program ID, asset ID, or any protocol authorization. The NatSpec correctly warns about this.

**Impact:** If an application contract treats `verifyProof(proof, instances) == true` as authorization without independently checking the public inputs, proofs can be replayed or reused across contexts.

**Recommendation:** Never expose this raw verifier as the application authorization layer. Wrap it with an application verifier that checks all public inputs before acting. At minimum, bind:

```text
domain_separator = hash(chainid, verifying_contract, protocol_version, vk_digest)
program_id / circuit_id
state root or commitment root
nullifier or unique action ID
recipient / caller / beneficiary when relevant
asset and amount constraints
expiry / epoch / fork identifier when relevant
```

This is a common audit focus for ZK systems: whether the Fiat-Shamir transcript and public statement include all required prover messages and statement data is explicitly called out in prior halo2/zkEVM audit goals.

### L-01: Invalid public instance range-check failures are deferred

Status: Fixed in the generator. The verifier now reverts immediately after the
public-instance absorption loop if any instance word is not canonical.

During transcript absorption, instance values are checked with:

```solidity
success := and(success, lt(inst_be, r))
buf_len := common_word(buf_len, inst_be)
```

but `success` is not enforced until after the rest of the transcript parsing. Invalid public inputs therefore still cause the verifier to read/hash later proof material before reverting.

**Impact:** Gas inefficiency and minor griefing if a wrapper pays for verification.

**Recommendation:** Revert immediately after the instance loop if any public input is non-canonical:

```solidity
if iszero(success) { revert(0, 0) }
```

This does not change accepted proofs.

### L-02: VK header values are not cross-checked against verifier constants

**Status:** Resolved. After the VK payload is embedded or copied with
`extcodecopy`, the verifier now cross-checks the generated header words for
instance count, domain `k`, and accumulator layout against the verifier's
compiled-in constants before calldata parsing continues.

The VK payload contains header values:

```text
num_instances = 19
k = 20
has_accumulator = 1
acc_offset = 11
num_acc_limbs = 7
num_acc_limb_bits = 56
```

The verifier also hardcodes these values in multiple places. Since the VK runtime is codehash-pinned, this is not attacker-controlled. But it is a generator-safety issue: if the emitted verifier constants and VK header ever diverge, failures may be confusing or, in worse cases, semantically wrong.

**Impact:** Low direct exploitability, but high debugging cost and generator safety risk.

**Recommendation:** After `extcodecopy`, assert the important header fields:

```solidity
if iszero(eq(mload(NUM_INSTANCES_MPTR), 19)) { revert(0, 0) }
if iszero(eq(mload(K_MPTR), 20)) { revert(0, 0) }
if iszero(eq(mload(HAS_ACCUMULATOR_MPTR), 1)) { revert(0, 0) }
if iszero(eq(mload(ACC_OFFSET_MPTR), 11)) { revert(0, 0) }
if iszero(eq(mload(NUM_ACC_LIMBS_MPTR), 7)) { revert(0, 0) }
if iszero(eq(mload(NUM_ACC_LIMB_BITS_MPTR), 56)) { revert(0, 0) }
```

### L-03: Quotient VM does not assert exact program termination

**Status:** Resolved. The compact quotient VM now reverts unless `q_pc == q_end`
after interpretation and `q_has_top == 0`, and generator tests assert the
planned stack/scratch region covers the validated VM operand-stack bound.

The quotient interpreter stops on:

```solidity
for { } lt(q_pc, q_end) { } { ... }
```

but does not assert `q_pc == q_end` afterward. Since the quotient program is pinned in the VK runtime, proof calldata cannot directly alter it. Still, exact termination is a cheap safety invariant and catches malformed generator output.

**Impact:** Low; generator or VK payload integrity issue, not a user-controlled issue.

**Recommendation:** Add:

```solidity
if iszero(eq(q_pc, q_end)) { revert(0, 0) }
if q_has_top { revert(0, 0) } // if the manifest expects empty stack
```

Also assert stack bounds in generator tests.

## Positive observations

The verifier has several good defensive choices:

* Exact ABI shape check for dynamic `bytes proof` and `uint256[] instances`.
* Exact proof length, instance length, and calldata size checks.
* Canonical Fr checks for instances, proof evaluations, and `q_evals`.
* Canonical padded Fp coordinate checks for proof G1 points.
* Non-zero top 16-byte rejection for BLS12-381 coordinate words, preventing transcript aliases.
* VK runtime length and codehash pinning at construction and rechecking before every proof.
* VK runtime uses an `INVALID || payload` layout, preventing accidental execution of payload bytes.
* Precompile return-size checks are present.
* `scalar_inv` rejects zero before calling `modexp`.
* Public accumulator identity encoding is treated canonically and non-canonical zero-like encodings appear rejected.
* The proof parser verifies it consumed exactly the generated proof bytes.

## Recommended test plan before production

1. **Differential tests against the native Rust verifier**

   * Valid proofs accepted by both.
   * Mutate every proof field and public input; both must reject.
   * Test transcript challenge equality against native verifier at each squeeze.

2. **ABI parser tests**

   * Wrong proof head.
   * Wrong instance head.
   * Short calldata.
   * Trailing calldata.
   * Correct proof bytes but wrong ABI offsets.
   * `proof.length = 0x1e60 +/- 1`.
   * `instances.length = 18`, `20`, and large values.

3. **Canonicality tests**

   * Instance equal to `FR_MODULUS`.
   * Evaluation equal to `FR_MODULUS`.
   * G1 coordinate with nonzero top padding.
   * G1 coordinate equal to `p`.
   * G1 off-curve point.
   * G1 wrong-subgroup point, if applicable to the target test harness.
   * Identity point for every G1 proof slot.

4. **Accumulator tests**

   * Canonical identity accepted only in the exact encoded form.
   * Non-canonical identity-like encodings rejected.
   * Unused high bits in packed limbs rejected.
   * Coordinates decoding to `(0,0)` rejected unless exact accumulator identity encoding.
   * `acc_offset` boundary tests.

5. **VK deployment tests**

   * Deployed VK runtime length is exactly `0x4281`.
   * Runtime byte `0` is `0xfe`.
   * Runtime codehash equals `EXPECTED_VK_CODEHASH`.
   * Payload header words equal verifier constants.
   * `extcodecopy(vk, VK_MPTR, 1, 17024)` reproduces the expected payload.

6. **EIP-2537 conformance tests on the target chain**

   * Non-identity `G1ADD`.
   * Non-identity `G1MSM`.
   * Pairing positive and negative vectors.
   * Invalid coordinate rejection.
   * Off-curve rejection.
   * Subgroup rejection.
   * Zero-scalar MSM invalid-point behavior.
   * Worst-case 78-term MSM gas.

7. **Production-build check**

   * No `gas_checkpoint` calls.
   * `verifyProof` callable through `staticcall`, if the integration expects it.
   * No trace logs emitted on valid proofs.

## Bottom line

The verifier is carefully generated and has many good checks. I would not ship it unchanged mainly because the active gas logging can break integrations, and the deployment/precompile assumptions are too important to leave to comments and identity-only smoke tests. Remove trace logging, add stronger target-chain precompile conformance tests, assert codegen invariants around absorbed G1 validation, and wrap the raw verifier with strict public-input/domain checks.

# Additional Static Review Notes

I did a static review of the pasted verifier/VK pair. I did **not** run the generator, compile the full source, or compare against native `midnight-proofs` test vectors, so the highest-risk remaining area is still "does this generated transcript/PCS/quotient schedule exactly match Rust?" That said, I do not see an obvious "accepts arbitrary invalid proof" bug in the pasted code. The main issues are around **assumptions that must be locked down**, **deployment/integration footguns**, and **test coverage needed for a generated verifier**.

## Summary

| ID | Severity | Area | Finding |
| -- | --: | --- | --- |
| 1 | Medium | Point validation / transcript | Proof G1 points are absorbed before curve/subgroup validation; safety depends on every absorbed point later being validated by EIP-2537 on the target chain. |
| 2 | Medium | Deployment | Constructor smoke-tests EIP-2537 but not `MCOPY`; deployed verifier can pass constructor and later be unusable on a non-Cancun fork/chain. |
| 3 | Low/Medium | Integration | Gas-logging render emits logs and is non-`view`; this can break verifier adapters that use `staticcall` or expect a pure/view verifier. |
| 4 | Low | Gas griefing | Resolved: non-canonical public instances revert immediately after the instance loop. |
| 5 | Low | Generated VM / VK coupling | Quotient VM safety relies on generated bytecode correctness; no runtime bounds checks protect malformed pinned bytecode. |
| 6 | Informational | Error handling | Most failures use `revert(0,0)`, making integration and production incident triage unnecessarily hard. |
| 7 | Informational | VK contract | VK runtime design is good, but should be CI-checked byte-for-byte against the verifier constants and generator manifest. |
| 8 | Informational | App-level binding | Raw verifier does not bind program semantics, chain, state roots, or authorization; integration must do this explicitly. |

The code already addresses several common verifier classes well: strict ABI shape, exact proof/instance length, canonical scalar checks, Fp range checks for uncompressed G1 encodings, VK codehash pinning at construction and per proof, `INVALID || payload` VK runtime, final success-or-revert behavior, and public accumulator canonical decoding plus G1MSM validation.

## 1. Absorbed proof G1 points are validated late and indirectly

**Severity: Medium**
**Location:** `common_uncompressed_g1`, all proof commitment reads

`common_uncompressed_g1` checks that each G1 encoding is canonical as two Fp coordinates, then immediately absorbs the 128-byte encoding into the transcript. It does **not** check that the point is on-curve or in the correct subgroup at that point. The comments say this is safe because every absorbed point is later consumed by G1MSM or pairing, whose precompiles validate curve/subgroup membership.

That assumption is central. Prior verifier audits call out exactly these two pitfall classes: proof points must be checked on the right curves, and public inputs must not have ambiguous encodings. zkSecurity's Risc0 verifier audit explicitly lists those as the "primary pitfalls" for proof verifiers.

For a canonical EIP-2537 implementation that validates every G1 input before MSM/pairing, this is likely fine. The risk is target-chain divergence or an optimized precompile implementation that skips validation for zero-scalar terms. Some of this verifier's MSM coefficients are Fiat-Shamir-derived and truncated; they should be nonzero except with negligible probability, but this is still an assumption worth testing directly.

**Impact:** If an absorbed, invalid point can avoid later precompile validation, it can influence transcript challenges without being bound to a valid group element. That is a classic Fiat-Shamir verifier soundness hazard.

**Recommendation:** Add negative tests on the exact deployment target/fork:

```text
- malformed affine coordinate, scalar 1 in G1MSM: must revert/fail
- malformed affine coordinate, scalar 0 in G1MSM: must revert/fail
- malformed F_COM, PI, advice, lookup, permutation, quotient commitment: verifyProof must revert
- identity points in each proof position: accepted/rejected exactly as native verifier does
```

If the target precompile does not validate zero-scalar inputs, either validate all absorbed proof points immediately with scalar 1, or ensure the generator never emits a path where an absorbed point can have zero contribution before being validated elsewhere.

## 2. Constructor checks EIP-2537 but not `MCOPY`

**Severity: Medium**
**Location:** `require_eip2537_precompiles`, runtime use of `mcopy`

The constructor smoke-tests G1ADD, G1MSM, and pairing. That is good. But the verifier runtime also depends on Cancun `MCOPY` via Yul `mcopy`. The constructor does not execute `mcopy`, so a chain/fork that supports the BLS precompile addresses but not `MCOPY` can deploy the contract and later fail at verification time.

The NatSpec says deploy only on chains/forks that support MCOPY and EIP-2537, but the constructor currently only enforces the EIP-2537 half.

**Impact:** Deployment can succeed while every proof verification later reverts. This is a liveness/deployment safety issue, not a proof-soundness issue.

**Recommendation:** Add a constructor-time `MCOPY` smoke test:

```solidity
assembly ("memory-safe") {
    mstore(0x80, 0x1234)
    mcopy(0xa0, 0x80, 0x20)
    if iszero(eq(mload(0xa0), 0x1234)) { revert(0, 0) }
}
```

Also include deployment CI against the exact chain/fork config, not only a local EVM.

## 3. Gas-logging render breaks `view`/`staticcall` verifier expectations

**Severity: Low/Medium**
**Location:** `gas_checkpoint`, `verifyProof`

`verifyProof` emits many `LOG1` checkpoints. This makes the function non-`view` in practice and incompatible with `staticcall`. Many verifier adapters and application contracts assume proof verifiers are `view` or call them via `staticcall`.

**Impact:** Integration failure or unexpected reverts in consuming contracts. If this render accidentally reaches production, it also permanently emits gas-left telemetry logs on every successful verification.

**Recommendation:** Keep the gas render as a separate artifact. Production verifier should remove `gas_checkpoint` entirely and mark `verifyProof` as `external view returns (bool)` if all remaining operations are static. At minimum, make the production generator fail if gas logging is enabled.

## 4. Public instance canonicality failure is deferred too long

**Severity: Low**
**Location:** transcript instance absorption

Status: Fixed. The generated transcript parser now checks `success` and reverts
immediately after the instance loop, before reading later proof material.

The instance loop does:

```yul
success := and(success, lt(inst_be, r))
buf_len := common_word(buf_len, inst_be)
```

but does not revert until after all proof commitments, challenges, evaluations, q-evals, `f_com`, and `pi` are parsed. This is not a soundness bug because the verifier eventually reverts, but malformed public inputs can force the contract through a large amount of transcript work first.

The Risc0 audit's public-input finding is directly relevant: reducing or accepting multiple representations creates ambiguity; the recommendation was to assert that public inputs are already reduced, not reduce them. Your verifier correctly asserts `< r`; it just enforces the result late.

**Impact:** Caller-pays gas griefing. Usually low, but more relevant if a relayer, rollup inbox, or batch processor subsidizes verification attempts.

**Recommendation:** Revert immediately after the instance loop:

```yul
if iszero(success) { revert(0, 0) }
```

You can still keep the exact transcript behavior for valid inputs.

## 5. Quotient VM safety relies entirely on pinned generated bytecode

**Severity: Low**
**Location:** quotient VM loop, `q_pc`, `q_end`, stack operations

The compact quotient VM is pinned by the VK codehash, so proof calldata cannot alter control flow. That is a strong design choice. However, malformed generated bytecode would not be sandboxed robustly:

```yul
let q_op := byte(0, mload(q_pc))
q_pc := add(q_pc, 1)
...
case 0x06 {
    q_sp := sub(q_sp, 0x20)
    q_top := addmod(mload(q_sp), q_top, r)
}
```

The VM trusts the generator/manifest for stack safety, operand bounds, constant-table bounds, and exact `q_pc == q_end`. That is acceptable for generated code, but it should be treated as a formal generator invariant, not as an informal assumption.

Trail of Bits' Axiom Halo2 review highlights the importance of generated-verifier memory conventions and tests, including the prior finding that a Solidity loader did not respect Solidity's free memory pointer. They recommended starting allocation at `0x80` and asserting the free memory pointer assumptions; the fix review later notes this was resolved by starting at `0x80` and checking `mload(0x40) == 0x80`.

**Recommendation:** Add generator-level checks that prove or assert:

```text
- q_pc ends exactly at q_end
- no instruction operand reads beyond q_end
- every PUSH_MEM pointer is within an initialized Fr slot
- every constant index is within q_const table
- stack depth never underflows/overflows its reserved range
- native callback indexes are exactly the generated set
- selector power indexes are within the precomputed y-power table
```

For production defense in depth, add a post-loop runtime check:

```yul
if iszero(eq(q_pc, q_end)) { revert(0, 0) }
if q_has_top { revert(0, 0) } // if expression boundaries require empty stack
```

only if that matches the VM semantics.

## 6. Empty reverts make production failures hard to diagnose

**Severity: Informational**
**Location:** most `revert(0,0)` paths

Most failures revert with no selector or data. That is gas-efficient, but it makes it difficult to distinguish malformed ABI, bad VK, non-canonical scalar, invalid G1, precompile failure, quotient VM failure, and pairing failure.

Least Authority made a similar recommendation in the Worldcoin Groth16 verifier audit: optimized verifier code should use accurate custom errors instead of opaque reverts to improve usage and debugging.

**Recommendation:** For production, consider a debug build with custom errors and a release build with empty reverts. At minimum, keep off-chain test harnesses that map failing mutations to sections.

## 7. VK contract design is good, but needs byte-level CI guarantees

**Severity: Informational**
**Location:** `Halo2VerifyingKey`

The `INVALID || payload` runtime is a good pattern: direct calls cannot execute arbitrary payload bytes, and the verifier copies from byte 1. The length relationship is correct in the pasted constants:

```text
VK return length:      0x4281 = 17025
payload length:        0x4280 = 17024
verifier expected len: 17025
```

The risk is not the design; it is generator drift. If the verifier constants, VK constructor return length, codehash, q-program offsets, or fixed/permutation commitment offsets diverge, the system becomes undeployable or unsound-by-construction.

**Recommendation:** Add CI tests that deploy the VK and assert:

```text
- address(vk).code.length == EXPECTED_VK_LENGTH
- address(vk).codehash == EXPECTED_VK_CODEHASH
- extcodecopy byte 1..end equals the generator payload bytes exactly
- VK header words match verifier-rendered constants:
  num_instances = 19
  k = 20
  has_accumulator = 1
  acc_offset = 11
  num_acc_limbs = 7
  num_acc_limb_bits = 56
- q_program_mptr + q_program_len lands before fixed_comms
- all fixed/permutation/G2 VK points are accepted by target EIP-2537 precompiles
```

## 8. Raw verifier must not be treated as application authorization

**Severity: Informational / Integration-critical**
**Location:** `verifyProof` API

The contract correctly warns that application contracts must bind the meaning of instances separately. This is important enough to repeat: a raw proof verifier only says "this proof verifies under this VK for these public inputs." It does not enforce chain ID, state root freshness, nullifier uniqueness, program ID, account authorization, or bridge domain.

Silent Protocol's audit makes a related point: users benefit from being able to check that open-sourced circuits compile down to the verifier keys used on-chain, in addition to assurance about the circuit statement itself.

**Recommendation:** The consuming contract should enforce a typed public-input schema, for example:

```text
instances[0]  = protocol/domain separator
instances[1]  = chain id or fork/domain id
instances[2]  = application/verifier version
instances[3]  = expected state root / IVC output root
instances[4]  = nullifier / replay tag
...
```

and reject proofs whose public inputs do not match the current application state.

## Positive observations

The following parts look notably strong:

* Exact ABI head checks and exact calldata size checks.
* Exact proof length and instance count checks.
* Canonical `< r` checks for proof evaluations, q-evals, and public instances.
* Canonical Fp encoding checks for uncompressed G1 calldata: top padding bytes zero and coordinates `< p`.
* VK length and codehash pinned both in the constructor and on every proof.
* VK runtime starts with `INVALID`, and verifier copies from byte 1.
* Public accumulator decoding is stricter than accepting any zero-like encoding.
* Public accumulator points are routed through G1MSM with scalar 1 before use.
* Final success path is terminal and returns ABI `true`; failures revert.
* Memory starts at `0x80` and the main assembly block is terminal, which avoids the exact Solidity free-memory-pointer issue Trail of Bits previously found in an EVM verifier loader.

## Production readiness checklist

Before shipping, I would require these tests/proofs:

```text
1. Native equivalence
   - Same VK, same proof, same instances accepted by Rust and Solidity.
   - Mutate every proof byte/word: Rust rejects iff Solidity rejects.
   - Transcript challenge snapshots match Rust after every squeeze.

2. Encoding/canonicality
   - instance = r, r+1, 2^256-1 reverts.
   - eval/q_eval = r reverts.
   - G1 hi padding nonzero reverts.
   - G1 x or y = p reverts.
   - malformed-but-in-field non-curve points revert.

3. Accumulator public inputs
   - canonical identity accepted only in exact encoding.
   - non-canonical zero-like encodings rejected.
   - invalid affine point rejected.
   - wrong accumulator equation rejected.
   - randomized batching cannot be bypassed with two bad equations in fuzz tests.

4. Target precompile behavior
   - G1MSM validates invalid points even with scalar 0.
   - G1MSM validates invalid points with scalar 1.
   - pairing validates invalid G1/G2.
   - gas limits are sufficient on the deployment chain.

5. Generator invariants
   - all memory regions non-overlapping by generated manifest.
   - quotient VM stack safety and operand bounds.
   - q_program length and q_end exactness.
   - final MSM term count equals input length / 0xa0.
   - every absorbed proof G1 is consumed by a validating precompile path.

6. Deployment invariants
   - VK codehash/length matches constants.
   - MCOPY smoke test passes.
   - production build has gas logging disabled.
```

My highest-priority changes would be: **add MCOPY smoke test**, **remove gas checkpoints for production**, **fail public-input canonicality immediately**, and **add target-chain negative tests proving all absorbed G1 points are actually validated by EIP-2537 even in zero-scalar MSM cases**.
