# Deployment, Incident Response, and Accepted Risks

Closes review item **L-9** (no incident-response or migration story) from
`docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md`, and records the wrapper
obligations that `AUDIT.md` TA-8 places on integrators.

## 1. What the deployed verifier is — and is not

A generated `Halo2Verifier` is **stateless and immutable**: no owner, no
pause, no upgrade path, no `sstore`/`delegatecall`/`selfdestruct`. That is
deliberate — an on-chain admin lever on a verifier is itself an attack
surface. Two consequences follow, and both land on the application wrapper:

1. **There is no on-chain mitigation for a post-deployment soundness bug.**
   The only lever is the wrapper above the verifier.
2. **A valid proof is valid everywhere, forever.** The transcript starts at
   `vk_digest`; nothing binds `block.chainid`, the verifier address, or the
   deployment. `verifyProof == true` is a statement about the proof and the
   circuit, not about *this chain* or *this application*.

## 2. Wrapper obligations (REQUIRED, not advisory)

Every production integration MUST satisfy all three; a wrapper that
hardcodes the verifier as `immutable`/`constant` and treats
`verifyProof == true` as authorization has **no recovery path and
unconditional cross-chain replay**:

- **W-1 — Replaceable verifier address.** The wrapper holds the verifier
  behind an updatable (governed/timelocked) address so a re-rendered
  verifier can be swapped in.
- **W-2 — Wrapper-held pause.** The wrapper can stop accepting proofs while
  an incident is investigated. The verifier itself cannot.
- **W-3 — Domain binding + replay protection.** The statement the circuit
  proves (or the wrapper's own checks over the public instances) MUST bind:
  `block.chainid`, the wrapper (or verifier) address, and an
  application-level anti-replay value (nullifier, nonce, or consumed-state
  root). Without this, any accepted proof can be replayed on every chain
  and against every deployment of the same bytecode.

- **W-4 — Call it so a wrong address cannot read as success (MF-5).** A
  low-level `verifier.staticcall(...)` returns `ok = true` with empty
  returndata when the target has **no code** — a wrong address, a wrong
  chain, or a wrapper configured before deployment reads as a valid proof.
  Call through the typed interface (Solidity ≥0.8 inserts the `extcodesize`
  check), or, on any low-level path, require `returndatasize() >= 32` AND a
  decoded `true`. If the wrapper uses `try/catch`, every catch branch is a
  rejection: the verifier's failures are custom errors, so `catch Error(string)`
  and `catch Panic(uint)` will not match them — use `catch (bytes memory)` or a
  bare `catch`.
- **W-5 — Bind the accumulator's meaning, not just its validity (MF-9).** For
  IVC renders, the verifier checks that the carried accumulator points decode
  canonically, are in the subgroup, and satisfy the batched pairing equation.
  It does NOT check that they are non-trivial or that they continue *your*
  chain: the canonical identity encoding `(O, O)` is a well-formed accumulator
  and passes by construction. Any "this accumulator continues the expected
  fold" rule belongs to the circuit or the wrapper.

`verifyProof`'s NatSpec states the same split: the raw verifier checks the
proof against the pinned VK and nothing else.

## 3. Deployment record

For every production deployment, record and publish:

| Item | Source |
| --- | --- |
| `BUILD_ID` and each preimage component | the deployed contract's `BUILD_ID` constant; components below |
| Feature profile string | `build.rs` export baked into the generator (`SOLIDITY_VERIFIER_FEATURES`) |
| `vk_digest`, VK runtime length/codehash | generated constants |
| SRS fingerprint + asset SHA-256 + ceremony reference | `REPRODUCIBLE_BUILDS.md` ("SRS Provenance") |
| Provenance tag preimage | the `RenderOptions::provenance` input, e.g. `keccak256("commit=<sha>,dirty=<bool>")` — deployment builds MUST set it |
| Compiler identity + flags | `REPRODUCIBLE_BUILDS.md` (pinned solc SHA-256, `--optimize-runs`) |
| Artifact manifest | `scripts/generate_artifact_manifest.sh` output |
| Target security level and accepted risks | §5 below |

`BUILD_ID` exists precisely so "which of our deployed verifiers has the
affected codegen?" is answerable from chain state during an incident.

## 4. Incident response and migration playbook

**On a suspected soundness/liveness bug in a deployed verifier:**

1. **Pause** intake at the wrapper (W-2). Verifier-level mitigation does not
   exist by design.
2. **Scope** the blast radius: enumerate deployments and read each
   `BUILD_ID`; match against the deployment records to find which builds
   carry the affected generator code, feature profile, or SRS.
3. **Assess replay exposure**: anything accepted by an affected verifier
   must be treated per W-3 — if the statement was not domain-bound, assume
   cross-chain/cross-deployment replay of every historical proof.
4. **Fix and re-render**: land the generator fix, re-run the full gated
   suite and the IVC bench, regenerate artifacts, record new hashes and a
   new `BUILD_ID` (with a fresh provenance tag).
5. **Migrate**: deploy VK first, then verifier (the constructor fails closed
   on a wrong VK), verify on-chain `BUILD_ID` matches the record, switch the
   wrapper pointer (W-1), unpause.
6. **Retire** the old verifier in the deployment record (it cannot be
   destroyed on-chain); wrappers must never point back at it.

**On a fork of the chain you are deployed to — check this first (MF-1).**
The verifier forwards exact scheduled gas to every precompile, so an upward
repricing does not degrade: it bricks `verifyProof` outright (liveness, never
soundness). The canonical symptom is a **sudden, total `PrecompileFailed`
rate immediately after a fork activation**, on proofs that verified the day
before and still verify against the native Rust verifier. Triage:

1. Compare the fork's precompile schedule against the deployed constants
   (`G1ADD_GAS`, `G1MSM_GAS_*`, `PAIRING_GAS_2PAIR`, `MODEXP_GAS`).
2. If any scheduled cost now exceeds the deployed bound, that is the cause;
   re-render (the generator takes the maximum over live schedules) and
   migrate per the steps above. There is no wrapper-side mitigation.

Worked example: EIP-7883 (Fusaka, mainnet 2025-12-03, testnets earlier)
removed the `/ 3` divisor from modexp pricing, taking the verifier's frame
from 1360 to 4064 gas. An artifact rendered with exact bounds but before the
MF-1 fix carries `MODEXP_GAS = 1360` and reverts every proof on any
post-Fusaka chain. Deployment of NEW artifacts now fails fast in the
constructor probes for every precompile the runtime calls, modexp included.

**The exposure is exactly the artifacts that carry exact bounds.** Note what
that implies for `deployments/sepolia/moonlight-wrap`: it is NOT affected. It
predates the exact-gas hardening entirely — all 17 of its `staticcall`s
forward `gas()`, including its three modexp sites — so a repricing is simply
absorbed from the caller's remaining gas. (Verified by reading the recorded
source, whose recompiled runtime matches `runtimeCodeHash` in
`deployment.json` byte-for-byte apart from the two immutable `AUTHORIZED_VK`
slots, so the recorded source is genuinely what is deployed.)

That is the trade-off worth stating plainly, because it is easy to get
backwards: **exact-gas forwarding is what creates repricing fragility.** The
older `gas()`-forwarding renders survive any upward repricing but are exposed
to the DoS that exact bounds were introduced to close (M-2) — a malformed
proof point burns 63/64 of the transaction budget instead of one scheduled
call. Neither property is free; the constructor probes exist so the fragility
the current design accepts is caught at deployment rather than in production.

## 5. Accepted risks (deployment owner sign-off)

### 5.1 Keccak transcript has no domain separation (I-5)

The Keccak transcript absorbs raw concatenated bytes with no
personalisation string or `COMMON`/`CHALLENGE` tags (the Blake2b transcript
upstream has both). Not exploitable in this protocol: every absorb is
fixed-length with pinned counts, so no two distinct valid inputs produce
the same byte stream, and `vk_digest` provides cross-circuit separation.
It cannot be fixed verifier-side — adding tags would break every proof from
the midnight-proofs prover; this is the same class of upstream protocol
change as M-4 (`vk_digest` coverage), and is **accepted as a documented
defence-in-depth gap** until the transcript changes upstream.

### 5.2 `vk_digest` coverage (M-4) — deferred upstream decision

`vk_digest` does not cover the SRS points, quotient VM program, accumulator
schema, or feature profile. Compensating controls: build-time SRS tau
binding, VK codehash pin, generated-constant cross-checks, and `BUILD_ID`
(which does cover all of the above, off-transcript). Widening the digest is
a prover-affecting protocol change, explicitly out of scope by owner
decision (2026-08-13).

### 5.3 No negative EIP-2537 subgroup probe at deployment (L5/P2.4) — deferred

The constructor smoke suite proves the BLS12-381 precompiles exist,
answer known-answer vectors, and respect the forwarded gas bounds; it
cannot prove that a chain's G1MSM implementation actually REJECTS
non-subgroup points — the exact property the verifier's soundness
delegates to the precompile. A negative-conformance probe needs a
pinned non-subgroup test vector (a valid Fp pair on the curve but
outside the r-torsion) plus deployment gas budget for one expected-fail
MSM. Deferred by owner decision (2026-08-20, roadmap P2.e): revisit
after the P7 executable-model phase, which introduces the point-codec
machinery such a vector generator would share. Until then the risk is
bounded by deploying only to chains running audited mainline clients,
per §2's chain-support checklist.

## 6. Reading a revert (MF-4)

`verifyProof` is success-or-revert: it returns `true` or reverts with one of
the typed errors below. The taxonomy exists so the first question during an
incident — *is this the chain, the build, or the proof?* — is answerable from
the 4-byte selector alone, without a trace.

| Error | Selector | Class | First thing to check |
| --- | --- | --- | --- |
| `BadCalldataShape()` | `0x1b99e37c` | Caller | Heads, lengths, and EXACT `calldatasize`. A calldata-appending relayer (ERC-2771, multicall, paymaster) cannot call this contract directly. |
| `VkMismatch()` | `0xa447d73e` | Deployment | The pinned VK address no longer has the expected runtime length/codehash, or a VK header word disagrees with the generated constants. |
| `NonCanonicalScalar()` | `0x77530042` | Proof | A public instance or proof scalar is `>= r`. Usually an off-chain repacking bug, not an attack. |
| `BadPointEncoding()` | `0xf27905ec` | Proof | A proof point violates the EIP-2537 padding/field bounds, or an accumulator public input failed canonical decoding. |
| `PrecompileFailed()` | `0x84e81692` | **Chain** | A precompile could not run: missing, repriced above the forwarded bound (see §4), or short-returning. Also raised when G1MSM *rejects* a proof point as off-curve/out-of-subgroup — the precompile is the validator, so that rejection surfaces here by design. |
| `ProofRejected()` | `0xc3b0d8cd` | Proof | The pairing ran and returned != 1, or a Lagrange denominator was zero (the squeezed `x` hit a domain point, probability ~n/r). |
| `QuotientProgramInvalid()` | `0x3cc81b89` | **Build** | The VK-pinned quotient program violated a structural invariant. Not reachable with a well-formed artifact; treat as a generator bug. |
| `MemoryLayoutViolated()` | `0xc9888d23` | **Build** | solc's stack-spill reservation overlaps the generated layout. The artifact was compiled off the pinned toolchain and can never verify anything; redeploy from the pinned `(version, --optimize-runs)` pair. |

Two rules of thumb:

- **Chain/Build classes are total, not probabilistic.** They fail every call,
  including calls that verified yesterday. A sudden all-or-nothing failure
  rate points here; a per-proof failure rate points at the Proof class.
- **A revert is never an accept.** Every path above fails closed. There is no
  configuration in which `verifyProof` returns `false` — see W-4 for why a
  wrapper must not treat a bare `staticcall` success as verification.
