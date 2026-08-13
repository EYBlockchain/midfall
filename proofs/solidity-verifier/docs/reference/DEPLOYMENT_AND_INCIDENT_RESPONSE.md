# Deployment, Incident Response, and Accepted Risks

Closes review items **L-9** (no incident-response or migration story) and
**L-10** (truncated-challenge soundness as a recorded accepted risk) from
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

**Upstream repricing note:** the verifier forwards exact EIP-2537/EIP-2565
scheduled gas. A fork that reprices those precompiles upward bricks
`verifyProof` (liveness, not soundness) and deployment of new artifacts
fails fast in the constructor probes. The migration path is the same
re-render + wrapper switch.

## 5. Accepted risks (deployment owner sign-off)

### 5.1 Truncated challenges cap PCS soundness at ≈ 2⁻¹⁰⁸ per attempt (L-10)

The `truncated-challenges` profile — which the canonical artifacts use, and
which mirrors the midnight-proofs prover — truncates `x3` to its low 128
bits after squeezing and truncates each `x1`/`x4` power to 128 bits at use.
Consequences (full derivation: review §L-10):

- Per-attempt false-acceptance probability of the isolated `x3` step is
  `(n + 9) / 2¹²⁸ ≈ 2⁻¹⁰⁷·⁹⁹` at `n = 2²⁰`, and ≈ **2⁻¹⁰⁷·⁶** after the
  ×1.3585 `mod r` sampling-bias factor. Untruncated sampling would give
  ≈ 2⁻²³⁴; the mask costs ~127 bits.
- The bound is essentially tight: an adversary can place all roots of the
  lying polynomial inside `[0, 2¹²⁸)`, so the attack is grinding `f_com`
  with expected work ≈ **2¹⁰⁸**.
- Edge case: `truncate(x1^i) = 0` (probability 2⁻¹²⁸ per power) silently
  drops query `i` from both the commitment and evaluation sides — a clean,
  symmetric failure.
- Assumptions: KZG binding fixes `f'` from `f_com`; `x3` avoids the poles of
  the batched rational function (fails with probability `11/2¹²⁸`).

**Decision (2026-08-13): ACCEPTED.** Rationale: the profile faithfully
mirrors the prover (a verifier-side change alone is impossible), and 2¹⁰⁸
expected grinding work per forgery attempt exceeds the target security
level below. Disabling the feature is a prover-side protocol change tracked
separately, not a verifier patch.

- **Target security level:** ≥ 2¹⁰⁰ expected work per false acceptance.
- **Sign-off:** deployment owner: ______________________ date: __________
  *(recorded per deployment; this repository documents the analysis and the
  default acceptance).*

### 5.2 Keccak transcript has no domain separation (I-5)

The Keccak transcript absorbs raw concatenated bytes with no
personalisation string or `COMMON`/`CHALLENGE` tags (the Blake2b transcript
upstream has both). Not exploitable in this protocol: every absorb is
fixed-length with pinned counts, so no two distinct valid inputs produce
the same byte stream, and `vk_digest` provides cross-circuit separation.
It cannot be fixed verifier-side — adding tags would break every proof from
the midnight-proofs prover; this is the same class of upstream protocol
change as M-4 (`vk_digest` coverage), and is **accepted as a documented
defence-in-depth gap** until the transcript changes upstream.

### 5.3 `vk_digest` coverage (M-4) — deferred upstream decision

`vk_digest` does not cover the SRS points, quotient VM program, accumulator
schema, or feature profile. Compensating controls: build-time SRS tau
binding, VK codehash pin, generated-constant cross-checks, and `BUILD_ID`
(which does cover all of the above, off-transcript). Widening the digest is
a prover-affecting protocol change, explicitly out of scope by owner
decision (2026-08-13).
