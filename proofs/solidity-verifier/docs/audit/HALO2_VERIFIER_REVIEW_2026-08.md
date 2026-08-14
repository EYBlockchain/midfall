# Halo2 BLS12-381 Solidity Verifier — Architecture Review, Conformance Check and Security Audit

**Artefacts under review**

| File | SHA-256 | Size |
| --- | --- | --- |
| `Halo2Verifier.sol` | `3861a403f7319e767610fc71a3ff5500b2c14e787a68703188d2f2629928e756` | 213,670 B / 3,682 lines |
| `Halo2VerifyingKey.sol` | `ec94cabe5691703e240b116c59bc2e7c83cbdefe2e4d02dbd64020d6a0294f19` | 78,098 B / 692 lines |

Both files are **byte-identical** to `midfall/proofs/solidity-verifier/fixtures/moonlight-wrap/`. This is the `AccumulatorEncoding::point_pair` replay fixture, rendered by Moonlight's `wrap_circuit_composes_two_fold_children_from_four_dummy_fold_proofs` at solidity-verifier commit `3fb6d84`.

**Reference implementation:** `midfall/proofs` (`src/plonk/*`, `src/poly/kzg/*`, `src/transcript/*`) and the generator at `midfall/proofs/solidity-verifier`.

**Method.** Four independent passes were run and reconciled: a line-by-line conformance diff against the Rust verifier; a cryptographic/soundness pass; an EVM/implementation pass; and an operational/key-management/supply-chain pass. Findings were then **executed**: both contracts were compiled with solc 0.8.30 (`--via-ir --optimize --optimize-runs=1 --evm-version cancun`, CBOR metadata stripped) and run under `revm 19` with `SpecId::PRAGUE` and the `blst` BLS12-381 precompiles, against the fixture calldata and 40 adversarial mutations.

---

## Executive summary

**The verifier is sound as rendered.** No Critical or High soundness break was found in the contract. Every phase that could be checked against staged reference code — transcript schedule and encodings, challenge order, instance handling, all four identity families, the y-batching algebra, linearization and quotient reconstruction, the multi-open reduction, and the pairing equation including which side carries the negation — conforms to `midfall/proofs`. The domain constants, the permutation `DELTA`, the base points and the VK codehash were all recomputed independently and match.

The code is also, by a wide margin, better defended than a typical generated verifier. It re-pins the VK by `extcodehash` **on every proof**, not just at construction. It pins both ABI head words, the proof length, the instance count and `calldatasize()` before touching any data-dependent calldata. It range-checks every scalar against `r` with `lt`, not `mod`. It rejects non-canonical EIP-2537 padding rather than normalising it (which would create transcript aliases). It routes every prover-supplied G1 through a subgroup-checking precompile. It compares the pairing result `== 1` rather than masking the low bit. And it asserts structural post-conditions on its own quotient interpreter (`q_pc == q_end`, empty stack, no live operand).

**The risk is not in the Solidity — it is around it.** The highest-severity finding is that `NEG_S_G2_BASE`, the trusted-setup element on which all soundness rests, is taken verbatim from whatever SRS the generator was handed, with no ceremony binding, no SRS hash, and no build-time consistency check — even though the generator *does* defend the G1 base with exactly such a check. Below that sit a cluster of build-reproducibility and deployment-assurance gaps, a compiler-configuration dependency that is not self-enforcing in the shipped artefact, and a weak deployment-time probe of precisely the two precompiles that decide acceptance.

One new, empirically-demonstrated issue: **a single off-curve point in the proof causes the verifier to consume ≈98.5% of whatever gas limit is supplied** (29.5M of a 30M limit, versus 316k for a structural rejection and 1.28M for a valid proof), because a failing EIP-2537 precompile consumes all gas forwarded to it. This is a griefing vector for any relayer, paymaster or batching wrapper.

### Findings at a glance

| ID | Severity | Title |
| --- | --- | --- |
| **H-1** | High | Trusted-setup element `NEG_S_G2_BASE` is unverifiable: no ceremony binding, no SRS pin, no build-time consistency check |
| **M-1** | Medium | `assembly ("memory-safe")` is factually false; the invariant that protects it is enforced only by an external test, under a floating pragma |
| **M-2** | Medium | Malformed curve points burn ~63/64 of the supplied gas instead of reverting cheaply (demonstrated) |
| **M-3** | Medium | Deployment probe is weakest exactly where acceptance is decided: `PAIRING_CHECK` and `G1MSM` are tested only with identity inputs |
| **M-4** | Medium | `vk_digest` does not cover the SRS points, the quotient program, the accumulator schema or the feature profile — the team's own TA-2 remediation is still open |
| **M-5** | Medium | Build is not reproducible as documented: three conflicting provenance stamps, empty artefact manifest, `--optimize-runs` unrecorded and environment-overridable, solc pinned by version string not hash |
| **L-1** | Low | Codegen certification covers the emitter→reference leg only; the Yul VM and native kernels are fixture-sampled, and the replay test recompiles committed fixtures |
| **L-2** | Low | Committed-instance commitment hard-wired to the identity; one MSM term silently omitted while the emitted comment claims otherwise |
| **L-3** | Low | 41 bare `revert(0, 0)` sites; `verifyProof` can never return `false` despite its signature |
| **L-4** | Low | Exact-`calldatasize` pin makes the verifier uncallable through ERC-2771 forwarders and similar calldata-appending relayers |
| **L-5** | Low | `CHALLENGE_MPTR` aliases `THETA_MPTR` — inert here, silent corruption for any circuit with user-phase challenges |
| **L-6** | Low | Quotient-VM operands are unvalidated raw memory pointers; safety rests entirely on codehash pinning plus emitter correctness |
| **L-7** | Low | Zero-slack memory adjacencies; `batch_invert` scratch ends exactly at `LAGRANGE_DENOMS_MPTR` and would corrupt silently, without reverting |
| **L-8** | Low | No on-chain provenance: no build id, no feature profile, CBOR metadata stripped |
| **L-9** | Low | No incident-response or migration story; no domain binding, so a valid proof replays across every chain and deployment |
| **I-1…I-7** | Info | Comments contradicting constants, dead code and constants, unreachable defensive branch, stale audit-doc anchors, missing transcript domain separation, two latent codegen divergences, unbound batching randomiser |

---

# Part I — How it works

## 1.1 Two contracts, and why

The system is a **circuit-specialised** verifier: the proof layout, memory map, quotient program and every constant are generated for exactly one `VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>`. It is not a generic Halo2 verifier and cannot verify a proof for any other circuit.

It ships as two contracts because the verifying key is too large to sit comfortably inside the verifier's own bytecode:

- **`Halo2VerifyingKey`** — a *data* contract. Its constructor writes a byte-blob into memory and `return`s it as runtime code. There is no executable logic in the deployed runtime at all.
- **`Halo2Verifier`** — the logic. A thin Solidity shell (`AUTHORIZED_VK`, a constructor, and `verifyProof`) wrapped around one very large `assembly` block that does the entire verification.

The verifier binds to its key by **address, byte length and codehash** (`EXPECTED_VK_LENGTH = 17025`, `EXPECTED_VK_CODEHASH = 0xe68d8936…cf52`), and re-checks that binding before every single proof, not just at deployment.

## 1.2 The VK contract: data as code

```solidity
constructor() {
    assembly {
        let runtime := 0x80
        let payload := add(runtime, 0x01)
        mstore8(runtime, 0xfe)                 // INVALID opcode
        mstore(add(payload, 0x0000), 0x56c0…)  // vk_digest
        …532 words total…
        return(runtime, 0x4281)                // 17025 bytes
    }
}
```

Byte 0 is an unconditional `INVALID` (`0xfe`), so a direct call to the VK address cannot execute the payload as code. The verifier copies from byte 1 onward:

```yul
extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)   // 17024 bytes
```

I reconstructed the runtime from the 532 `mstore`s, prepended the `0xfe`, and confirmed `keccak256` equals `EXPECTED_VK_CODEHASH` and the length equals 17025 — so the pinned hash covers the `INVALID` prefix, and the two contracts are mutually consistent. Because the runtime is pure returned data, **this codehash is compiler- and optimiser-independent**, which is a genuinely good design property: the VK half of the system is trivially reproducible even though the verifier half is not (see M-5).

The payload layout, in 32-byte words from `VK_MPTR = 0x3680`:

| Words | Content | Value in this artefact |
| --- | --- | --- |
| 0 | `vk_digest` (Blake2b-512 over the pinned constraint system, reduced) | `0x56c0824f…4f66` |
| 1 | `num_instances` | 19 |
| 2 | `k` (log₂ domain size) | 20 |
| 3 | `n_inv` | 1/2²⁰ mod r |
| 4–6 | `omega`, `omega_inv`, `omega_inv_to_l` | order-2²⁰ root; ω⁻¹⁰ |
| 7–10 | `has_accumulator`, `acc_offset`, `num_acc_limbs`, `num_acc_limb_bits` | 1, 11, 7, 56 |
| 11–14 | `G1_BASE` (4 words, EIP-2537 padded) | canonical BLS12-381 G1 generator |
| 15–22 | `G2_BASE` (8 words) | canonical G2 generator |
| 23–30 | `NEG_S_G2_BASE` (8 words) | −[s]G₂ from the trusted setup |
| 31… | quotient VM constant pool (178 words) + packed program (143 words, `0x11cf` bytes) | |
| … | 27 fixed commitments, then 18 permutation commitments (4 words each) | |

The header ends exactly at `0x7900 = CHALLENGE_MPTR` — the VK region and the challenge region abut with zero slack.

I verified numerically: `n_inv · 2²⁰ ≡ 1 (mod r)`; `omega` has exact multiplicative order 2²⁰; `omega · omega_inv ≡ 1`; `omega_inv_to_l = omega_inv¹⁰`, consistent with `|rotation_last| = 10` and `blinding_factors = 9`; `G1_BASE` and `G2_BASE` are the canonical generators; `NEG_S_G2_BASE` is on the twist, in the r-order subgroup, and is not ±G₂; all 45 VK G1 commitments are on-curve and in the r-subgroup; and none of the 10 simple-selector commitments is the point at infinity (an identity selector commitment would have silently zeroed every identity in its bucket).

## 1.3 The verifier's memory map

The single most unusual design decision: the generated code **does not use Solidity's free-memory pointer at all**. Every address is an absolute constant baked in at codegen time, starting at `0x1000`.

```
0x0000–0x005f   Solidity scratch          (never written)
0x0040          free-memory pointer       (never written, never read)
0x0080–0x0fff   solc's via-IR stack-spill reservation
0x1000          TRANSCRIPT_MPTR = RETURN_MPTR = QUOTIENT_RETURN_MPTR
                 ↳ streaming Keccak buffer, peaks at 0x1ce0
                 ↳ later reused for PCS scaling, the acc-batch preimage,
                    the ec_pairing frame, and finally the returned word
0x3580–0x363f   scalar_inv modexp frame
0x3680–0x78ff   VK payload (copied by extcodecopy)
0x7900–0x7a3f   challenges: theta β γ trash y x x1 x2 x3 x4
0x7a40–0x7f7f   f_com, pi, acc lhs/rhs, Lagrange scratch, quotient, pairing slots
0x7f80–0x931f   rotation points, x1 powers, q_eval sets
0x9480–0xa13f   REVERSED_EVALS (102 spilled proof evaluations)
0xa140–0xb13f   proof G1 commitments, by category
0xb140          SELECTOR_ACC_MPTR = BATCH_INV_SCRATCH_MPTR
0xb280–0xe33f   the fused 78-pair final G1MSM input (0x30c0 bytes)
0xe340          end
```

Three addresses are deliberately aliased (`0x1000` three ways, `0xb140` two ways). I traced the write map in program order and confirmed all of them are **lifetime-disjoint reuse, not collisions**: the transcript is dead by line 1377, long before `0x1000` is next touched at line 3570; `batch_invert` runs exactly once (line 1431) and finishes before the selector buckets are zeroed at line 1612.

The strategy is fast — an absolute `mload` costs 3 gas and needs no pointer arithmetic — and it is why this verifier lands at ~1.28M gas. It is also the source of finding **M-1**: the annotation `assembly ("memory-safe")` that unlocks solc's stack-to-memory mover is, on its own terms, false, and the invariant that keeps it safe (`solc's spill reservation < 0x1000`) is checked only by a test in the generator repo, never in the shipped bytecode.

## 1.4 The verification flow

`verifyProof(bytes proof, uint256[] instances)` — selector `0x1e8e1e13`. For this circuit: proof = 7,776 bytes, instances = 19 words, total calldata = 8,516 bytes exactly.

**Phase 0 — envelope.** Before touching anything data-dependent, four independent pins:

```yul
calldataload(0x04) == 0x40        // proof head
calldataload(0x24) == 0x1ec0      // instances head
calldataload(0x44) == 0x1e60      // proof length
calldataload(0x1ec4) == 19        // instance count
calldatasize()     == 0x2144      // no missing or trailing bytes
```

This closes the classic hand-rolled-parser hole where an attacker supplies arbitrary ABI offsets and relocates the instance array. All five were confirmed by mutation testing (Appendix A, N23–N30, D-block).

**Phase 1 — VK load.** `extcodesize` and `extcodehash` are both re-checked, then `extcodecopy` from byte 1. Six header words are cross-checked against constants baked into the verifier (`19, 20, 1, 11, 7, 56`).

**Phase 2 — accumulator pre-validation.** Runs *before* the transcript, so malformed accumulator public inputs cannot influence challenge derivation. Described in §1.6.

**Phase 3 — transcript.** A streaming Keccak buffer. `common_word` appends a 32-byte big-endian word; `common_uncompressed_g1` validates and appends 128 bytes; `squeeze_to` hashes the buffer, **reseeds the buffer with the digest**, and samples `digest mod r`. That reseed is exactly equivalent to the Rust `squeeze()`, which finalises a clone and re-inits a fresh `Keccak256` over the output.

The absorb/squeeze schedule, verified byte-for-byte against `src/plonk/verifier.rs` and `src/poly/kzg/mod.rs`:

```
vk_digest → committed_pi (128 zero bytes) → 19 → 19 instances
→ 15 advice → [θ] → 2 lookup-m → [β] [γ] → 6 perm-Z
→ (helper + acc) ×2 → [trash] → 1 trashcan → [y]
→ 4 quotient limbs → [x] → 102 evaluations → [x1] [x2]
→ f_com → [x3, truncated to 128 bits] → 5 q_evals → [x4] → pi
```

Every prover-controlled value is absorbed strictly before any challenge that depends on it. `pi` is last and no challenge depends on it.

Two validation policies matter here:

- **Scalars** (19 instances, 102 evaluations, 5 q_evals) are checked `lt(v, r)` — a strict canonicality check, so `v = r` is rejected, not silently reduced. Non-canonical encodings would otherwise create transcript aliases.
- **G1 points** get their EIP-2537 padding checked (top 16 bytes of each `_hi` word must be zero) and each coordinate bounded by `p−1`, but **no on-curve or subgroup check here**. Validity is deferred: the code relies on every absorbed point later reaching an EIP-2537 `G1MSM` or `PAIRING_CHECK`, both of which do perform subgroup checks. That is a *codegen-time* invariant (`ProtocolPlan::validate`), and it is why the malformed-point gas behaviour in M-2 exists.

**Phase 4 — Lagrange.** One 30-element batch inversion computes `x−ω^i` inverses plus `(xⁿ−1)⁻¹`; from these come `l_last` (index 0), `l_blind` (Σ indices 1–9), `l_0` (index 10) and `L_0…L_18` (indices 10–28) for the instance evaluation. If `x` lands on the domain, the batch product is zero, `batch_invert` returns 0, and the verifier reverts — so the `xⁿ = 1` degeneracy fails closed.

**Phase 5 — quotient identity.** See §1.5.

**Phase 6 — PCS.** Halo2's multipoint reduction (GWC-style with r-polynomial interpolation, not SHPLONK). 5 rotation sets of cardinality 1, 2, 2, 3, 3 over rotations {−10, −1, 0, +1}; batching by truncated powers of `x1` within a set and `x4` across sets; the whole commitment side collapses into **one fused 78-pair `G1MSM`**.

**Phase 7 — pairing.** §1.7.

## 1.5 The quotient identity — a bytecode interpreter in Yul

The interesting engineering choice. Rather than emitting ~49 straight-line polynomial identities as Yul (which blows past the 24KB contract limit), the generator compiles them to a small stack-machine bytecode, stores that program **inside the VK payload**, and ships an interpreter in the verifier.

Consequences:
- The program is covered by `EXPECTED_VK_CODEHASH`, so it cannot be tampered with post-deployment.
- The verifier avoids thousands of `PUSH32`/`mstore` immediates.
- The interpreter is ~1,500 lines of Yul with 11 implemented opcodes, including two "native kernels" (`NATIVE_PERMUTATION 0x19`, `NATIVE_LOOKUP 0x1f`) that run the permutation and LogUp arguments as hand-written Yul rather than interpreted arithmetic.

The 49 identities are `y`-batched by Horner: `A := A·y + eval_j`, so identity *j* receives coefficient `y^(48−j)`, matching the Rust reverse fold in `linearization/verifier.rs`. Ten "simple selector" buckets accumulate separately and are multiplied into the commitment side at `x1^42`, which is how selector-compressed gates are handled.

The interpreter asserts three structural post-conditions before proceeding:

```yul
q_pc == q_end            // consumed exactly the program
q_has_top == 0           // no live expression left
q_sp == 0xb8e0           // stack pointer restored
```

An unknown opcode hits `default { revert(0, 0) }`. These are good defences; the residual concern is **L-6** (operands are raw memory pointers with no bound check).

## 1.6 The accumulator — recursive-proof handling

`has_accumulator = 1`, `acc_offset = 11`: public inputs 11–18 encode **two G1 points**, each as 2 coordinates × 2 packed words, with each 381-bit `Fp` coordinate carried as 7 limbs of 56 bits packed 4-per-word.

The codec is a shifted one: an encoded value `c` decodes to `c + 1`, and encoded `p−1` decodes to `0`. The point at infinity gets a single canonical encoding — `x = p−1 + 2⁵⁶` (the identity flag), `y = p−1` — checked by exact 4-word equality against pinned constants.

The decoder is carefully written and I could not break it:

- `check_acc_coord_packing` bounds packed word 0 below `2²²⁴` and word 1 below `2¹⁶⁸`, making the limb split a **bijection** — no two encodings of the same coordinate.
- The reconstructed coordinate is bounded by `p−1`, and `hi < 2¹²⁸` (the EIP-2537 pad rule).
- A decoded `(0, 0)` outside the sentinel path is explicitly rejected, so affine infinity has exactly one accepted encoding.
- `PACKED_0_WITH_ID_FLAG − PACKED_0 = 2⁵⁶` exactly — no carry into the neighbouring limb.
- The `sub(packed, first_adjust)` cannot underflow: the identity probe only runs behind a `calldataload(src) >= base` prefilter.

Both decoded points are then forced through `G1MSM` with scalar 1 — not to compute anything, but because **the precompile is the on-curve/subgroup validator**. The comment says so explicitly, and the code does it even for identity points and unit scalars, which is exactly right: skipping the call would let a malformed non-identity point hide behind a zero scalar.

The accumulator's own pairing equation `e(acc_rhs, G₂) = e(acc_lhs, [s]G₂)` is then folded into the KZG pairing by **randomised batching** rather than naive multiplication (which would let two false equations cancel):

```yul
alpha = keccak256("pairing-batch-acc-kzg" ‖ kzg_rhs ‖ kzg_lhs ‖ acc_rhs ‖ acc_lhs) mod r
if alpha == 0 { alpha = 1 }
PAIRING_RHS += alpha · ACC_RHS
PAIRING_LHS += alpha · ACC_LHS
```

`alpha` is drawn only after all four G1 points are final, so if either equation is false the combined one holds for at most one `alpha` in `Fr` — a ~2⁻²⁵⁵ forgery probability. The zero-draw guard prevents the accumulator equation from being accidentally dropped. This is correct.

## 1.7 The final pairing

```
e(final_com − v·G + x3·π, G₂) · e(π, −[s]G₂) = 1
```

which rearranges to the standard KZG single-opening identity `e(C − vG + x3·π, G₂) = e(π, [s]G₂)`. The Rust reference negates the G₂ *generator* instead of `s·G₂`; algebraically the same equation, and the generated comment (lines 3653–3665) explains the LHS/RHS naming inversion honestly.

`ec_pairing` checks three things — staticcall success, `returndatasize() == 0x20`, and `mload(scratch) == 1` (strict equality, not a low-bit mask) — and reverts on entry if `success` is already false, so no path hands control back to a caller that would report success for an unverified proof.

---

# Part II — Conformance against `midfall/proofs`

Every phase of the Rust verifier was diffed against the Solidity. The recovered circuit shape, derived from the artefacts and cross-checked for internal consistency: `k=20`, `cs_degree=5`, `blinding_factors=9`, `rotation_last=−10`, 15 advice columns (1 phase, 0 user challenges), 27 fixed columns of which 10 are simple selectors, 18 permutation columns → 6 sets of `chunk_len=3`, 2 LogUp lookups × 1 chunk, 1 trashcan, 4 quotient limbs, 2 instance columns (1 committed + 1 non-committed with 19 public inputs), 49 quotient identities (29 gate + 13 permutation + 6 lookup + 1 trash), 102 evaluations, 34 proof G1s, 5 KZG point sets, 78 final-MSM terms. Feature profile implied: `keccak-transcript` + `committed-instances` + `truncated-challenges` ON; `single-h-commitment` and `fewer-point-sets` OFF.

## 2.1 Conformance matrix

| # | Phase | Rust reference | Solidity | Verdict |
| --- | --- | --- | --- | --- |
| 1 | Hash function | Keccak256, plain `update`, no domain prefix (the `BLAKE2B_PREFIX_*` tags apply only to the Blake2b impl) | Streaming buffer, one `keccak256` per squeeze (`:399,:460`) | **MATCH** |
| 2 | Squeeze / reseed | `out = clone().finalize()`, then `state := Keccak::new().update(out)` (`implementors.rs:198`) | `h0 = keccak(buf)`, `mstore(TRANSCRIPT_MPTR, h0)`, cursor → +32 (`:461-467`) | **MATCH** |
| 3 | Digest → Fr | `BigUint::from_bytes_be(digest) % r` — modular reduction, not rejection sampling | `mod(h0, r)` (`:466`) | **MATCH** (identical, incl. identical bias — see note below) |
| 4 | Scalar absorb encoding | `to_repr()` (LE) reversed → 32 BE bytes | Calldata word verbatim (BE); shim pre-reverses off-chain | **MATCH** |
| 5 | Point absorb encoding | 128-byte EIP-2537 padded uncompressed; identity = 128 zero bytes (`implementors.rs:283`) | `common_uncompressed_g1` copies 4 words verbatim after pad/`Fp` checks (`:434-455`) | **MATCH** |
| 6 | Initial seeding | `vk.hash_into` → `common(&transcript_repr)`, one Fq → 32 BE bytes | `common_word(buf_len, mload(VK_DIGEST_MPTR))` (`:1091`) | **MATCH** on encoding; digest *value* not independently recomputable |
| 7 | Committed-instance commitments | Caller-supplied, absorbed and opened as real PCS queries (`verifier.rs:90,356,610`) | Hard-coded 128 zero bytes = identity (`:1101-1111`) | **MATCH only under `committed_instances = [identity]`** → **L-2** |
| 8 | Instance count + values | Absorb `F::from_u128(len)` then each value | `common_word(…, 19)` then 19 range-checked words (`:1118-1132`) | **MATCH** |
| 9 | Advice / phase order | Per phase: all advice, then that phase's challenges | One phase, 15 G1s, no user-challenge squeeze | **MATCH** |
| 10 | Challenge schedule | θ → lookup-m → β → γ → perm-Z → helpers+acc → trash (unconditional) → trashcans → y → quotient limbs → x → evals → x1,x2 → f_com → x3 → q_evals → x4 → π | Identical (`:1178,1196,1197,1256,1273,1296,1330,1331,1343,1377`) | **MATCH** — verified byte-for-byte |
| 11 | `x3` truncation | `truncate(x3)` = low 128 bits (`kzg/mod.rs:456`) | `and(mload(X3_MPTR), 2¹²⁸−1)` immediately after squeeze (`:1353`) | **MATCH** |
| 12 | `x1`/`x4` power truncation | Accumulator full precision, each emitted power truncated | `acc := mulmod(acc,x1,r)` full; stored value masked (`:3011,:3379`) | **MATCH** |
| 13 | `x2` | Not truncated | Unmasked | **MATCH** |
| 14 | Trailing-data check | `Transcript::assert_empty` | `proof_cptr == NUM_INSTANCE_CPTR` (`:1395`) + exact `calldatasize` | **MATCH** (Solidity stricter) |
| 15 | Instance evaluation | `l_i_range(x, xⁿ, …)`, inner product | Fixed `L_0…L_18` (`:1457-1466`) | **MATCH** given `max_rotation == 0` over instance queries (codegen-enforced) |
| 16 | Lagrange formula | `L_i(x) = ωⁱ(xⁿ−1)/(n(x−ωⁱ))` | `l_i_common · inv(x−ωⁱ) · ωⁱ` (`:1436-1442`) | **MATCH** |
| 17 | `l_last` / `l_blind` / `l_0` | `l_evals = l_i_range(x, xⁿ, −(b+1)..=0)`; `b = 9` | slot 0 / Σ slots 1–9 / slot 10 (`:1446-1452`) | **MATCH** |
| 18 | Identity family order | gates → permutation → lookups → trash (`plonk/mod.rs:516-607`) | Inline gate prefix → VM (gates, `NATIVE_PERMUTATION`, `NATIVE_LOOKUP`) → trash suffix | **MATCH** |
| 19 | `y`-power aggregation | Reverse fold: identity *j* gets `y^(m−1−j)`, `m = 49` | Horner from the front + selector gap/tail bookkeeping — same exponents | **MATCH** (all 21 in-bytecode gaps and 10 selector tails checked arithmetically) |
| 20 | Selector compression | Simple-selector fixed evals replaced by `ONE`, identity attributed to the gate's first simple selector | Selector eval hard-coded `0x1`; 10 buckets × `x1^42` paired with the right fixed commitments (`:3491-3510`) | **MATCH** |
| 21 | Permutation argument | `l_0(1−z_0)`; `l_last(z_L²−z_L)`; `l_0(z_i − z_{i−1}^last)`; per-chunk with `βx·DELTA^(chunk·len)` | Identical (`:2095-2130`); `DELTA = 7^(2³²)` and `DELTA³` verified numerically | **MATCH** |
| 22 | LogUp argument | `(l_0+l_last)Z`; `h·Πf − Σ_j Π_{k≠j} f_k`; `((Z_next−Z−sΣh)(t+β)+m)·active`; θ-compression | Identical, but prefix/suffix products instead of `product · f⁻¹` (`:2179-2196`) | **MATCH** on value; see L-2 note below |
| 23 | Trash argument | `fold(acc·τ + e) − (1−q)·trash_eval` | `:2861-2865` | **MATCH** |
| 24 | Quotient reconstruction | limb scalars `(1−xⁿ)(x^{n−1})^k` | `x_split = x^(2²⁰−1)`, `one_minus_x_n` (`:2942-2965, 3479-3490`) | **MATCH** |
| 25 | Expected opening scalar | `expected_eval −= eval` for the `None` group | `QUOTIENT_EVAL_MPTR := −A` (`:2921`), 43rd eval of set 0 at `x1^42` | **MATCH** |
| 26 | PCS scheme | Halo2 multipoint (GWC-style with r-poly interpolation), **not** SHPLONK | Same reduction shape | **MATCH** |
| 27 | Rotation sets | `construct_intermediate_sets` then `sort_by_key((len, i))` | 4 rotations, 5 sets of size 1,2,2,3,3 | **MATCH** for this VK |
| 28 | `x1` batching | `q_com[s] = Σ x1ⁱ C_{s,i}`, `q_eval_set[s] = Σ x1ⁱ e_{s,i}` | 43 truncated powers; per-set folds; MSM scalars `x1ⁱ·x4ˢ` | **MATCH** |
| 29 | `f_eval` | Reverse fold `acc = acc·x2 + (q_eval_s − r_s(x3))/Π(x3−p)` | Sets 4→0 (`:3214-3366`), algebraically identical form | **MATCH** |
| 30 | `v` | `inner_product([q_evals…, f_eval], truncated_powers(x4))` | `:3390-3395` | **MATCH** |
| 31 | `final_com` | `msm_inner_product([q_coms…, f_com], truncated_powers(x4))` | Single fused 78-term G1MSM (`:3396-3559`) | **MATCH** |
| 32 | Pairing / negation | `e(π, s_g2)·e(final_com − vG + x3π, n_g2) = 1` — G₂ **generator** negated | `e(final_com − vG + x3π, G₂)·e(π, −[s]G₂) = 1` — `s·G₂` negated | **MATCH** — same equation, sign carried on the other element |
| 33 | Domain constants | `EvaluationDomain` | VK words 2–6 | **MATCH — verified numerically** |
| 34 | `blinding_factors` / `rotation_last` | `max(3, max_advice_queries) + n_trash + Σchunks + 3 = 9`; `−10` | 9 negative Lagranges; `ω⁻¹⁰` | **MATCH** |
| 35 | `quotient_poly_degree` | `cs_degree − 1 = 4` | 4 quotient limbs | **MATCH** |
| 36 | G1/G2 bases | `G1Affine::generator()`, `params.g2()`, `−params.s_g2()` | VK words 11–30 | **MATCH** for G1/G2 (byte-compared to canonical generators); `NEG_S_G2` unverifiable → **H-1** |

### Note on challenge sampling bias

Both sides compute `keccak256(...) mod r` on a **256-bit** digest reduced into a **255-bit** prime field. This is *not* the usual "wide hash, negligible bias" situation: `floor(2²⁵⁶/r) = 2`, so 20.8% of residues have three preimages and the rest have two. Statistical distance from uniform is **7.47%**.

That sounds bad and is not. Soundness bounds depend on the *maximum* challenge probability, which is inflated by `3/(2²⁵⁶·(1/r)) = 1.3585×` — **0.44 bits**. Negligible, and bit-identical to the Rust reference, so it is a shared property rather than a divergence. Recorded here because the naive "≈2⁻¹²⁷ bias" figure often quoted for Fiat-Shamir reductions does not apply at this digest/field width and should not be carried into a security argument.

## 2.2 Where Solidity is *stricter* than Rust

Worth recording, because a reader of the Rust cannot assume these:

1. ABI head words, proof length, instance count and `calldatasize()` are all pinned (Rust takes typed arguments).
2. The VK runtime is re-pinned by `extcodesize` **and** `extcodehash` on **every** proof.
3. Six VK header words are cross-checked against baked-in constants.
4. Public instances are range-checked `< r` before absorption.
5. EIP-2537 pad canonicality is enforced — top 16 bytes zero, coordinate ≤ `p−1`.
6. `scalar_inv` rejects both `x ≥ r` and `x == 0`; Rust's `invert().unwrap()` **panics** instead.
7. `batch_invert` rejects any non-canonical or zero denominator; Rust's `ff::BatchInvert` silently **skips** zeros, yielding `L_i = 0` and continuing.
8. Quotient-VM structural post-conditions; unknown opcode reverts.
9. Every precompile call checks `returndatasize()` exactly; the pairing result is compared `== 1`, not masked.
10. Deploy-time smoke tests for MCOPY and three EIP-2537 precompiles, including a known-answer `G1ADD(G,G) = 2G` vector.
11. `ec_pairing` reverts on entry when `success` is already false.
12. Accumulator canonical-encoding checks (exact identity sentinel, unused-bit rejection, `Fp` bound, decoded-`(0,0)` rejection).
13. Every decoded accumulator point is forced through `G1MSM` even at scalar 1, purely for the precompile's validation.
14. An extra, randomised pairing equation for the public accumulator.

## 2.3 Where Solidity is *laxer* or behaviourally different

| Item | Difference | Assessment |
| --- | --- | --- |
| **Point validity timing** | Rust's `G1Projective::read` does on-curve + subgroup checks at read time. Solidity absorbs raw calldata into Fiat-Shamir with only pad/`Fp` checks, deferring validity to a later `G1MSM`/pairing. | Fails closed at runtime for all 34 absorbed points — I traced each to a validating precompile. But coverage is a **codegen-time** invariant, not a runtime one: an emitter change that drops a point from the MSM removes its only validation. It is also the direct cause of **M-2**. |
| **Committed instances** | Hard-coded identity; no ABI channel. | **L-2**. Sound as rendered (empirically confirmed below), unsound if the assumption is ever violated. |
| **LogUp with `f_j + β = 0`** | Solidity's prefix/suffix product computes the correct `Σ_j Π_{k≠j}(f_k+β)` and proceeds; Rust's `product * f.invert().unwrap()` **panics**. | Solidity accepts proofs on which Rust aborts. The Solidity value matches the *documented* identity, so this is a robustness gain — but it is a genuine accept/reject divergence on adversarial input and should be recorded as intentional. |
| **`x` landing on the domain** | Solidity reverts; Rust continues with `L_i = 0`. | Negligible-probability divergence. |
| **Multi-proof** | Solidity is single-proof only. | Documented non-goal. |
| **Feature coupling** | Prover and verifier must be built with matching `truncated-challenges` / `fewer-point-sets` / `single-h-commitment`. A mismatch changes the proof length and is caught by the length pin — fails closed, but with no diagnostic. | Feeds **L-8**. |

## 2.4 Two latent codegen divergences (inert for this VK)

- **Permutation `z_last` query order.** Rust emits all `(x, z_i)`/`(ωx, z_i)` pairs first, then the `x_last` queries in **reverse** set order. The generator emits `Cur, Next, Last` interleaved per set in forward order. For this VK the resulting point-set structure is identical, because no new rotation and no new commitment is introduced between the two placements — I traced it. It is **not** an order-insensitive transformation in general.
- **Fixed-eval counting.** Rust reads `num_fixed_columns − num_simple_selectors` (column-based); the generator counts non-simple *queries*. Both equal 17 here. A circuit with a rotated fixed query would make Rust under-read and Solidity over-read.

Neither is a live bug. Both should become explicit generator assertions rather than accidents.

## 2.5 What could not be verified against the reference

1. **The accumulator path has no Rust counterpart** in `midfall/proofs` — decoding, the second pairing equation and the randomised batching are all application-level (`midnight-circuits` / Moonlight). The construction is internally sound, but the *orientation contract* (that instances 11–14 are the `[s]`-side and 15–18 the `[1]`-side, matching what the producing circuit exposes) is an assumption. Getting it backwards breaks completeness, not soundness.
2. **`vk_digest = 0x56c0824f…4f66`** cannot be recomputed without the concrete `ConstraintSystem`.
3. **`NEG_S_G2_BASE`** cannot be checked without the ceremony transcript → **H-1**.
4. **The quotient VM bytecode's arithmetic content.** All *structural* properties were verified — 49 identities in the right order, correct `y` exponents, every operand pointer landing inside the absorbed-evaluation window `[0x9480, 0xb140)`, constant-table indices within the 178-word reservation, clean termination. What was not verified is that the ~29 emitted gate expressions encode the intended circuit; that needs the circuit definition.
5. **Upstream `construct_intermediate_sets`** (`src/poly/kzg/utils.rs`) was not available; the generator's re-implementation could only be checked for internal consistency. Note the generator's own caveat: it groups commitments **by memory pointer** where Rust groups **by value**, which is only safe under the single-committed-instance restriction.

---

# Part III — Findings

Severity reflects impact on the *deployed system*, not on the Solidity in isolation. Line references without a filename are `Halo2Verifier.sol`.

---

## H-1 — High — `NEG_S_G2_BASE` is unverifiable trusted-setup material with no ceremony binding and no build-time consistency check

**Where:** VK contract lines 88–95 (`neg_s_g2_*`); generator `src/lowering/vk.rs:93-98`.

```rust
let g1_pt: G1Affine = G1Affine::generator();
let g2_pt: G2Affine = self.params.g2().to_affine();
let neg_s_g2_pt: G2Affine = (-self.params.s_g2()).to_affine();
```

`neg_s_g2` is taken verbatim from whatever `params` the generator was handed. The G1 side **is** defended — `vk.rs:81-92` asserts `sum(g_lagrange) == G1Affine::generator()` with a good comment explaining why. There is no analogous check on the G2 side:

- nothing asserts `params.g2() == G2Affine::generator()`;
- nothing checks that `s_g2` corresponds to the *same* τ that produced `g_lagrange`;
- nothing binds either point to a named ceremony transcript;
- no SRS file hash, ceremony id or transcript URL is recorded anywhere. `CODEGEN_ASSURANCE_DOSSIER.md:46` lists "SRS assumption | Midnight SRS asset names, sizes, and expected source" as a **required manifest record**; no such record exists. The only provenance is a URL in `README.md:192` and `SRS_DIR=…/zk_stdlib/examples/assets` in the fixture README.

**What I could verify:** `G1_BASE` and `G2_BASE` are exactly the canonical BLS12-381 generators. `NEG_S_G2_BASE` is a valid on-curve point of E′(Fp2) with `b = 4(1+i)`, in the r-order subgroup, and is not ±G₂. That is the limit of what is checkable without the transcript.

**Failure scenario.** An attacker substitutes the SRS file in `SRS_DIR` with one whose τ they know — or a build host is compromised. The generator emits `neg_s_g2 = −[τ_evil]G₂`. Every downstream control passes: `certify_quotient_program`, `certify_quotient_builds_agree`, `validate_generator_invariants`, the codehash pin, the trace differential, the replay fixture. All of them check *self-consistency*, and the artefact is perfectly self-consistent. The attacker then forges KZG openings for arbitrary statements and `verifyProof` returns `true`. Nothing on-chain or at build time detects it.

**Remediation** (all implementable with the API already in use):

1. `assert_eq!(self.params.g2().to_affine(), G2Affine::generator())`.
2. Add a build-time SRS pairing consistency check: commit the polynomial `f(X) = X` in the Lagrange basis (`Σ ωⁱ·L_i`, from the `g_lagrange` the generator already consumes) to obtain `[τ]G1`, then assert `e([τ]G1, G2) == e(G1, s_g2)`. This proves `neg_s_g2` is the negation of the same τ that generated the commitment basis.
3. Pin the SRS by SHA-256 in the generator; record it and the ceremony transcript reference in the artefact manifest; fail the render on mismatch.
4. Publish `neg_s_g2` alongside the ceremony's published τ point so a third party can verify the negation independently.

Patch **P11** implements (1) and (2).

---

## M-1 — Medium — `assembly ("memory-safe")` is factually false, and the invariant that protects it is enforced only outside the artefact, under a floating pragma

**Where:** lines 203, 336, 345 (the annotations); lines 58–59 (`TRANSCRIPT_MPTR = RETURN_MPTR = 0x1000`); first write at line 463. Template: `templates/contracts/Halo2Verifier.sol:2,98`.

All three assembly blocks are annotated `("memory-safe")` but write to absolute addresses (`0x1000 … 0xe340`) never derived from the free-memory pointer. The generator's own documentation admits it (`docs/architecture/MEMORY_LAYOUT.md`, "Solidity Memory Model Boundary"):

> "…also factually untrue … The annotation is what enables solc's stack-to-memory mover, which reserves spill slots upward from `0x80` … Observed reservations range from `0x80` (none) to `0x8e0`."

The mitigation lives entirely **outside** the shipped artefact: a generator-side test, `compiled_memoryguard_does_not_overlap_generated_layout`. The `.sol` has no runtime assertion, and the pragma is floating (`^0.8.24`), so a downstream integrator recompiling with a different solc release, `--via-ir` setting or optimiser schedule can move the reservation with no signal.

**Measured headroom.** I compiled the artefact across four compiler versions and extracted the runtime prologue's `mstore(0x40, X)`:

| solc | viaIR | runs | runtime bytes | FMP init | headroom to `0x1000` |
| --- | --- | --- | --- | --- | --- |
| 0.8.24 | true | 1 | 29,567 | `0x8c0` | 1,856 B |
| 0.8.26 | true | 1 | 21,295 | `0x8e0` | 1,824 B |
| 0.8.28 | true | 1 | 21,286 | `0x8e0` | 1,824 B |
| 0.8.30 | true | 1 | **21,286** | `0x8e0` | 1,824 B |
| 0.8.30 | true | 200 | 21,318 | `0x8e0` | 1,824 B |
| 0.8.30 | true | 100000 | 29,836 | `0x8e0` | 1,824 B |

So the reservation **does vary with compiler version** (`0x8c0` vs `0x8e0`) — the invariant is not a fixed quantity — and the surviving margin is 57 words, unmonitored at runtime.

**Failure scenario.** Compile with a solc/optimiser combination whose stack-limit evader reserves ≥ `0xF80` bytes. The prologue then emits `mstore(0x40, X)` with `X > 0x1000` and a live Yul spill slot sits at ≥ `0x1000`. The first transcript write — `mstore(TRANSCRIPT_MPTR, h0)` at line 463, or `calldatacopy(buf_len, cptr, 0x80)` at line 453 — overwrites it. If the clobbered local is `success` (line 974) or `proof_cptr` (line 1155), the terminal checks at 1395 / 3666 / 3678 read attacker-influenced garbage.

**A second, immediately concrete consequence.** The floating pragma is not merely theoretical. I compiled and attempted deployment under `revm` Prague:

```
solc 0.8.24 runs=1     : DEPLOY FAILED -- HALT CreateContractSizeLimit   (29,567 B > 24,576)
solc 0.8.30 runs=1e5   : DEPLOY FAILED -- HALT CreateContractSizeLimit   (29,836 B > 24,576)
solc 0.8.30 runs=1     : DEPLOYED
```

**The contract as shipped is undeployable at the minimum compiler version its own pragma permits.** `^0.8.24` advertises compatibility the artefact does not have.

**Remediation.** Two lines, both cheap:

```solidity
pragma solidity 0.8.30;                                    // pin exactly
```
```yul
if gt(mload(0x40), TRANSCRIPT_MPTR) { revert(0, 0) }       // ~6 gas, once
```

The guard makes the invariant self-enforcing in the deployed bytecode instead of depending on a test in another repository. Patches **P2** and **P3**.

*Related:* the constructor's `require_eip2537_precompiles()` runs in the **creation** frame under the same false annotation and writes `0x1000`–`0xe200`, but the generator's guard test inspects only the *runtime* prologue (`src/evm.rs:233-268` is explicitly typed for runtime). Fail-closed in practice (a corrupted `authorizedVk` spill would fail the codehash `require`), but the asymmetry looks unintended. Also: the shipped comments at lines 316–317 and 347 claim "generated scratch starts at `0x80`", contradicting `TRANSCRIPT_MPTR = 0x1000` on line 58 — this is precisely the stale belief the team's own TA-5 finding identified as the hazard, and it is hardcoded in the template so **every** render ships it (**I-1**).

---

## M-2 — Medium — A malformed curve point burns ≈63/64 of the supplied gas instead of reverting cheaply

**Where:** every `staticcall(gas(), 0x0c, …)` — lines 911, 956, 3558, 3573, 3584, 3629, 3643 — and the deferred-validation policy documented at lines 425–429.

Because `common_uncompressed_g1` deliberately does **not** run a curve check (§2.3), an invalid point survives until it reaches a `G1MSM`. EIP-2537 precompiles that reject their input **consume all gas forwarded to them**, and `staticcall(gas(), …)` forwards 63/64 of what remains.

**Measured** (revm Prague, single flipped byte in `advice[0].x_lo`):

| tx gas limit | off-curve point | invalid evaluation | bad EIP-2537 pad | valid proof |
| --- | --- | --- | --- | --- |
| 2,000,000 | **1,979,170** | 1,279,485 | 315,950 | — |
| 5,000,000 | **4,932,295** | 1,279,485 | 315,950 | — |
| 30,000,000 | **29,541,670** | 1,279,485 | 315,950 | — |
| 500,000,000 | **492,197,920** | 1,279,485 | 315,950 | 1,279,482 |

A cryptographically-invalid proof costs a bounded 1.28M. A structurally-malformed one costs 316k. But a proof containing **one byte** that puts a point off-curve costs whatever you were willing to spend — 98.5% of it, at zero marginal cost to the person who chose that byte.

**Failure scenario.** Any component that pays gas on someone else's behalf or continues after a failed verification:

- A relayer / paymaster / ERC-4337 bundler submitting user proofs pays 30M instead of 1.3M — a 23× amplification, chosen by the user, per transaction.
- A wrapper doing `try verifier.verifyProof(…) { } catch { }` regains control with 1/64 of the gas, almost certainly too little to finish, so the whole transaction reverts anyway — the `catch` branch becomes unreachable in practice.
- A batch verifier looping over N proofs is destroyed by one bad point in the first.

**Remediation.** Cap the gas forwarded to the validating calls. EIP-2537 `G1MSM` pricing is a pure function of input length (`k · 12000 · discount[k] / 1000`), with no data dependence, so an **exact** constant is computable at codegen time; a 2× margin absorbs any schedule change:

```yul
// was: staticcall(gas(), 0x0c, ptr, len, out, 0x80)
staticcall(G1MSM_GAS_78, 0x0c, ptr, len, out, 0x80)
```

This turns a 30M burn into a bounded ~1M. Patch **P1**. Note the cap must be generous and codegen-derived — a hand-tuned value that is too tight becomes a liveness bug on a chain with a different schedule.

---

## M-3 — Medium — The deployment probe is weakest exactly where acceptance is decided

**Where:** lines 202–286 (`require_eip2537_precompiles`); template `PrecompileSmoke.sol`.

The smoke test hardens `G1ADD` with a known-answer vector and states the reasoning explicitly and correctly (lines 229–238):

> "Every probe above uses the point at infinity, which is exactly the input an implementation gets right without doing any curve arithmetic — a precompile that returns its zero-filled input, or zeros for anything, satisfies them… So add one vector whose answer a stub cannot guess."

That reasoning was **not applied to the two precompiles that decide the outcome**:

- **`0x0f` PAIRING_CHECK** (line 282) is probed only as `PAIRING_CHECK([(0,0),(0,0)]) == 1`. A chain whose `0x0f` returns `1` unconditionally, or omits G2 subgroup checks, passes deployment and then accepts **every** proof — `ec_pairing` is the sole accept gate.
- **`0x0c` G1MSM** (line 272) is probed with `0x30c0` bytes of all-zero terms. Line 270 says "the production verifier uses G1MSM… **as the subgroup validator** for absorbed proof points" — and then tests it with 78 identity terms, exercising no rejection behaviour at all.

The team already found this. `AUDIT.md` **TA-6, "Precompile Smoke Tests Are Too Weak For Deployment Confidence"**, is rated **Low**, carries **no `Status:` line** (it is un-triaged — every other TA item has one), and recommends exactly: known-valid and known-invalid pairing equations, invalid G1/G2 encodings that must fail, and boundary scalars `0, 1, r−1, r`. None are present. `ARCHITECTURE_REVIEW_2026-08.md` §7 concedes the residual state: *"EIP-2537 semantics (incl. subgroup checks) | Assumed per spec; constructor smoke proves existence/arithmetic, not rejection behavior | **Assumed**"*.

**Verified good:** the strict `returndatasize()` checks do make the verifier fail closed on a chain **without** EIP-2537 — a staticcall to an empty account succeeds with `returndatasize() == 0`. I confirmed this: the constructor reverts under `SpecId::CANCUN`, `SHANGHAI` and `MERGE`. So *existence* is genuinely proven; *correctness* is not.

**Remediation.** Add constant-size known-answer probes (deployment-gas cost only): a true pairing `e(G,G₂)·e(−G,G₂) == 1`, a **false** pairing `e(G,G₂)·e(G,G₂) == 0`, a `G1MSM` known answer `[2]·G == 2G`, and a negative probe with a known wrong-subgroup encoding that must cause the precompile to fail. Give TA-6 a `Status:` and re-rate it — with the whole accept path resting on `0x0f`, Low is too low. Patch **P5**.

---

## M-4 — Medium — `vk_digest` does not cover the SRS points, the quotient program, the accumulator schema, or the feature profile

**Where:** `../proofs/src/plonk/mod.rs:246-277`; line 1091 (absorption); lines 1018–1023 (header cross-check). Team's own finding: `AUDIT.md` TA-2, and item 2 of their "Time-Boxed Audit Priorities Before Production".

`transcript_repr` hashes `VERSION`, `k`, fixed commitments, permutation commitments, and the `Debug` strings of `domain.pinned()` / `cs.pinned()`. It does **not** cover `G1_BASE` / `G2_BASE` / `NEG_S_G2_BASE`, the quotient VM constant pool or bytecode, the accumulator schema, or the Cargo feature profile (`truncated-challenges`, `outer-fewer-point-sets`, `outer-single-h-commitment`). The transcript therefore does not bind them.

The on-chain header cross-check covers 6 of 31 header words (`num_instances`, `k`, `has_accumulator`, `acc_offset`, `num_acc_limbs`, `num_acc_limb_bits`). `vk_digest`, `n_inv`, `omega`, `omega_inv`, `omega_inv_to_l` and all three base points are not cross-checked. Codehash pinning makes this non-exploitable post-deploy, but the comment's claim that these checks "catch generator drift" is narrower than it reads.

**On the wrong-VK question specifically:** a wrong-but-well-formed VK **cannot** be paired with this verifier — the constructor reverts on codehash mismatch, and the loader re-checks on every proof. I confirmed both empirically (a 1-bit-mutated VK and an EOA address both revert the constructor). But a VK generated from a *different SRS or feature profile* for the same circuit produces a self-consistent verifier+VK pair that no digest distinguishes. That residual compounds H-1 and L-8.

**Remediation.** Absorb `EXPECTED_VK_CODEHASH` into the transcript, or redefine `vk_digest` over the full runtime payload — the team's own TA-2 recommendation, still open.

---

## M-5 — Medium — The build is not reproducible as documented

**Where:** `fixtures/moonlight-wrap/README.md:17`, `docs/audit/REVIEW_PACKET.md:60-84`, `docs/audit/CODEGEN_ASSURANCE_DOSSIER.md:34-47`, `src/evm.rs:179-183,208`, `tests/ivc_accumulator_replay.rs:55`, `scripts/install_pinned_solc.sh:29-34`.

Three mutually unreconcilable provenance stamps exist for this artefact:

| Source | Stamp |
| --- | --- |
| `fixtures/moonlight-wrap/README.md:17` | solidity-verifier commit `3fb6d84` |
| `REVIEW_PACKET.md:67` | repository commit `a096e71746e401404f250817ca4e857bac1eef56` |
| `CODEGEN_ASSURANCE_DOSSIER.md:36` | Midfall revision `53dc872f495104046d96bdac0a690f903dc0c537` |

> Correction (2026-08-12): the three stamps are not actually contradictory —
> they index different things (fixture-render commit of this repo, packet-time
> commit of this repo, and the Midfall *dependency* revision). They were
> merely unlabeled. Each source now says which identity it records; the
> canonical table is "Provenance Identities" in
> `docs/reference/REPRODUCIBLE_BUILDS.md`. (This row's dossier citation was
> also off by one — `:37` → `:36`.)

`REVIEW_PACKET.md` §4 "Artifact Manifest" — the table meant to pin *this* artefact — reads `fill per artifact` for all eleven hash rows. `docs/reference/REPRODUCIBLE_BUILDS.md`, cited from three places as where the hashes live, was not in scope.

The recorded solc flag list is also incomplete. Both the dossier (`:40`) and the packet (`:71`) record `--bin --optimize --via-ir --evm-version cancun --no-cbor-metadata` — **`--optimize-runs` is missing**. `src/evm.rs:179-183` reads it from the environment (`SOLC_OPTIMIZE_RUNS`, default `200`), while the one test that exercises this fixture pins a *different* value (`tests/ivc_accumulator_replay.rs:55: const SOLC_OPTIMIZE_RUNS: u32 = 1`).

**This is not cosmetic.** As measured under M-1, the setting is load-bearing for *deployability*: at `runs=100000` the runtime is 29,836 bytes and the deployment halts with `CreateContractSizeLimit`. A "reproducible" build whose success depends on an unrecorded environment variable is not reproducible.

Separately, `install_pinned_solc.sh` downloads the compiler over HTTPS and validates it only by its own `--version` output, which a substituted binary forges trivially. `binaries.soliditylang.org` publishes SHA-256 and keccak-256 for every release in `list.json`; the script uses neither. For a project whose entire reproducibility claim rests on the string `0.8.30+commit.73712a01`, pinning by version string rather than content hash is the wrong pin. (`Darwin-arm64` also maps to `macosx-amd64`, so Apple Silicon developers run an x86 compiler under Rosetta — a different binary from CI, unchecked.)

**Remediation.** Fill the manifest for the real deployment artefact; add `--optimize-runs <N>` to the recorded flags and remove the env override from the reproducible path; reconcile the three stamps to one; ship `REPRODUCIBLE_BUILDS.md` with the artefact; verify solc by SHA-256. Patch **P13**.

**Credit where due:** the VK half *is* solidly reproducible. Its runtime is pure returned data, so `keccak256(0xfe ‖ payload) = 0xe68d8936…cf52` at length 17,025 is solc- and optimiser-independent. I recomputed it from source and it matches. That is a good design property worth preserving.

---

## L-1 — Low — Codegen certification covers the emitter leg only; the leg that executes on-chain is fixture-sampled

**Where:** `src/lowering/quotient_numerator/vm/certify.rs:129-225`, `vm/reference.rs:20-27`, `src/lowering/plan.rs:167-183`, `tests/ivc_accumulator_replay.rs:18-45`.

The certification is real and unconditional — `LoweringPlan::new` panics the render if `certify_quotient_program` or `certify_quotient_builds_agree` fails, the challenge seed derives from the finalised bytecode + constant table + expression trees + VK payload, and the dual build with recognizers disabled turns every shape recognizer into a checked optimisation. That is better than most generated-verifier projects. Its coverage boundary is narrow, though, and the boundary is where a supply-chain attack would land:

1. **The front end is uncovered.** Certification compares emitted bytecode against the `QuotientExpr` the lowering itself produced. A bug in the halo2-`Expression` → `QuotientExpr` translation is wrong on both sides and agrees with itself. The team identified this exact hazard for *pointers* and built `validate_quotient_mem_ptrs` (`plan.rs:346-348`: *"certification cannot do this: it compares the bytecode against the expression tree, so a pointer that is wrong in both agrees with itself"*) — but not for expressions.
2. **Native kernels are uncovered.** `NATIVE_PERMUTATION` / `NATIVE_LOOKUP` / `NATIVE_IDENTITY` are checked only for stream position (`certify.rs:180`: *"Native markers carry no arithmetic here."*). The permutation and LogUp kernels are trusted code.
3. **The on-chain Yul VM is uncovered.** `reference.rs:20-27` scopes it explicitly: the reference-interpreter → Yul leg is covered "by the opcode and memory-token table conformance tests and by the per-identity Rust/Solidity trace differential on fixture circuits". §7 adds: *"an opcode no fixture emits has unverified runtime semantics."*

**Direct answer to "could a malicious edit produce an accepting verifier that still passes the repo's own tests": yes.** Edit `templates/partials/quotient_numerator/*.yul` or a native kernel. `certify` never touches Yul. The SRS-free replay test compiles **committed pre-rendered `.sol` from the fixture directory**, not fresh template output — its own header says so: *"the replay keeps passing after a codegen change — it just stops testing current output."* The only gate that would catch it is the SRS-gated trace differential, which per §10 runs weekly / on push-to-main, not in the default CI job.

**Remediation.** Pin a digest of the `templates/` tree as a constant checked by a CI test, so any template edit forces an explicit fixture re-render and README commit-stamp bump. Needs no SRS. Longer term: extend certification to the front end by evaluating `vk.cs()` expressions directly at the same challenge assignment, and add a native-kernel differential independent of fixture coverage. Patch **P14**.

---

## L-2 — Low — Committed-instance commitment hard-wired to the identity; one MSM term silently omitted while the emitted comment claims otherwise

**Where:** lines 1101–1111 (128 zero bytes absorbed); line 3023 (`// q_eval_set[0]: 43 commitment(s)`); lines 3397–3399 (the MSM skips `x1^1`). Generator: `src/lowering/encoding/mod.rs:255-258, 409-415`.

The eval side computes `q_eval_set_0 = Σ_{i=0..42} x1ⁱ · eval[table[i]]` — 43 terms. The commitment side materialises only 42: line 3397 stores scalar `1`, then line 3399 jumps straight to `x1^2`. The orphaned eval is `table[1] = REVERSED_EVALS[0] = 0x9480`, the committed-instance column's evaluation. The omission is consistent with `committed_pi = G1Affine::identity()` (an identity commitment contributes nothing to an MSM), but **no comment, constant or runtime check states it**, and the emitted comment on line 3023 actively contradicts the emitted code.

**Empirically confirmed sound as rendered.** In the fixture, `eval[0] = 0x0000…0000`. Setting it to any other value is rejected (test N4, reject at 1,279,485 gas — i.e. it runs to the pairing and fails there). This is exactly the expected behaviour: with an identity commitment the batch check pins the claimed opening to zero, and `x1^1 ≠ 0`, so the column is fully constrained. Omitting the identity term from the MSM is a gas optimisation, not a soundness gap.

**The risk is drift, not the current render.** If a future render ever needs a non-identity committed-instance commitment, this verifier would keep hashing 128 zero bytes and keep omitting the term, verifying the wrong statement with no runtime signal. The counts (43 vs 42), the exponent multiset, and the `0x30c0` MSM length are all independently hardcoded, so the discrepancy is invisible to every existing check.

**Remediation.** Either emit the identity term explicitly (`G1_IDENTITY_MPTR` at line 144 exists for exactly this and is currently unused — dead), or add a generator invariant asserting that per point set the multiset of `x1` exponents in the MSM equals `{0 … m−1}` minus exactly the indices of commitments *proven* to be the identity, and render a comment naming the omitted index. Patch **P7**.

---

## L-3 — Low — 41 bare `revert(0, 0)` sites; `verifyProof` can never return `false`

**Where:** 41 sites including 212, 338, 367, 439, 610, 1007, 1024, 1048, 1064, 1133, 1316, 1369, 1395, 1482, 2620, 3666, 3678. The only reason-carrying failure is the constructor's `require(…, "invalid vk")`.

At the call site, "malformed calldata shape" (338), "VK code changed under us" (1007), "non-canonical instance" (1133), "bad proof" (3666) and out-of-gas are all indistinguishable — empty returndata. That materially degrades incident response: you cannot tell a VK swap from a bad proof.

Separately, line 3679 unconditionally stores `1`, so `verifyProof` returns `true` or reverts; it never returns `false` despite `returns (bool)`. This is documented at line 324, but integrators writing the idiomatic `if (!verifier.verifyProof(p, i)) { … }` get a bubbled empty revert rather than the false branch.

**Remediation.** Give each failure class a 4-byte custom-error selector — `mstore(0x00, shl(224, sel)); revert(0x00, 0x04)` — writing at `0x00`/`0x04` is legitimate scratch and does not disturb the layout. At minimum distinguish ABI-shape, VK-mismatch, canonicality, precompile-failure and pairing-failure. Patch **P4**.

---

## L-4 — Low — The exact-`calldatasize` pin makes the verifier uncallable through calldata-appending relayers

**Where:** lines 1042–1045 (`calldatasize() == 0x2144`).

The check is correct and fail-closed, but it means the verifier cannot be called through anything that appends calldata: ERC-2771 trusted forwarders append the 20-byte original sender; several relayer, multicall and paymaster patterns append context words. Confirmed empirically — test N25 (20 appended bytes) reverts, as does N24 (32 appended zero bytes).

The four other pins (head words at 337, proof length at 1037, instance count at 1038, terminal `proof_cptr == NUM_INSTANCE_CPTR` at 1395) already make trailing bytes unreadable by the parser, so relaxing to `>=` loses nothing. Either relax it, or state the constraint in the `verifyProof` NatSpec — right now an integrator hits an empty revert with no diagnostic (see L-3).

---

## L-5 — Low — `CHALLENGE_MPTR` aliases `THETA_MPTR`

**Where:** line 83 (`CHALLENGE_MPTR = 0x7900`), line 89 (`THETA_MPTR = 0x7900`), line 1178. Template `TranscriptProofParser.yul:127`, `Constants.sol:66`.

Inert here: this circuit has zero user-phase challenges, so the template's per-phase squeeze loop rendered nothing, and `CHALLENGE_MPTR` is referenced only by its own declaration.

**For any circuit with ≥ 1 user-phase challenge**, the template emits `squeeze_to(buf_len, add(CHALLENGE_MPTR, 0x0))` → writes `0x7900`; line 1178 then unconditionally does `squeeze_to(buf_len, THETA_MPTR)` → overwrites `0x7900`. Every later read of the user challenge silently returns theta. The transcript still matches the prover (the squeezes happen in order), so the proof simply fails to verify — a permanent, silent liveness break; and if a gate happens to be satisfied under the substitution, a soundness break.

**Remediation.** Give `CHALLENGE_MPTR` its own window and add a planner assertion that the challenge window and the theta-window slots do not intersect. Patch **P8**.

---

## L-6 — Low — Quotient-VM operands are unvalidated raw memory pointers

**Where:** `q_ptr := shr(240, mload(q_pc))` at 1798, 1832, 1839, 1885, 1931; `and(shr(232, q_word), 0xffff)` at 1919, 1937, 1981; `q_sel_idx` / `q_sel_gap` at 2628–2648; stack arithmetic at 1801, 1811, 1910.

Every operand is a `u8`/`u16` used directly as a memory address (`mload(q_ptr)`, `mload(add(q_const_mptr, shl(5, qconst)))`, `mstore(add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx)))`) with no bound check. `q_sel_gap` is 16 bits but the y-power table holds only 49 entries, so `gap > 48` reads into the VM stack region. `case 0x06` does `q_sp := sub(q_sp, 0x20)` with no underflow guard, and the terminal `eq(q_sp, 0xb8e0)` check does **not** catch a *balanced* underflow.

None of this is attacker-reachable today: the program lives in the codehash-pinned VK payload, and I confirmed no code path writes into `0x3680…0x7900` after the `extcodecopy`. The safety argument is entirely "the emitter never produces such a program" — there is no on-chain validator. **This becomes Critical if the VK is ever made upgradeable or parameterised.**

**Remediation.** Clamp operands at decode time (~10 gas each): `if or(lt(q_ptr, 0x9480), gt(q_ptr, 0xb140)) { revert(0,0) }`; `q_sel_gap < 49`; `q_sel_idx < 10`; `if lt(q_sp, 0xb900) { revert(0,0) }` before the `sub`. Patch **P12**.

---

## L-7 — Low — Zero-slack memory adjacencies; `batch_invert` scratch would corrupt silently

**Where:** lines 486–599, 1431; `BATCH_INV_SCRATCH_MPTR = 0xb140`, `LAGRANGE_DENOMS_MPTR = 0xb580`.

I recomputed all of these; every one is exactly correct and every one has **zero** slack:

- With the 30 Lagrange inputs, `batch_invert`'s forward pass writes 28 prefix products to `0xb140…0xb4c0` and the modexp frame to `0xb4c0…0xb580` — ending *exactly* at `LAGRANGE_DENOMS_MPTR`. One more denominator and the frame's first word (the literal `0x20` base-length) overwrites `denominator[0]`; the backward pass then reads it and produces silently wrong inverses **with no revert** — the modexp still succeeds and `ret` stays 1.
- VK payload `0x3680 + 0x4280 = 0x7900` = `CHALLENGE_MPTR` exactly.
- `REVERSED_EVALS 0x9480 + 0xcc0 = 0xa140` = `ADVICE_COMMS_MPTR_BASE` exactly.
- The proof-commitment regions chain exactly to `0xb140`.
- Fused MSM `0xb280 + 0x30c0 = 0xe340` exactly.

The `batch_invert` case is the dangerous one because it fails *silently*. Add an explicit planner assertion `scratch_len >= (n−2)·32 + 0xc0`. Patch **P9**.

*(I also hand-verified `batch_invert`'s algorithm for n = 2, 3, 4 and 30 — the prefix/backward-pass indexing is correct, and the one-past-the-end `gp_mptr` decrement in the final iteration is computed but never dereferenced.)*

---

## L-8 — Low — No on-chain provenance

**Where:** artefact-wide; `src/evm.rs:208` (`--no-cbor-metadata`); `ARCHITECTURE_REVIEW_2026-08.md` §8: *"Feature flags ↔ expected proof schema | **Recorded nowhere in the artifact**"*.

Nothing in the deployed runtime identifies the generator commit, the feature profile, the circuit, or the SRS. CBOR metadata is stripped, so Sourcify/Etherscan metadata matching is unavailable and source verification requires exact-flag recompilation — which M-5 shows is not fully specified.

Proof-schema mismatches fail closed (rejected proofs, not accepted ones), so this is an incident-response problem rather than a soundness one. But during an incident, "which of our deployed verifiers has the affected codegen?" is unanswerable from chain state.

**Remediation.** Emit `bytes32 public immutable BUILD_ID = H(generator_commit ‖ feature_list ‖ vk_digest ‖ EXPECTED_VK_CODEHASH ‖ srs_hash)`. One immutable, zero runtime cost on the verify path, and fleet inventory becomes mechanical. Patch **P10**.

---

## L-9 — Low — No incident-response story, and no domain binding

**Where:** artefact (zero `sstore` / `delegatecall` / `selfdestruct` / owner / pause / upgrade); line 1091; `AUDIT.md` TA-8, F-4.

Immutability is the right call here: no admin key means no admin-key compromise, and `verifyProof` stays `external view`. Deploy ordering is enforced fail-closed (VK first; a wrong VK reverts the constructor — confirmed empirically). Two consequences are undocumented:

**(a) Incident response.** If a soundness bug is found post-deployment there is no on-chain mitigation whatsoever. The only lever is the application wrapper. Nothing in the repo states the corollary requirement: **every wrapper must hold the verifier behind a replaceable address and must have its own pause.** A wrapper that hardcodes the verifier as `immutable` or `constant` has no recovery path at all. This belongs in the generated NatSpec.

**(b) Cross-chain / cross-deployment replay.** The transcript begins at `vk_digest`. There is no `chainid`, no verifier address, no domain separator anywhere. A proof valid against this bytecode is valid against **every** deployment of this bytecode on **every** chain, forever. The NatSpec does tell wrappers to bind chain/domain — the right architectural split for a raw verifier — but a deployer who treats `verifyProof == true` as authorisation has an unconditional cross-chain replay.

---

---

## Informational

**I-1 — Comments contradict constants.** Lines 316–317 and 347 claim "generated scratch starts at `0x80`"; line 58 says `TRANSCRIPT_MPTR = 0x1000`. Hardcoded in `templates/contracts/Halo2Verifier.sol:54-59,98-99`, so every render ships it. Both also cite `docs/MEMORY_LAYOUT.md`; the real path is `docs/architecture/MEMORY_LAYOUT.md`. This is exactly the stale belief TA-5 identified as the hazard. Patch **P6**.

**I-2 — Dead code and contradictory documentation.** `QUOTIENT_RETURN_MPTR` (154), `Q_COM_MPTR` (132), `G1_IDENTITY_MPTR` (144, whose comment describes "the four `mload`s below" that do not exist), `TRACE_U256_MPTR` (160) are all declared and never used. `X_N_MINUS_1_INV_MPTR` is written at 1475 and never read. The `r` parameter of `validate_public_accumulator` (869) is never used in the body. The VM opcode table (1765–1776) documents ~22 opcodes; 11 are implemented — `FOLD_MAIN (0x0a)` and `MUL (0x07)` are described in prose but have no `case`. The constructor's MSM smoke window (`0xb140…0xe200`) differs from the production window (`0xb280…0xe340`); same length, different base, so it does not pre-expand the actual range despite the comment's claim.

**I-3 — Unreachable defensive branch.** `load_acc_point` lines 830–839 handle "x carried the identity flag but the whole-point sentinel did not match". Given the packing check makes the codec a bijection, `x_is_id` implies x's words are exactly the canonical identity words, and requiring `y` to decode to zero implies y's words are too — so `is_acc_encoded_identity` would already have returned true. Harmless defensive dead code; worth a comment saying so rather than leaving a reader to derive it.

**I-4 — The audit chain's evidence map points at a source tree that no longer exists.** `CODEGEN_ASSURANCE_DOSSIER.md:57-65` maps every checkpoint to `src/codegen/protocol.rs`, `src/codegen/evaluator.rs`, `src/codegen/pcs.rs`, `src/transcript.rs` and `templates/partials/quotient_numerator/QuotientNumeratorBlock.yul`. **None of the Rust paths exist.** The tree is `src/lowering/*`. (Correction
2026-08-12: this finding itself overreached on one item —
`templates/partials/quotient_numerator/QuotientNumeratorBlock.yul` DOES exist,
alongside `QuotientHelpers.yul`; the dossier row citing it was correct.) `AUDIT_FINDINGS.md`'s "Files reviewed (deep read)" list is entirely `src/codegen/*`; finding M1 anchors at `src/codegen/util.rs:443-448`. `ARCHITECTURE_REVIEW_2026-08.md` §11 concedes the drift and defers to a companion assessment that was not in scope. Consequence: the ~20 findings marked "Fixed with named tests" in the 2026-05-11 addendum could not be re-verified against the current tree.

**I-5 — No transcript domain separation.** The Keccak transcript is a bare `keccak256` over concatenated raw bytes, matching Rust. This is weaker than the Blake2b transcript in the same file, which uses a personalisation string plus `COMMON`/`CHALLENGE` byte tags. Not exploitable here — every absorb is fixed-length and every count is pinned and re-checked, so no two distinct valid inputs produce the same byte stream, and `vk_digest` provides cross-circuit separation. A missing defence-in-depth layer, not a vulnerability.

**I-6 — Two latent codegen divergences.** See §2.4 — permutation `z_last` query order, and column-vs-query fixed-eval counting. Inert for this VK; should be explicit assertions.

**I-7 — The accumulator batching randomiser is not bound to `vk_digest`.** `alpha = keccak256("pairing-batch-acc-kzg" ‖ 4 G1 points)` (line 3612). Sound as-is — the four points transitively commit to everything, and `alpha` is drawn after they are final. Including `vk_digest` in the preimage is free and would make the binding local rather than transitive.

---

## Prior-findings hygiene

| ID | Claim | Verdict against this artefact |
| --- | --- | --- |
| 2026-05-06 #1 | VK codehash only checked in constructor | **Closed.** Re-checked per proof, lines 1004–1007. Confirmed empirically. |
| F-4.1 | Pathological `num_limb_bits` from VK | **Closed.** Header cross-check hardcodes 56/7. |
| F-4.2 | Dead `if and(eq(coord,1), 0)` branches | **Closed.** Absent. |
| F-6 | `delta` literal only checked off-line | **Value verified** (`0x8634d0aa…189d7` is the correct `Fr::DELTA`), but still a bare literal — the "nothing in the build forces a check" complaint stands. |
| TA-4 / F-3 | Gas checkpoints in production | **Closed.** Zero LOG opcodes; `external view`; single terminal return. |
| TA-5 | False `memory-safe` annotation | **Consequence removed** (layout at `0x1000`); annotation still false; guard is runtime-only; shipped comments still say `0x80`. → **M-1**, **I-1**. |
| TA-5 rec. | "Use `pragma solidity 0.8.24;` or the exact version tested" | **Not done.** Both artefacts still carry `^0.8.24` while the pinned compiler is 0.8.30 — and 0.8.24 does not produce a deployable contract. → **M-1**. |
| TA-2 / priority #2 | Define and test `vk_digest` coverage | **Open.** → **M-4**. |
| TA-6 | Precompile smoke tests too weak | **Partially addressed** (G1ADD known-answer only); no `Status:` line; pairing/G1MSM recommendations unimplemented. → **M-3**. |
| TA-7 | Zero-denominator / root-of-unity cases | **No status recorded.** The code does fail closed (verified), but the recommended forced-challenge negative tests were not found. |
| TA-8 / F-4 | Raw verifier binds no application semantics | **Documented** in NatSpec, correctly. Residual: no incident-response/migration guidance. → **L-9**. |
| 2026-05-11 #9 | Identity committed-instance policy | **Accepted restriction**, correctly scoped. → **L-2**. |
| 2026-05-11 #1–#8, #10; M1, M2 | Various, marked Fixed | **Could not re-verify** — anchors point at `src/codegen/*`, which no longer exists. → **I-4**. |

---

# Part IV — Improvements

Grouped by the axes you asked about. Items marked **[P*n*]** have a corresponding diff in the patch set.

## 4.1 Readability

The code is already unusually well commented — the comments explain *why*, not *what*, and several of them (the `first_adjust` bitwise-vs-arithmetic note at 660–665, the `batch_invert` early-`leave` rationale at 575–579, the pairing LHS/RHS naming inversion at 3653–3665) are exactly the kind of thing that saves a reviewer an hour. Keep that. The problems are specific:

1. **Comments that contradict the code must go.** The `0x80` claim (316–317, 347) is worse than no comment: it asserts the property that TA-5 was about, and asserts it wrongly. Interpolate `{{ memory.low_memory_scratch_start|hex() }}` instead of hardcoding. Fix the `docs/MEMORY_LAYOUT.md` path. **[P6]**
2. **Delete dead constants, or explain them.** `QUOTIENT_RETURN_MPTR`, `Q_COM_MPTR`, `G1_IDENTITY_MPTR`, `TRACE_U256_MPTR`, `X_N_MINUS_1_INV_MPTR`, the unused `r` parameter. `G1_IDENTITY_MPTR`'s comment describing non-existent `mload`s is actively misleading. If they are placeholders for future emitter modes, say so in one line each.
3. **The VM opcode table should list what is implemented.** Documenting 22 opcodes when 11 have `case` arms sends a reviewer looking for handlers that do not exist.
4. **Emitted counts must match emitted code.** Line 3023 says "43 commitment(s)" and emits 42. Whatever the resolution to L-2, the comment and the code have to agree — a generated comment that lies is a defect in the generator. **[P7]**
5. **Name the aliases.** `TRANSCRIPT_MPTR = RETURN_MPTR = QUOTIENT_RETURN_MPTR = 0x1000` and `SELECTOR_ACC_MPTR = BATCH_INV_SCRATCH_MPTR = 0xb140` are correct but invisible. Emit a short "lifetime map" comment block at each alias site stating which phase owns the window and which line the previous owner dies at. A future reader should not have to trace 2,000 lines to establish it, as I did.
6. **Mark the unreachable branch.** `load_acc_point` 830–839 is dead by construction; one sentence saying why turns a puzzle into a defence.

## 4.2 Correctness

Nothing found is wrong today. These are the places where correctness rests on something invisible:

1. **Make the memory invariant self-enforcing.** One `if gt(mload(0x40), TRANSCRIPT_MPTR) { revert }`. This is the single highest value-per-byte change in the whole set. **[P2]**
2. **Pin the pragma.** `pragma solidity 0.8.30;`. The current `^0.8.24` claims compatibility that demonstrably does not exist — 0.8.24 produces a 29,567-byte runtime that cannot be deployed. **[P3]**
3. **Assert the `batch_invert` scratch capacity in the planner** rather than relying on the arithmetic landing exactly on `LAGRANGE_DENOMS_MPTR`. This one fails *silently*, which makes it worse than the others. **[P9]**
4. **Turn the two latent codegen divergences into assertions** — permutation `z_last` emission order, and column-vs-query fixed-eval counting. Both are currently "happens to be inert".
5. **Wire the declared generator errors.** `GeneratorError::RotatedInstanceQuery` and `UnsupportedInstanceColumnShape` have `Display` impls but no construction site anywhere in the reviewed tree. Either wire them or delete them — a declared-but-unreachable error reads as a guarantee that is not there.
6. **Fix `CHALLENGE_MPTR`'s aliasing** before any circuit with user-phase challenges is rendered. **[P8]**

## 4.3 Soundness

1. **Bind the SRS.** The build-time pairing check `e([τ]G1, G₂) == e(G1, s_g2)` closes the gap between "the generator emitted what it was given" and "what it was given is the ceremony's key". Plus `assert params.g2() == G2Affine::generator()`. **[P11]**
2. **Extend `vk_digest` coverage**, or absorb `EXPECTED_VK_CODEHASH` into the transcript, so the base points, the quotient program, the accumulator schema and the feature profile are bound rather than merely pinned. (The team's own TA-2.)
3. **Strengthen the deployment probe** with a false-pairing case and a wrong-subgroup rejection case. The current probe proves the precompiles *exist*; the accept decision needs them to be *correct*. **[P5]**
4. **Bound the quotient-VM operands.** Defence in depth today; mandatory the moment the VK stops being immutable. **[P12]**
5. **Assert the committed-instance identity invariant at codegen**, or plumb the commitment through calldata. **[P7]**

## 4.4 Robustness

1. **Cap the gas forwarded to validating precompile calls.** This is the change with real operational impact: it converts an attacker-chosen 30M-gas burn into a bounded ~1M. **[P1]**
2. **Custom errors for every revert class.** Five selectors, ~4 bytes of returndata each, and incident response stops being guesswork. **[P4]**
3. **Relax the `calldatasize` pin to `>=`,** or document the constraint. The other four pins already carry the security property. Today, calling through an ERC-2771 forwarder produces an empty revert that no one will diagnose quickly.
4. **Emit a `BUILD_ID` immutable.** Fleet inventory and incident scoping become mechanical instead of archaeological. **[P10]**
5. **Verify solc by SHA-256, not by version string.** **[P13]**
6. **Pin a `templates/` tree digest in CI.** This is the cheapest possible closure of the L-1 gap: it does not need the SRS, and it forces a template edit to be accompanied by an explicit fixture re-render. **[P14]**
7. **Write the incident-response section.** Wrapper-held replaceable verifier address; wrapper pause; migration means redeploy VK → verifier → repoint every wrapper; wrappers must absorb `block.chainid` and their own address into the statement.

## 4.5 What not to change

Some things that look like smells are correct and should be left alone:

- **The absolute memory layout.** It is why this verifier costs 1.28M rather than 2M+. Guard it (P2); do not rewrite it to use the free-memory pointer.
- **Deferring curve checks to the precompiles.** Implementing on-curve checks for 381-bit coordinates in Yul would be far more expensive and far more error-prone than letting `G1MSM` do it. The right fix for the resulting gas behaviour is the gas cap (P1), not in-Yul validation.
- **Success-or-revert instead of returning `false`.** It is the safer default for a verifier. Just make the reverts distinguishable (P4).
- **Immutability with no admin, no pause, no upgrade.** Correct for a raw verifier. The gap is documentation of the wrapper's obligations, not the design.
- **The randomised accumulator batching.** Multiplying the two pairing equations would have been the obvious and wrong thing to do; this is the right construction, correctly ordered.
- **The VK-as-data contract with an `INVALID` prefix.** Cheap, tamper-evident, and compiler-independent to reproduce.

---

# Part V — Patch set

Diffs are against `midfall/proofs/solidity-verifier`. The generated `.sol` files are build outputs, so every fix belongs in a template or in the generator. Patches are ordered by value-per-line-changed, not by finding severity.

Applicable diffs are in `patches/`. Where a fix needs generator logic rather than a template edit, the diff is a precise sketch with the exact insertion point named.

| Patch | Fixes | Type | Risk |
| --- | --- | --- | --- |
| **P1** | M-2 | gas cap on validating precompile calls | low — needs a codegen-derived constant |
| **P2** | M-1 | runtime free-memory-pointer guard | trivial |
| **P3** | M-1 | pin the pragma | trivial |
| **P4** | L-3 | custom error selectors | mechanical, touches every revert site |
| **P5** | M-3 | strengthen the deployment probe | low; deploy-gas only |
| **P6** | I-1 | fix contradictory comments | trivial |
| **P7** | L-2 | committed-instance invariant + honest comment | generator assertion |
| **P8** | L-5 | un-alias `CHALLENGE_MPTR` | planner change |
| **P9** | L-7 | assert `batch_invert` scratch capacity | planner assertion |
| **P10** | L-8 | `BUILD_ID` immutable | trivial |
| **P11** | H-1 | SRS ceremony consistency check | build-time only |
| **P12** | L-6 | quotient-VM operand bounds | ~10 gas/operand |
| **P13** | M-5 | pin solc by SHA-256 | trivial |
| **P14** | L-1 | template-tree digest gate in CI | test-only |

---

## P2 — runtime memory-safety guard *(do this one first)*

Six gas, once per call, and it converts M-1 from "protected by a test in another repo" to "protected by the deployed bytecode".

```diff
--- a/templates/contracts/Halo2Verifier.sol
+++ b/templates/contracts/Halo2Verifier.sol
@@
         assembly ("memory-safe") {
+            // The generated layout below writes absolute addresses starting at
+            // TRANSCRIPT_MPTR. The `memory-safe` annotation above is what lets
+            // solc's stack-to-memory mover reserve spill slots upward from
+            // 0x80; that reservation is compiler-version and optimiser
+            // dependent (observed 0x8c0 on 0.8.24, 0x8e0 on 0.8.26+). If it
+            // ever reaches TRANSCRIPT_MPTR, the first transcript write would
+            // clobber a live Yul local. Assert the invariant here so it is
+            // enforced by the deployed bytecode rather than by a generator-side
+            // test the integrator does not run.
+            if gt(mload(0x40), TRANSCRIPT_MPTR) { revert(0, 0) }
             // This block owns the call-frame memory and remains terminal.
```

Add the same guard at the top of `require_eip2537_precompiles`, which runs in the **creation** frame that the generator's existing guard test does not inspect.

---

## P3 — pin the pragma

`0.8.24` does not produce a deployable contract (29,567 B runtime vs the 24,576 B EIP-170 limit — verified under revm Prague). The floating pragma advertises compatibility the artefact does not have.

```diff
--- a/templates/contracts/Halo2Verifier.sol
+++ b/templates/contracts/Halo2Verifier.sol
@@ -1,2 +1,6 @@
 // SPDX-License-Identifier: CC0-1.0
-pragma solidity ^0.8.24;
+// Pinned, not floating. The generated layout's correctness depends on solc's
+// stack-spill reservation staying below TRANSCRIPT_MPTR, and the runtime size
+// depends on --optimize-runs. Verified: 0.8.24 emits a 29,567-byte runtime,
+// which exceeds EIP-170 and cannot be deployed.
+pragma solidity {{ template_constants.pinned_solc_version }};
```

Same change in `templates/contracts/Halo2VerifyingKey.sol` and `templates/contracts/Halo2QuotientEvaluator.sol`. Emit `--optimize-runs` into a comment header at the same time, so the artefact records the setting it was built with.

---

## P1 — bound the gas forwarded to validating precompile calls

EIP-2537 `G1MSM` pricing is `k · 12000 · discount[k] / 1000` — a pure function of input length, no data dependence — so an exact constant is computable at codegen time. A 2× margin absorbs any future schedule change while still bounding the burn.

```diff
--- a/templates/partials/verifier/Constants.sol
+++ b/templates/partials/verifier/Constants.sol
@@
+    // Gas caps for the EIP-2537 calls that double as curve/subgroup
+    // validators. A precompile that rejects its input consumes ALL gas
+    // forwarded to it, and `staticcall(gas(), ...)` forwards 63/64 of the
+    // remainder -- so an unbounded call turns one malformed proof byte into a
+    // full-gas-limit burn for whoever pays. These are the EIP-2537 costs for
+    // the exact input lengths this verifier renders, doubled for margin.
+    uint256 internal constant G1MSM_GAS_1PAIR = {{ g1msm_gas_1pair }};
+    uint256 internal constant G1MSM_GAS_FUSED = {{ g1msm_gas_fused }};
+    uint256 internal constant G1ADD_GAS       = {{ g1add_gas }};
+    uint256 internal constant PAIRING_GAS_2   = {{ pairing_gas_2pair }};
```

```diff
--- a/templates/partials/verifier/AccumulatorHelpers.yul
+++ b/templates/partials/verifier/AccumulatorHelpers.yul
@@ -292
-                        out := staticcall(gas(), {{ ...g1msm_address|hex() }}, acc_scratch, {{ ...g1_msm_pair_bytes|hex() }}, ACC_LHS_MPTR, {{ ...g1_bytes|hex() }})
+                        out := staticcall(G1MSM_GAS_1PAIR, {{ ...g1msm_address|hex() }}, acc_scratch, {{ ...g1_msm_pair_bytes|hex() }}, ACC_LHS_MPTR, {{ ...g1_bytes|hex() }})
@@ -397
                         out := staticcall(
-                            gas(),
+                            G1MSM_GAS_1PAIR,
                             {{ ...g1msm_address|hex() }},
```

The same substitution is needed at the six emitter-generated sites (generated lines 3558, 3573, 3584, 3629, 3643 and the `ec_pairing` call at 622), which come from `src/lowering/kzg/mod.rs` and `templates/partials/verifier/FinalPairing.yul`.

**Add the gas-cost model next to the plan** so the constants cannot drift from the input lengths:

```rust
// src/lowering/plan.rs
/// EIP-2537 G1MSM gas for `k` pairs: k * 12000 * discount[k] / 1000.
fn g1msm_gas(k: usize) -> u64 { /* EIP-2537 discount table */ }

// asserted at plan time:
assert_eq!(fused_msm_pairs * G1_MSM_PAIR_BYTES, fused_msm_input_bytes);
let g1msm_gas_fused = 2 * g1msm_gas(fused_msm_pairs);
```

**Caveat.** The cap must be generous and codegen-derived. A hand-tuned value that is too tight becomes a liveness bug on a chain with a different gas schedule — which is a worse failure than the griefing it prevents. If you would rather not take that risk, the weaker alternative is to document the behaviour loudly in the NatSpec so integrators know to bound the gas they hand the verifier themselves.

---

## P5 — strengthen the deployment probe

Currently `G1ADD` gets a known-answer vector and the two precompiles that decide acceptance get identity inputs only. Add three probes; all are constant-size and cost deployment gas only.

```diff
--- a/templates/partials/verifier/PrecompileSmoke.sol
+++ b/templates/partials/verifier/PrecompileSmoke.sol
@@ (after the existing G1ADD known-answer block)
+            // Known-answer G1MSM: [2]*G == 2G. The identity-input probe below
+            // is satisfied by any implementation that echoes zeros; this one
+            // is not. G1MSM is the verifier's subgroup validator for every
+            // absorbed proof commitment, so a wrong G1MSM is a soundness bug,
+            // not a liveness bug.
+            mstore(add(scratch, 0x00), {{ g1_gen_x_hi }})
+            mstore(add(scratch, 0x20), {{ g1_gen_x_lo }})
+            mstore(add(scratch, 0x40), {{ g1_gen_y_hi }})
+            mstore(add(scratch, 0x60), {{ g1_gen_y_lo }})
+            mstore(add(scratch, 0x80), 2)
+            if iszero(staticcall(gas(), 0x0c, scratch, 0xa0, scratch, 0x80)) { revert(0, 0) }
+            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
+            if iszero(and(
+                and(eq(mload(add(scratch, 0x00)), {{ g1_two_x_hi }}),
+                    eq(mload(add(scratch, 0x20)), {{ g1_two_x_lo }})),
+                and(eq(mload(add(scratch, 0x40)), {{ g1_two_y_hi }}),
+                    eq(mload(add(scratch, 0x60)), {{ g1_two_y_lo }}))
+            )) { revert(0, 0) }
+
+            // Negative G1MSM probe: a point that is on the curve but NOT in
+            // the r-order subgroup must make the precompile fail. This is the
+            // one property the whole deferred-validation strategy rests on and
+            // the one property no existing probe tests.
+            mstore(add(scratch, 0x00), {{ g1_wrong_subgroup_x_hi }})
+            mstore(add(scratch, 0x20), {{ g1_wrong_subgroup_x_lo }})
+            mstore(add(scratch, 0x40), {{ g1_wrong_subgroup_y_hi }})
+            mstore(add(scratch, 0x60), {{ g1_wrong_subgroup_y_lo }})
+            mstore(add(scratch, 0x80), 1)
+            if staticcall(gas(), 0x0c, scratch, 0xa0, scratch, 0x80) { revert(0, 0) }
+
+            // Known-FALSE pairing: e(G, G2) * e(G, G2) != 1. The identity probe
+            // below only proves the precompile can say "true"; the verifier's
+            // entire accept decision is `PAIRING_CHECK(...) == 1`, so an
+            // implementation that always returns 1 must be caught here.
+            //  ... build the two-pair input (G, G2), (G, G2) ...
+            if iszero(staticcall(gas(), 0x0f, scratch, 0x0300, scratch, 0x20)) { revert(0, 0) }
+            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
+            if iszero(iszero(mload(scratch))) { revert(0, 0) }   // must be 0
+
+            // Known-TRUE pairing: e(G, G2) * e(-G, G2) == 1.
+            //  ... build the two-pair input (G, G2), (-G, G2) ...
+            if iszero(staticcall(gas(), 0x0f, scratch, 0x0300, scratch, 0x20)) { revert(0, 0) }
+            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
+            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }
```

The generator already has `G1_BASE` and `G2_BASE`, so the generator/two-G constants are free. A wrong-subgroup point can be produced once, offline, and baked in as a constant (any point on E(Fp) with order ≠ r — e.g. map a fixed seed into E(Fp) and skip cofactor clearing).

Also: give `AUDIT.md` TA-6 a `Status:` line and re-rate it. With the accept path resting entirely on `0x0f`, Low is too low.

---

## P11 — bind the trusted setup at build time *(highest-severity fix)*

The generator already runs the analogous check for G1 and explains why. Extend it to G2 and to τ.

```diff
--- a/src/lowering/vk.rs
+++ b/src/lowering/vk.rs
@@
             let g1_pt: G1Affine = G1Affine::generator();
             let g2_pt: G2Affine = self.params.g2().to_affine();
             let neg_s_g2_pt: G2Affine = (-self.params.s_g2()).to_affine();
+
+            // The G1 base is validated above by reconstructing it from
+            // g_lagrange. Do the same work on the G2 side, which is currently
+            // taken on trust from `params` and is the element every soundness
+            // guarantee rests on.
+            //
+            // 1. G2_BASE must be the canonical generator, for the same reason
+            //    G1_BASE must be: the emitted pairing equation assumes it.
+            assert_eq!(
+                g2_pt,
+                G2Affine::generator(),
+                "SRS G2 base is not the canonical BLS12-381 generator; the \
+                 emitted pairing equation would not be the KZG identity"
+            );
+
+            // 2. NEG_S_G2 must be the negation of [tau]G2 for the SAME tau
+            //    that produced g_lagrange. Without this the generator will
+            //    happily emit a verifier keyed to an SRS whose toxic waste the
+            //    submitter knows -- and every other control in this repo
+            //    (certification, codehash pinning, trace differential, replay
+            //    fixture) checks self-consistency only, so all of them pass.
+            //
+            //    Commit f(X) = X in the Lagrange basis: [tau]G1 = sum_i w^i L_i.
+            let omega = self.vk.get_domain().get_omega();
+            let mut w = <Fq as ff::Field>::ONE;
+            let tau_g1 = g_lagrange
+                .iter()
+                .map(|g| { let t = *g * w; w *= omega; t })
+                .fold(G1Projective::identity(), |acc, t| acc + t)
+                .to_affine();
+            assert!(
+                bls12_381::pairing_check(&[
+                    (&tau_g1,          &G2Affine::generator()),
+                    (&(-G1Affine::generator()), &self.params.s_g2().to_affine()),
+                ]),
+                "SRS inconsistency: s_g2 does not correspond to the tau that \
+                 generated g_lagrange; NEG_S_G2_BASE would be emitted from an \
+                 SRS unrelated to the commitment basis"
+            );
```

Additionally, and outside the code: pin the SRS by SHA-256 in the generator, fail the render on mismatch, and record the hash plus the ceremony transcript reference in the artefact manifest. `CODEGEN_ASSURANCE_DOSSIER.md:46` already lists this as a required record; it is simply not being produced.

---

## P10 — on-chain build identity

```diff
--- a/templates/partials/verifier/Constants.sol
+++ b/templates/partials/verifier/Constants.sol
@@
+    /// @notice Identifies the exact build that produced this verifier.
+    /// @dev keccak256(generator_commit || feature_list || vk_digest ||
+    ///      EXPECTED_VK_CODEHASH || srs_sha256). Nothing else in the deployed
+    ///      runtime identifies the codegen, the feature profile, or the SRS
+    ///      (CBOR metadata is stripped), so during an incident this is the
+    ///      only way to answer "which of our deployments has the affected
+    ///      codegen?" from chain state alone.
+    bytes32 public immutable BUILD_ID = {{ build_id }};
```

Zero cost on the verify path. Publish the preimage components alongside the deployment record.

---

## P4 — custom errors

Every revert is currently `revert(0, 0)`. Writing a selector at `0x00` is legitimate scratch use and does not disturb the generated layout (which starts at `0x1000`).

```yul
// helper, emitted once in AssemblyHelpers.yul
function fail(sel) {
    mstore(0x00, shl(224, sel))
    revert(0x00, 0x04)
}
```

Minimum useful taxonomy:

| Selector | Meaning | Current sites |
| --- | --- | --- |
| `BadCalldataShape()` | ABI heads, proof length, instance count, `calldatasize` | 338, 1048 |
| `VkMismatch()` | `extcodesize` / `extcodehash` / header cross-check | 1007, 1024 |
| `NonCanonicalScalar()` | instance, eval or q_eval ≥ r | 1133, 1316, 1369, 1399 |
| `BadPointEncoding()` | EIP-2537 pad, coordinate ≥ p, accumulator packing | 439, 440, 445, 448, 1064 |
| `PrecompileFailed()` | any precompile success/returndatasize failure | 212, 224, 273, 284, 610, 1482 |
| `ProofRejected()` | the final pairing | 3666, 3678 |
| `QuotientProgramInvalid()` | VM structural post-conditions | 2620, 2654, 2661, 2668 |

Declare them in the contract so the ABI carries them and off-chain tooling can decode.

---

## P7 — make the committed-instance invariant explicit

Two changes, one in the generator, one in the emitted comment.

```rust
// src/lowering/encoding/mod.rs -- where committed-instance commitments are pinned
assert!(
    committed_instance_comms.iter().all(|c| *c == G1_IDENTITY_MPTR),
    "committed-instance commitments are pinned to the G1 identity; a \
     non-identity commitment would require a calldata channel and an MSM \
     term that this emitter does not produce"
);
```

```rust
// src/lowering/kzg/mod.rs -- per-set MSM emission
// Emitted x1 exponents must be {0..m-1} minus exactly the indices of
// commitments proven to be the identity. Anything else means a real
// commitment was dropped from the batch while its eval stayed in q_eval_set.
let emitted: BTreeSet<usize> = /* exponents actually emitted */;
let omitted: BTreeSet<usize> = (0..m).collect::<BTreeSet<_>>()
    .difference(&emitted).copied().collect();
assert_eq!(omitted, identity_commitment_indices,
    "point set {s}: MSM omits x1 exponents {omitted:?} but only \
     {identity_commitment_indices:?} are identity commitments");
```

And fix the emitted comment so it stops lying:

```diff
-                    // q_eval_set[0]: 43 commitment(s)
+                    // q_eval_set[0]: 43 evaluation terms, 42 commitment terms.
+                    // x1^1 is omitted because commitment 1 (the committed
+                    // instance) is pinned to the G1 identity and contributes
+                    // nothing to the MSM. The KZG batch still constrains its
+                    // evaluation to zero. Asserted in kzg/mod.rs.
```

---

## P8 — un-alias `CHALLENGE_MPTR`

```diff
--- a/templates/partials/verifier/Constants.sol
+++ b/templates/partials/verifier/Constants.sol
@@
-    uint256 internal constant CHALLENGE_MPTR = {{ memory.challenge_mptr }};
+    // User-phase challenge window. MUST NOT overlap the named challenge slots
+    // below: TranscriptProofParser squeezes phase challenges to
+    // CHALLENGE_MPTR + 32*i and then unconditionally squeezes theta to
+    // THETA_MPTR. If the windows alias, phase-1 challenge 0 is silently
+    // overwritten by theta.
+    uint256 internal constant CHALLENGE_MPTR = {{ memory.user_challenge_mptr }};
```

with a planner assertion:

```rust
assert!(
    memory.user_challenge_mptr + 32 * num_user_challenges <= memory.theta_mptr,
    "user-phase challenge window overlaps the named challenge slots"
);
```

---

## P9 — assert `batch_invert` scratch capacity

The current arithmetic lands *exactly* on `LAGRANGE_DENOMS_MPTR` with zero slack, and overflowing it corrupts silently — the modexp still succeeds, so nothing reverts.

```rust
// src/lowering/layout/memory.rs, where BATCH_INV_SCRATCH is sized
// Forward pass writes (n-2) prefix products, then a 0xc0-byte EIP-198 frame.
let required = (n.saturating_sub(2)) * 32 + 0xc0;
assert!(
    batch_inv_scratch_len >= required,
    "batch_invert scratch is {batch_inv_scratch_len} bytes but needs \
     {required} for n={n}; overflow silently corrupts denominator[0] and the \
     backward pass returns wrong inverses WITHOUT reverting"
);
```

---

## P12 — bound the quotient-VM operands

Defence in depth while the VK is immutable; mandatory if it ever stops being.

```diff
--- a/templates/partials/quotient_numerator/QuotientHelpers.yul
+++ b/templates/partials/quotient_numerator/QuotientHelpers.yul
@@ (at each operand decode)
             let q_ptr := shr(240, mload(q_pc))
+            // Operands are raw memory addresses from the pinned program. The
+            // codehash pin is the only thing standing between a malformed
+            // program and arbitrary memory access; clamp anyway so the
+            // property is local to this file.
+            if or(lt(q_ptr, {{ memory.reversed_evals_mptr|hex() }}),
+                  gt(q_ptr, {{ memory.vm_operand_max|hex() }})) { revert(0, 0) }
@@ (selector bucket write)
+            if iszero(lt(q_sel_idx, {{ num_simple_selectors }})) { revert(0, 0) }
+            if iszero(lt(q_sel_gap, {{ num_identities }})) { revert(0, 0) }
@@ (stack pop)
+            if lt(q_sp, {{ memory.vm_stack_floor|hex() }}) { revert(0, 0) }
             q_sp := sub(q_sp, 0x20)
```

Note the existing terminal check `eq(q_sp, 0xb8e0)` does **not** catch a balanced underflow (pop-then-push restores the pointer), which is why the floor check is needed at the pop site.

---

## P13 — pin solc by content hash

```diff
--- a/scripts/install_pinned_solc.sh
+++ b/scripts/install_pinned_solc.sh
@@
+# Content hash, not version string. `--version` output is trivially forged by a
+# substituted binary, and this project's entire reproducibility claim rests on
+# the compiler being exactly this one.
+PINNED_SOLC_SHA256="<sha256 from binaries.soliditylang.org/${platform}/list.json>"
+
 if [[ ! -x "$solc_path" ]] || ! "$solc_path" --version | grep -q "Version: ${PINNED_SOLC_VERSION}"; then
   url="https://binaries.soliditylang.org/${platform}/${binary}"
   echo "[install-solc] downloading $url"
   curl -fsSL "$url" -o "$solc_path"
+  actual="$(sha256sum "$solc_path" | cut -d' ' -f1)"
+  if [[ "$actual" != "$PINNED_SOLC_SHA256" ]]; then
+    echo "[install-solc] SHA-256 mismatch: got $actual, expected $PINNED_SOLC_SHA256" >&2
+    rm -f "$solc_path"
+    exit 1
+  fi
   chmod +x "$solc_path"
 fi
```

Also fix the `Darwin-arm64 → macosx-amd64` mapping, or record explicitly that Apple Silicon runs an x86 binary under Rosetta and is therefore not the CI compiler.

---

## P14 — gate template edits in CI

The cheapest closure of L-1. Needs no SRS, so it runs in the default CI job.

```rust
// tests/template_digest.rs
/// The replay fixtures compile committed pre-rendered .sol, so a template edit
/// changes what deploys without changing what any SRS-free test compiles. Pin
/// the template tree so an edit must be accompanied by a fixture re-render and
/// a README commit-stamp bump.
#[test]
fn template_tree_digest_is_pinned() {
    const EXPECTED: &str = "<sha256 of the sorted template tree>";
    assert_eq!(hash_dir("templates/"), EXPECTED,
        "templates/ changed. Re-render the fixtures (see \
         fixtures/*/README.md), update the source-commit stamps, then update \
         this digest.");
}
```

---

## Patch validation

P2 and P3 were applied to the generated `Halo2Verifier.sol`, recompiled with the pinned toolchain and re-run through the full test suite:

| | baseline | with P2 + P3 | delta |
| --- | --- | --- | --- |
| runtime size | 21,286 B | 21,299 B | **+13 B** |
| deployment gas | 5,330,806 | 5,333,769 | +2,963 |
| valid-proof gas | 1,279,482 | 1,279,513 | **+31** |
| test outcomes (32 cases) | 1 accept / 31 reject | identical | — |

Thirty-one gas and thirteen bytes to move the memory invariant from "enforced by a test in another repository" into the deployed bytecode. The other patches were not compiled, since they require generator changes.

---

## Suggested sequencing

1. **P3, P2, P6** — one afternoon, no behavioural risk, closes the compiler-configuration exposure and stops the artefact from shipping comments that contradict it.
2. **P11** — the only High. Build-time only, no on-chain change, no gas cost.
3. **P5, P1** — deployment assurance and the gas-griefing bound. P1 needs the gas model, so it is the longest of the group.
4. **P4, P10, P13, P14** — operational quality: diagnosable failures, fleet inventory, supply-chain pinning, template gating.
5. **P7, P8, P9, P12** — generator hardening. None affect the current artefact's behaviour; all convert "happens to be correct" into "asserted correct".

---

# Part VI — Operational readiness checklist

Before production deployment, a deployer should be able to produce evidence for every line. Items marked ✅ were verified during this review for this artefact; the rest are deployment-specific.

**Trusted setup**

1. Name the ceremony, its transcript URL, and the SHA-256 of the exact SRS file used for this render. Record all three in the manifest.
2. Independently recompute `−[τ]G₂` from the ceremony's published τ point and confirm it equals `NEG_S_G2_BASE` (VK words 23–30). Do not accept the generator's output as its own evidence.
3. ✅ `G2_BASE` (words 15–22) is the canonical BLS12-381 G2 generator and `G1_BASE` (words 11–14) the canonical G1 generator.
4. Run the build-time pairing check `e([τ]G1, G₂) == e(G1, s_g2)` (**P11**) before generating anything you intend to deploy.

**Build reproducibility**

5. Install solc by SHA-256, not by version string. Record the hash.
6. Record the complete flag set **including `--optimize-runs`**; confirm `SOLC_OPTIMIZE_RUNS` is unset in the build environment. ⚠️ At `runs=100000` the runtime exceeds EIP-170 and will not deploy.
7. Recompile from the pinned generator commit and confirm the verifier source hash matches the deployed source byte-for-byte.
8. Confirm the generator commit, Midfall revision and Cargo feature list are one consistent triple, and record the exact feature flags — `truncated-challenges`, `outer-fewer-point-sets`, `outer-single-h-commitment` — that the prover must match.

**Key / VK binding**

9. ✅ `keccak256(0xfe ‖ VK payload) = 0xe68d8936…cf52`, length 17,025 — recomputed from source and confirmed against `EXPECTED_VK_CODEHASH` / `EXPECTED_VK_LENGTH`.
10. Deploy VK first, then `Halo2Verifier(vkAddress)`. Confirm `AUTHORIZED_VK()` returns the intended address. ✅ A 1-bit-mutated VK and an EOA address both revert the constructor.
11. ✅ VK header words match the circuit: `num_instances=19`, `k=20`, `has_accumulator=1`, `acc_offset=11`, `num_acc_limbs=7`, `num_acc_limb_bits=56`.
12. ✅ Domain self-consistency: `n_inv · 2ᵏ ≡ 1`; `omega` of exact order `2ᵏ`; `omega · omega_inv ≡ 1`; `omega_inv_to_l = omega_inv^|rotation_last|`.

**Chain**

13. ✅ The target chain must be at Prague/Pectra with EIP-2537 at `0x0b`/`0x0c`/`0x0f` **and** MCOPY (Cancun). Pre-fork deployment reverts in the constructor — verified fail-closed under `CANCUN`, `SHANGHAI` and `MERGE`.
14. Do **not** rely on `require_eip2537_precompiles()` as a correctness gate (**M-3**). Independently run against the target chain: a true pairing, a **false** pairing, a non-identity `G1ADD`, a non-identity `G1MSM`, an off-curve G1 rejection, and a wrong-subgroup G1 rejection.
15. Confirm the deployment transaction supplies enough gas for the 78-pair (`0x30c0`-byte) G1MSM probe. ✅ Deployment cost 5,330,806 gas under revm Prague.

**Application layer**

16. The wrapper must hold the verifier behind a **replaceable** address and must have its own pause. There is no on-chain recovery in the verifier.
17. The wrapper must bind `block.chainid`, its own address, program/state identifiers, nullifiers and freshness into the statement. A proof valid here is valid on every chain and every deployment of this bytecode.
18. Record that `verifyProof` returns `true` or reverts — never `false`. Callers must not treat a failed `staticcall` as a decodable negative result.
19. ⚠️ The verifier cannot be called through ERC-2771 forwarders or any relayer that appends calldata (**L-4**), and a malformed point burns ~63/64 of the gas you hand it (**M-2**). Bound the gas passed to `verifyProof` from the wrapper.

**Post-deployment**

20. Publish the deployed runtime bytecode and its keccak for both contracts, plus the full manifest from steps 1–8. Nothing on-chain identifies the build (**L-8**), so this record is the only provenance that will exist.
21. Maintain an inventory mapping each deployed address to its generator commit, feature profile, SRS hash and circuit. Without a `BUILD_ID` immutable this cannot be reconstructed from chain state during an incident.

---

# Appendix A — Empirical test log

**Environment.** solc 0.8.30 (`--optimize --optimize-runs=1 --via-ir --evm-version cancun`, CBOR metadata off) → `revm 19`, `SpecId::PRAGUE`, `blst` feature. VK deployed with a 17,025-byte runtime and codehash `0xe68d8936…cf52`, matching `EXPECTED_VK_CODEHASH` exactly. Verifier deploy cost 5,330,806 gas.

**Baseline.** The unmodified fixture calldata (8,516 bytes) verifies in **1,279,482 gas** — reproducing the figure in `fixtures/moonlight-wrap/README.md` exactly, which independently confirms the artefact, the fixture and the compiler settings are mutually consistent.

**40 adversarial cases. 1 accepted (the valid proof), 39 rejected.**

| # | Mutation | Result | Gas |
| --- | --- | --- | --- |
| P1 | unmodified fixture | **ACCEPT** | 1,279,482 |
| N1 | `advice[0].x_lo` last byte flipped | reject | 492,197,920 ⚠️ |
| N2 | `perm_z[0].x_lo` last byte flipped | reject | 492,197,920 ⚠️ |
| N3 | `quotient_limb[0].x_lo` flipped | reject | 492,197,920 ⚠️ |
| N4 | `eval[0]` (committed instance) + 1 | reject | 1,279,485 |
| N5 | `eval[50]` + 1 | reject | 1,279,473 |
| N6 | `f_com.x_lo` flipped | reject | 492,197,920 ⚠️ |
| N7 | `q_eval[0]` + 1 | reject | 1,279,473 |
| N8 | `pi.x_lo` flipped | reject | 492,205,857 ⚠️ |
| N9 | `eval[0]` set to 0 | ACCEPT — *no-op; fixture value is already 0* | 1,279,482 |
| N10 | `eval[0] = r` | reject | 316,790 |
| N11 | `q_eval[0] = r` | reject | 315,830 |
| N12 | `instance[0] = r` | reject | 316,760 |
| N13 | `instance[0] = r + 1` | reject | 316,760 |
| N14 | `instance[0]` + 1 | reject | 1,279,473 |
| N15 | `instance[10]` + 1 | reject | 1,279,473 |
| N16 | `instance[11]` + 1 (acc lhs) | reject | 492,197,436 ⚠️ |
| N17 | `instance[18]` + 1 (acc rhs) | reject | 492,190,350 ⚠️ |
| N18 | `advice[0].x_hi` top byte nonzero (bad pad) | reject | 315,950 |
| N19 | `advice[0].y_hi` top byte nonzero (bad pad) | reject | 315,950 |
| N20 | `advice[0].x = p` (coordinate = modulus) | reject | 315,920 |
| N21 | `advice[0] = (1,1)` off-curve | reject | 492,197,902 ⚠️ |
| N22 | `advice[0] = (0,0)` identity | reject *(valid encoding; fails at the pairing)* | 1,278,321 |
| N23 | calldata truncated by 32 B | reject | 315,000 |
| N24 | calldata + 32 trailing zero bytes | reject | 316,240 |
| N25 | calldata + 20 bytes (ERC-2771 style) | reject | 316,720 |
| N26 | ABI head[0] `0x40 → 0x60` | reject | 315,920 |
| N28 | proof length `0x1e60 → 0x1e5f` | reject | 315,920 |
| N29 | instance count `19 → 18` | reject | 315,920 |
| N30 | instance count `19 → 20` | reject | 315,920 |
| N31 | wrong function selector | reject | 315,920 |
| D1 | ABI head[1] `0x1ec0 → 0x1f00` | reject | 315,890 |
| D2 | ABI head[1] `0x1ec0 → 0x1ea0` | reject | 315,920 |
| D3 | ABI head[0] `0x40 → 0x20` | reject | 315,920 |
| D4 | proof length `0x1e60 → 0x1e80` | reject | 315,920 |
| E1 | both accumulator points = canonical identity encoding | reject | 1,265,123 |
| E2 | acc lhs = `p−1`/`p−1` without ID flag (decodes to `(0,0)`) | reject | 315,980 |
| E3 | acc lhs word0 bit ≥ 224 set (packing violation) | reject | 315,950 |
| E4 | acc lhs/rhs swapped | reject | 1,279,473 |

*(N27 was a no-op — the mutation coincided with the original byte — and is superseded by D1/D2.)*

**Deployment-time cases**

| Case | Result |
| --- | --- |
| Deploy under `SpecId::CANCUN` / `SHANGHAI` / `MERGE` | constructor reverts — fail closed ✅ |
| Verifier pointed at a 1-bit-mutated VK | constructor reverts — codehash pin holds ✅ |
| Verifier pointed at an EOA address | constructor reverts ✅ |
| solc 0.8.24, runs=1 (29,567 B runtime) | `HALT CreateContractSizeLimit` ⚠️ |
| solc 0.8.30, runs=100000 (29,836 B runtime) | `HALT CreateContractSizeLimit` ⚠️ |
| solc 0.8.30, runs=1 (21,286 B runtime) | deploys ✅ |

**What the log establishes**

- Three distinct rejection gas signatures — ~316k structural, ~1.28M cryptographic, and ~63/64-of-limit for curve-validity failures. The third is **M-2**, and it is not a rounding artefact: it scales exactly with the supplied limit (1.98M of 2M; 29.5M of 30M; 492M of 500M).
- The committed-instance evaluation is pinned to zero by the KZG batch (N4 rejects, fixture value is 0), which empirically settles the **L-2** analysis: the omitted `x1^1` MSM term is a gas optimisation, not a soundness gap.
- Every ABI-envelope mutation is caught cheaply, before any curve work — the calldata parser has no zero-fill or relocation hole.
- The identity encoding is accepted as a *valid* G1 encoding (N22) but does not shortcut the pairing.
- The accumulator codec rejects non-canonical and packing-violating encodings early (E2, E3, 315–316k) and rejects a plausible-looking canonical identity substitution at the pairing (E1) — the accumulator instances are bound by the proof, so they cannot be swapped for the trivial case.

---

# Appendix B — Verified-correct inventory

Recording what was checked and found sound, so the report distinguishes "verified" from "not looked at".

**Fiat–Shamir**
- The VK is bound: `vk_digest` is the first absorbed word, and `transcript_repr` covers the constraint system, all fixed commitments and all permutation commitments. No weak-Fiat-Shamir / "Frozen Heart".
- Absorb-before-squeeze ordering matches `src/plonk/verifier.rs` and `src/poly/kzg/mod.rs` exactly. Every prover-controlled value is absorbed strictly before any challenge depending on it; `π` is last and no challenge depends on it.
- Reseed semantics match Rust; back-to-back squeezes (β/γ, x1/x2) produce distinct challenges.
- No value used in the identity is unabsorbed: all 1,552 VM operand pointers and all 141 raw `mload`s in the identity code resolve into the absorbed-evaluation window `[0x9480, 0xa140)`. Zero point into uninitialised memory.
- No challenge can be influenced after derivation: slots `0x7900…0x7a40` are never rewritten except the intentional `x3` mask, which mirrors Rust. Verified by an exhaustive scan of every constant-address `mstore`/`mcopy`/`calldatacopy` destination.

**Field elements**
- All 19 instances, 102 evaluations and 5 q_evals are checked `lt(v, r)` — so `v = r` is rejected, not reduced.
- No Fq/Fr confusion: every `addmod`/`mulmod` uses `FR_MODULUS`. Base-field comparisons use dedicated split `BLS_P_HI` / `BLS_P_MINUS_ONE_LO` constants, verified equal to the top 16 / bottom 32 bytes of `p−1`.
- The transcript absorbs the *same* word that was range-checked — no absorb/use divergence.

**Curve points**
- EIP-2537 padding enforced for every proof G1; malformed encodings revert rather than being normalised (which would create transcript aliases).
- All 31 proof commitments plus `f_com` appear exactly once in the 78-pair fused G1MSM; `π` passes through its own G1MSM; both accumulator points are forced through G1MSM. **Every prover-supplied G1 reaches a subgroup-checking precompile.**
- No prover-supplied point reaches `0x0b` G1ADD (which does not subgroup-check) without prior validation.
- All 45 VK commitments are on-curve and in the r-subgroup; none of the 10 simple-selector commitments is the identity.

**Accumulator**
- The limb decomposition is canonical and bijective; the coordinate is bounded by `p−1` and `hi < 2¹²⁸`; the identity has exactly one accepted encoding; a decoded `(0,0)` outside the sentinel is rejected; `PACKED_0_WITH_ID_FLAG − PACKED_0 = 2⁵⁶` exactly, with no carry.
- `acc_offset` is fixed at 11 and `11 + 2·2·2 = 19` matches the pinned instance count — not attacker-shiftable.
- The decoded accumulator is not decorative: it is folded into the pairing inputs before `ec_pairing`.
- The randomised batching is sound: `alpha` is drawn over exactly `0x220` bytes covering all four already-final points, with a zero-draw guard.

**MSM and linear combinations**
- Exactly 49 identities, positions 0–48, each consuming one `y` step; order matches `partially_evaluate_identities`. All 21 in-bytecode selector gaps and 10 rendered tails are arithmetically correct — every bucket lands on `Σ y^(48−j)·eval_j`. No two identities share a coefficient.
- All 102 evaluations are opened exactly once across the 5 point sets (42+6+6+33+15 = 102). None missing, none double-counted.
- Truncated `x1`/`x4` powers are used identically on the commitment and evaluation sides.
- The 78 `(point, scalar)` pairs are written contiguously over exactly `0x30c0` bytes — no stale memory in the MSM buffer.
- `batch_invert` fails closed on zero and on non-canonical input, and correctly `leave`s before the backward pass on a failed modexp. Algorithm hand-verified for n = 2, 3, 4, 30.

**Pairing**
- `ec_pairing` checks staticcall success, `returndatasize() == 0x20`, and `mload == 1` (strict), in that order — a short or empty return cannot be read as success. Input is `0x300` bytes = exactly 2 pairs.
- Orientation is the standard KZG identity at `x3`.

**EVM level**
- Calldata bounds: four independent pins executed before any data-dependent read; ABI offsets cannot be attacker-chosen; proof section lengths sum to `0x1e60` exactly and the terminal cursor check re-proves it dynamically.
- VK pinning: `extcodesize` **and** `extcodehash` re-checked on every proof, before `extcodecopy`; the pinned hash covers the `INVALID` prefix (recomputed); no deploy-order footgun.
- Memory: all three address aliases are lifetime-disjoint reuse, proven by tracing the write map in program order. **No write anywhere below `0x1000`** — Solidity's scratch, free-memory pointer and zero slot are never touched. No write into the VK region after `extcodecopy`. Every constant-address `mload` reads a written region.
- Precompiles: all 13 call sites capture success, check `returndatasize()`, and are ultimately enforced. Input lengths are correct for the EIP-2537 ABI throughout. Input/output buffer aliasing is safe.
- Control flow: `success` is initialised once and every accumulation is converted to a revert at a section boundary. There is no path reaching the terminal `return` without the pairing having passed. `verifyProof` is correctly `view`.
- Arithmetic: no `signextend`/`sar`/`sdiv`/`smod`/`slt`/`sgt` anywhere; every `div`/`mod` has a nonzero constant or `r` as divisor; `scalar_inv` rejects `0` and `≥ r`, closing the "modexp returns 0 for `x ≡ 0 mod r`" alias; the accumulator's `sub(packed, first_adjust)` cannot underflow.
- Quotient VM: structural post-conditions fail closed on over-read, live operands and dropped stack entries; unknown opcodes revert; the constant-table index maximum is 177, exactly filling the 178-word reservation.
- Gas/DoS: every loop bound is a codegen constant or comes from the codehash-pinned VK; calldata size is pinned; peak memory is a constant `0xe340`. No attacker lever makes the cost depend on proof *contents* — **except** the precompile-failure path in M-2.

**Documentation accuracy**
- `MEMORY_LAYOUT.md`'s theta-relative offset table matches the artefact exactly for all 26 entries.
- `HALO2_MIDNIGHT_VERIFIER_SPEC.md` §6's VK word layout matches the VK source word-for-word.
- `fixtures/moonlight-wrap/calldata.bin` is 8,516 bytes = `INSTANCE_CPTR (0x1ee4) + 19·32`, and `proof_len = 0x1ec4 − 0x64 = 7,776` — both exactly as the artefact's constants require.
- Selector `0x1e8e1e13 = keccak("verifyProof(bytes,uint256[])")[0:4]` ✅.
- Documentation drift is confined to I-1 (the `0x80` comments) and I-4 (stale `src/codegen/*` anchors in the audit chain).


---

*Review performed 12 August 2026 against `fixtures/moonlight-wrap` (`Halo2Verifier.sol` `3861a403…`, `Halo2VerifyingKey.sol` `ec94cabe…`). Static analysis was cross-checked by execution under revm 19 / `SpecId::PRAGUE` with solc 0.8.30. Items in §2.5 and Appendix B's caveats mark what could not be verified from the material available — in particular the trusted setup (H-1), the `vk_digest` preimage, the arithmetic content of the quotient bytecode, and the accumulator's orientation contract with the producing circuit.*
