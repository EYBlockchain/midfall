# Solidity Verifier Codegen Audit

> **Path-migration note (2026-08-12).** These findings were written against
> the pre-rename source tree; `src/codegen/` has since been refactored into
> `src/lowering/`. Historical `**File:**` citations (including line numbers)
> are preserved as the audit record; translate with the migration map at the
> top of `AUDIT.md` when re-verifying. The release-facing status table below
> has been updated to cite current code and test names.

**Repository:** `halo2-solidity-verifier-exp`
**Scope:** halo2 → midnight-proofs port of the on-chain KZG/BLS12-381 verifier
codegen and emitted Yul.
**Files reviewed (deep read):**

- `src/codegen/util.rs`, `memory.rs`, `protocol.rs`, `transcript.rs`,
  `generator.rs`, `pcs.rs`, `quotient/mod.rs`, `evaluator.rs`
- `templates/contracts/Halo2Verifier.sol`, `templates/partials/quotient_numerator/QuotientNumeratorBlock.yul`
- `docs/architecture/MEMORY_LAYOUT.md`, `docs/reference/QUOTIENT_NUMERATOR_EVALUATOR.md`

The audit explicitly looked for the bug classes the requestor flagged
(EIP-2537 padding, transcript / hash-to-challenge mismatches, MSM index
errors, batch-invert zero handling, memory-region collisions, lookup /
permutation chunk boundaries, blinding rows, `omega_inv_to_l` exponent,
dummy-eval transcript handling, `proof_total()` ↔ calldata cursor
agreement, `num_committed_instances` boundary, panics/TODOs in the
emitted artifact, EIP-2537 precompile constants, padded-G1-loaded-as-2
issues, etc.). Each individual class was instrumented by reading the
relevant emitter, the corresponding Yul, and the supporting offset
arithmetic.

Bottom line: I did **not** find a clear, exploitable correctness bug in
the production verifier path. The codebase has clearly been hardened
since the original BN254 fork — every high-risk surface I checked
(transcript domain separation, EIP-2537 canonicality, proof-cursor
agreement, batch_invert zero check, KZG fused MSM, accumulator
randomization) lines up with the documented midnight-proofs
convention. The findings below are mostly **Suspicious / Hardening**
items where the code is correct today but the invariants are subtle
enough to be worth pinning down.

---

## Current reconciliation status

This file is the open-issues ledger for the assurance dossier in
[`docs/audit/CODEGEN_ASSURANCE_DOSSIER.md`](./CODEGEN_ASSURANCE_DOSSIER.md).
The older finding text is retained below for audit history; the table here is
the release-facing status snapshot as of 2026-05-11.

| Finding | Status | Evidence |
| --- | --- | --- |
| M1 lookup helper/accumulator cursor grouping | Fixed | `Data::new` now derives section starts from `ProofCalldataLayout`; `proof_layout_preserves_lookup_helper_accumulator_grouping` locks the interleaved helper/accumulator order. |
| M2 ambiguous advice commitment order metadata | Fixed | `CommitmentRead::Advice` is category-only; column/query identity lives in eval and PCS plans. `ProtocolPlan::validate` and commitment group tests cover plan drift. |
| 2026-05-11 #1 lookup quotient identity count | Fixed | `lookup_chunks.iter().map(|chunks| chunks + 2).sum()` is used in planning and validation; `lookup_identity_source_handles_variable_chunk_counts` covers variable chunk counts. |
| 2026-05-11 #2 fixed eval count | Fixed | `proof_evaluation_counts().fixed` counts `EvalRead::Fixed` entries from the protocol plan instead of fixed columns. |
| 2026-05-11 #3 challenge phase remapping | Fixed | `ProtocolPlan::from_constraint_system` sizes phases by the max of advice and challenge phases; `plan_allows_challenge_phase_beyond_advice_phases` covers this case. |
| 2026-05-11 #4 packed32 operand widths | Fixed | Operand decoding and width bounds are enforced by `validate_quotient_program` / `validate_quotient_const_slots` / `validate_quotient_mem_ptrs` in `src/lowering/quotient_numerator/vm/mod.rs`; `quotient_vm_safety_validator_rejects_malformed_programs` covers stack underflow, unknown memory tokens, and truncated operands, and `quotient_vm_lengths_are_derived_from_opcode_spec` pins operand widths to the opcode spec. (The names previously cited here — `validate_packed_quotient_operand` and `packed32_validator_rejects_logical_operand_width_corruption` — never landed under those identifiers; corrected 2026-08-12.) |
| 2026-05-11 #5 reserved memory writes | Fixed | Trace and helper templates avoid Solidity-reserved memory writes; `templates_do_not_write_solidity_reserved_memory_slots` checks `mstore(0,`, `mstore(0x00,`, and related reserved forms. |
| 2026-05-11 #6 external quotient return overlap | Fixed | External quotient output uses `QUOTIENT_RETURN_MPTR`; template validation checks output length and disjointness from the copied quotient frame. |
| 2026-05-11 #7 structured selector-run trace | Fixed | Selector-run grouping is disabled when trace is enabled, preserving per-identity trace events through direct quotient blocks. |
| 2026-05-11 #8 proof layout count reconstruction | Fixed | `ProofCalldataLayout::from_protocol` replays `protocol.proof.commitments` and panics on category drift; `proof_layout_rejects_commitment_order_drift` covers it. |
| 2026-05-11 #9 identity committed instance policy | Accepted restriction | `SolidityGenerator::SUPPORTED_COMMITTED_INSTANCE_COMMITMENT` exposes the identity policy and shape validation requires exactly one committed and one non-committed instance column. Generic committed-instance commitments remain out of scope. |
| 2026-05-11 #10 shape profiling undercount | Fixed | `emit_acc_leaf` records fallback VM ops for constant and short-memory accumulator opcodes. |

Production-scope exclusions remain: generic Halo2 circuit support, generic
committed-instance commitments, application wrapper binding/replay policy, and
chains without the expected EIP-2537 semantics.

---

## Critical — None identified

I traced the highest-risk vectors end-to-end and could not find a
break:

- **Transcript domain separation.** `templates/contracts/Halo2Verifier.sol`
  (lines ~990–1100) absorbs `vk_digest`, the 128-byte zero
  `committed_pi` identity, the BE `num_instances` length scalar, then
  each BE instance, before any proof bytes. This matches the patched
  `Hashable<Keccak256> for G1Projective::to_input` in midnight-proofs
  (the previous emitter used the 48-byte ZCash compressed encoding;
  the new emitter is consistent with the patched native verifier).
- **EIP-2537 padded G1 (4 words).** Every commitment read goes
  through `common_uncompressed_g1` (lines ~480–520):
  `if shr(128, x_hi_word) { revert(0,0) }`, the BLS12-381 Fp range
  check `(hi, lo) ≤ p − 1`, and a verbatim `calldatacopy` of 0x80
  bytes into the transcript. There is no path where a 2-word load
  reaches a precompile.
- **Squeeze-to-Fr.** `squeeze_to` (~line 528) reseeds with the 32-byte
  Keccak digest and samples `mod(h0, FR_MODULUS)` exactly once per
  challenge. No truncation/length mistake (`buf_len` is reset to 32).
- **`scalar_inv` location.** `scalar_inv` (~line 340) intentionally
  uses the dead transcript region just below `VK_MPTR`
  (`p := sub(VK_MPTR, 0x100)`). The verifier never calls it before
  transcript absorption is finished, and the comment correctly
  documents that this avoids collisions with PCS scratch when the VK
  payload shrinks.
- **`batch_invert` zero check.** Production `batch_invert` (~line 540)
  rejects the input batch if the **product** is zero
  (`if iszero(gp) { ret := 0; leave }`) and short-circuits the
  singleton case via `if iszero(x) { ret := 0; leave }`. With the
  current call sites (Lagrange denominators + the GWC dummy/Lagrange
  basis Montgomery batch in `pcs.rs`) every input is provably
  non-zero by Fiat–Shamir, so the product check is sufficient.
- **EIP-2537 precompile constants.** Constructor smoke test (line 192)
  exercises `0x0b` G1ADD, `0x0c` G1MSM and `0x0f` PAIRING_CHECK at
  deploy time and reverts on absent / size-mismatched returndata.
- **Public-accumulator pairing batch.** The `acc_pair_alpha` derivation
  (lines ~1530–1610) keccaks the full
  `domain || PAIRING_RHS || PAIRING_LHS || ACC_RHS || ACC_LHS` payload
  *after* the MSM is fully constructed, defeats the trivial
  multiplicative-cancellation attack, and falls back to `1` only when
  the digest happens to be `0` (probability ≈ 2⁻²⁵⁶).
- **Quotient VM dispatch.** `templates/partials/quotient_numerator/QuotientNumeratorBlock.yul`
  dispatch covers `0x01..0x1e`, with `default { revert(0,0) }` on the
  inner token switches (so out-of-range token indices fail closed).
  The `q_y_inv` modexp uses a separate `q_inv_scratch =
  program.stack_mptr` from `scalar_inv`’s transcript pad, eliminating
  the previous large-VK collision risk.

---

## High — None identified

I audited the calldata cursor agreement, the EIP-2537 padded
serialization, the multi-prepare KZG (Block 5) MSM term count, the
linearization expansion of the quotient limbs and selectors, the
public-accumulator decoding and identity-flag fixup, and the dummy
eval/transcript handling. All pass the consistency checks I could
construct from the code alone.

The two items I want to flag for follow-up review are below.

---

## Medium

### M1. `cd_byte` cursor groups lookup helpers/accumulators in a different physical order than the verifier reads them

**File:** `src/codegen/util.rs:443–448`

```rust
let mut cd_byte = proof_cptr_bytes;
cd_byte += G1_BYTES * meta.advice_indices.len();
cd_byte += G1_BYTES * meta.num_lookups;            // multiplicities
cd_byte += G1_BYTES * meta.num_permutation_zs;     // perm Z
cd_byte += G1_BYTES * lookup_helper_total;         // ALL helpers
cd_byte += G1_BYTES * meta.num_lookups;            // ALL accumulators
cd_byte += G1_BYTES * meta.num_trashcans;
let quotient_limb_cd = cd_byte;
```

**File:** `templates/contracts/Halo2Verifier.sol:~1130–1150`

```yul
{%- for chunks in lookup_chunks %}
// lookup {{ loop.index0 }}: {{ chunks }} helper(s) + 1 acc
for { let end := add(proof_cptr, ... ) } lt(proof_cptr, end) { } {
    ... helpers ...
}
buf_len := common_uncompressed_g1(buf_len, proof_cptr)  // accumulator
calldatacopy(lookup_z_walk, proof_cptr, 0x80)
proof_cptr := add(proof_cptr, 0x80)
{%- endfor %}
```

The on-chain reader interleaves `helpers + acc` per lookup. The
codegen-side `cd_byte` walk above sums "all helpers, then all
accumulators". The total byte count is identical
(`G1_BYTES * (Σchunks + num_lookups)`), and `cd_byte` is only used to
derive `quotient_limb_cd` / `eval_cd`, so the **current** code is
correct.

The reason this is medium and not just suspicious: any future change
that exposes a per-lookup calldata pointer (say, to read an individual
helper commitment from calldata directly during quotient evaluation)
will compute the wrong offsets if it follows this cursor convention.
The cursor walk should mirror the actual on-chain interleaving — even
when only the running total is consumed today.

**Suggested fix:** rewrite the helper/acc accumulator as a per-lookup
loop (mirroring `templates/contracts/Halo2Verifier.sol`) so the math is locally
obvious rather than relying on commutativity of the running sum.

```rust
for &chunks in &meta.lookup_chunks {
    cd_byte += G1_BYTES * chunks;   // helpers for this lookup
    cd_byte += G1_BYTES;             // accumulator for this lookup
}
```

### M2. `ProofReadPlan::commitments` stores phase-sorted `column` indices but iterates in original-column order

**File:** `src/codegen/protocol.rs:312–318`

```rust
proof.commitments.extend(
    advice_indices
        .iter()
        .copied()
        .map(|column| CommitmentRead::Advice { column }),
);
```

`advice_indices[orig_col]` holds the **proof position** of the
original column after phase sorting, so the *value* placed in
`CommitmentRead::Advice { column }` is the proof index, but the
iteration order is the original column order, not the proof
order. Concretely with phases = `[1, 0]`:

- `advice_indices = [1, 0]`
- `proof.commitments = [Advice{column=1}, Advice{column=0}]`
  ↑ but proof slot 0 in calldata is the phase-0 column (orig col 1)
  and proof slot 1 is phase-1 (orig col 0).

So `proof.commitments[i]` does not satisfy "the column read at proof
slot i" *and* the `column` field's semantic (orig vs phase-sorted)
flips depending on viewpoint. Today this is benign because the only
consumer (`proof_total()` at line 536) just reads `commitments.len()`,
but any downstream code that iterates `proof.commitments` and
dereferences `column` will get either the wrong order or the wrong
identifier mapping.

**Suggested fix (one of):**

1. Iterate phases explicitly so the resulting vector is in physical
   proof order:
   ```rust
   for phase in 0..num_phase {
       for (orig_col, p) in cs.advice_column_phase().iter().enumerate() {
           if *p as usize == phase {
               proof.commitments.push(CommitmentRead::Advice { column: orig_col });
           }
       }
   }
   ```
2. Or change the `column` field's documented meaning to "phase-sorted
   index" and add a doc-comment + unit test pinning the contract.

---

## Suspicious / hardening

### S1. `Lagrange & instance-evaluation` block depends on `num_neg_lagranges ≥ 1`

**File:** `templates/contracts/Halo2Verifier.sol:~1295–1340`

```yul
let mptr := X_N_MPTR
let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR),
                                       {{ num_neg_lagranges }})))
if iszero(mload(NUM_INSTANCES_MPTR)) {
    mptr_end := add(mptr_end, 0x20)
}
...
let l_blind := mload(add(X_N_MPTR, 0x20))
let l_i_cptr := add(X_N_MPTR, 0x40)
for { let l_i_cptr_end := add(X_N_MPTR, {{ (num_neg_lagranges * 32)|hex() }}) }
    lt(l_i_cptr, l_i_cptr_end) { l_i_cptr := add(l_i_cptr, 0x20) } {
    l_blind := addmod(l_blind, mload(l_i_cptr), r)
}
```

Reading slot `1` (`l_blind` seed) and slot `num_neg_lagranges` (`l_0`)
both assume the loop produced at least 2 Lagrange denominators. With
the standard halo2 construction `num_neg_lagranges = blinding_factors
+ 1 ≥ 2`, so this holds in practice. But the protocol-side
`rotation_last = -(blinding_factors + 1)` is computed with no lower
bound check.

**Suggested fix:** add `assert!(meta.rotation_last.unsigned_abs() >=
1, ...)` (or `>= 2` if blinding is required) early in
`ProtocolPlan::from_constraint_system` so the codegen fails fast on
edge-case constraint systems. Equivalently, render the template only
for `num_neg_lagranges >= 2`.

### S2. Linearization formula uses `x_split = x^(n-1)` (not the more common `x^n`)

**File:** `templates/contracts/Halo2Verifier.sol:~1420–1440`,
`docs/reference/QUOTIENT_NUMERATOR_EVALUATOR.md:~452`

```yul
let x_pow_2i := x
let x_pow_2i_minus1 := 1
for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {
    x_pow_2i_minus1 := mulmod(
        mulmod(x_pow_2i_minus1, x_pow_2i_minus1, r), x, r)
    x_pow_2i := mulmod(x_pow_2i, x_pow_2i, r)
}
let x_split := x_pow_2i_minus1            // = x^(n-1)
let one_minus_x_n := addmod(1, sub(r, x_pow_2i), r)
```

That arithmetic is *correct* given the documented midnight-proofs
convention `linear_com = (1 − x^n) · Σ_i x^(i(n−1)) · Q_i`, but it
diverges from the upstream halo2 PSE convention `Σ_i x^(in) · Q_i`,
which is the formula most reviewers will check first. If an
auditor compares the limb scalar against a halo2-PSE reference
implementation they will see a mismatch that is not, in fact, a bug.

**Suggested fix:** add a single-line comment in
`generate_pcs_computations` (Block 5) pointing to
`midfall/proofs/src/poly/kzg/mod.rs` so the convention is
self-documenting:

```yul
// midnight-proofs splits h(x) as Σ_i x^(i*(n-1)) * h_i(x) (NOT x^(i*n)).
// Matches multiopen.rs::compute_linearization_commitment.
```

### S3. `compute_dummy_queries` panics on duplicate `(comm, rotation)` pairs

**File:** `src/codegen/pcs.rs:194–201`

```rust
Some(_) => {
    panic!(
        "duplicate (commitment, rotation) query at index {i}: \
         compute_dummy_queries cannot run on a non-deduplicated \
         query list"
    );
}
```

This is a programmer-side invariant; it is not reachable on a
well-formed PCS query schedule. But it is an unconditional panic
inside the generator, so a future bug elsewhere (e.g. duplicate
permutation queries due to a chunk-len off-by-one) would manifest as a
generator panic at codegen time rather than a structured error.

**Suggested fix:** convert the panic into a `debug_assert!` plus a
typed `Err(...)` return, threaded through `try_new`. Same for the
`unreachable!("proof_cptr must be a literal byte offset")` in
`util.rs:439`.

### S4. `f_eval` / `v` Horner direction relies on undocumented prover convention

**File:** `src/codegen/pcs.rs:~1100–1230` (Block 4),
`src/codegen/pcs.rs:~1290–1320` (Block 5)

The Block 4 reverse-Horner accumulator emits

```text
f_eval = Σ_{s=0..n_sets-1} π_s · x2^s
```

and Block 5 forward-Horner emits

```text
v = Σ_{s=0..n_sets-1} q_evals[s] · x4^s + x4^{n_sets} · f_eval
```

i.e. `π_0` and `q_evals[0]` get the constant coefficient `1`. This is
the midnight-proofs `multi_prepare` convention. There is no inline
comment binding the direction to a Rust source line; a reader following
the upstream halo2 PSE GWC implementation (which folds with the highest
power on the highest-index set) will see a sign/order mismatch that is
again not a real bug.

**Suggested fix:** annotate Block 4 with the Rust source-of-truth and
add a unit test that pins `f_eval` for a 2-set, 3-set fixture against
a known reference vector.

### S5. `g1msm_gas_cap` switch caps at `k = 128`; large MSMs fall through to the default branch

**File:** `templates/contracts/Halo2Verifier.sol:~700–860`

```yul
case 128 { discount := 519 }
// EIP-2537 G1MSM gas: k * discount[k] * 12000 / 1000.
cap := add(50000, div(mul(mul(k, discount), 12000), 1000))
```

If `k > 128`, `discount` keeps the initial value `519`. The downstream
formula stays well-defined and the cap is just a *gas* cap (a too-low
cap would revert the call, not corrupt state). Today the only
≥128-term call site is the fused final MSM, whose term count is
bounded by `final_msm_shape(...)`. If a future circuit ever drives
`final_msm_terms` over 128, the cap will silently use the asymptotic
discount `519` rather than the precise table value, which can
under-estimate gas and revert valid proofs.

**Suggested fix:** either extend the table up to the realistic upper
bound, or add a debug assertion in `final_msm_shape` that the term
count is `<= 128` (with a clear panic message when it's exceeded), so
the contract is rebuilt with a larger table before deployment.

### S6. `acc_pair_alpha` zero-fallback uses `1` rather than re-hashing

**File:** `templates/contracts/Halo2Verifier.sol:~1545–1555`

```yul
let acc_pair_alpha := mod(keccak256(batch_ptr, 0x220), r)
if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }
```

If the keccak digest is exactly `0 mod r`, the prover knows alpha
in advance and could craft pairing inputs that satisfy the batched
equation while individually failing. The probability is 2⁻²⁵⁶, and
the security argument is fine; an auditor will flag this as a
deterministic-low-entropy-fallback hardening point.

**Suggested fix:** in the iszero branch, re-hash with a domain
prefix (`keccak256("acc-batch-alpha-fallback" || alpha_seed)`) until
non-zero, or reject the proof. The cost is a single extra keccak in a
2⁻²⁵⁶ branch, so always-rehash is cheap.

### S7. Proof repacker returns typed errors

**Status:** fixed.

`SolidityGenerator::repack_proof` now returns
`Result<Vec<u8>, RepackError>` with length and compressed-G1 offset details.
`SolidityGenerator::encode_calldata` wraps repacking and also checks the
public-instance vector length before ABI encoding.

---

## Things I checked and did NOT find an issue with

This is the deliberate "no bug here" list, recorded so the next
auditor can skip the hot paths I already burned time on:

- **`omega_inv_to_l = ω^{rotation_last}`** (`generator.rs:466`).
  `rotation_last = -(blinding_factors + 1)`. The Lagrange seed loop
  walks `ω^{rot_last}, ω^{rot_last+1}, ...`, so slot 0 holds
  `L_{rot_last}(x) = l_last`, slot `num_neg_lagranges` holds `L_0(x)`.
  Aligned with halo2 PSE.
- **Advice memory layout vs phase reordering**
  (`util.rs:514`, `Halo2Verifier.sol:~1050`).
  `advice_comms[orig] = comms_base + 4·advice_indices[orig]` and the
  Yul reader stores phase 0 advice 0 at `comms_base`, phase 0 advice 1
  at `comms_base + 4`, etc. The mapping is consistent in both
  directions for any phase permutation.
- **`Data::new` calldata cursor walk**
  (`util.rs:439–520`). Total byte count agrees with
  `transcript_buffer_words_bound` (`generator.rs:2965–3022`).
- **`construct_intermediate_sets` deduplication**
  (`pcs.rs:~270–360`). Sets are deduplicated by the underlying
  `EcPoint` memory pointer, so the dummy-query logic that depends on
  pointer equality is well-defined.
- **EVM identity convention.** `G1_IDENTITY_MPTR` is reserved as a
  4-word region, never written. EIP-2537 (0,0,0,0) is the canonical
  point-at-infinity. The "committed instances all alias
  `G1_IDENTITY_MPTR`" pattern in `util.rs:498` matches the patched
  `committed_pi = G1::identity()` in midnight-proofs.
- **Scratch lifetimes.** `MemoryArena` (`memory.rs:~200–500`) tracks
  permanent vs phase-scoped scratch and asserts non-overlap in
  `validate()`. The PCS-fixed window
  (`rot_points`, `x1_powers`, `q_eval_set`, ...) is fixed-offset
  inside the `theta`-relative slot 52+ band, with capacity sized
  by `final_msm_shape`. No collision between batch-invert scratch and
  PCS scratch; `BATCH_INV_SCRATCH_MPTR` is allocated inside the
  scratch allocator rooted at `selector_acc_mptr`.
- **`num_committed_instances` branching.** `committed_instance_evals`
  is filtered by `q.column < nb_committed_instances`
  (`protocol.rs:340–345`), and the eval read pointer is the same
  `eval_cptr` cursor used everywhere else. No double-counting.
- **`proof_total()` agreement.**
  `protocol.rs:535` returns `commitments.len() + evals.len()`, used
  only for sanity. The actual byte-level proof length is
  `transcript_buffer_words_bound` × on-chain reads, and matches
  `repack_proof`'s output length.

---

## Recommended next steps

1. Land **M1** and **M2** with unit tests pinning the calldata
   ordering (M1) and the `column` semantics (M2). Both are mechanical
   refactors.
2. Add inline "Rust source-of-truth" comments for the items in S2 and
   S4 to make future auditors faster.
3. Convert the panics in S3 / S7 to typed errors so a generator-time
   bug surfaces as a structured failure rather than a panic in CI.
4. Extend the `g1msm_gas_cap` table beyond `k = 128` (or assert the
   bound) before any circuit pushes the fused final MSM past that
   width (S5).
5. Optional: re-hash on the `acc_pair_alpha == 0` branch (S6); the
   probability is negligible, but the cost of doing it right is a
   single keccak.

No production-blocking finding. The verifier should be safe to deploy
at the current revision, modulo the engineering hygiene items above.

---

## 2026-05-11 additional audit findings

I found several real issues worth fixing.

### High-confidence bugs

1. **Lookup quotient identity count is wrong for chunked lookups**

`ProtocolPlan::from_constraint_system` uses:

```rust
let lookup_identity_count = num_lookups * 3;
```

But `Evaluator::lookup_computations()` emits:

```text
boundary + one helper per chunk + accumulator
= 2 + lookup_chunks[lookup]
```

So any lookup with more than one helper chunk will make this assertion fail:

```rust
assert_eq!(lookup.len(), meta.protocol.quotient.lookup)
```

Fix:

```rust
let lookup_identity_count: usize =
    lookup_chunks.iter().map(|chunks| chunks + 2).sum();
```

Also fix lookup metadata currently using:

```rust
let lookup_index = identity_index / 3;
```

That is wrong for variable chunk counts.

---

2. **`proof_evaluation_counts().fixed` counts columns, not fixed eval queries**

This is wrong:

```rust
fixed: meta.num_fixeds - meta.num_simple_selectors,
```

Proof evals are query-based, not column-count-based. A fixed column can be queried at multiple rotations, or not queried at all.

Use the protocol plan instead:

```rust
fixed: meta.protocol.proof.evals.iter()
    .filter(|e| matches!(e, EvalRead::Fixed(_)))
    .count(),
```

Otherwise the public diagnostic API can panic on valid circuits because:

```rust
counts.proof_total() == meta.num_evals
```

will fail.

---

3. **Challenge phase remapping can panic if challenges use a phase beyond advice phases**

`ProtocolPlan::from_constraint_system` computes:

```rust
let num_phase = *cs.advice_column_phase().iter().max().unwrap_or(&0) as usize + 1;
```

Then it uses that same `num_phase` for `cs.challenge_phase()`. If a challenge phase exceeds the max advice phase, indexing can go out of bounds.

Safer:

```rust
let max_advice_phase = cs.advice_column_phase().iter().copied().max().unwrap_or(0);
let max_challenge_phase = cs.challenge_phase().iter().copied().max().unwrap_or(0);
let num_phase = max_advice_phase.max(max_challenge_phase) as usize + 1;
```

---

4. **Packed32 VM validator does not enforce operand widths**

`decode_packed_quotient_instruction()` validates opcode support, but many operands are allowed to contain arbitrary 24-bit values even when the logical operand is `u8` or `u16`.

Examples that should be rejected:

```rust
Q_OP_PUSH_CONST_U8        // arg must be <= u8::MAX
Q_OP_ADD_CONST_U8         // arg must be <= u8::MAX
Q_OP_MUL_CONST_U8         // arg must be <= u8::MAX
Q_OP_PUSH_CONST           // arg must be <= u16::MAX
Q_OP_ADD_CONST            // arg must be <= u16::MAX
Q_OP_MUL_CONST            // arg must be <= u16::MAX
Q_OP_PUSH_MEM_U16         // arg must be <= u16::MAX
Q_OP_ADD_MUL_MEM_MEM_CONST_U8 // scalar arg must be <= u8::MAX
```

The packer emits valid values, but the "safety validator" claims to reject malformed finalized programs. Right now it misses these packed operand-width corruptions.

---

5. **Trace-only paths still write to memory slot `0`**

You have tests/comments saying templates should not write Solidity-reserved memory, but trace failure paths do:

```solidity
mstore(0, 34)
revert(0, 0x20)
```

and generated PCS trace code emits:

```rust
"mstore(0, {}) revert(0, {WORD_BYTES:#x})"
```

Your string test only catches `"mstore(0x00,"`, not `"mstore(0,"`.

Use `RETURN_MPTR` or `TRACE_U256_MPTR` instead.

---

6. **External quotient return buffer is not modeled in the memory planner**

Main verifier writes external quotient output to:

```solidity
let q_out := SELECTOR_ACC_MPTR
...
staticcall(..., q_out, qext.output_len)
```

But `selector_accumulators` is registered with length:

```rust
selector_len = num_simple_selectors * WORD_BYTES
```

while the output length is:

```rust
2 * WORD_BYTES + selector_len
```

So the first two words of output intentionally overlap the following quotient temp/state area. This may be safe temporally, but the memory planner does not model it. Add a phase-scoped region for the external quotient output or use the low-memory `QUOTIENT_RETURN_BUFFER_START`.

---

7. **Structured selector-run trace drops per-identity trace events**

In structured-loop mode, grouped selector runs go through:

```rust
selector_run_quotient_block(...)
```

but that path does not take `trace` and does not emit `push_quotient_trace` per identity. Trace builds with `CodegenConfig::quotient_structured_loops = true` can miss quotient identity trace IDs.

Fix by disabling selector-run grouping under trace, or by emitting trace events inside the grouped loop.

---

### Design / hardening issues

8. **Proof layout still recomputes commitment order from counts**

`ProofCalldataLayout::from_protocol()` receives `ProtocolPlan`, but it does not actually replay `protocol.proof.commitments`; it reconstructs the order from counts. If protocol order changes later, layout can silently drift.

Better: build sections by walking `protocol.proof.commitments`, then validate category grouping.

---

9. **Committed-instance commitment is hard-coded to identity**

`Data::new()` does:

```rust
let committed_instance_comms =
    (0..meta.num_committed_instances)
        .map(|_| EcPoint::new(Ptr::memory("G1_IDENTITY_MPTR")))
```

and the Solidity transcript always absorbs identity committed_pi. That is fine for the zk_stdlib identity-commitment shape, but it is not a general "one committed instance column" verifier. This should be surfaced as an explicit generator restriction/API name, not only comments.

---

10. **Shape profiling undercounts fallback VM ops**

`emit_acc_leaf()` emits accumulator ops but does not call:

```rust
record_fallback_vm_op()
```

So `fallback_vm_ops` is misleading when limb profiling is enabled. Not a correctness bug, but it weakens tuning data.

---

## Additional review findings — 2026-05-12

The findings below were added after the reconciliation snapshot above. They are
review notes until each item is fixed with code/test evidence or explicitly
excluded from production scope.

### Critical / High

#### 1. Possible unbound evaluation in `q_eval_set[0]`

In PCS sub-block 3, `q_eval_set[0]` folds 43 evaluations:

```solidity
let q_eval_set_0 := mload(0x8a00)
...
for { let i := 1 } lt(i, 0x2b) { i := add(i, 1) } { ... }
```

This includes the `x1^1 * mload(0x8500)` term. However, in the final MSM
construction, the scalar sequence jumps from scalar `1` to `x1^2`:

```solidity
mcopy(0xa300, 0x98c0, 0x80)
mstore(0xa380, 1)

mcopy(0xa3a0, 0x9940, 0x80)
mstore(0xa420, mload(add(X1_POWERS_MPTR, 0x40))) // x1^2
```

There is no point term with scalar `x1^1`.

If `mload(0x8500)` is not intentionally the evaluation of a committed identity
polynomial, then this is a soundness bug: the prover can choose that evaluation
to satisfy quotient/permutation identities without it being bound by the KZG
opening check.

**Recommendation:** Confirm what polynomial `0x8500` represents. If it is the
transcript-absorbed `committed_pi = identity`, document this explicitly and add
a differential test that mutating `0x8500` causes verification failure. If it
is not identity-committed, add the missing MSM term with scalar `x1`.

#### 2. Public accumulator identity may collapse the recursive/IVC guarantee

`load_acc_point` accepts the exact encoded identity for both accumulator points,
and the final pairing batch accepts a trivially true accumulator equation if:

```solidity
ACC_LHS = identity
ACC_RHS = identity
```

This may be valid for an "empty accumulator" case. But if this verifier is
intended to enforce that an IVC accumulator actually carries a prior proof
state, then accepting both identity points lets the caller bypass the recursive
accumulator check.

**Recommendation:** If the protocol requires a non-empty accumulator, reject
`(ACC_LHS, ACC_RHS) = (O, O)` or bind an explicit public input/state flag
proving that the empty accumulator is allowed.

### Medium

#### 3. Proof G1 validation relies entirely on later EIP-2537 use

`common_uncompressed_g1` only checks that coordinates are canonical Fp
encodings. It does not check the curve equation or subgroup. The comments rely
on every absorbed proof commitment later being consumed by G1MSM or pairing.

That is acceptable only if every deployment target implements EIP-2537 exactly.
EIP-2537 requires Fp elements to be 64-byte big-endian values with top 16 bytes
zero and `< p`, and states that MSMs and pairings must perform subgroup checks.
([Ethereum Improvement Proposals][1])

This contract's smoke test only uses identity inputs. It does not test
non-identity curve arithmetic, subgroup rejection, or invalid-point rejection.

**Recommendation:** Add deployment or CI conformance tests using invalid G1/G2
points and non-subgroup points. Consider explicitly validating proof
commitments with scalar-1 G1MSM when the verifier is deployed to
non-mainnet/custom EVMs.

**Gas-cost note:** For the current Moonlight dump this strict runtime check
would be material but not catastrophic. A single scalar-1 G1MSM over the 32
proof commitments costs about `240,768` precompile gas under the EIP-2537
discount table. Including `f_com` and `pi` as well makes it 34 G1 points, about
`254,184` precompile gas before memory/call overhead, so roughly `~260k` total.
Checking each point with its own scalar-1 G1MSM would be worse, about `408k`
precompile gas for 34 points. A cheap G1ADD-based check would only be about
`12.8k` for 34 points, but it does not provide the subgroup validation this
finding is concerned with.

#### 4. Debug gas checkpoints make verification non-static

`gas_checkpoint()` emits `LOG1` throughout verification:

```solidity
function gas_checkpoint(id) {
    log1(0, 0, or(shl(248, id), gas()))
}
```

This means `verifyProof` cannot be called through `STATICCALL`. Many verifier
integrations assume verification is side-effect-free and call verifiers
statically.

**Recommendation:** Remove gas checkpoints from production builds, or gate them
behind a separate debug build.

#### 5. Accumulator/KZG pairing batching needs a written soundness argument

The verifier batches two pairing equations with:

```solidity
alpha = H(kzg_rhs, kzg_lhs, acc_rhs, acc_lhs)
```

and checks:

```text
e(kzg_rhs + alpha * acc_rhs, G2)
*
e(kzg_lhs + alpha * acc_lhs, -sG2)
= 1
```

This is probably sound in the random-oracle model, but both equations' G1
inputs are prover-influenced. The contract should include or reference a proof
that this Fiat-Shamir batching cannot be manipulated through fixed-point
selection of accumulator points.

**Recommendation:** Document the batching lemma and add negative tests where
one equation is valid and the other is invalid.

### Low / Informational

#### 6. `q_program` interpreter lacks defensive invariants

The quotient VM does not check final stack state, stack bounds, or that operands
stay inside expected memory regions. The program is VK-pinned, so this is not
attacker-controlled at runtime, but generator bugs become verifier soundness
bugs.

**Recommendation:** In debug/test builds, assert:

```text
q_pc == q_end
q_has_top == 0
q_sp == base_stack_pointer
all memory operands are in approved ranges
```

#### 7. Raw verifier does not bind application semantics

The verifier proves only that a proof verifies under the pinned VK and supplied
public instances. It does not bind state roots, program IDs, chain IDs,
nullifier domains, or application authorization.

**Recommendation:** Wrapping contracts must domain-separate and validate all
public instances before accepting `verifyProof()`.

#### 8. Invalid proofs revert instead of returning `false`

This is documented, but it is an integration hazard. Any wrapper must use
`try/catch` or let invalid proofs revert the whole transaction intentionally.

---

## Spec-level review findings - 2026-05-12

This review found several spec-level bugs and underspecified areas. The most
important ones are below.

EIP-2537 note: the BLS12-381 padded G1/G2 encodings broadly match EIP-2537's
128-byte G1 and 256-byte G2 point encoding, and the addresses `0x0b`, `0x0c`,
and `0x0f` match G1ADD, G1MSM, and pairing. But EIP-2537 also says
variable-length operations such as MSM/pairing must error on empty input, and it
explicitly does **not** subgroup-check G1ADD, while MSMs and pairings must
subgroup-check. Those details affect several bugs below. ([Ethereum Improvement
Proposals][1])

### Highest-impact issues

#### 1. Quotient VM persistent state aliases the quotient stack

In Section 10.5, quotient VM state is placed at:

```text
B = T + W*c
eval_numer_mptr = B
trace_id_mptr = B + W
selector_power_mptr = B + 2W
```

But in Section 9.5, `quotientTmp` is allocated with length
`C.quotientCseTemps * W`, and then `quotientStack` is allocated immediately
afterward. That means the persistent state begins exactly where the stack
begins, unless `C.quotientStackWords` is secretly meant to include the state
area.

Impact: operand stack writes can overwrite `eval_numer`, `trace_id`, or the
selector-power table. Different implementers may allocate either "stack only" or
"state plus stack," producing different verifiers.

Fix: define a separate `quotient_state` region:

```text
quotientStateLen = (2 + selectorPowerWords) * W
quotientState = AllocAfter(... after quotient temps ...)
quotientStack = AllocAfter(... after quotient state ...)
```

Or explicitly define `C.quotientStackWords` as including persistent state,
operand stack, and native callback scratch.

#### 2. Scalar-inversion scratch can be allocated inside Solidity-reserved memory

Section 9.5 defines:

```text
scalarInvScratch = AllocPhaseScratch(
  scalar_inv_scratch,
  max(vkStart - 0x100, 0),
  0xc0,
  ScalarInv
)
```

But Section 9.1 says any nonzero planned region must start at `>= 0x80`. If
`vkMptr < 0x180`, then `max(vkMptr - 0x100, 0)` is below `0x80`, violating V3.
For example, `vkMptr = 0x80` gives scratch start `0x00`.

Impact: the planner can deterministically produce an invalid memory map for
plausible VK starts.

Fix: either require `vkMptr >= 0x180`, or change the allocation formula and
separately prove it cannot overlap the permanent VK region:

```text
scalarInvStart = max(vkMptr - 0x100, 0x80)
require scalarInvStart + 0xc0 <= vkMptr
```

#### 3. Compact quotient program decoding needs a byte length, but the VK layout does not store one

Section 5.3 says decoding is parameterized by an explicit unpadded byte length
`n`. Section 5.4 allows reserving more program words than are used, leaving
unused reserved words as zero.

But the VK header and section layout do not store `n`.

Impact: if a verifier decodes all reserved program words, the trailing zero
bytes become opcode `0x00`, which is invalid. If a verifier trims trailing
zeros, valid programs ending in zero bytes become ambiguous. Clean-room
implementations can diverge.

Fix: add `quotient_program_byte_len` to the VK header, or define it as a
generated verifier constant that is part of conformance and pinning. Do not
infer it from section length or trailing zeros.

#### 4. Accumulator validation is not specified

The spec defines accumulator tail sizes, limb width, memory regions, and a
pairing-batch domain tag, but it does not define the actual accumulator
validation equations.

Missing items include:

- limb packing order and endianness inside public-input scalar words;
- limb range checks;
- reconstruction modulo the BLS12-381 base field;
- point-on-curve and subgroup checks;
- semantics of the "fixed-base scalar tail";
- the MSM/pairing equations being checked;
- how the `pairing-batch-acc-kzg` domain tag is used.

Impact: two conforming implementations could accept different accumulator
tails. Worse, an implementation could validate only the shape and not the
accumulator relation.

Fix: add a normative accumulator-validation section with exact public input
parsing, reconstructed points/scalars, curve checks, batching challenge
derivation, MSM construction, and pairing equation.

#### 5. `x_split` is undefined in the quotient commitment contribution

Section 10.1 says the quotient commitment side contributes:

```text
(1 - x^n) * sum_i x_split^i Q_i
```

But `x_split` is never defined.

Impact: this is a soundness-critical scalar. Implementers may use `x`, `x^n`, a
truncated challenge, or a Halo2-specific split challenge. Only one can be
correct.

Fix: define the exact split power. For example, if intended:

```text
x_split = x^n
```

then say:

```text
(1 - x^n) * sum_i (x^n)^i Q_i
```

Also define how this interacts with the "outer single-H" feature.

#### 6. PCS query order and proof-evaluation read order differ, but no mapping is defined

Main proof evaluations are read in this order:

1. committed-instance evaluations;
2. advice evaluations;
3. fixed evaluations;
4. etc.

PCS queries are ordered differently:

1. advice queries;
2. committed-instance queries;
3. permutation product queries;
4. etc.

The spec only says that the PCS query count must equal the main
proof-evaluation count before appending the synthetic linearization query.

Impact: count equality is not enough. Each PCS query needs a precise pointer to
the claimed evaluation scalar read earlier. Otherwise an implementation could
pair an advice commitment with a committed-instance evaluation, or vice versa.

Fix: define an explicit query-to-evaluation-slot map. For every PCS query triple
`(C, rho, e)`, specify exactly which evaluation-read entry supplies `e`.

#### 7. Dummy evaluation count is ambiguous

Section 6 defines the main proof-evaluation count as the list length before
dummy PCS evaluations are appended. Section 7 takes an evaluation scalar count
`E` for the proof layout. Section 8 says the transcript absorbs "all main
evaluation scalars, including dummy evaluation scalars when enabled."

Impact: `E` can mean either raw main evaluations or raw plus dummy evaluations.
That changes proof length, transcript state, and the PCS query schedule.

Fix: introduce separate names:

```text
E_raw      = non-dummy proof evaluations
E_dummy    = dummy evaluations added by fewer-point-sets planning
E_total    = E_raw + E_dummy
```

Then state:

```text
proof layout uses E_total
transcript absorbs E_total
protocol invariant before dummy uses E_raw
PCS query list after dummy uses E_total
```

#### 8. Empty MSMs are possible but EIP-2537 rejects empty variable-length inputs

The spec says identity commitments are omitted from MSM input but still
contribute to scalar equations. If a point set contains only identity
commitments, the commitment-side MSM for that set has zero terms. Similarly,
accumulator or final MSM shapes may be zero in some feature combinations.

EIP-2537 requires variable-length operations such as MSM and pairing to error on
empty input. ([Ethereum Improvement Proposals][1])

Impact: a verifier that blindly calls G1MSM with zero terms will revert on
proofs that the mathematical spec may intend to handle.

Fix: define zero-term MSM behavior in the generated verifier:

```text
if msm_terms == 0:
    result = G1 identity
else:
    call G1MSM precompile
```

Also add a validation rule requiring every generated precompile call to have a
nonzero input length unless the precompile ABI allows empty input.

#### 9. The spec overstates subgroup validation for G1ADD paths

Section 8 says every absorbed proof G1 must later be consumed by an EIP-2537 path
that validates curve and subgroup membership. But EIP-2537's G1ADD precompile
does not subgroup-check; MSMs and pairings do. ([Ethereum Improvement
Proposals][1])

Impact: if an implementation routes an untrusted proof point through G1ADD and
treats success as subgroup validation, the spec's stated invariant is false.

Fix: say specifically:

```text
Every untrusted proof G1 must be passed to G1MSM or pairing, or otherwise
explicitly subgroup-checked, before its value can affect acceptance. G1ADD
success is not a subgroup check.
```

### Medium-impact issues and conformance hazards

#### 10. `vk_digest` is not defined

Header word 0 is `vk_digest`, and the transcript begins by absorbing it. But the
spec never defines how to compute it.

Impact: proof compatibility depends on this digest. Two clean-room
implementations can produce different transcript challenges for the same VK.

Fix: define the exact VK digest algorithm: serialization order,
inclusion/exclusion of quotient sections, fixed/permutation commitments, KZG
parameters, domain separators, endianness, and hash/reduction rules.

#### 11. "Truncated challenges" are not specified

Section 8 says:

```text
If truncated challenges are enabled, stored powers of x1 and x4 are truncated
as in the Midnight verifier...
x3 is truncated immediately after squeezing.
```

This is not a clean-room specification.

Impact: truncation changes the accepted proof language. "As in Midnight" is an
external implementation dependency.

Fix: specify exactly:

- number of bits retained;
- whether truncation happens before or after reduction mod `r`;
- whether powers are computed from truncated or full values;
- whether transcript absorption uses truncated or full challenge words;
- how `x3` truncation is encoded.

#### 12. `fold_selector` encoding silently limits selector count and selector gaps

Opcode `0x0b fold_selector` uses a 24-bit operand:

```text
s = w >> 16      // 8 bits
g = w mod 2^16  // 16 bits
```

So it supports at most 256 selector buckets and selector gaps below 65536.

Impact: large circuits can become unencodable or, worse, incorrectly encoded if
the generator truncates.

Fix: add static validation:

```text
numSimpleSelectors <= 256
every selector gap <= 65535
```

Or add a wider selector-fold opcode.

#### 13. `c_perm = d - 2` can be zero or negative

Section 6 defines:

```text
c_perm = d - 2
z_perm = ceildiv(|P|, c_perm)
```

If `d <= 2` and there are permutation columns, this divides by zero or by a
negative number.

Impact: undefined generator behavior.

Fix: require:

```text
if |P| > 0 then d >= 3
```

Probably reject `d < 3` globally unless there is a proven reason to allow it.

#### 14. `omega_inv_to_l` / `rotationLast` notation is inconsistent

Header word 6 is:

```text
omega_inv_to_l = omega^{-L}, where L = |rho_last|
```

But permutation identities use:

```text
z(omega^{rho_last} x)
```

And the memory planner uses `|M.rotationLast|` as a count.

Impact: `|rho_last|` could mean absolute value of a rotation, cardinality of a
rotation set, or list length. These are not interchangeable.

Fix: use distinct names:

```text
rho_last_value       // actual rotation exponent
num_rotation_last    // count of last-rotation entries
omega_inv_to_l = omega^{-rho_last_value}
```

#### 15. ABI canonicality is not fully specified

Section 7 explicitly requires the first head word to be `0x40`, exact proof
length, exact instance length, and no trailing calldata. But canonical ABI also
requires the second dynamic head to point exactly after the padded proof blob,
and the `bytes` padding should be checked if canonical encoding is required.

Impact: calldata malleability and implementation divergence. One verifier may
accept nonzero proof padding or weird dynamic heads; another may reject.

Fix: state exact checks:

```text
head0 == 0x40
head1 == 0x60 + ceilword(proof_len)
proof_padding_bytes == 0
instances_len == EXPECTED_NUM_INSTANCES
calldatasize == 0x04 + head1 + 0x20 + 32 * instances_len
```

Also require `head1` not to overlap the proof area.

#### 16. Simple selector lowering is unsafe unless selector usage is restricted

The spec says simple-selector fixed-column queries lower to constant `1` and
are excluded from proof-evaluation reads.

That is correct only if those fixed-column queries occur solely as the gate's
selector factor and are later reintroduced through selector buckets.

Impact: if a simple-selector fixed column is referenced as a normal fixed
expression anywhere else, lowering it to `1` changes the quotient identity.

Fix: add validation:

```text
A simple-selector fixed column may only occur as the designated selector of its
own gate.
Any other query to that fixed column is inadmissible.
```

Or treat such columns as non-simple fixed columns when queried normally.

#### 17. Native quotient callbacks are not fully validated by the bytecode validator

The VM validator checks stack shape, but it cannot verify that:

- `native_permutation` folds exactly the permutation identity range;
- `native_lookup` folds exactly the lookup identity range;
- `native_identity(i)` corresponds to the declared global identity position;
- callbacks advance selector/main accumulators exactly as the interpreted stream
  would.

Impact: native callbacks are correctness-critical but mostly outside the
bytecode validation model.

Fix: add a native-callback manifest:

```text
callback_id
start_identity_index
identity_count
target sequence
required scratch words
```

Then require validation that callback markers exactly cover their declared
identity ranges without overlap or gaps.

#### 18. External quotient frame base is underdefined

Section 11 defines:

```text
F0 = VK_MPTR
F1 = max(VK_MPTR + |VK_payload|, REVERSED_EVALS_MPTR + W*E)
```

Then later uses:

```text
B_q = QUOTIENT_FRAME_BASE
L_q = QUOTIENT_FRAME_LEN
```

But it never explicitly states:

```text
QUOTIENT_FRAME_BASE = F0
QUOTIENT_FRAME_LEN = F1 - F0
```

Impact: external evaluator implementations may copy the frame to a different
base than the absolute addresses expect.

Fix: define those equalities normatively and require that all absolute memory
addresses used by the external evaluator are the same as in the main verifier
after copying.

#### 19. Bad-challenge zero denominators are undefined in KZG batching

Section 8 computes:

```text
d_j = product_{p in P_j}(x3 - p)
t_j = (a_j - R_j(x3)) * d_j^{-1}
```

But it does not say what happens if `x3` equals one of the rotation points.

Impact: inversion of zero is undefined. An implementation using
`modexp(0, r-2, r)` will get `0`, silently changing the equation.

Fix: require:

```text
if d_j == 0: revert
```

This is a rare random-oracle edge case, but the verifier spec should still be
total.

### Smaller but real spec bugs

#### 20. Accumulator text contradicts itself

Section 4 says a point-and-scalar accumulator tail contains two points plus two
scalar words. Later, Section 12 says:

```text
The current accumulator encoding contains two point coordinates and two carried
scalars.
```

"Two point coordinates" is one affine point, not two points.

Fix: change it to:

```text
two affine points, i.e. four base-field coordinates, and two carried scalar
words
```

#### 21. Seven-limb arithmetic text contradicts the opcodes

Section 12 says limb-specialized quotient VM instructions use:

```text
seven limbs, six linear coefficients, 49 schoolbook products, and 13 output
diagonals
```

But `LIN7`, `BILIN7_ROW`, `BILIN7_PAIRWISE`, and `MODARITH7` use seven
coefficient/memory pairs or 13 diagonal coefficients.

Impact: implementers cannot know whether six or seven linear coefficients are
expected.

Fix: correct the count or explain which coefficient is implicit.

#### 22. `num_instances` is ambiguous with two instance columns

Admissible inputs require exactly two instance columns: one committed and one
non-committed. The ABI has a single `uint256[] instances`, and the VK header has
`num_instances`.

Impact: `num_instances` could mean total instance cells across both columns, or
only non-committed public-input scalars.

Fix: define:

```text
num_instances = length of the non-committed public-input vector supplied in ABI
```

And separately define whether committed-instance-column evaluations are always
proof scalars, always zero, or derived from some other source.

#### 23. The synthetic linearization query is underspecified

The spec says the synthetic linearization query must be last and is expanded
into quotient-limb terms and simple-selector terms. But it does not fully
define:

- its rotation point;
- its claimed scalar evaluation;
- exact quotient-limb coefficients;
- exact selector commitment coefficients;
- whether identity commitments are allowed in it;
- how it is represented in the query-to-evaluation map.

Impact: this is PCS-critical and must be deterministic.

Fix: add a subsection defining the synthetic query as an explicit virtual
commitment/evaluation pair and its expansion into MSM terms.

### Summary

The biggest correctness blockers are:

1. quotient state/stack aliasing;
2. scalar-inversion scratch violating reserved memory;
3. missing quotient program byte length;
4. missing accumulator validation semantics;
5. undefined `x_split`;
6. ambiguous dummy evaluation counts;
7. missing query-to-evaluation mapping.

These should be fixed before treating the document as a conformance spec. The
rest are mostly edge-case, interoperability, or validation issues, but several
could still become soundness bugs in a generated verifier.


## 2026-08-13 — independent external review (MF series)

An independent review of the rendered `moonlight-wrap` artifacts (verifier
sha256 `555ed976…6798`, VK `7ca78ec2…b7ec`; byte-identical to
`fixtures/moonlight-wrap/`) run as three separate passes — cryptographic
implementation, ZK/protocol soundness, and EVM/software security — plus a
line-by-line equivalence pass against `midfall/proofs` and machine
recomputation of every recomputable constant.

**No soundness-relevant defect was found.** The transcript schedule is
byte-exact against the Rust verifier, every absorbed proof point provably
reaches a subgroup-enforcing precompile, the linearization/PCS algebra is
exact, and the memory plan has no live overlaps. Findings are one liveness
bug and a set of hardening/diagnostic items.

| ID | Sev | Finding | Disposition |
| --- | --- | --- | --- |
| MF-1 | High | `MODEXP_GAS = 1360` is the EIP-2565 price; EIP-7883 (Osaka/Fusaka) prices the same frame at 4064, so every proof reverts `PrecompileFailed` on a repriced chain — and the constructor never probed modexp, so deployment succeeded silently | **Fixed** (`modexp_gas_word_frame` takes the max over live schedules; constructor modexp known-answer probe added) |
| MF-2 | Low | The memory-layout guard — the only on-chain check for a bad recompile — reverted bare | **Fixed** (`MemoryLayoutViolated()`, typed on the runtime and constructor paths) |
| MF-3 | Low | Quotient VM: fold-on-empty re-folds a stale top; native callbacks reset `q_sp` instead of asserting it, hiding dropped operands; u16 const indexes unclamped; `q_sp` unbounded | **Fixed** (four guards; u8 indexes keep their documented exemption, u16 do not) |
| MF-4 | Low | `PrecompileFailed` / `BadPointEncoding` / `ProofRejected` conflated chain faults with rejected input on three paths | **Fixed** (cause flags threaded through `batch_invert` and `validate_public_accumulator`; `ec_pairing` split; triage table in `DEPLOYMENT_AND_INCIDENT_RESPONSE.md` §6) |
| MF-5 | Info | A low-level `staticcall` to an address with no code returns success — a mis-wired wrapper reads it as a valid proof | **Documented** (wrapper obligation W-4) |
| MF-6 | Info | Single-reduction `mod r` sampling bias (max point mass ≈1.36× uniform) | **Accepted**, parity with the Rust reference; already covered by §5.1's ×1.3585 factor. Regenerate in lockstep if the reference moves to 512-bit reduction |
| MF-7 | Info | 128-bit truncated challenges cap batching soundness | **Accepted**, already recorded and signed off as §5.1 (L-10) |
| MF-8 | Info | Set-0 has 43 eval terms but 42 commitment terms (the committed-instance column's commitment is the identity), so its eval is forced ≈0 only indirectly via x1-batching | **Documented** in the PCS emitter |
| MF-9 | Info | The canonical identity accumulator `(O, O)` is well-formed and passes the pairing layer | **Documented** (wrapper obligation W-5) |
| MF-10 | Info | Native-identity selector folds appeared to hardcode a `y¹` gap | **WITHDRAWN — false positive.** All three emission sites already use `selector_fold.gap_for(identity)`; the fixed `Some(1)` is confined to `native_identity_estimate_block`, a size/gas proxy for gate-selection that is never emitted, and whose doc comment explicitly warns against "fixing" it to call `gap_for` (the fold plan is derived from the selection outcome, so it does not exist yet at that point). Recorded so the warning is not overridden by a future reviewer making the same mistake. |
| MF-11 | Info | The transcript stream is positionally framed (a point and four scalars are byte-identical) | **Accepted**; identical to §5.2 (I-5). Any future variable-length section would need explicit length tags |
| MF-12 | Info | `assembly ("memory-safe")` is unsound by the letter of the annotation | **Accepted**; safe here via the terminal block + FMP guard + pinned pragma, now noted at the annotation site |

Also proposed by the review and **withdrawn on inspection**: a CI job
recomputing `vk_digest` from the rendered VK payload. The payload word is
written directly from `self.vk.transcript_repr()` in `lowering/vk.rs` — a
single expression over a single in-memory VK, not two independent paths — so
such a test would assert `x == x`. The residual it was meant to close (that
`vk_digest` binds the *semantic* constraint system) is not reachable this way;
it is covered by the trace-replay tests and, off-transcript, by `BUILD_ID`.
See §5.3 for the standing M-4 decision.

**Not closed by these commits:** the committed fixtures and the Sepolia
deployment predate the MF-1 fix and are marked STALE; regeneration needs the
pinned solc. The replay harness also cannot exercise EIP-7883 — the pinned
revm 19 has an Osaka spec, but its modexp handler is still `berlin_run` — so
real coverage awaits a revm bump; `src/evm.rs` records that gap at the
`SpecId` pin.

[1]: https://eips.ethereum.org/EIPS/eip-2537 "EIP-2537: Precompile for BLS12-381 curve operations"
