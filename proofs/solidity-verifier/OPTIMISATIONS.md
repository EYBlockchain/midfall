# Gas-cost analysis & optimisation roadmap

> Companion to [`ARCHITECTURE.md`](./ARCHITECTURE.md). See §2 (on-chain
> primitives), §5.4 (benchmark commands), §7 (tradeoffs), and §9
> (generalisation roadmap) for cross-references.

## 1. Baseline

`forge test --gas-report` currently reports per-call `verify()` cost of
≈ **11.25 M gas** on BLS12-381, with a ±11-gas spread across the 9
distinct call-sites in `test/PoseidonVerifier.t.sol` (the spread is
calldata-length variation only):

```
| verify | 11 253 184 | 11 253 185 | 11 253 184 | 11 253 195 | 9 |
```

This is ≈ 40× a flat BN254 halo2-solidity-verifier (~250–300 k gas for a
comparable circuit). This document explains where the delta comes from
and what it would take to close.

## 2. Why 11.25 M?

The gap decomposes into five stacked sources. Rough orders of magnitude:

### 2.1 Curve: BLS12-381 vs BN254 (~5–10×)

halo2-solidity-verifier targets **BN254** via the mainnet `alt_bn128`
precompiles (0x06 / 0x07 / 0x08). Our crate targets **BLS12-381** via
the Prague-era EIP-2537 precompiles (0x0b / 0x0c / 0x0f). Rough per-op
costs:

| op              | BN254 (alt_bn128) | BLS12-381 (EIP-2537) |
|-----------------|-------------------|----------------------|
| G1 add          | 150 gas (0x06)    | 375 gas (0x0b)       |
| G1 mul          | 6 000 gas (0x07)  | ~12 k + 22·k gas for k-term MSM (0x0c) |
| 2-pair pairing  | ~113 000 gas (0x08) | ~124 000 gas (0x0f) |

More importantly, halo2-solidity-verifier batches *everything* into a
single ~30–50 term MSM and one 2-pair pairing, so most of its gas
budget is just those two precompile calls. On BLS12-381 the same two
calls are ~2× more expensive, and the verifier also makes **many
more** G1ADDs / ModExp calls along the way (curve decompression,
`Fr`-inverse for Lagrange, Fp-powers for y-recovery) because we don't
pre-bake constants.

### 2.2 Architecture: interpreter vs template-generated flat code (~4–5×)

halo2-solidity-verifier is a **template-based code-generator**: for a
given circuit it emits a flat Yul/Solidity verifier where every gate,
every lookup, every permutation-check scalar is hard-coded as an
immediate. No loops, no VK-blob walks, no runtime bytecode
interpretation.

Our verifier is the opposite — it's a **runtime interpreter** over a VK
blob (see `ARCHITECTURE.md` §2.1–2.2). Concretely the expensive bits
are:

- `_loadVk()` + `extcodecopy` of a ~6 KB VK blob (paid once up front).
- `_evalBytecode` walks RPN opcodes for every gate / lookup / trashcan
  expression, per-expression, per-evaluation. Each opcode does at
  least one `Fr` op (`_frMul` / `_frAdd`) plus stack-memory accounting.
  For poseidon this is evaluated for 22 identity expressions.
- Each of the ~22 identity evaluations calls back into `_evalBytecode`,
  so the per-gate cost is dominated by interpreter overhead, not by
  the field op itself.
- The lookup / trashcan bytecode trees add another dozen interpreter
  passes.

halo2-solidity-verifier inlines every `Fr` op as a constant-address
`MULMOD` / `ADDMOD` in the compiled bytecode, so the per-gate cost
collapses to literally a few hundred gas.

### 2.3 Solidity vs Yul assembly (~2×)

halo2-solidity-verifier emits raw Yul (and/or inline-assembly Solidity)
end-to-end: direct memory pointers, no Solidity-level bounds checks,
no free-memory-pointer bumps, no ABI-decode overhead. Our verifier is
plain Solidity 0.8.24 with `via_ir` but still pays for:

- `bytes calldata proof` ABI decoding + `_readPoint48` / `_readScalar32`
  helpers.
- Dynamic-array memory allocation for intermediates (`commScalars`,
  `identities_points` / `identities_scalars`, …).
- Solidity's free-memory-pointer plus per-call stack frames and
  per-call `SELFCODESIZE` etc.

### 2.4 Dev-time instrumentation (~0.5–1 M gas)

Every transcript op (`_squeeze*`, `_absorb*`) emits a `TraceChallenge`
/ `TraceReadScalar` / `TraceReadPoint` event, every algebraic
intermediate emits `TraceIntermediate`, and every phase emits
`PhaseGas`. A single `LOG2 <32 bytes>` costs ~1 500 + 32·8 ≈ 1 750
gas; we emit **hundreds** of these over the course of one `verify()`.

These exist specifically to power the §3-bullet-4 trace-diff harness
against the Rust side — a production deploy should strip them
(compile-time `emit` → `/* */` or a no-op trace library) and save
~0.5–1 M gas outright.

### 2.5 Single-shot keccak transcript (~100–300 k gas)

Solidity's `keccak256` opcode only supports one-shot hashing, so
`Transcript.buf` accumulates everything and every `_squeeze64`
rehashes the entire buffer. For a ~9 KB transcript across ~30
squeezes, that's O(n²) in keccak input size. halo2-solidity-verifier
uses a sponge-friendly construction (or just one flat call per
squeeze) — not O(n²).

## 3. Closing the gap

Rough sizing, stackable (applied cumulatively on top of the 11.25 M
baseline):

| Change                                                               | Savings    | Effort       |
|----------------------------------------------------------------------|------------|--------------|
| Strip `Trace*` + `PhaseGas` events                                   | 0.5–1 M    | trivial      |
| Flatten keccak transcript (per-squeeze hashing, not cumulative)      | 0.1–0.3 M  | small        |
| Port hot loops (Fr arithmetic, RPN interpreter) to Yul assembly      | 1–2 M      | medium       |
| Replace RPN interpreter with `render_verifier(&VkInfo)` template codegen (see `ARCHITECTURE.md` §9 workstream #3) | 3–5 M      | medium–large |
| Switch to BN254 + mainnet `alt_bn128` precompiles                    | 5–8 M      | rewrite the curve layer (`eip2537.rs` → `bn254.rs`) + a new SRS |

In other words: the current 11.25 M is the cost of **(a) BLS12-381 +
(b) a fully general interpreter-driven verifier + (c) full
instrumentation**, not a fundamental limitation.

- Dropping to the 0.5–1 M range **on BN254** is achievable with the §9
  workstreams (generic codegen + strip instrumentation).
- Staying **on BLS12-381**, the realistic floor is maybe 1.5–3 M no
  matter what, because of the per-op precompile pricing alone.

## 4. Recommended sequencing

If the goal is production deployment, the cheapest-first ordering is:

1. **Strip instrumentation** (trivial, ~1 M gas). Gate `Trace*` and
   `PhaseGas` events behind a build-time flag so `generate --release`
   emits a no-op trace library and the equivalence tests still run
   against the instrumented build.
2. **Flatten keccak transcript** (small, ~0.2 M gas). Replace the
   cumulative buffer with per-squeeze `keccak256(prev_state ‖
   absorbed)` — still byte-for-byte compatible with the Rust sponge
   as long as the absorb ordering matches.
3. **Yul-asm hot path** (medium, ~1.5 M gas). Rewrite `_frMul` /
   `_frAdd` / `_frInv` / `_evalBytecode` in inline assembly. Preserve
   the Solidity entry point so tests still type-check.
4. **Template codegen** (medium-large, ~4 M gas). Add
   `render_verifier(&VkInfo) -> String` next to `render_verifying_key`
   and switch `PoseidonVerifier.sol` to the generated output. This
   is also the prerequisite for circuit generalisation (§7.1–7.2 in
   ARCHITECTURE.md).
5. **BN254 curve port** (large, ~6 M gas). Only worth doing after
   (1)–(4) because the BLS12-381 interpreter dominates the budget
   until those are landed. Requires a new trusted-setup + a BN254
   SRS loader + rewriting `eip2537.rs` → `bn254.rs` + the obvious
   changes in `codegen.rs` point serialisation.

After (1)–(3) alone the cost should fall to ≈ 8–9 M. After (1)–(4) to
≈ 3–5 M. After (1)–(5) to ≈ 250–500 k, matching halo2-solidity-verifier.

## 5. Measurement pointers

- `forge test --gas-report` (ARCHITECTURE.md §5.4) prints the
  min/avg/median/max/#calls row for each external function.
- `forge test --match-test test_verify_poseidon_proof -vv`
  (ARCHITECTURE.md §5.4) prints one `  . <phase>` line per `PhaseGas`
  event — useful for attributing cost to individual phases (transcript
  absorbs, identity evaluation, linearization, multi_prepare, final
  pairing).
- `PhaseGas(name, gasUsed)` event indices follow the Phase numbering
  in `ARCHITECTURE.md` §2.2 (Phase 0 through Phase E). Any optimisation
  should be able to show a per-phase gas delta, not just a single
  aggregate number.
