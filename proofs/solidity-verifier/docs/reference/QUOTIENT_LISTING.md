# Quotient-VM Listing and Identity Manifest

The compact quotient VM stores most custom-gate arithmetic as bytecode in the
VK payload (`quotient_program` words) with a constant table
(`quotient_const` words). The Solidity only contains the interpreter, so a
reviewer who audits the generated contracts, and not the generator, cannot see
from the `.sol` files which bytes implement which gate polynomial.

`SolidityGenerator::render` therefore also returns two text artifacts:

| Field | Content |
| --- | --- |
| `RenderedArtifacts::quotient_listing` | Annotated disassembly, organised by identity `j` |
| `RenderedArtifacts::quotient_manifest` | JSON identity manifest (hashes, offsets, execution plan, constants, slot map) |

They are produced on every `render` call (Vm lowering is the only quotient
lowering in this crate) and never change the rendered Solidity: the listing is
built after the verifier, VK and evaluator sources, from the same converged
plan, and a crate test renders with and without it and compares the sources.
Measured cost on the Moonlight wrap verifier (49 identities, 4559-byte
program): about 8-12 ms on top of a 120-122 ms render. Callers that only write
`verifier` / `verifying_key` see the same Solidity; the only behavioural change
is that `render` returns `GeneratorError::Planning { stage: "quotient listing", .. }`
if the validation below fails.

## What the listing is built from

The listing is decoded from the program bytes and constant words **as they are
embedded in the rendered VK payload** (after run compaction and word packing;
only the zero padding of the last program word is stripped), by the decoder in
`src/lowering/quotient_numerator/vm/disasm.rs`. That decoder is written against
the operand layouts of `templates/partials/quotient_numerator/QuotientNumeratorBlock.yul`
and does not reuse the builder's length walker or stack validator. It covers
all 31 opcodes of the ABI.

The identity metadata comes from the generator's existing execution manifest
(`QuotientProgramPlan::execution_manifest`, `QuotientIdentitySource`,
`QuotientTarget`), i.e. the same source of truth as
`SolidityGenerator::quotient_identity_manifest`. Slot names come from the
generator's evaluation plan (`Data`), the same map the verifier's proof reader
uses.

## Render-time checks (fail closed)

Rendering fails, naming the identity where applicable, if any of these fails:

1. The program bytes and constant words read back from the VK payload equal
   the finalized builder output, reserved constant words and program padding
   are zero, and `q_program_mptr` / `q_const_mptr` equal `VK_MPTR + 32 * offset`.
2. The decoded instructions split into identity-stream items with the VM stack
   discipline (binary ops need two values, folds exactly one, native markers an
   empty stack, the program ends on a boundary), and the item kinds and native
   callback indices equal the execution plan.
3. The rendered listing lines tile program bytes `[0, len)` exactly once.
4. Inline prefix + program items + trash suffix execute identities `0..m-1`
   exactly once, in order.
5. For every interpreted (VM) identity:
   * the fold opcode matches its bucket (`FOLD_MAIN` for main,
     `FOLD_SELECTOR k` for simple-selector bucket `k`) and the selector gap
     equals `j - (previous j in bucket k)` (0 for the first), recomputed from
     the identity order alone;
   * every memory operand is a published evaluation slot;
   * the bytes, run through a Rust interpreter of the VM, equal
     `Expression::evaluate` of the gate polynomial
     `vk.cs().gates()[g].polynomials()[p]` at 4 pseudo-random points (leaves
     bound through the same slot map; simple-selector fixed columns are 1, as
     in `partially_evaluate_identities`). The points are derived from
     keccak256 of the program and constant table, so renders are reproducible;
   * when both sides expand within 4096 monomials, the symbolic expansion of
     the bytes equals the expansion of the gate polynomial.

**Limit.** These checks tie the pinned VK bytes to the Rust gate expressions
through a Rust interpreter of the VM ABI. They do not check the Yul
interpreter; its semantics are covered by the EVM tests (fixture tests,
shape-fuzz and trace-differential tests), not by this check. They also do not
check the inline-prefix and native-callback Yul snippets, which the listing
prints verbatim for review, and they take the slot map (which eval word holds
which query) from the generator's evaluation plan; the manifest publishes that
map (`slots[].eval_index`) so it can be compared with the Rust verifier's
evaluation read order.

## Listing format

1. Header: generator version, VK runtime length and codehash (the value the
   verifier pins as `EXPECTED_VK_CODEHASH`), `VK_MPTR`, payload/memory ranges
   and keccak256 of the constant table and program, `m`, and the simple-selector
   buckets with their tail exponents.
2. Fold semantics and the render-time check results.
3. Identity index: `j`, `y^(m-1-j)`, bucket, execution kind, program bytes,
   source.
4. One section per identity, in `j` order:
   * header: `j`, gate name / polynomial index (or family and local index),
     bucket, `y` power, execution kind;
   * VM identities: byte range, memory range, constants used, check result,
     then a **program block**;
   * inline identities: the Yul the verifier contains for that identity;
   * native gate identities: the `NATIVE_IDENTITY` program block and the Yul of
     its callback case;
   * permutation / lookup / trash families: the native marker block (or "no
     program bytes" for the trash suffix), the Yul block, and one line per
     identity with its fold position and meaning.
   In Yul snippets, `;; 0xADDR=name` is an annotation added by the listing.
5. Evaluation-slot map: memory address, name, kind, eval index, detail.
6. Constant table: index, memory, VK payload offset (as in the
   `mstore(add(payload, 0x....), ...)` lines of the VK source), reference
   count, value, readable form (`1`, `2^56`, `-1`, `r - 0x…`).

A program block starts with `  >>> program [start, end) <kind> j=...` and ends
with `  <<< program [start, end)`. Each line is

```text
  <offset> <memory> <raw bytes grouped by field>  <MNEMONIC> <operands>
```

Dynamic opcodes (`MODARITH7`, `LIN7`, `BILIN7_*`, `AFFINE_SUM`, `RUN_*`) print
one line per sub-term with its own offset and bytes; lines without an offset
cover no bytes. Memory operands are printed as slot names, constants as
`c[i]=<hex> (<readable>)`, e.g. `c[2]=0x100000000000000 (2^56)` or
`c[8]=0x73eda753..00000000 (-1)` (hex above 20 digits is abbreviated; the
constant table has the full words). A VM block ends with the polynomial rebuilt from its bytes,
with the largest common monomial factored out.

Slot names: `a_<col>`, `f_<col>`, `ci_<col>` (committed instance), rotation
suffixes `_next`, `_prev`, `_nextK`, `_prevK`; `sigma_<i>`, `perm_z_<s>[_next|_last]`,
`lk<l>_m`, `lk<l>_h<c>`, `lk<l>_z[_next]`, `trash_<t>`, `ch_<i>` (user
challenge), `dummy_<i>`; VM tokens `l_0`, `l_last`, `l_blind`, `beta`,
`gamma`, `x`, `theta`, `trash_challenge`, `instance_eval`.

## Manifest format

`format = "halo2_solidity_verifier/quotient-vm-manifest"`, `format_version = 1`.

| Key | Content |
| --- | --- |
| `generator` | crate name and version |
| `render` | `vk` (`separate`/`embedded`), `quotient` (`inline`/`external_pinned`), `trace` |
| `vk` | `runtime_codehash` (keccak256 of `0xfe \|\| payload`), `codehash_pinned_by_verifier`, runtime/payload lengths, `payload_keccak256`, `header_words`, `vk_mptr` |
| `program` | `keccak256`, `length_bytes`, payload word offset/count, payload and runtime byte offsets, `memory_start`/`memory_end`, `padding_bytes` |
| `constants` | `keccak256` (of the used words, 32-byte big-endian each), `count`, `reserved_words`, offsets, `table[]` = `{index, value, readable, vk_payload_offset, memory, refs}` |
| `memory` | `VK_MPTR`, `REVERSED_EVALS_MPTR`, `num_evals`, `CHALLENGE_MPTR`, `SELECTOR_ACC_MPTR`, quotient scratch/state pointers |
| `tokens` | VM memory tokens: `{token, symbol, name, memory}` |
| `slots` | evaluation-slot map: `{memory, name, kind, column?, rotation?, index?, eval_index?, detail}` |
| `identities` | `m`, per-family counts, `simple_selector_fixed_columns`, `selector_buckets[] = {index, fixed_column, identities, tail_exponent}` |
| `program_items` | stream items in program order: `{index, kind, byte_start, byte_end, identities, native_index?}` |
| `entries` | one per identity in `partially_evaluate_identities` order (see below) |
| `validation` | points, seed, counts of VM identities checked numerically / symbolically, scope statement |
| `listing` | keccak256 and length of the listing text |

Each `entries[j]` has `j`, `source` (`family` = `gate` with gate index/name,
constraint index/name, polynomial index; or `permutation` / `lookup` / `trash`
with `local_index`), `target` (`main`, or `selector` with `selector_index`,
`fixed_column`, `gap`), `y_exponent = m-1-j`, and `execution`:

| `execution.kind` | Extra fields |
| --- | --- |
| `inline_direct_prefix` | `inline_index` |
| `vm_bytecode` | `program_item`, `byte_start`, `byte_end`, `memory_start`, `constants_used`, `fold`, `max_stack`, `monomials` |
| `native_gate_callback` | `program_item`, byte range of the marker, `native_index` |
| `native_permutation` / `native_lookup` | `program_item`, marker byte range, `fold_position`, `family_size`, `meaning` |
| `trash_suffix` | `fold_position`, `family_size`, `meaning` |

VM entries also carry `check` (reference, points agreeing, symbolic result).

## Auditor workflow: regenerate from deployed bytes

`examples/quotient_listing.rs` re-derives the program blocks from a VK and the
manifest, without the generator:

```bash
cargo run --release -p halo2_solidity_verifier --example quotient_listing -- \
    Halo2VerifyingKey.sol QuotientManifest.json \
    --listing QuotientListing.txt \
    --verifier Halo2Verifier.sol \
    [--evaluator Halo2QuotientEvaluator.sol] \
    [--out regenerated-blocks.txt]
```

The first argument may also be the deployed VK runtime as hex
(`0xfe || payload`, e.g. `cast code <vk>`). The tool:

1. parses the payload words (`mstore(add(payload, ...), ...)` lines, or the
   runtime), and hashes the runtime (`extcodehash`);
2. finds the constant table by the manifest's keccak256 and reports the payload
   shift `delta` (words) between this VK and the manifest's layout;
3. extracts the program (length from the manifest), checks the padding and its
   keccak256; when `delta != 0` it also moves every memory-pointer operand
   `>= VK_MPTR` by `-32*delta` bytes and compares that hash;
4. decodes the program with the crate decoder, re-renders every program block
   from the bytes and the manifest's names, and compares with the manifest
   (item kinds, byte ranges, identities, constants used, fold bucket and gap)
   and, with `--listing`, block by block with the shipped listing, plus the
   listing's keccak256;
5. with `--verifier`, checks `EXPECTED_VK_CODEHASH_WORD` and
   `EXPECTED_VK_LENGTH` against this runtime; in the interpreting contract (the
   verifier, or `--evaluator` for a pinned external quotient evaluator) it checks
   `VK_MPTR`, `q_const_mptr`, `q_program_mptr`, the `q_end` length and the
   memory anchors (`REVERSED_EVALS_MPTR`, `CHALLENGE_MPTR`, `SELECTOR_ACC_MPTR`,
   the VM token symbols) against the manifest shifted by `32*delta`;
6. with `--out`, writes the program blocks re-rendered in this VK's own
   addresses.

Exit status: `0` all checks pass exactly; `2` all checks pass only after the
reported payload shift; `1` otherwise.

### Payload shift

A VK whose header has a different number of words than the manifest's (for
example a generator that adds a `quotient_manifest_hash` certificate word at
header word 11) moves the quotient sections and every later verifier memory
region by the same number of words. The constant table is unaffected (it holds
field constants, not addresses), so the tool locates it by hash; the program
changes only in its memory-pointer operands, so the tool checks equality after
the inverse relocation and reports how many operands were moved. The tests in
`tests/quotient_listing_tool.rs` cover an exact round trip, the one-word shift,
and corrupted VK, listing and verifier inputs.

The VM decoder used by the tool is the same crate code that produced the
listing (`halo2_solidity_verifier::quotient_listing`), so a reviewer who wants
an independent reading should also check a few blocks by hand against the
`QuotientNumeratorBlock.yul` switch cases; the opcode table and operand layouts
are listed in `docs/reference/QUOTIENT_NUMERATOR_EVALUATOR.md`.
