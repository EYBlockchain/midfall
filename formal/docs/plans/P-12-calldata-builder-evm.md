# P-12 - `calldata.rs` + `builder/*` + `evm.rs`: the repack and render surface

Status: BLOCKED on P-10c only for ordering reasons; all types it needs exist except one
helper listed below. ~1,316 Rust lines.

## Item 0 - a missing helper, port this first

`scalar_le_to_be_word` (QVM:934-944) is **not ported** - `VmTypes.lean:62` lists it
explicitly among the items P-09a declined as a proof-repacking byte helper. But
`lowering/calldata.rs:19` imports it and `repack_proof` uses it. So it must land here,
with its `QVM:` cite, before `calldata.rs` can port. This is a hole left between P-09a
(declined it as not-vocabulary) and P-12 (needs it) - the same class as the five unowned
`vm/mod.rs` helpers P-10 reported.

## Items

| file | lines | what | why it matters |
|---|---:|---|---|
| `lowering/calldata.rs` | 160 | `repack_proof`, `encode_calldata`, `repacked_proof_scalar_layout_for_test`, `repacked_proof_layout_plan` | PLAN 9.5's `repackProof` and `encodeCalldata` - the whole of `end_to_end_noAcc`'s right-hand side, and P-SE proof step P6 (`repack_spec_wire`, `calldata_roundtrip`, `calldata_canonical`, `proofLen_eq_repackedLen`) |
| `builder/mod.rs` | 69 | the builder module surface | |
| `builder/api.rs` | 162 | `try_new` - mirrors the validation at `api.rs:21+` | **`Supported` is meant to mirror `try_new` plus what the proofs need.** P-SE's D2 makes non-vacuity of `Supported` a requirement, so `try_new`'s checks are the reference for that |
| `builder/render.rs` | 220 | `render`, `render_quotient_evaluator` | produces `RenderedArtifacts` - the golden-test target |
| `builder/repack.rs` | 27 | | |
| `evm.rs` | 656 | `encode_calldata`, `FN_SIG_VERIFY_PROOF` | PLAN 9.5's `encodeCalldata`; the selector `0x1e8e1e13` that `ShellModel` and the attack's FIX about restricting to the `verifyProof` arm both need |

## Hazards

1. **`calldata_canonical` is already flagged false-ish** (PLAN 13: "instance words >= r
  and trailing bytes may be accepted"), and review F1 already repaired `end_to_end_noAcc`
  to require run existence. Do not re-litigate either; port the code faithfully and
  report what the decoder actually accepts, since P-SE's D7 asserts EXACT canonicity in
  both modes over raw `Word256` - if the code contradicts D7, that is a stop-and-report.
2. **`repack_proof` returns `Result<Vec<u8>, RepackError>`** and P-06 ported
  `RepackError` with verbatim Display strings. Reuse them; `GeneratorError.fromRepackError`
  already exists.
3. **P-09e finding F-3 is live here**: `fixed_scalar_count` is not total on the domain
  `validate_for_num_instances` accepts (the `usize::MAX` sentinel makes `:160` saturate
  while `:177` wraps). If `calldata.rs` or `builder/api.rs` reaches that path, report it.
4. **`FN_SIG_VERIFY_PROOF` is a keccak-derived selector.** Gate it against a computed
  `abiSelector` of the signature string, not against a pasted literal - the project has
  already been bitten by pasted selectors (R-38 finding 1).
5. **Do not import `Generator.Vk`** (D-P17: it pulls in `Instances/ExponentModel`, and
  P-SE stage 2 files must not transitively import a concrete model). `LoweringPlan.lean`
  already established that pattern and the reason.
6. **`List.range'` takes a count, not an inclusive end; `List.zipIdx` yields
  `(element, index)`.** See plans/README.md - one of these was the basis of a false
  defect claim last package. Verify before acting on any inherited claim, including this
  brief's.

## Rules

`docs/plans/README.md` standing notes; the six `Quotient/` files plus `LoweringPlan.lean`
and `Abi.lean`; `P-SE-evidence/attack.md` FIX lines (binding - several concern calldata
and the `verifyProof` selector). **R-41**, **R-48**, **D-P19**, **D-P17** all apply.
Binding: PLAN section 4; `Vec` -> `List`; R4 release profile.

**No idle builds.** Register the module (R-50). Do NOT edit Rust files, `Statements.lean`,
`SORRY.md`, or another package's Lean file. Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from the current base.
- At least 12 gates, including a computed-selector gate (hazard 4) and round-trip gates
  on `repack_proof` / `encode_calldata` over the tracked `calldata.bin` and `proof.bin`
  fixtures - read from disk at `#eval` time per D-P19, not pasted.
- **Required finding**: what `repack_proof` and the calldata decoder actually accept on
  the fixture corpus, and whether that agrees with P-SE D7 (EXACT canonicity) or
  contradicts it.
