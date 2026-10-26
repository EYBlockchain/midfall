# P-09c - the quotient VM builder (emits the finalized bytecode)

Status: READY - P-09a landed the vocabulary, P-09b the interpreter it must agree with.

**Why this is now the critical path.** D-P20 item 3: `qvm_compile_correct` cannot be
*stated* in Lean until the builder exists, because the certifier's seed hashes the
**finalized bytecode** - an artifact nothing in the tree can currently regenerate. This
package produces it.

## Scope - the builder only, not the validator or the recognizers

The VM compiler is ~3,600 lines and is split three ways (P-09c builder, P-09d
validator+walker+usage, P-09e shape recognizers). Taking only the builder keeps the
package inside a size that can survive an interruption - the kzg package was killed
mid-write at 1,493 lines and had to be recovered, and a 3,600-line task makes that
failure mode much worse.

Port, from `lowering/quotient_numerator/vm/mod.rs`:

| range | item |
|---|---|
| ~1071-1091 | `QuotientProgramBuilder` struct + `Default` |
| ~1091-1106 | `with_limb_vm_ops` |
| ~1104-1212 | `identity_expr`, `fold_identity`, `native_permutation`, `native_lookup`, `native_identity`, **`finish`** |
| ~1218-1256 | `assignment`, `parse_expr` |
| ~1256-1420 | `emit_expr`, `try_emit_pow5`, `try_emit_limb_decomposition`, `emit_affine_terms` |
| ~1420-1530 | `try_emit_limb_shape`, `try_emit_modarith7_shape`, `modarith7_shape_has_u8_const_slots`, `limb_shape_has_u8_const_slots` |
| ~1530-1660 | `emit_limb_shape`, `emit_modarith7_shape`, `emit_const`, `emit_mem_literal` |
| ~1660-1800 | `try_emit_add_product`, `product_add_fits_u8_slot`, `product_add_macro`, `emit_product_add`, `emit_binary_expr`, `emit_acc_leaf` |
| ~1800-1885 | `op0`, `op_binary`, `push_stack`, `pop_stack`, `u16`, `u24`, `u32`, `const_slot`, `const_fits_u8_slot`, `peek_u8_const_slots` |
| ~1885-1975 | `compact_quotient_runs` |

Resolve the exact ranges against `git show HEAD:` before porting - the offsets above are
derived from a relative listing and P-09a found my ranges were off by a few lines.

**Out of scope** (do not pull in): `quotient_program_usage`, `validate_quotient_program`,
`validate_quotient_program_operands`, the operand walker, `quotient_op_len`, and the
standalone recognizer functions. Those are P-09d/P-09e.

## Hazards

1. **`finish()` is the artifact boundary.** Its output is what the certifier hashes and
   what the Yul embeds. Port it exactly, and gate that `finish` on a hand-built program
   produces a byte string that P-09b's interpreter can actually execute and agrees with.
   That single gate is the first real emitter-vs-interpreter certification leg in the
   tree - the thing the Rust does probabilistically and we can now do by construction.
2. **The builder is `&mut self` with an instruction buffer, a const table and a stack
   depth counter.** Every `emit_*` appends and may allocate const slots. Model the
   mutation as an explicit state fold and prove nothing reorders: a gate that pins the
   byte sequence for a small expression is worth more than any amount of reasoning about
   the fold.
3. **`try_emit_*` returning false must fall back, never half-emit.** This is the safety
   property P-09a hazard 4 could only test at the type level. Check whether a failed
   `try_emit` leaves the instruction buffer untouched; if it can emit before deciding,
   that is a reference finding. Gate it by asserting buffer length is unchanged after a
   rejected attempt.
4. **`compact_quotient_runs` rewrites already-emitted bytes.** It runs after the emits and
   can change offsets. Confirm the ordering relative to `finish` in the Rust, and gate
   that compaction preserves the interpreter's result - feed a program through both
   uncompactified and compactified and require the same field element. If the Rust has no
   such test, say so; that is exactly the kind of pass a Lean proof should pin.
5. **Width and slot decisions in the emitters** (`const_fits_u8_slot`,
   `product_add_fits_u8_slot`, `peek_u8_const_slots`, `u16`/`u24`/`u32`) choose encodings
   by value magnitude. Each boundary is a place an off-by-one is invisible. Gate each
   boundary at value-1, value, value+1.
6. **`with_limb_vm_ops` is the `QUOTIENT_VM_LIMB_VM_OPS` default toggle** (config.rs:
   `DEFAULT_QUOTIENT_LIMB_VM_OPS = true`). R8: both branches ported and the deployed one
   identified.
7. **Do not re-declare anything from P-09a.** If you need the validator or the walker,
   report the need rather than importing the compiler sideways.

## Rules

Read first: `docs/plans/README.md` standing notes - especially **register your module**
(R-50) and the `lake env lean` trap; `Quotient/VmTypes.lean` and `Quotient/VmReference.lean`
for style and for what is already available; REVIEW.md R-30, R-38, R-40, R-41, R-48,
R-50, D-P19.

**D-P19 binds you**: where a gate's expectation lives in an artifact (the `.yul` template,
the reference source), read it at `#eval` time with a reachability gate first.
**R-41**: perturbations actually run inside each gate's scope; report failures to redden.
**R-48**: build your own fixture or assert distinctness before comparing pointers.
**D-P17**: no theorems in a file importing `Instances/`.

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds** - background them and keep working. If you are interrupted, leave the
file either compiling or not registered; a half-written registered module is how R-50
happened.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 511 across 37 files.
- At least 14 gates, and specifically: the `finish`-to-interpreter agreement gate
  (hazard 1), the no-half-emit gate (hazard 3), and the compaction-preserves-result gate
  (hazard 4). Those three are the point of the package.
- A finding stating whether `qvm_compile_correct` is now **statable** in Lean, and if not,
  exactly what is still missing.
