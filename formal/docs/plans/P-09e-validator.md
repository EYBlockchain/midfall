# P-09e - the QVM validator (QVM-01) and operand walker

Status: READY. P-09a/b/c/d landed the vocabulary, interpreter, builder and certifier.

Reference: `lowering/quotient_numerator/vm/mod.rs`, the validator cluster:

| range | item |
|---|---|
| 2009-2138 | `validate_quotient_program(bytes) -> Result<usize, String>` (structural; returns max stack) |
| 2139-~2500 | **`validate_quotient_program_operands`** - QVM-01, the `Supported.qvm` predicate |
| ~2313-2757 | the operand walker and per-opcode operand validation |
| 2758-~2800 | `validate_quotient_mem_token` |
| 2184-2268 | constant-table slot bounds validation |
| ~2817-3059 | `read_u16`, `quotient_mem_token_from_name`, `quotient_op_len`, affine-sum and modarith7 op-len helpers |

Lean target: `formal/Midfall/Generator/Quotient/VmValidator.lean`.

## Why this matters beyond completeness

PLAN 9.5's `Supported.qvm` is literally
`validateQuotientProgramOperands g.plan = .ok ()`. Until this lands, `Supported` - the
hypothesis of `lowering_equivalence` - cannot be constructed. It is also the only place
the QVM's safety story is stated: the doc says it "fails closed: the first violation is
an error and generation stops before any verifier or VK is rendered", and that
structural validation runs first "because its checked decoder guarantees every operand
offset walked below is in bounds". That guarantee is exactly what D-P20 item 2 turned
into a question, so read hazard 2 before writing anything.

## Hazards

1. **The two-phase dependency is a soundness claim, not style.** `validate_quotient_
   program_operands` calls `validate_quotient_program` first and then walks operands,
   relying on the first phase to have proven every offset in bounds. Gate that: build a
   program that is structurally valid but has an out-of-range operand, and one that is
   structurally invalid, and show the second is rejected by phase 1 rather than
   panicking in phase 2. If phase 2 can panic on a program phase 1 accepted, that is a
   reference finding and a hole in `Supported.qvm`.
2. **D-P20 item 2 interacts here.** P-09b found that in the *certifier's* memory model
   every address read succeeds (memory is a PRNG over all u32), so an out-of-bounds
   fault cannot arise there. The validator is about the *program*, not the memory - so
   `qvm_validated_noOOB` may be about this layer after all. State plainly which memory
   model the validator's bounds refer to, and whether the plan's `.oob` fault class is
   meaningful against it. Do not assume the earlier reading was wrong; reconcile them.
3. **`quotient_op_len` already exists in `Midfall.Generator.QuotientBuilder`** (P-09c
   ported compaction-scoped copies and left two notes at VmBuilder.lean:1286 and :1424
   saying P-09d would absorb them - P-09d found that misdirected, since the general
   versions are `vm/mod.rs` items). You own them now: port the general forms, make
   VmBuilder's copies unnecessary, and **report** exactly what to retire rather than
   editing VmBuilder.lean (not your file). Gate that the general and scoped forms agree
   on every fixture so the retirement is safe.
4. **Error strings are the interface.** Every `Err` here is a `format!` string that
   callers may embed, and P-09b found the same `Err` aborts a build on one path and
   rejects a render on another. Enumerate them, carry payloads in a closed fault type,
   and gate the rendering verbatim - in the style VmReference used for its nine.
5. **Widths again.** Operand indices are `usize`, slots are `u8`, pointers `u16`/`u32`.
   P-09c found a real divergence in a helper (`coefficientOperands` and the zero-guard)
   by checking boundaries at value-1/value/value+1. Do the same for every bound the
   validator enforces: the 255/256 const-slot boundary, the stack-words limit, the
   u16 pointer ceiling.
6. **Do not pull in the shape recognizers** (QVM:3156-3227, 3649-3813) - they are P-09f.
   If the validator needs a recognizer, report it.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` trap; line numbers
from `git show HEAD:<path>`; **register your module** - R-50), and the four Quotient
files. REVIEW.md R-30, R-38, R-40, R-41, R-48, R-50, D-P19, D-P20.

**R-41** (perturbations actually run; report failures to redden), **R-48** (own fixture
or assert distinctness), **D-P17** (no theorems in a file importing Instances/),
**D-P19** (read artifacts at `#eval` time; reachability gate first).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file compiling or
unregistered - never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 597 across 39 files.
- At least 12 gates, including the two-phase dependency gate (hazard 1) and the
  scoped-vs-general `quotient_op_len` agreement gate (hazard 3).
- **Required finding**: state whether `Supported.qvm` is now constructible, and reconcile
  the validator's bounds with D-P20 item 2's finding about the certifier's memory model.
