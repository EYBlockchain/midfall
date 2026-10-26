# P-09f - the QVM shape recognizers

Status: READY. Last piece of the QVM block. P-09c left four hook slots standing in for
these (`QuotientShapeRecognizers` with `noShapeRecognizers` as the conservative
instantiation); this package supplies the real ones.

Reference: `lowering/quotient_numerator/vm/mod.rs`, the recognizer cluster:

| range | item |
|---|---|
| 3156-3227 | `quotient_limb_shape`, `quotient_pow5_base`, `quotient_limb_subshape`, `quotient_modarith7_shape` |
| 3649-3813 | the structural matchers (foreign-field forms recognised from the expression tree) |
| 3440-3530 | the `u16::try_from(..).ok()?` producers P-09a hazard 2 identified as the fallback mechanism |
| 3815-4083 | remaining recognizer/accumulator helpers in the same cluster - enumerate against `git show HEAD:` and correct this table |

Lean target: `formal/Midfall/Generator/Quotient/VmRecognizers.lean`.

## The invariant this package exists to establish

P-09a hazard 4 found that the fallback property is **not guaranteed by the type**: a
6-term or 8-term `Lin7` is well-typed, and what prevents mis-evaluation is the
recognizers' length guards (QVM:3667, 3714, 3753), the fixed-width encoding, and
`finish()`'s build-time panic. P-09c then found (F-5) that two recognizer
postconditions - `matched` is non-empty, and the limb residue is smaller than the input
- are **not enforced at all**, and demonstrated the consequence: a hook returning an
empty `matched` list makes the builder report depth 0 and emit a program the interpreter
rejects. This package is where those obligations become real.

## Hazards

1. **The doc states a hard design constraint**: shapes are "recognized from the
   expression tree alone", and "adding a limb opcode must never make correctness depend
   on a gate label or on a hand-maintained list of circuit gadgets". Gate that, not just
   the outputs: show two structurally identical trees under different nominal contexts
   recognise identically. If any recognizer reads a label, that is a reference finding.
2. **The two unenforced postconditions (P-09c F-5).** For the real recognizers, prove or
   gate: `matched` non-empty whenever the recognizer returns a shape, and the residue is
   strictly smaller than the input. These are the properties the builder's recursion
   silently depends on. If they cannot be established, say exactly which case fails
   rather than leaving the hook contract aspirational.
3. **The u16 fallback is the safety valve.** P-09a found oversized limb pointers make
   `try_from(..).ok()?` return `None` and the builder falls back to generic Fr opcodes.
   Gate the boundary at 0xffff/0x10000 and show the fallback emits a *valid, differently
   encoded* program rather than a rejected one.
4. **Wire the real hooks and re-run P-09c's gates.** P-09c's dual-build comparison
   (F-4) could only be exercised with a hand-supplied LIN7 hook against
   `noShapeRecognizers`, and it said plainly that this "is NOT the Rust's claim about
   real recognizers on a real circuit". Replace the hooks and state whether that
   caveat can now be retired - that is the acceptance test for this package.
5. **Do not re-implement the builder or the validator.** Import them. If a recognizer
   needs something from P-09d's validator that isn't exposed, report it.
6. **Retire VmBuilder's stale notes if you are the one who makes them stale** - but
   report rather than edit: VmBuilder.lean is not your file. P-09e already named the
   scoped-walker retirement (VmBuilder.lean:1239-1303 and the notes at :1286,
   :1423-1424); add yours to the same list.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`; **register your module** -
R-50), and the five existing `Quotient/` files.

**R-41** (perturbations actually run inside each gate's scope; report failures to redden
and fix gates that cannot see their own scope - P-09e had to repair two gates that
couldn't distinguish their boundary values, and said so), **R-48** (own fixture or
assert distinctness), **D-P17** (no theorems in a file importing Instances/), **D-P19**
(read artifacts at `#eval` time).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file compiling or
unregistered - never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 629 across 40 files.
- At least 12 gates, including the label-independence gate (hazard 1), the two
  postcondition gates (hazard 2), and the u16 fallback gate (hazard 3).
- **Required finding**: whether P-09c's F-4 caveat can be retired now, and what remains
  between this and a real-circuit recognizer claim.
