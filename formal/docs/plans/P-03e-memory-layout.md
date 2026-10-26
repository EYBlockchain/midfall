# P-03e - complete the Layout row: `VerifierMemoryLayout::new` (MEM:591-973)

Status: READY. Depends only on already-landed work. Closing it is what makes PLAN 9.5's
`Supported.layout` (`g.plan.memory.WellFormed`) statable against a real plan rather than
a placeholder, and it removes a workaround P-08 had to build.

## Why this exists

`Layout.lean` declined to port `VerifierMemoryLayout::new` on the stated grounds that
`ConstraintSystemMeta` and `VerifierMemoryLayoutConfig` "do not exist in this tree yet".
Both do now (Encoding.lean:364 and Layout.lean:970), so the reason is void - recorded as
R-49. Because the note said otherwise, P-08 had to thread `memory_layout_for` through a
`VkBuildEnv` shim rather than call the real constructor.

Good news discovered while scoping: the supporting machinery is **already ported** -
`MemoryArena` (19 refs), `allocPhaseScratch` (7), `ThetaWindowLayout` (8) and
`MemoryPhase` (42) all live in `Layout.lean`. So this is the 383-line function plus two
missing helpers, not a rebuild of the arena model.

## Deliverable

Extend `formal/Midfall/Generator/Layout.lean` (or a new `LayoutMemory.lean` if the file
is too large - your call, say which and why) with:

1. `batch_invert_scratch_bytes` and `batch_invert_input_words` from `layout/memory.rs`
   (grep for them; they are outside the 591-973 range and are not yet ported).
2. `VerifierMemoryLayout.new` - MEM:591-973 in full, in source order, every `let` and
   every `alloc_phase_scratch` call, with R1 cites.
3. Replace the `VkBuildEnv` shim usage **as a finding, not an edit**: Vk.lean is not your
   file. Report that the shim can now be retired and what it would take.

## Hazards - each must be answered

1. **Phase-scoped disjointness is not global disjointness.** The Rust comment at the top
   of the arena section says low-memory helpers are phase-scoped "because the transcript
   buffer is no longer live once algebra/precompile work begins". So two regions may
   legitimately overlap if their phases are disjoint. Check what `MemoryMap.WellFormed`
   (P-03d) actually asserts - if it is a global pairwise-disjointness test, then either
   it is wrong for phase-scoped regions or `new` will fail it, and **that is a finding
   about the statement surface, not something to work around by loosening the test.**
   PLAN 9.5's `Supported.layout` says "disjoint, aligned, above solc spill window"; this
   package is where that wording meets reality.
2. **The `.expect("constructor G1MSM smoke bounds are non-empty")`** on a five-element
   array literal's `.max()` is an unreachable panic. Argue it at the site (R5) rather
   than porting a default, and do not silently turn it into `0`.
3. **Alignment and rounding inside `alloc_phase_scratch`.** It is already ported, but
   `new` is the first caller that passes *computed* byte sizes rather than constants.
   Verify the rounding behaviour on a size that is not a multiple of `WORD_BYTES`
   (e.g. `q_com_trace_len`, which comes from a PCS input_bytes field) and gate it.
4. **`commitment_g1_count(meta)`** here is the Abi.lean function ported in P-05
   (`commitmentG1Count`). Do not re-implement it; call the existing one, and if the Rust
   actually uses a different local helper, say which and cite it.
5. **The result must be checkable.** The headline gate is: build a real
   `VerifierMemoryLayout` for the poseidon-shaped fixture and assert
   `MemoryMap.WellFormed` on it, plus pin the concrete addresses the reference's own
   tests use. A `new` that no gate ever calls is how this gap survived two packages.
6. **Above the solc via-IR spill window.** `LOW_MEMORY_SCRATCH_START` was moved 0x80 ->
   0x1000 by misc-fixes step 2 for exactly this reason, and there is an existing
   `compiled_memoryguard_does_not_overlap_generated_layout` gate. Confirm `new`'s
   allocations respect it and say what the margin is.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`), `Layout.lean`'s header, and
`Kzg.lean`'s header as an example of auditing inherited claims.

Binding: PLAN section 4 (R1-R11). `Vec` -> `List` in the Generator row. R4: release
profile, so no overflow panic and `debug_assert!` compiled out, but indexing and
division by zero do panic.

**R-48 applies to you directly**: the shared `verifierLayoutFixture` has every PCS base
at 0, so any pointer-comparison gate on it is vacuous. Build your own fixture with
distinct bases or assert pairwise distinctness first, and say which.

**D-P17 applies**: you may import `Midfall/Instances/` for `#eval` gates but a file that
imports it must not state theorems - `scripts/checks.sh` now enforces this and has been
shown to fail on a planted violation.

**No idle builds.** Run `lake build` in the background and keep working while it runs.

Do NOT edit any Rust file, `Statements.lean`, `SORRY.md`, or another package's Lean file
(Vk.lean's shim stays; report it). Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 424 across 34 files.
- At least 10 `#eval` gates, each with a perturbation actually run inside its scope,
  including the WellFormed gate on a real fixture and the alignment gate on a
  non-word-multiple size.
- Non-vacuity evidence for every boolean gate.
- A finding stating whether `MemoryMap.WellFormed` is the right predicate for
  phase-scoped regions (hazard 1), since PLAN 9.5's `Supported.layout` depends on the
  answer.
