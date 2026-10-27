# P-13d - the contract shells: `contracts/*.sol` + the glue. The last port package

Status: READY. `templates/contracts/{Halo2Verifier,Halo2VerifyingKey,Halo2QuotientEvaluator}.sol`
(500 lines total). When this lands, the generator port is complete and P-SE begins.

Reuse `VerifierPartials.lean`'s layer (`PartialCtx` now 50 fields, `jinjaFor`,
`occ`/`artifactMatch`/`includeBoundary`, `readDump`). Do not build a parallel renderer.

## What P-13a and P-13c handed you

* **`-%}` right-trim is used here and nowhere in the partials.** `Halo2Verifier.sol:91,96,
  111,115,117`. P-13c pinned the rule from source (QNB uses it 5 times in macro defs);
  you must make it *behave* correctly, not just exist.
* **The root template also loses its final newline** - the dump ends `}` with no LF.
  P-13a found this; nobody has gated it yet. You own it.
* **Non-trimming `{# #}` comment blocks leave whitespace-only lines** (D:1891 from
  QNB:328-480). Expect the same class here.
* **The glue shape**: parent literal text + `"    "` + `renderX ctx` per include, in
  `verifierIncludes` order (`Templates.lean` already pins that order).
* `{%- match -%}` with a `Some with (_)` arm appears in the contract templates.

## Hazards

1. **Re-measure.** My briefs have been wrong about counts in five consecutive packages.
   Verify every number here against `git show HEAD:`.
2. **`Halo2VerifyingKey.sol` is a separate artifact with its own dump.** The tracked
   `target/poseidon-fixture-dump/` contains both `.sol` files - gate each render against
   *its own* artifact, not against the other. `DVK:68` and `DVK:99` were already used by
   P-13b/P-13c as evidence for `hex_padded` and `const_max`; do not disturb those.
3. **`Halo2QuotientEvaluator.sol` may not be exercised by the deployed profile at all.**
   If the poseidon dump renders it empty or absent, **say so plainly** and gate it
   structurally or synthetically with a label - do not present a vacuous byte gate as
   evidence. This is the trap P-13b avoided and I mis-framed.
4. **`render_eq_print` is an architectural equation, not semantic correctness.** PLAN
   9.5 lists it as a theorem. If you can state it as a definitional equality in Lean,
   say what it actually establishes and what it does not - the project has been bitten
   repeatedly by statements that are true for the wrong reason (review F1 was exactly
   this class).
5. **D-P17**: no `Generator.Vk`, no `Midfall/Instances/`. **`List.range'` takes a count;
   `List.zipIdx` yields `(element, index)`.**
6. **Gate-design lesson from P-13c**: `occursOnce` plus a prefix boundary is satisfied by
   a *truncated* render. If you write a byte-exactness gate, assert the length too. The
   orchestrator added that to gate 48; do not reintroduce the hole in new gates.

## Rules

Read first: `docs/plans/README.md` standing notes; `VerifierPartials.lean` (the layer and
68 gates whose style to match); `Templates.lean`; `P-SE-evidence/attack.md` FIX lines
(binding).

**R-41**, **R-48**, **D-P19**, **D-P13**. Binding: PLAN section 4; `Vec` -> `List`;
R4 release profile.

**No idle builds.** Multi-line anchored edits have cost the orchestrator ten swallowed
lines across three repairs this session - re-read what you changed, rebuild after each.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 913 across 50 files.
- At least 10 gates, each byte-exactness gate also asserting length (hazard 6).
- **Required finding**: state whether the generator port is now COMPLETE - i.e. can
  `render g o` be evaluated in Lean for the deployed profile and compared byte-for-byte
  to the tracked artifacts? If any gap remains, name it precisely. That is the gate on
  starting P-SE.
