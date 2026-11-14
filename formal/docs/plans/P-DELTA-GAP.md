# P-DELTA - the one real gap the sketch audit found.

**Supersedes P-RESTORE, which over-flagged.** An initial audit called eight missing `EnvAgrees`
fields a weakening. **Seven were wrong** - documented relocations or genuine redundancies, recorded
with reasons in `Inv.lean:432-450` under a header titled "DROPPED FROM THE SKETCH, with the
reason". One is real.

## The real gap: `delta`

The sketch needs `delta : E.delta = (Nat.cast blsDeltaLiteral : Fr p)`. It was dropped because
**`blsDeltaLiteral` does not exist in the tree** - the design comment itself says the Lean constant
does not exist yet. Recorded consequence: the contract hard-codes the permutation delta literal
(`QuotientNumeratorBlock.yul:1407`), and tying it to `E.delta` needs a generator-side constant
first. **So `E.delta` is unconstrained by the specs while the contract hard-codes a value.**

1. Find the literal the generator emits (artifact `QuotientNumeratorBlock.yul:1407` and the Rust
   producing it). Establish value and provenance - do not invent a constant to match.
2. Define the Lean constant; add `delta` back to `EnvAgrees` verbatim from the sketch.
3. Re-discharge `fxEnvAgrees`. If it fails at the fixture, **that is the finding** - report it, do
   not re-weaken the field.
4. Show the field is load-bearing, or state plainly that no counterexample can be built.

## Verify the redundancy claim rather than trust it

`Inv.lean` argues `g1BaseWords`/`g2BaseWords`/`negSG2Words` are redundant because the base points
are part of the VK payload image and `Inv`'s `.vk` clause pins that image byte for byte. Probably
right - but it is an argument, not a proof. **Confirm the three header slots (sketch names 11, 15,
23) actually fall inside the pinned byte range.** If any does not, that is a second real hole.

## Consolidate the deviation log

The reasons exist but live in `Inv.lean`'s comment. `docs/plans/P-SE-statements.md` is the file
whose **stated job** is the sketch-vs-implementation record, and none of these eight appeared there
- which is why the first audit mis-called seven relocations as weakenings.

* Copy the `EnvAgrees` deviation record into `P-SE-statements.md` (or link precisely).
* Standing rule: a rename, arity change, or dropped field on a sketched statement requires a line
  in that file **in the same commit**.
* **Audit `Inv`, `SupportedS`, `Snapshot`, `LoweringCorrect` and the ten specs' conclusions for
  UNDOCUMENTED drops.** `EnvAgrees` was resolvable because it was annotated; the risk is a
  structure where a drop was not annotated.

## NOT in scope

* Do **not** restore the seven relocated/redundant fields - that means inventing functions the
  original author deliberately declined to invent.
* Do **not** revert `omegaOrder` to `omega ^ n = 1` - P-ENV strengthened it on a human decision.
* Do **not** remove `BlkIsEmitter` - it fixed a statement false as written. **Added hypotheses that
  fix a false statement stay; dropped sketch fields are the only thing to reconsider.**

## Constraints

* **Never weaken a statement to make it provable or to make an exhibit pass.**
* **D-P23 both halves** for anything new, as theorems.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts as a hole; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, or
  `scripts/check_statement_fingerprints.py` (another agent owns it now). No git add/commit.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5212 jobs**, **56 tracked
sorries**, 122 modules, Statements hash OK. `EnvAgrees` is at `Midfall/Lowering/Inv.lean:451`;
consumers: `Partials.lean` (ten specs), `Obligations.lean`, `Instances/SurfaceFixture.lean`.

Read first: `Midfall/Lowering/Inv.lean:432-450` (**the existing deviation note - read it before
assuming anything is missing**), sketch section L line 1521, the pinned artifact's
`QuotientNumeratorBlock.yul:1407`, `docs/plans/P-SE-statements.md`.

## Acceptance

- `delta` restored with a real constant, or a precise report of why it cannot be.
- The redundancy claim verified or refuted.
- Deviation log consolidated with the same-commit rule.
- **Required finding**: any *undocumented* dropped or narrowed sketched field elsewhere in A-R -
  that class is worth more than `delta` itself.