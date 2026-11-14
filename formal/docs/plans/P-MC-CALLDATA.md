# P-MC-CALLDATA - M-C, first tranche: the 7 `Calldata.lean` holes.

Status: READY, **fully unblocked** — independent of M8, of the solc-hop decision, and of
`Eip2537.Holds`. This is the largest mechanical tranche on the board.

## Why Calldata first within M-C

It is the most mechanical of M-C's three groups (Calldata 7, Accumulator 12, Qvm+QvmFold 9),
and it sits **upstream of the run leg every spec depends on**: `hcd : decodeCalldata … = some
(ms, instW)` is a hypothesis of all ten specs. Closing these makes the calldata layer a
proven bridge rather than an assumed one.

**Overlap with P-RESTORE3**: the sketch's `encodeCalldata_faithful` and
`repackProof_faithful` obligations are in this area. The holes here are named
`calldata_canonical`, `repack_spec_wire`, `proofLen_eq_repackedLen`,
`sum_commitmentReadGroups` (+3). **Read P-RESTORE3's verdicts first if they have landed** —
if it restored a faithfulness obligation, it belongs in this package's scope, not a later one.

## The holes (from `SORRY.md`)

| line | theorem |
|---|---|
| 370 | `sum_commitmentReadGroups` |
| 385 | `proofLen_eq_repackedLen` |
| 416 | `calldata_canonical` |
| 434 | `repack_spec_wire` |
| 444, 466, 483 | three more — read the file, the names sit above the `sorry` |

**The statement authority is section H, `docs/plans/P-SE-semantic-equivalence.md:1111-1314.**
Check each implemented statement against its sketch before proving it — P-RESTORE2 found
several specs had drifted, and one was **false as written**. If a statement here is weaker or
false relative to the sketch, **restore it first, then prove the restored form.**

## Deliverable

1. **Prove as many of the 7 as fit**, in file order. Target: register **56 → 50** if all land;
   any partial count is fine if each remaining hole is unchanged and compiling.
2. **D-P23 both halves as theorems** per claim: a satisfiability witness AND a falsification.
   For `calldata_canonical` the falsification is the interesting one — show a non-canonical
   encoding that a naive `decodeCalldata ∘ encodeCalldata` round trip would accept.
3. **`proofLen_eq_repackedLen` matters beyond its size**: `proofLen` is pinned at 4320 in two
   places already (`poseidonCtx` and `poseidonProofLayout`). If this is the lemma tying the
   repacked length to the proof length, it is what makes the ABI geometry honest.
4. **Record any statement you had to restore** in `docs/plans/P-SE-statements.md` — the
   same-commit rule now applies to dropped or narrowed sketched fields.

## Constraints

* **Never weaken a statement to make it provable.** Report instead. This is a standing human
  instruction, and it has been violated-by-drift before.
* **`Instances/` confinement (D-P17)**: `Calldata.lean` is theorem-bearing — no `Instances/`
  import. If a witness needs concrete bytes, the exhibit goes in `Instances/` and the
  statement stays portable.
* **Elaborator walls, all previously hit here**: `decide` reduces for exponentiation at
  255-bit `r` but **not** for inversion; `rw [ZMod.card]` on a goal mentioning
  `Fintype.card (ZMod blsP)` costs ~4 GiB and gets killed — **pre-prove cardinalities as
  `have`s**; `whnf` of a pair `==` on a fold dies at default `maxRecDepth` — generalise over
  the literal; `bs.size` vs `bs.data.size` are defeq but not syntactically equal, so `rw`
  won't cross them — pick one spelling per step.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.** Five silent losses caught this way.
* **SORRY.md traps**: `sorry` in a string literal counts as a hole; comment edits shift
  `file:line` pins. Regenerate with `scripts/gen_sorry.sh`; verify three-way agreement;
  budget a full `checks.sh` run (~8.5 min).
* **Gate changes must keep all 13 sections green and be shown to redden** (R-41).
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Full-gate actual 5.12 GiB tree / 4.44 GiB largest.
* **`kat_gate` traps**: no unused `simp` args or unused-variable bindings in `#eval` files;
  heavy `decide`s go in a file with no `#eval` (the `G2Kernel.lean` pattern).
* **Perturbations via `lake build`**, never `lake env lean`; whole-repo APFS clone under /tmp;
  in `lake env lean` pass `-DautoImplicit=false`.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck — land in order, stop at a boundary.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5212 jobs**, 122 modules; `checks.sh` green: **56 tracked sorries**, 1305
KATs across 91 files, 231 fragments, 12 fact families, 8 bundles with 5 gap defs, 30 pins.
**D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Lowering/Calldata.lean` (the 7 holes and their docstrings, which name
their Rust sources), `docs/plans/P-SE-semantic-equivalence.md` **section H lines 1111-1314**
(the statement authority), `Midfall/Generator/Abi.lean` (`poseidonProofLayout`, `proofLen`),
`docs/plans/P-SE-statements.md` (deviation log), `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 56**.
- Each proved claim has a witness and a falsification as theorems.
- **Required finding**: of the 7, how many were provable as stated versus needing restoration
  from the sketch first — and does any of them unlock a `Partials` or `Accumulator` hole that
  was listed as blocked behind a missing bridge?