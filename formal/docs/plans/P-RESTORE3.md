# P-RESTORE3 - triage the 17 annotated-but-absent sketched obligations.

Status: READY, and **directly required by the objective**: *restore the originals (modulo
signature changes due to renamings etc); never change the specs/theorems to make them
vacuous, always keep them as-is, strong.*

P-RESTORE2 swept 404 sketched declarations: 25 absent, **8 unannotated (now fixed)**, and
**17 annotated-but-absent.** Annotation makes a gap *visible*; it does not make it *correct*.
R11's lesson is that an annotated reason can itself be wrong — the `Inv.lean:443-447`
redundancy argument was confident, recorded, and false. **These 17 have never been checked.**

## The list to triage

From P-RESTORE2's sweep (names as they appeared in the sketch):

| name | section | why it matters |
|---|---|---|
| `encodeCalldata_faithful` | H | the calldata the contract receives is what the model built — without it `decodeCalldata` and the encoder can drift apart and both specs still pass |
| `repackProof_faithful` | H | same for the repack path; `repackProof` is in the architecture list, its faithfulness obligation is not |
| `repackProof`, `encodeCalldata`, `hEncode`, `hRepack`, `hProofLayout`, `hoisted`, `irCheck` | H | helper hypotheses / fields the sketch's specs name; check whether each landed under another name or is genuinely missing |
| `qvm_yul_refines` | O/P | the quotient-VM refinement — a named obligation of the Qvm layer |
| `points_subgroup_checked` | (LoweringCorrect) | **deferred with its vacuity proved** — verify that the deferral is still the right call now that `Holds` is exhibited |
| `EvaluatorFrame`, `FrameWellFormed` | (Surface) | the evaluator-frame obligations the sketch's `LoweringCorrect` fields reference |
| `vkDigest_slot0` | (Inv) | a slot pin |
| `qext` | (Qvm) | quotient extension helper |

**Re-derive the list yourself** from the sketch rather than trusting this table — the sweep
matched by name and can produce false negatives, and the agent's own report said so.

## For each: one of three verdicts, recorded

1. **RESTORE** — it is a real obligation the tree should carry. Land it, verbatim from the
   sketch, and **consume it** somewhere (a spec hypothesis, a checklist field). A restored
   obligation nothing uses is decoration — that was the `PartialRejects` failure.
2. **ALREADY PRESENT under another name** — record the rename in `P-SE-statements.md`.
   (`publicInstanceEval` → `instanceEvalOf` was exactly this.)
3. **GENUINELY DEFERRED, with a reason that HOLDS** — but **verify the reason**, don't inherit
   it. `points_subgroup_checked` was deferred because its conclusion was proved unconditional;
   re-check that now, since `Holds` and `g1Decodes` have changed the landscape since.

## Priority within the list

**The `*_faithful` pair first.** `encodeCalldata_faithful` and `repackProof_faithful` are the
kind of obligation that, if missing, means the specs are proving things about a calldata
format nothing tied to the contract's actual bytes — and `hcd : decodeCalldata … = some
(ms, instW)` is a hypothesis of **every** spec. If the encoder's faithfulness is not stated
anywhere, that is a larger hole than anything P-RESTORE2 found.

## Constraints

* **Never weaken a statement to make it provable or to make an exhibit pass.** Report instead.
* **If restoring an obligation makes a fixture exhibit fail, that is the finding** — fix the
  fixture, as P-RESTORE2 did with the 2-word payload. Do not re-weaken the obligation.
* **D-P23 both halves as theorems** for anything restored: witness AND falsification.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts as a hole; comment edits shift
  `file:line` pins → budget a full `checks.sh` run (~8.5 min) and regenerate with
  `scripts/gen_sorry.sh`; verify three-way agreement.
* **Gate changes must keep all 13 sections green and be shown to redden** (R-41).
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Full-gate actual: 5.12 GiB tree / 4.44 GiB largest.
* **`lake env lean`**: pass `-DautoImplicit=false`. No unused `simp` args in `#eval` files —
  the `[apply]` hint matches `kat_gate`'s value regex.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck — land in order and stop at a**
  **boundary.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5212 jobs**, 122 modules; `checks.sh` green: **56 tracked sorries**, 1305
KATs across 91 files, **231 statement fragments**, 12 fact families, 8 bundles with 5 gap
defs, 30 pins, Statements hash OK. `VkSlotsAgree` is at `Inv.lean:609`; the deviation log is
`docs/plans/P-SE-statements.md` (see its "The audit" section); sketch sections H, L, N, O, P.

Read first: `docs/plans/P-SE-statements.md` (**the deviation log and the sweep method**),
`docs/plans/P-SE-semantic-equivalence.md` sections H (Calldata, lines 1111-1314), L
(1471-1617), N (1794-1931), O/P (1932-2077), `Midfall/Lowering/Calldata.lean`,
`Midfall/Lowering/Inv.lean:432-450` (the dropped list — and note R11: an annotated reason
there was already found false once).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Every one of the 17 has a recorded verdict: restored / renamed-and-recorded / deferred with
  a **verified** reason.
- **Required finding**: how many of the 17 were genuinely missing obligations, and does any
  restored obligation make an existing spec hypothesis load-bearing in a way it was not
  before? That is the question the whole restoration has been driving at.