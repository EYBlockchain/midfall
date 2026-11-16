# P-INLINE - implement D-P39: inline the contract-level constants so `RunShell` is inhabited.

Status: **THE CRITICAL PATH.** `lowering_equivalence` is proved but vacuous at every Surface
because `RunShell` has **no runs at all** — the emitted arm leaves 61 identifiers free and
`curveSurface.bindLocals = []`. D-P39 decides the fix. **The test of this package: `RunShell`
becomes inhabited.** If it does not, the decision is wrong and must be revisited — say so.

## The decision (D-P39, `docs/design.md`)

The emitted Yul is a **fragment**; its free identifiers are the Solidity wrapper's
`uint256 internal constant` declarations. **solc inlines those at every use site, including
inside function bodies.** So define the embedding as a specified inlining transform:

```lean
inlineContractConstants : List (String × Nat) → YulBlock → YulBlock
```

Substitute each constant's literal at every **use site** — expressions, call arguments, and
**inside `funDef` bodies** — threading parameters so a **shadowing binder is not substituted**.
Values come from the table `RunEmitted.shellLets` already uses. **No new numbers.**

## Why the obvious fix fails — measured, do not repeat the discovery

P-RUNSHELL proved binding `RunEmitted.shellLets` at the **arm level only** is insufficient:
- **a Yul function is not a closure** — `Step.callOk` binds params + zeroed rets only;
- **6 of 8 emitted helpers** read names their own signature cannot supply (`scalar_inv` 4,
  `ec_pairing` 5, `common_uncompressed_g1` 3, `squeeze_to` 2, `batch_invert` 1,
  `transcript_init` 1);
- binding all 61 free names to zero is **still stuck** — the gate passes and it dies in a helper.

**So inlining must descend into function bodies.** That is the whole point.

## Deliverable, in order

1. **`inlineContractConstants`** + a proof that the result has **no free identifiers**
   (`freeNames (inlineContractConstants consts (armBody S)) = []`). `FrameWalk.freeNames` and
   `RunShellInversion`'s structural `exprHasVar` both exist — **prefer `exprHasVar`'s shape**,
   since `freeNames` goes through `WellFounded.fix` and forces `native_decide`.
2. **`RunShell`'s program becomes the inlined arm.** This is a signature change to a sketched
   definition — permitted because the sketched form is **false as written** (`runShell_curveSurface_empty`).
   Record it in `P-SE-statements.md` **in the same commit**.
3. **`shell_unfolds` restated to the ARM form**, with the fingerprint registry moved in the
   **same commit** (D-P27). `Surface.lean:257-261` already assigns this restatement.
4. **THE TEST: `RunShell` is now inhabited.** Exhibit a concrete run at `curveSurface`. If you
   cannot, **stop and report** — the decision is wrong, and that is a better outcome than a
   forced proof.
5. **Then re-check `ir_refines` at `modelIr curveSurface`.** P-RUNSHELL refuted it *because* the
   shell side was empty. With the shell inhabited, is it still refuted? **That is the question
   this whole package exists to answer.**

## Shadowing — the subtle part, get it right

A `funDef` parameter or `let` binder may **reuse a constant's name**. Inlining must not substitute
under a shadowing binder, or the semantics change. **Prove a lemma about this and test it with a
planted shadow** — e.g. a helper with a parameter named `VK_MPTR`. If the transform substitutes
there, it is wrong and no downstream theorem saves it.

## Constraints

* **`lake build` green does NOT mean the KAT gates passed** — a false `eval … -- expect true` is
  an info line. **Always run `python3 scripts/kat_gate.py`.** (R-71)
* **Do NOT round-trip files over ~1500 lines through the `read` tool** — it silently truncated a
  1967-line file and dropped 612 lines. `Surface.lean` and `Qvm.lean` are both over that line.
* **Never weaken a statement to make it provable.** If inlining does not fix inhabitation, report.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **34 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work.**
* **KAT pins asserted** (`EXPECTED_KAT_TOTAL = 1338`, `EXPECTED_KAT_FILES = 96`) — move
  deliberately with a reason. `gen_sorry.sh` is locale-fixed. `sha256sum` is at `/sbin`.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`. Do NOT git add or commit.
* **Another agent may be in `Qvm.lean` — do not touch it.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5218 jobs**; `checks.sh` green: **40 tracked sorries**, 1338 KATs, 374 fragments.

Read first: `docs/design.md` **D-P39**, `Midfall/Instances/RunShellInversion.lean` (the
refutation and its mechanism), `Midfall/Lowering/RunEmitted.lean` (`shellLets`, `bindInside`,
the fragment note at :67-76), `Midfall/Lowering/Surface.lean` (`RunShell`, `bindLocals`,
`shell_unfolds`, :257-261), `Midfall/Yul/ShellModel.lean` (`armBody`, `modelIr`, `wrap`),
`Midfall/Lowering/FrameWalk.lean` (`freeNames`), `vendor/.../BigStep.lean:189` (`Step.callOk`).

## Acceptance

- `lake build`, `bash scripts/checks.sh` **and** `python3 scripts/kat_gate.py` green.
- `inlineContractConstants` landed, with the shadowing lemma and its planted test.
- **`RunShell` exhibited inhabited** at `curveSurface`.
- `shell_unfolds` restated with the registry moved in the same commit.
- **Required finding**: is `ir_refines` at `modelIr curveSurface` still refuted? If yes, name
  the remaining mechanism — the entry-path guard difference is the candidate, since `wrap` runs
  the callvalue guard and 13 ABI bounds tests and `RunShell` does not.