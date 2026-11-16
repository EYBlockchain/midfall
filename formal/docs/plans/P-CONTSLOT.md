# P-CONTSLOT - the third per-arm pass: the const-slot correspondence. Closes the hole.

Status: READY, bounded, **~45% of one hole remaining**. P-READOFF proved the read bound for 24 of
26 arms and identified that the binding constraint is **not** the read bound but a third per-arm
fact nobody had named.

## The obstacle, in P-READOFF's words

> the correspondence between the slots `evalQuotientIdentityStep` reads via `constAt` and the
> `konst` operands `visitQuotientOperands` returns. Those are **independent code over the same
> bytes** and nothing in the tree relates them; phase 2 bounds slots the **walker** names, and
> the interpreter is only safe if the walker names every slot the interpreter reads.

**That pass is the same size as the two already done.** `numConsts_eq_build_length` and
`constAt_ok_of_lt` already landed — build on them.

## Deliverable

1. **Enumerate, per arm, which const slots the interpreter reads** (`constAt` indices) and which
   the walker returns as `konst` operands. **Differential enumeration before induction (R-70)**
   — run both, compare, find disagreements **before** proving. Watch the payload trap again.
2. **Prove the correspondence lemma** — every slot the interpreter reads is one the walker names.
3. **Then close `qvm_validated_noBoundsFault`** (`Qvm.lean:768`) at its **sketch strength**.
   Its second conjunct is `constSlotOutOfRange`; the first needs the walk induction over
   `identitySegment` plus locality lemmas moving between absolute and segment-relative indices.
4. **If the first conjunct still resists**, land what you can and report the exact remaining
   obstacle — P-READOFF's report on the read bound is the model for how to do that.

## Also: two arms still unproved

`AFFINE_SUM` and `MODARITH7` are **measured**-agreeing but not **proved**. The obstacle is
**chaining**: `AFFINE_SUM` needs the second fold's start to equal the first fold's result
(`usedA = 3l`); `MODARITH7` needs five such chains behind a flag-dependent header. `fold_blocks_noRF`
is the tool and it works — the two RUN arms are the proof. **Lower priority than the hole.**

## Standing rules — read these, they are recent

* **`lake build` green does NOT mean the KAT gates passed.** A false `eval ... -- expect true` is
  an info line, not a build error. **Always run `python3 scripts/kat_gate.py`** to check gates.
  (R-71 / R23 — this was invisible for 180 turns.)
* **Do NOT round-trip files over ~1500 lines through the `read` tool.** It silently truncated a
  1967-line file and a splice dropped 612 lines. Use direct file access. `Qvm.lean` is now 2803
  lines — **this package is squarely in the danger zone.**
* **Audit against A–R only where a sketch exists.** 11 of 40 holes have no sketch; `noBoundsFault`'s
  is in section **Q** (plan:2268-2271), not O. State which source you audited against.
* **Never weaken a statement.** The hole is at universal sketch strength; keep it there.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **34 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work.**
* **KAT pins are asserted** (`EXPECTED_KAT_TOTAL = 1338`, `EXPECTED_KAT_FILES = 96`). Move them
  deliberately and say why; do not work around them.
* **`gen_sorry.sh` is locale-fixed**; `sha256sum` exists at `/sbin/sha256sum` — no shim.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~14 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Surface.lean`, `RunShell`,
  `ir_refines`, `readScheduleAgrees`. Do NOT git add or commit. Leave no scratch.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5218 jobs**, 128
modules; `checks.sh` green: **40 tracked sorries**, 1338 KATs across 96 files, 374 fragments.
`Qvm.lean` is 2803 lines: section 7 = stride agreement, section 8 = read bound, hole at :768.

Read first: `Midfall/Lowering/Qvm.lean` **sections 7 and 8** (reuse `NoRF`, `fold_blocks_noRF`,
`numConsts_eq_build_length`, `constAt_ok_of_lt`), `Midfall/Generator/Quotient/VmCertify.lean`
(`visitQuotientOperands`, `identitySegment`), `VmReference.lean` (the step), plan section Q
lines 2268-2271 (the sketch), `docs/REVIEW.md` R-70 and R-71, `docs/ETA.md` R23.

## Acceptance

- `lake build`, `bash scripts/checks.sh` **and `python3 scripts/kat_gate.py`** green.
- The const-slot correspondence proved.
- **`qvm_validated_noBoundsFault` closed at sketch strength** → register **39**. If it cannot
  close, the exact remaining obstacle, as precisely as P-READOFF's.
- **Required finding**: does the walker name every slot the interpreter reads, or is there an
  arm where it does not? A disagreement there would be a real bug in the reference port.