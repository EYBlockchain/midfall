# P-RAM - make OOM prevention an enforced mechanism, not prose.

Status: READY, and **now a standing requirement of the objective**: *always monitor ram
consumption and prevent OOM.* Today the knowledge exists only as comments inside
`Midfall/Lowering/RunEmitted.lean` - nothing enforces it, so the next package can repeat the
crash.

## What actually happened, measured

| moment | peak lean RSS | outcome |
|---|---|---|
| pre-crash session | **8.7 GB** (six `native_decide` in one process) | session killed |
| per-unit `native_decide` | **16.8 GB** on a 32 GB host | **host went down**, 52-72 GB swap |
| per-unit `#eval` | 3.8-4.6 GB | killed by watchdog |
| final shipped state | **2.34 GB** | green |

**Root cause is structural, not a leak:** `EvmState.memory` is `Nat -> UInt8`, so every
`mstore` wraps the previous function and a deep run builds a long closure chain - slow *and*
memory-heavy. Compounding: each unit re-spelled the emitted helper block.

**Also true: other `lean` processes run on this machine concurrently (~660 MB each).** A
first-attempt watchdog mis-credited them to this session. Any guard must scope to **its own
process tree**, not all `lean`.

## Deliverable

1. **`formal/scripts/ram_guard.sh`** - a small, dependency-free tool that reports:
   physical memory, bytes free, swap used, the RSS of the **current process tree** (not all
   `lean`), and a verdict `OK / TIGHT / DANGER` against explicit thresholds. It must be
   callable *before* a heavy run and *as a wrapper around* one (`ram_guard.sh --limit 6G --
   lake build`), killing **only its own subtree** when the limit is exceeded - the pattern
   `RunEmitted.lean` already describes.
2. **A memory section in `checks.sh`** reporting headroom on every gate run, so drift is
   visible before it is fatal. **Keep it cheap** - a report, not a gate that can fail the
   build. If you make it fail, justify why.
3. **A written budget in `docs/PLAN.md` section 12** as a standing rule (number it - the next
   free slot is **D-P31**): any package that evaluates in the VM must (a) state an expected
   peak, (b) run under `ram_guard.sh`, and (c) report measured peak RSS in its results. A
   gate that cannot run within budget is **narrowed or dropped, with the reason recorded** -
   exactly what P-EXEC did when it withdrew the `Instances` theorem form.
4. **Add the clause to the standing brief template** in `docs/plans/README.md` so every future
   subagent inherits it without me writing it by hand each time.

## Constraints

* **Do not change any Lean file.** This is tooling and documentation.
* **`checks.sh` must stay green and must not get slower by more than ~1 s.** My own anchored
  edits have broken this file repeatedly - insert with a script that asserts the anchor
  appears exactly once, then verify with `bash -n` and a full run.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check` for Lean claims; for shell, `bash -n` plus a real run.
* **Never perturb the working tree in place.**
* **D-P23 / R-41 apply to tooling too**: the guard must be **shown to work** - spawn a
  subprocess that allocates past the limit and confirm it is killed, and confirm an ordinary
  `lake build` passes untouched.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Host: **32 GB physical**, currently ~2.3 GB swap used, 2 unrelated `lean` processes running.
Build green at **5154 jobs**, 108 modules; `checks.sh` green: 64 tracked sorries, **1286 KATs
across 85 files**, 111 statement fragments, 12 fact families, 8 + 23 bundles, 30 baseline
pins, Statements hash OK.

Read first: `Midfall/Lowering/RunEmitted.lean` lines 40-60 and 210-260 (the measurements and
the sharing fix), `docs/PLAN.md` section 12 (the standing rules list), `scripts/checks.sh`
(structure - 12 sections), `docs/plans/README.md`.

## Acceptance

- `ram_guard.sh` exists, is `bash -n` clean, reports the four numbers, and **is demonstrated
  to kill a runaway subprocess while leaving a normal build alone**.
- `checks.sh` shows a memory line and still exits 0.
- D-P31 recorded in `design.md`/`PLAN.md`, and the brief template carries the clause.
- **Required finding**: what is the **measured peak RSS of a full `lake build` and of
  `checks.sh`** on this host today? That is the baseline every future budget is set against,
  and we have never measured it.
