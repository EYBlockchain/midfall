# v2-bundle — hand-over package for the V2 plan

## What goes where

| file | lands at | by |
|---|---|---|
| `docs/PLAN-V2.md`, `docs/EXECUTION-V2.md` | `formal/docs/plans/` | T0.4 (orchestrator) |
| `docs/QUEUE.md`, `docs/STATUS.md` | `formal/docs/` | T0.4 |
| `docs/GOAL-PROMPT.md` | the orchestrator's `/goal` (paste it). Since 2026-11-17 it is the PLAN-V3 version; the V2 version is at tag `formal/v2-cutover` | the human |
| `docs/background/formal-lowering-review.md` | not landed; background only (the original review, findings F1–F11) | — |
| `lean/Midfall/LoweringV2/{Program,Statements}.lean`, `lean/Midfall/Lowering/LegacyVacuity.lean` | `formal/Midfall/…` | Q0.1 |
| `lean/Midfall/Tools/ConeSorries.lean` | `formal/Midfall/Tools/` | Q0.2 |
| `tools/ConeSorriesTest.lean` | stays here; run once from `formal/` (it contains deliberate sorries) | Q0.2 |
| `probe/*.lean` | the source for `Instances/CodegenAgreement.lean` | G.1 |

## Publish

The bundle is committed on its own branch, `v2/bundle`, based on `formal/baseline`. The agent's
working tree and `formal/baseline` are untouched. The orchestrator's T0.4 fetches it from `origin`,
so push it first:

```bash
git push -u origin v2/bundle
```

## Then

Give the orchestrator `docs/GOAL-PROMPT.md` as its `/goal`. It does the cut-over at the next package
boundary:

1. it drains P-RUNLEG;
2. it tags `formal/v1-final`;
3. it records D-V2;
4. it fetches this bundle;
5. it works through `QUEUE.md` from the top.
