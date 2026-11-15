# P-GATEINTEG - a whole `LoweringCorrect` field can be deleted and no gate notices. Fix that.

Status: **GATE INTEGRITY.** P-SCHED proved it by perturbation:
- **P8**: delete `readScheduleAgrees` from `LoweringCorrect` **entirely** → build green, all
  three text gates green, and the fingerprint gate **still prints "9 LoweringCorrect fields"**.
- **P7**: gut a field's conclusion to the self-equality `ms.map Msg.slot = ms.map Msg.slot` →
  passes all three gates.
- **P6**: delete a KAT gate and its `#eval` line → unseen, because the KAT section reports a
  **count** and asserts no total.

**The claim that all 48 obligation fields are gate-tracked is currently false. The printed count
is a literal, not a derived fact.**

## Deliverable

1. **Derive the field count from the structure, don't hard-code it.** Parse
   `structure LoweringCorrect` and enumerate its fields; the gate must fail if the parsed count
   disagrees with the registry. Same for `PartialSpecs` and any other tracked structure.
2. **Require every parsed field to appear in the registry.** A field with no pin should redden —
   that is exactly what P8 slipped through.
3. **Reject self-equality conclusions.** A field or theorem whose conclusion is
   `X = X`, `X ↔ X`, or `∀ …, P → P` is trivially decidable and should be caught. The
   `PIN IS TRIVIALLY DECIDABLE` check already exists for Surface pins — **extend it to
   `LoweringCorrect` fields and to spec conclusions.**
4. **Assert a KAT total.** The KAT section should fail if the count moves unexpectedly, not just
   print it. Pin the expected total and require regeneration to update it deliberately.

## Acceptance test — the perturbations must now REDDEN

Re-run P6, P7, P8 exactly as P-SCHED described them, **on a clone**, and show each now reddens.
A gate change that has not been observed to fail is decoration (R-41). **Report the before/after
for each.**

## Also worth doing while you are in the gate scripts

**`gen_sorry.sh` was just fixed** (BSD `cut -c` counting bytes under non-UTF-8 locales). Verify
it is stable under `LC_ALL=C`, `C.UTF-8`, `en_US.UTF-8` — the fix claimed all three; confirm.

## Constraints

* **Do NOT change any Lean statement.** This is gate tooling only. `readScheduleAgrees` stays
  exactly as it is — refuted at the deployment, unweakened, with `gap_readScheduleAgrees_pin`
  recording what it needs.
* **All 13 sections must stay green** after the change, and each new check must be shown to
  redden on its target.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work.**
* **`sha256sum` exists at `/sbin/sha256sum`** — do not add a shim.
* **Never run `checks.sh` while a file is being edited.** Gate 9–17 min.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, or any Lean file. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5218 jobs**, 128
modules; `checks.sh` green: **40 tracked sorries**, 1334 KATs across 96 files, 245 fragments,
9 `LoweringCorrect` fields claimed, 30 pins.

Read first: `scripts/check_statement_fingerprints.py` (the `LoweringCorrect` field list and the
`PIN IS TRIVIALLY DECIDABLE` check), `scripts/check_hypothesis_bundles.py`, `scripts/kat_gate.py`,
`scripts/checks.sh`, `Midfall/Lowering/Obligations.lean` (the structure — **read only**).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- **P6, P7, P8 all redden after the fix** — with before/after evidence.
- Field counts derived from the structures, not hard-coded.
- **Required finding**: how many `LoweringCorrect` and `PartialSpecs` fields are currently
  **untracked**, and does any of them matter? P-SCHED found one by accident; this should find
  the rest systematically.