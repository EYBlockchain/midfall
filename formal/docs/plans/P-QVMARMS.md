# P-QVMARMS - the one shared gap blocking six Qvm holes: per-opcode `consumed` agreement.

Status: READY, unblocked, and **mechanical but large**. P-QVM diagnosed all six remaining Qvm
holes as needing the same machinery:

> per-opcode agreement between `evalQuotientIdentityStep`'s `consumed` field and the validator's
> `quotientOpLen` / `visitQuotientOperands` across **~25 arms**, plus a loop induction over the
> fuel-bounded walks.

## The six holes

| hole | file |
|---|---|
| `qvm_compile_correct_identity` | `Qvm.lean:631` |
| `qvm_compile_correct_certifier` | `Qvm.lean:698` |
| `qvm_compile_correct_program` | `Qvm.lean:713` |
| `qvm_compile_correct_stream` | `QvmFold.lean:434` |
| `builder_segments_total` | `Qvm.lean:995` |
| `qvm_validated_noBoundsFault` | `Qvm.lean:768` — **restored to sketch strength by P-QVM; keep it there** |

**`quotientFold_matches_linearization` (`QvmFold.lean:376`) is separate** — it needs a
`sparse = naive` induction plus a `groupedAdd` ordering invariant. P-QVM checked it against
`computeLinearizationCommitment` and found the statement **plausible as written**. Do it only if
the arms work finishes early.

## Approach

1. **Enumerate the arms first** — list every opcode in `evalQuotientIdentityStep` and the matching
   `quotientOpLen` case, and note any that disagree **before** proving anything. A disagreement
   found by enumeration is a finding; one found mid-proof is a wasted day.
2. **Prove the per-arm agreement as one lemma per arm** (or a `decide`-able table if the arms are
   enumerable). Prefer a **single case-split lemma** over 25 separate theorems if it reduces.
3. **Then the loop induction** over the fuel-bounded walk.
4. **Then the holes**, in the order above — `qvm_compile_correct_identity` is the archetype and
   P-QVM **measured it true at its smallest witness** (7-byte segment, zero constants, evaluates
   to exactly the reference field element). So it is a proof gap, not a statement gap.

## Verify rather than inherit — this has been wrong six times in a row

**Six false premises have been found in orchestrator briefs this session.** Before spending a
day on this, confirm:
- that all six really need the same machinery (P-QVM's claim, from an interim report);
- that none is vacuous — P-QVM verified none are, and computed the archetype's smallest witness;
- that `builder_segments_total` is **not** self-contained — P-QVM found my ordering premise
  wrong: it is an interpreter-totality claim as hard as the archetype.

If the shared-gap diagnosis is wrong for some of the six, **say which and stop on those.**

## Constraints

* **Never weaken a statement to make it provable.** `qvm_validated_noBoundsFault` was just
  restored to sketch strength after five packages of silent drift — do not re-narrow it.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **32 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work.**
* **The gate suite just changed** — `check_statement_fingerprints.py` now parses structures and
  asserts per-field coverage, and `kat_gate.py` asserts `EXPECTED_KAT_TOTAL = 1334` /
  `EXPECTED_KAT_FILES = 96`. **If you add KATs you must move those pins deliberately and say
  why.** Do not work around them.
* **`gen_sorry.sh` is locale-fixed** — do not revert it.
* **`sha256sum` exists at `/sbin/sha256sum`** — no shim.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~14 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Surface.lean`, `RunShell`,
  `ir_refines`, or `readScheduleAgrees` — several are open human decisions. Do NOT git add or
  commit. Leave no scratch.
* **Durability**: land incrementally, keep the tree green, interim report after the arms
  enumeration, and revert-and-report rather than carrying broken work forward.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5218 jobs**, 128 modules; `checks.sh` green: **40 tracked sorries**, 1334 KATs
across 96 files, **374 fragments across 10 LoweringCorrect and 16 PartialSpecs fields (parsed)**.

Read first: `Midfall/Lowering/Qvm.lean` (the holes, `qvm_validated_windows` as a worked example,
the validator), `Midfall/Lowering/QvmFold.lean`, `Midfall/Generator/Quotient/` (`VmReference`,
`VmBuilder`, `VmCertify` — where `evalQuotientIdentityStep` and `quotientOpLen` live), sketch
sections O and P from line 1932, `docs/plans/P-SE-statements.md`, `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 40**.
- The arms enumeration landed, with any disagreements found **before** proving.
- As many of the six as fit — **one closed is fine if the arms work is sound and landed**.
- **Required finding**: was P-QVM's shared-gap diagnosis correct for all six? And does the
  per-opcode `consumed`/`quotientOpLen` agreement hold, or did the enumeration find an opcode
  where the interpreter and the validator disagree?