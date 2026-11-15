# P-QVM - M6 first tranche: the 9 Qvm/QvmFold holes. Independent of the ir_refines decision.

Status: READY and **unblocked** — nothing here depends on `RunShell`, `ir_refines`, or the
contract-level-binding question. These are the per-identity compile-correctness theorems of the
quotient VM.

## The holes

| file:line | theorem |
|---|---|
| `Qvm.lean:631` | `qvm_compile_correct_identity` |
| `Qvm.lean:698` | `qvm_compile_correct_certifier` |
| `Qvm.lean:713` | `qvm_compile_correct_program` |
| `Qvm.lean:755` | `qvm_validated_noBoundsFault` |
| `Qvm.lean:796` | `qvm_validated_windows` |
| `Qvm.lean:815` | `builder_segments_total` |
| `QvmFold.lean:325` | `identityCorrespondence_of_bridge` |
| `QvmFold.lean:363` | `quotientFold_matches_linearization` |
| `QvmFold.lean:421` | `qvm_compile_correct_stream` |

**Statement authority: sections O and P** (`P-SE-semantic-equivalence.md:1932-2077`). Read
each against its sketch before proving — five packages have found drift, and one found a
statement **false as written**.

## Suggested order

1. **`builder_segments_total`** — likely the most self-contained (a counting/segment fact).
2. **`qvm_validated_noBoundsFault`** and **`qvm_validated_windows`** — the validator safety pair.
3. **`qvm_compile_correct_identity`** — the archetype; the other `compile_correct_*` probably
   follow its shape.
4. **`quotientFold_matches_linearization`** — the fold↔linearisation bridge; likely the most
   valuable and the hardest. Do not leave it unattempted if 1–3 go quickly.

**Land in order and stop at a boundary.** Four proved with five compiling beats nine
half-attempted.

## Second deliverable: two tooling defects, both cheap, both gate-integrity

1. **`scripts/gen_sorry.sh` truncates two declaration columns by one character** —
   `Piop.lean:67` and `Statements.lean:123` rows come out mangled (`…:= sorry\`` → `…:= sorr\``),
   so the generator and the committed table disagree for reasons unrelated to any package.
   **Find and fix the truncation.** A register that rewrites itself wrongly will eventually
   hide a real hole.
2. **`shellConsts_matches_artifact_ok` is decorative** — gutted to the constant `true`, the KAT
   still prints `true`. Confirmed by two independent packages. The named fix: turn it into a
   `decide` theorem `pinnedConstants = RunEmitted.solConstants ++ RunEmitted.shellLocals`,
   which cannot be gutted. **Do it only if it does not cost the Qvm work** — it is hygiene.

## Constraints

* **Never weaken a statement to make it provable.** Report instead. Standing human instruction.
* **Check for vacuity before proving.** This project has found **four** headline hypotheses
  false or vacuous as written, three of them in the plan itself. If a `qvm_compile_correct_*`
  hypothesis is unsatisfiable — e.g. it quantifies over a validated VM that nothing validates —
  **say so; that is a better result than proving it.**
* **`evaluatorRuntime := none` at both Surfaces** is a known gap (`qvm_yul_refines` is blocked
  on it). Check whether any of these nine quietly depends on it, and report which do.
* **D-P23 both halves as theorems** for every claim closed. Falsification-deletion gap
  measured **30 times**; claim no persistence coverage.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work** — 241
  lines of proof lost once. Use content saves; verify with `git status` after each restore.
* **SORRY.md traps**: string-literal `sorry` counts as a hole; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh` (after fixing it) and verify three-way agreement.
* **Method rule**: before claiming a name is missing, try the unprefixed spelling, check for a
  project definition shadowing a Mathlib one (`divCeil` is `Exec/Arith.lean:53`), and remember
  `import Midfall` resolution ≠ this file's import closure.
* **`sha256sum` EXISTS at `/sbin/sha256sum`** — a previous package wrongly reported it missing.
  Do not add a shim or 'fix' this.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~9–17 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Surface.lean`, `RunShell`, or
  `ir_refines` — the binding question is an open human decision. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5218 jobs**, 128 modules; `checks.sh` green: **41 tracked sorries**, 1330 KATs
across 96 files, 245 fragments, 6 gap defs, 30 pins, Statements hash OK.

Read first: `Midfall/Lowering/Qvm.lean`, `Midfall/Lowering/QvmFold.lean`,
`Midfall/Generator/Quotient/{VmReference,VmBuilder,VmCertify,Disasm,YulEmit}.lean`, sketch
sections O and P from line 1932, `docs/plans/P-SE-statements.md`, `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 41**.
- `gen_sorry.sh` truncation fixed and shown by regenerating to a byte-identical table.
- **Required finding**: which of the nine are provable as stated, which are vacuous or blocked
  on `evaluatorRuntime`, and whether `quotientFold_matches_linearization` holds.