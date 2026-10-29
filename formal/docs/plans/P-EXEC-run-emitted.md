# P-EXEC - run the emitted program through the vendored semantics. The check that subsumes the queue.

Status: READY, and it reframes P-ARITY's finding rather than continuing it.

## The situation

P-ARITY found **9 unchecked well-formedness dimensions**, the biggest being **builtin argument
arity** - the emitted program calls 27 distinct builtins and no argument list is checked
anywhere. It correctly declined to close that cheaply, because the dialect has no arity
function, so a static check needs a **hand-written table - a new unverified source of truth**.

**That judgement is right, and it points at a better answer.** A wrong-arity builtin call has
no `Step` rule, so the semantics **gets stuck**. So do missing helpers, misplaced `leave`,
duplicate declarations, and use-before-declaration. **Running the program catches all of them
at once, with the semantics as the ground truth and no new table.**

I verified: **nothing in the tree runs the emitted program.** `runContractIR_inhabited
(:260)` runs the *imported solc IR*, not `GenAst` output. So the generator's central claim -
*the emitted AST **is** the deployed program* - has never been supported by executing it.

## Deliverable, in priority order

1. **A stuck-state check per emitted helper and slice.** For each of the 8 helpers and each
   slice, run the vendored big-step semantics on a minimal configured world and assert the
   run **terminates in a state the semantics recognises** (normal, revert, or the documented
   halt) rather than getting stuck. This is the cheap, high-coverage version.
2. **A whole-`emitMain` run on real calldata.** We now have a fixture that **verifies** - the
   regenerated 2,640-byte poseidon proof from `formal-baseline-v1`. Build the calldata the
   ABI codec describes, wire `ExternalCalls`/`ExternalGas` as `runContractIR_inhabited`
   does, and run. **If this reaches an accept, it is the single strongest piece of evidence
   the project has** - the emitted AST executing and accepting a real proof.
3. **Report honestly if (2) is not reachable this package.** Precompile responses, `G2`
   encoding, and the missing `validate_public_accumulator` may block it. Say exactly which,
   and land (1) regardless.

## Why this is worth more than the 9 gates it replaces

* **No new source of truth.** The vendored step rules are the arbiter, not a table I wrote.
* **It catches what static checks structurally cannot** - a program can pass every name,
  arity and placement gate and still be stuck on the first instruction.
* **It is the actual claim.** PLAN section 8 wants `render = lower.map print` by construction;
  execution is what makes "it is the deployed program" mean something.

## Constraints

* **No DSL extension, no fork edit.** Use the vendored semantics as it stands.
* **`Instances/` confinement** - if a concrete world needs the fixture, the run lives in
  `Instances/`; the *statement* that it does not get stuck should be as portable as possible.
* **Do not weaken the semantics to make a run succeed.** If a stuck state is found, **that is
  a finding about the emitter**, not an obstacle. Report it; do not patch around it.
* **Fuel / termination:** `Bridge.noWritersFuel` is still `fun _ _ => sorry`, so a run may
  need a fuel bound. Use one and say so - do not pretend it terminates unconditionally.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp.
* **D-P23 / R-41**: every new gate needs a demonstrated failure mode. A stuck-state gate that
  cannot be made to fail is decoration - inject a wrong-arity builtin call on a clone and
  confirm the gate reddens.
* `SORRY.md` delta should be zero. Numbers from `lake build` and `scripts/checks.sh`.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5153 jobs**; `checks.sh` green: 64 tracked sorries, **1280 KATs across 84
files**, 111 statement fragments, 12 fact families, 23 spec-theorem bundles, 30 baseline
pins, 107 modules, Statements hash OK.

Read first: `Midfall/Yul/Bridge.lean` (`Run`, `RunCommitted`, `WorldLocal`, the view lemmas,
`noWritersFuel`), `Midfall/Instances/ImportedIR.lean:260` (`runContractIR_inhabited` - the
pattern to copy), `vendor/yul-semantics/YulSemantics/BigStep/Step.lean` (the step rules that
define stuck), `Midfall/Lowering/GenAst.lean` (`emitMain`, `emitHelpers`),
`Midfall/Instances/DeployedProfile.lean` (the real calldata and the artifact-facing view
`artifactPlanView`).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1280.
- The per-helper/slice stuck-state gate exists and is shown to redden on a wrong-arity call.
- **Required finding**: does the whole emitted program run, and does it accept? If it gets
  stuck, name the exact instruction and which of the 9 unchecked dimensions it corresponds to
  - that is the first *empirical* answer to whether the static queue matters.
