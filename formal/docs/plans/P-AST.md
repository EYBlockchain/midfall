# P-AST - emit Yul ASTs. The critical path, and it fixes R-62's new defect.

Status: READY. Decided by **D-P25** (generator emits ASTs; `stmtsBeq` is the check of
record; token comparison is the CI tripwire) and **D-P26** (constructor helpers first, no
DSL extension until that proves painful). Scope is **per-deployment first** (D-P24).

## Why this is the critical path, not a nice-to-have

1. **R-62 found a statement defect that only AST emission fixes properly.** The ten `*_spec`
   theorems quantify over every Surface, but `Surface.blk` is a free field whose only
   constraint is `main_concat`, and `L.main` comes from the free `lower`. A Surface with
   `blk .finalPairing := return(0, 0)` satisfies every hypothesis and refutes the
   conclusion. **The ten theorems are false as stated.** The fix is to pin `blk` to the
   generator function and make that equation a hypothesis of each spec theorem.
2. **Every block of the only Surface is a placeholder.** Verified: `fxPartialBlocks`
   (`SurfaceFixture.lean:155`) gives each block a single dummy `mstore`. That blocks P5
   (the calibration point PLAN 14.4 pulled forward), P7, P9, P10.

## Deliverable: FinalPairing end to end

Do **one** partial completely rather than all of them partially.

1. **Parameterised AST builder** for `FinalPairing` and its `ec_pairing`/`fail` helpers,
   using **constructor helpers** (D-P26). `finalPairing_ast` and `failFunction_ast` already
   exist as fixed `yul%` snapshots - generalise them into functions of the plan, do not
   start from scratch.
2. **Check it against the text port** with the token comparator (`yulTokens`), NOT printed
   text. R-62 measured that `normalise_sol.py` reports differences on identical code -
   Lagrange 73 vs 60 lines, FinalPairing 6 vs 3 - from line breaks and decimal-vs-hex
   spelling alone. A tripwire that fires on identical input is worse than none.
3. **Wire it into the test Surface** so `blk` returns real ASTs for at least `finalPairing`,
   replacing the dummy.
4. **Add the `blk` pin** and make it a hypothesis of `finalPairing_spec` (and the other nine
   spec theorems, even while their blocks stay placeholders - the hypothesis form is what
   makes them true).
5. **Demonstrate the pin bites**: a Surface with a planted `blk` must fail it.

## Constraints

* **Do NOT extend the vendored DSL** in this package. D-P26 says constructor helpers first;
  if you conclude they are genuinely unworkable for some construct, **stop and report** with
  the specific blocker rather than editing `vendor/`.
* **`yul%` cannot splice Lean values** - only literal numbers, strings, identifiers. That is
  why this is constructor work, not quotation work.
* **D-P23 non-vacuity obligation applies to everything you state**: each new pin needs a
  satisfiability witness AND a falsifiability demonstration.
* The three gates now enforce structure - `check_duplicate_facts.py` (with discovery),
  `check_statement_fingerprints.py` (type-only, comments stripped),
  `check_hypothesis_bundles.py` (joint exhibits). **Expect them to redden** when you change
  `blk` or add fields; update them honestly, do not weaken them.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50). `lake env lean` does not apply lakefile
  options - numbers from `lake build` and `scripts/checks.sh`.
* **R-41**: every new pin needs a demonstrated failure mode.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Lean project `formal/`. Build green
at **5143 jobs**; `checks.sh` green: 64 tracked sorries all owned, **1150 KATs across 76
files**, 63 statement fragments, 9 fact families, 7 registered headline bundles (6 jointly
exhibited), 100 modules reachable, Statements hash OK.

Read first: `docs/plans/README.md` standing notes; `docs/REVIEW.md` R-62 (the `blk` defect)
and R-60; `docs/design.md` D-P24..D-P26; `Midfall/Generator/VerifierPartials.lean` (the text
port you are checking against); `Midfall/Generator/YulGolden.lean` (the `yulTokens`
comparator and the existing AST snapshots); `Midfall/Lowering/Surface.lean` (`blk`, and the
`irCheck`-as-projection pattern from S1 - copy that approach); `Midfall/Lowering/Partials.lean`
(the ten spec theorems needing the hypothesis).

**No idle builds.** Multi-line anchored edits have broken files repeatedly this session
including the orchestrator's own - re-read what you changed, rebuild after every edit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green, all three structural gates still green.
- `FinalPairing` AST builder exists, agrees with the text port under the token comparator,
  and is wired into the test Surface.
- The `blk` pin exists, is a hypothesis of the spec theorems, and is demonstrated to bite.
- **Required finding**: can P5 (`finalPairing_spec`) now be *attempted*? Name what still
  blocks it - the review says the remaining blocker is the real-curve model so
  `Eip2537.Holds` is satisfiable, not the AST. Confirm or correct that.
