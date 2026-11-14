# M8-SCOPE — what `lowering_equivalence`'s remaining difficulty actually is, measured

**Status: SCOPING NOTE, produced by P-CSURFACE step 2. Nothing here is a proof.** Its one
job is to turn "M8: uncosted — the largest open estimate in the project" (docs/ETA.md R7)
into a number with a basis, and to say plainly where the number is a measurement and where
it is still a guess. Per the ledger's own rule (R6), every prescription below is labelled
**TRIED** or **GUESSED**.

Read with: `docs/PLAN.md` §7 and the M8 milestone row, `docs/ETA.md` R7,
`Midfall/Lowering/Surface.lean` (`Surface.shell`, `shell_unfolds`, `Surface.irCheck`,
`Surface.irRuntime`, `RunContractIR`, `RunShell`, `ObsEquiv`, `DeploymentW`),
`Midfall/Lowering/Obligations.lean` (`LoweringCorrect.ir_refines`,
`lowering_equivalence` and its blocker list), `Midfall/Yul/ImportSolcIR.lean` (the pin
and its two decisions), `Midfall/Instances/ImportedIR.lean` (the only exhibited
`RunContractIR`), and the two files this package lands:
`Midfall/Instances/CurveSurface.lean` and `Midfall/Instances/IrCheckBlindness.lean`.

---

## 0. The headline, before the detail

**M8 as currently formulated cannot be proved, and the reason is not difficulty but
shape.** `LoweringCorrect.ir_refines` quantifies over every `ir` satisfying
`S.irCheck ir = true`, and `irCheck` does not constrain the program in any way that
bears on observational equivalence. This is not a gap to be closed by work on the proof —
it is a property of the hypothesis, and it is now demonstrated in the tree as a theorem
(`IrCheckBlindness.irCheck_accepts_both_outcomes` +
`irCheck_admits_different_observables`): **two objects both pass `irCheck` and their
runs differ in a field `ObsView` compares.** So `ir_refines` is not "hard", it is
**false as stated** — there are IRs the hypothesis admits for which the conclusion cannot
hold.

That is the third time this project has found its difficulty had relocated rather than
shrunk (R5, R7), and it is the finding the estimate ledger exists to force. The rest of
this note sizes what is left once the formulation is fixed.

---

## 1. `irCheck` — what it verifies, what it does not, and whether the gap is exploitable

### What it verifies (the whole of it)

`Surface.irCheck` (Surface.lean, R-60 S1) is a projection of `Surface.runtimeName`:

1. the sub-object named `runtimeName ir.name` **exists** inside `ir`; and
2. no **top-level** statement of that sub-object's code block calls a user function the
   **top level** does not declare — where "a call" means a call in statement position or
   in a `let`-initialiser (`unresolvedTop`).

That is all. It is a name-resolution sanity check on one object's outermost statement
list. Its stated purpose (attack.md, the `Evaluator.rel` entry) is to detect an
un-rewritten `memoryguard(x)`, which the vendored dialect elaborates as a call to a
user function nothing declares. For that one job it works: `fxIrMemoryguard` and the
planted rename `fxIrRenamed` are both rejected, and `ImportedIR.irCheck_holds_at_imported`
shows it accepts the real artifact.

### What it does NOT check

Everything else. Concretely, and each of these is now a computed case in
`Midfall/Instances/IrCheckBlindness.lean`, run against the **real 2,898-line pinned
artifact** rather than a toy:

| mutation | `irCheck` | equivalent to the artifact? |
|---|---|---|
| alpha-rename every helper and all its call sites | **true** | yes (identity) |
| wrap a top-level store address in `add x 0` (inverse of a real optimizer fold) | **true** | no |
| change every `revert(p, 0)` inside a helper body to `revert(p, 32)` | **true** | **no — different return data** |
| delete the first statement of every helper body | **true** | **no** |
| mutate the **creation** object's `codecopy` size | **true** | **no — different deployed code** |
| rename a declaration and leave its call site (the planted rename) | false | no |

The mechanism is structural, not incidental: `unresolvedTop` walks `b.any` over the
**top-level** list only, so **no function body is ever inspected**, and the creation
object is never inspected at all. `irCheck_accepts_any_top_level_clean_block` states the
general fact — any block whose top-level calls resolve is accepted, whatever it computes —
and `irCheck_eq_of_top_level_agreement` states the equality form: two blocks agreeing on
top-level resolution are **indistinguishable** to the check.

### Is the gap exploitable? Yes, trivially, and that is the point

`irCheck_accepts_both_outcomes` exhibits `irRet` (runtime = one `ret(0,32)`) and
`irRev` (runtime = one `revert(0,0)`), both accepted by `rfl`.
`irCheck_admits_different_observables` shows their first statements produce
`HaltKind.ret` and `HaltKind.revert` respectively — and `ObsView` **carries**
`outcome` and `halted : Option (HaltKind × List UInt8)` (Bridge.lean:373), which are
precisely what `Obs.isRevertOrHalt` and `Obs.returnData` read. So the two objects are
distinguishable **at exactly the level `ObsEquiv` compares at**, and
indistinguishable to the hypothesis.

**Consequence for M8.** `ir_refines` says: for ALL `ir` with `irCheck ir = true`,
`ObsEquiv (RunContractIR … ir …) (RunShell …)`. Take the shell model to be
observationally equivalent to one of `{irRet, irRev}` — which is what the fixture's
shell is, since `fxShell` runs the assembly and halts — and the other is a
counterexample. The statement is **refutable, not unproved**. No amount of simulation work
rescues it, because the hypothesis is the broken part.

### What M8 must therefore do instead — three options, costed

| option | what it is | cost | label |
|---|---|---|---|
| **(A) Name the hop as an assumption** | a D-P36a-shaped record: "the pinned `ir` of the pinned sources under the pinned solc is a semantics-preserving lowering of the generated assembly", five-ish named constants, registry + axiom probe | **1–2 sessions** | GUESSED, but the shape is exactly `Assumptions/CurvePairing.lean`, which took 1 session (R7) |
| **(B) Strengthen `irCheck` into a real translation validator** | PLAN §7's original `IRCheck.lean`: prove `irCheck ir = true → ObsEquiv ir (ShellModel.wrap L)`. Requires a machine-checked link between solc's assembly→IR lowering and the shell model — i.e. verifying the compiler | **not estimable**; this is a research programme, larger than the whole project to date | GUESSED, and the guess is "months, not sessions" |
| **(C) Restrict the quantifier** | state `ir_refines` about the ONE pinned object rather than all of the check's preimage, and prove the simulation for it | simulation cost only, see §3 | GUESSED |

**Recommendation: (A), with (C) as the eventual upgrade if the hop is ever to be removed.**
(B) is what PLAN §7's wording ("a verified checker") actually promised, and the honest
statement is that it was never sized. Note that (A) is not a new kind of move for this
project: D-P36 chose exactly this shape for the pairing (R6/R7), and it cost one session
and bought the landmark. The trusted-base row in PLAN §1 gains "solc's via-IR lowering
preserves the observable semantics of the generated assembly, at solc 0.8.30 commit
73712a01 under the pinned settings" — which is already, in substance, what
`ImportSolcIR.lean` DECISION 1 asserts in prose.

---

## 2. `shell_unfolds` — the pin holds the model, not the entry path

### What it says

`shell.codeBlock = L.headGuard ++ bindLocals ++ L.main` (Surface.lean, R-58 F3). It is
what makes `RunShell` and `RunVerifier` be about one program instead of three, and the
fixture exhibits it by `rfl`.

### The concrete difference between the model and the artifact

The model's entry path, first statement: the head guard
`if gt(mload(0x40), 0x1000) { revert(0,0) }`. Then straight into the assembly.

The artifact's entry path, from the pinned import (`ImportedIR.verifierRuntime`, first
three of 28 top-level statements, all three of which are the only ones the exhibited run
executes):

1. `mstore(64, memoryguard(128))` — the free-memory-pointer prologue;
2. `if iszero(lt(calldatasize(), 4)) { let selector := shift_right_224(…) ; switch
   selector … }` — the **selector test and ABI dispatch**;
3. a call to `revert_error_42b3…()`, whose body is `revert(0,0)` — the **fall-through
   for an unroutable call**.

So the deployed entry path does four things the model does not: it **rejects a call
carrying value**, it **tests `calldatasize ≥ 4`**, it **routes on the 4-byte selector**,
and it **ABI-decodes arguments into memory** before the body runs. The model does none of
them: it runs the verifier body unconditionally, from zeroed memory, with the raw calldata
unread.

Three concrete consequences, each of which is a thing M8 has to pay for:

* **Different answers on the same calldata.** A 4-byte calldata with a selector that is
  not `verifyProof` reverts in the artifact and **runs the verifier body** in the model.
  Any `ObsEquiv` between the two is therefore false for inputs outside the
  `verifyProof` arm — which is exactly why `lowering_equivalence` carries
  `hsel : bytesTake cd 0 4 = some fnSigVerifyProof` and `ir_refines` does not.
* **Different initial memory.** The artifact's prologue writes the free-memory pointer
  (at `0x80` in the pinned `ir`, at `0x8e0` in the deployed bytes — DECISION 1, and
  `ImportedIR.witness_freePointer_is_the_ir_value` is the state fact). The model's
  `callState` is all-zero. `ObsView` deliberately excludes memory, so this one is
  invisible to the equivalence — which is a **reason the equivalence is stated at view
  level**, not a free pass: any Inv clause about memory below the argument region is
  about state the artifact never produces.
* **Different return encoding.** The model's terminal is `return(RETURN_MPTR, 0x20)`
  with the word 1 (`traceReturn_spec`); the artifact's dispatcher cleanup ABI-encodes
  the return. Same `abiTrue`, arrived at by different code.

### What M8 must build

A **dispatcher model**: a `YulObject` whose `codeBlock` is callvalue-check + length
check + selector switch + ABI decode, with a `verifyProof` arm that runs
`headGuard ++ bindLocals ++ main`, and then `shell_unfolds` restated as design2 had it:
*"the `verifyProof` ARM of shell runs headGuard ++ bindLocals ++ main from dispatcher
memory"*. That restatement is what Surface.lean's `shell` field doc already says M8 owes.

Two sub-costs, and the second is the real one:

* writing the dispatcher into the model — mechanical, and the AST is already in the tree
  inside the imported artifact;
* **re-deriving every per-partial pre-condition against dispatcher-written memory.** The
  `Inv` clauses and `calldataPre` are stated against a frame whose argument region the
  dispatcher filled. Today they are stated against a frame the model hands them. Every
  per-partial spec that is proved (M-B, none are yet) has to be proved against the
  dispatcher frame instead. **This is the item most likely to be mis-sized in this note**,
  because no spec has been proved at all, so there is no datum for how much of the
  per-partial work is frame-dependent.

**Cost: 2–4 sessions**, GUESSED, and the guess is anchored on the one comparable datum in
the ledger: R-58's five-pin repair (Surface.lean's own repair round) plus the fixture's
construction, both of which were single-session mechanical passes over an existing record.
Multiply by the number of partials whose pre mentions memory the dispatcher writes.

---

## 3. `ir_refines` — the IR-to-shell simulation, i.e. the substance

Assuming §1 option (A) or (C) fixes the formulation, what is left is a simulation between
two concrete Yul programs: the imported runtime block (28 top-level statements, 76 user
functions) and the shell model (`headGuard ++ bindLocals ++ main`, 47 statements at the
fixture).

### What exists to build on

* **The vendored big-step semantics** — `YulSemantics.BigStep.Step`/`Run`,
  `ObjectRun`, `Contract`, `Observation.RunCommitted`. **TRIED**: the whole
  `ImportedIR` witness is built out of these and lands today.
* **`Bridge.RunCommitted`, `Bridge.ObsView`, `ObsEquiv`, `ExternalCalls.WorldLocal`**
  — the equivalence vocabulary, already used by four view-transport lemmas. **TRIED**: they
  elaborate and the fixture exercises them.
* **`memoryguard`/`setimmutable` Step rules** — the D-P15 prerequisite, landed by
  P-VEND (9fe74f9). **TRIED**: `ImportedIR.guardOpen` derives the memoryguard step in the
  open dialect today. This was recorded as a blocker and it is genuinely gone.
* **The imported artifact itself** — 4,221 generated lines, digest-pinned, ten gates.
  **TRIED**: it builds, `irCheck` accepts it, and one run of it is exhibited.
* **`Run.det`** — generic whole-program determinism, `Bridge.lean:191`. **TRIED**: it is
  a one-line application of the vendored `Run.det`. But its hypothesis
  `dialect_deterministic` is a **registered sorry** (Bridge.lean:186, 77 `Op`
  constructors, each needing the `builtinWithExternal` match unfolded). That is ledger item
  **M-D**, costed 2–5 sessions, and it is a prerequisite for any simulation that wants to
  say "the step I matched is the only step there was".
* **mathlib**: nothing. This is not algebra; there is no library here to lean on. The
  honest statement is that mathlib's role in M8 is zero, and any estimate that assumed a
  library shortcut is repeating the R1/R4 error (a named lemma's absence read as the
  fact's absence — here, the reverse).

### What does not exist

* **A relation between the two programs.** Not a proof — a *statement* that means "this IR
  is this assembly". The current stand-in is `irCheck`, and §1 shows what that is worth.
* **Any exhibited run of the IR on a `verifyProof` calldata.** The only
  `RunContractIR` witness in the tree is on **empty calldata**, and it **reverts**
  (`ImportedIR.witness_is_a_revert`). There is no accepted calldata at any model in the
  tree — `gap_runLeg_unexhibited` — so there is at present **no interesting pair of runs
  to simulate**. A proof of `ir_refines` restricted to the exhibited case would be a
  proof about a revert, and would say nothing about the verifier.
* **The per-partial specs it would have to compose with** (M-B, 12 of them, none proved).

### The dependency that is easy to miss

M8's simulation is **downstream of the run leg**, and the run leg is not an M8 item. Until
somebody exhibits a calldata that `decodeCalldata` accepts at a real Surface and a
snapshot the pipeline produces, `RunContractIR` has exactly one witness and it is a
revert. So the honest ordering is: **run leg first, then simulation** — and the run leg is
currently uncosted in the ledger as an M8 prerequisite (it sits inside M-C's 8–14, which
was costed as "Accumulator 12 + Calldata 7 + Qvm 9", not as "an accepted proof fixture").

**Cost of the simulation itself, once the formulation is fixed and the run leg exists:
3–6 sessions**, GUESSED, anchored on the only datum the project has for step-simulation
work: P-BRIDGE closed 3 sorries including MF-4 in one session, and R3's canonicity walk
(50 min) — both of which were walks over an existing relation. A 76-function IR against a
47-statement assembly is a bigger walk with no existing relation, so the anchor is weak
and this is the number in this note I would trust least.

---

## 4. Is `ir_refines` even the right formulation?

**No — not with `irCheck` as its only hypothesis, and the reason is now a theorem rather
than an opinion.** Three specific defects:

1. **The quantifier is vacuous in the wrong direction.** `∀ ir, irCheck ir = true → …`
   ranges over a set that includes programs that do not contain the verifier at all
   (`irCheck_accepts_any_top_level_clean_block`). A hypothesis whose extension includes
   counterexamples cannot be weakened into usefulness by proving more.
2. **It is an implication from a Bool, so strengthening it is invisible.** The R-60 S1
   history is the warning: the check was a free field, then a projection, and in both
   shapes the only thing tying it to the run relation was a human reading. A trusted hop
   stated as `f : YulObject → Bool` will drift again.
3. **It puts the compiler inside the theorem when the compiler cannot be inside the
   theorem.** "The IR refines the shell" is a claim about solc. The project already
   decided, twice, not to verify its toolchain: D-P36a assumes the pairing rather than
   constructing Fp12, and DECISION 1 puts the Yul-optimizer hop in the trusted base
   explicitly. `ir_refines` as written asks for the thing those two decisions declined.

### The statement I think is right

Replace the field with two named things, in the shape D-P36a established:

* **A named assumption**, e.g. `Midfall.Assumptions.solcViaIrPreservesObservables`: for
  the pinned sources, pinned solc digest and pinned settings triple, the imported `ir`
  runtime and the generated assembly are `ObsEquiv` under world-local calls and a
  constant gas oracle. Registry record + axiom probe, exactly like `assumption_dP36a`.
  This is **one line**, and D-P36's third condition ("the assumption be one line and not a
  shield for work not done") is met because there is no work on the other side of it —
  unlike the pairing, where six clauses were already proved.
* **A proved bridge for the part that is ours**: the `verifyProof` arm of the dispatcher
  model runs `headGuard ++ bindLocals ++ main` (§2), so
  `RunShell`-about-the-model implies `RunShell`-about-the-dispatcher-on-`verifyProof`
  calldata. That is a simulation, but a **finite, in-tree** one between two Yul programs
  we both hold, rather than a claim about a compiler we do not model.

Then `lowering_equivalence` transports through the bridge plus the assumption, and the
trusted base gains one honest, named, gate-enforced row instead of carrying a theorem that
is false as stated.

**This is a recommendation, not a decision** — it changes the trusted base, and PLAN §1's
trusted-base list is a human-owned artefact. It is also a **statement-shape change to a
`LoweringCorrect` field**, which the fingerprint and bundle gates will both redden, so it
needs a re-pin in the same commit as the edit (D-P27 precedent).

---

## 5. The first non-guessed total to `lowering_equivalence`

The ledger's standing number is **"16–27 sessions plus M8"**, with M8 explicitly
uncosted (R7: "I decline to number M8 until it is scoped rather than guess a third time").
Here is the numbering, with each line labelled.

| item | sessions | basis |
|---|---|---|
| M-B — the 12 `Partials` specs | 4–6 | extrapolated (unchanged; still no datum — R7's "what would most improve this ledger" #1 is still unaddressed) |
| M-C — Accumulator 12 + Calldata 7 + Qvm/QvmFold 9 | 8–14 | by count (unchanged) |
| M-D — `dialect_deterministic` + transport | 2–5 | **TRIED-adjacent**: the 77-`Op` case split is measured in the source, the 200k-heartbeat wall was hit for real (R7/M-D note) |
| M-E — `lowering_equivalence` transport | 1–2 | its own hint says "provable now"; **GUESSED** |
| Surface over the curve codecs | **0 — DONE this package** | measured: landed, build green |
| **M8-a — restate the hop (option A)** | **1–2** | anchored on D-P36a's actual cost of 1 session (R7) |
| **M8-b — dispatcher model + `shell_unfolds` restatement** | **2–4** | GUESSED, weakly (§2) |
| **M8-c — the run leg as an M8 prerequisite** | **2–4** | GUESSED; note this may overlap M-C, and the overlap is unknown |
| **M8-d — the IR↔shell bridge** | **3–6** | GUESSED, least trusted (§3) |
| **M8 subtotal** | **8–16** | |
| **TOTAL to `lowering_equivalence`** | **25–43 sessions** | |

**Stated plainly, because that is the point of the exercise:**

* The old "16–27 plus M8" was **not** an upper bound. M8 is **8–16 sessions**, so the
  honest total is **25–43**, a revision **upward by roughly 9–16 sessions** — the first
  time this ledger's total has moved up by more than a single item.
* **M8 is large.** It is now the second-biggest item on the path after M-C, and it is
  bigger than M-B and M-D put together. Anyone quoting "16–27" is quoting a number that
  silently assumed M8 ≈ 0.
* **Wall-clock**: at the ledger's observed 1–2 sessions per active hour and its
  availability-dominated history, **9–18 calendar weeks** rather than the 6–11 currently
  recorded. The R7 caveat — "unchanged only if M8 is small" — has resolved in the bad
  direction.
* **The one thing that would collapse the range**: proving a single `Partials` spec. It
  would put a real datum under M-B (4–6, pure extrapolation) and under M8-b's
  "re-derive the pre-conditions against dispatcher memory" (the same unknown, twice).
  That is now ledger note "what would most improve this ledger" #1 **and** #4.
* **What is NOT in any of these numbers**: option (B), verifying the compiler. If a human
  decides the hop must be proved rather than named, M8 stops being estimable and this note
  should be treated as void. Say so before the next package is briefed.

---

## 6. What this package landed, so the above has a footing

* `Midfall/Instances/CurveSurface.lean` — `curveSurface : Surface blsR G₁z G2fold blsGT`
  installing `g1CodecZ` and `g2foldToEip` over the D-P36a pairing; `curveBundle`
  exhibits the four-way headline conjunction at it; `curveBundleCore` adds the deployment
  and the IR pair. `bundle_holds_empty` at the fixture is **kept and still true**.
* `Midfall/Instances/IrCheckBlindness.lean` — the §1 table as a gate
  (`irCheckBlindness_ok`, an `#eval` the KAT gate runs) plus the theorems that make it a
  statement about the definition rather than about five lucky cases.
* `gap_holds_unexhibited` re-pointed (its "no Surface installs the codecs" claim was made
  false by this package, and a stale gap is the failure mode the record itself names), with
  the two new tokens added to **both** registry sides in the same commit:
  `gapHoldsBlockers_ok` in Lean and `HOLDS_GAP_TOKENS` in
  `scripts/check_hypothesis_bundles.py`.
