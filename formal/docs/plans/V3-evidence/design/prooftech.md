<!-- Design memo behind PLAN-V3 (M5 — proof technology). Written by one design pass and kept as delivered, with local paths made repository-relative. Decision numbers inside predate PLAN-V3 §2 (D-P53 onward): follow that table. Where this memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text. -->

# PLAN-V3 design memo: proof technology for the Yul side

Scratch directory (everything below lives here; nothing in the repository was touched):
`docs/plans/V3-evidence/lean/prooftech/`

Please verify the accuracy and completeness of this memo before relying on it; every number is reproducible with the commands listed under measurements.

## 0. Verdict

- **Adopt now:** per-deployment rows on literal slices, a verified demonic `wp` engine, and the lawful executable dialect. All three are typechecked, and they close TraceReturn in 13 lines.
- **Adequate today for:** loop-free blocks. vkLoading executes in 75 ms with a 250 ms kernel check.
- **Not demonstrated:** loops at scale. The tactic executes the whole lagrange slice (5 loops, `batch_invert`, a demonic `staticcall`) in 21.5 s, but the kernel re-check of the proof term did not complete.
- **No evidence either way:** the MSM loops (their helpers are not emitted at HEAD) and the quotient VM (no Yul-level statement exists).
- **Consequence for the plan:** the first ticket is a certificate-cost probe (T3.0) with a measured accept line. No loop-bearing row should be started before it.

## 1. What exists

### 1.1 `run_adequacy`

- `Interp.run_adequacy (hE : E.Lawful) : Run E.toDialect prog st0 V' st' o ↔ ∃ n, Interp.run E n prog st0 = .ok (V', st', o)` is at `vendor/yul-semantics/YulSemantics/Adequacy.lean:772`. It is generic in a lawful `ExecDialect` and the file has no `sorry`.
- `Interp.adequacy` (`:740`) is the form block proofs need: all five code classes, arbitrary `funs`, `V`, `st`.
- `EVM.run_adequacy` (`:786`) is the hypothesis-free instance at the **closed** dialect `EVM.evm`, where `stepOp` returns `none` for `gas`, the call family and `create`/`create2`.
- **It does not cover the open Bridge dialect as shipped.** No `ExecDialect` over `Bridge.Dialect` exists in the tree; `Midfall/Lowering/RunEmitted.lean:33` records that one was attempted and not landed.
- **Built in scratch:** `execOf c g cf gf` with `execOf_lawful` (`P1_Exec.lean`, 171 lines, axioms `[propext, Quot.sound]`). It covers `Bridge.Dialect c g` whenever both oracles are function graphs.
  - `callsOf_graph` shows `callsOf product` is the graph of `honestOf (honestRelations product)`.
  - So `honest_adequacy` gives adequacy at exactly the dialect of conjunct 2 and `BlockProgress`.
- **It cannot cover conjuncts 1 and 3.** `permissive c` is not functional and `g` is arbitrary, so no lawful executable dialect exists there.

### 1.2 Can the fuel interpreter be evaluated on the deployment AST?

Yes, by `#eval`, at the open honest dialect with `product := fun _ => true`.

| Run | Result | Time |
|---|---|---|
| traceReturn, `success = 1` | `halt`, `ret`, 32 bytes | all of E2.lean: 12.97 s including about 9 s of imports |
| traceReturn, `success = 0` | `halt`, `revert`, 4 bytes | same file |
| vkLoading | `normal`, `success = 1`, `activeWords = 471` | same file |
| vkLoading ++ transcriptParser | `normal`, 12 variables, `activeWords = 815` | same file |
| … ++ lagrange (modexp `staticcall` through `honestOf`) | `normal`, 13 variables, `activeWords = 841` | same file |
| whole program `asmOf poseidonPv poseidonM 7 0` (292 statements, 6,816 tokens) | `halt`, `ret`, payload `abiTrue` | 9,798 ms |

- The calldata is synthetic (4,484 bytes, proof region zero), not the fixture; the pairing is mocked true.
- The run shows the AST at HEAD is not stuck on that input. It says nothing about Lean acceptance.
- Kernel evaluation of the interpreter on a symbolic state is a different matter; see section 2.

### 1.3 Does `dialect_deterministic` apply to the prefix?

- No. `dialect_deterministic` (`Midfall/Yul/Bridge.lean:229`) needs `c.Functional` and `g.Functional`. The composition applies `runBody_iff_slices` at `permissive (callsOf product)` with an arbitrary `g`.
- `runs_agree_of_wp` (`WPX.lean`, proved, axioms `[propext, Quot.sound]`) replaces it. If `wp` shows every run of a statement list ends at one named endpoint, any two runs agree, for any `c` and `g`.
- The prefix is call-free and gas-free, so its `wp` evaluation never consults an oracle. This is fix (a) of finding C-3 without generalising `Step.det`.

### 1.4 What TraceReturn.lean's lemmas cover

`Midfall/LoweringV2/Blocks/TraceReturn.lean` is 1,053 lines. Its S1 to S6 lemmas are **site-specific inversions**:

- S1 `tr_slice`: the slice as a statement list, via stuck-site definitions for a symbolic constant table.
- S2 `tr_iszero_val` / `tr_iszero_zero`: only the expression `iszero(success)`.
- S3 `tr_guard_skip`: only that guard.
- S4 `tr_mstore_step` / `tr_mstore_o`: only `mstore(trRetExpr, 1)`.
- S5 `tr_ret_step` / `tr_ret_o` and `readBytes_storeWord_one`.
- S6 `fail_lookup` and `tr_fail_*`: the `fail` helper.

Each new statement shape needs a new 20 to 40 line lemma. The generic `wp_sound` subsumes S2 to S6. S1 disappears per deployment (section 5). Only `readBytes_storeWord_one` was reused by the prototype.

## 2. Recommended proof technology, with the prototype

### 2.1 The engine (typechecked)

`WP.lean`, 419 lines, no `sorry`, `wp_sound` depends on `[propext]` only.

- Five mutually recursive, fuel-indexed predicate transformers: `wpE`, `wpA`, `wpS`, `wpSS`, `wpL`. They are generic in the `Dialect`.
- Two parameters:
  - `B : BT D`, the built-in transformer. `BSound` says `B op args st Q` implies `Q r` for every result the relation admits.
  - `C : CT D`, a call-summary table. `CSound` says each summary is a valid contract of the body it replaces.
- `wp 0 = False`, and every stuck configuration is `False`. A proof of `wp n … Q` therefore says: for every oracle answer the code terminates within the fuel, is never stuck, and ends in `Q`.

Exact statement:

```lean
theorem wp_sound (hB : BSound D B) (hC : CSound D C) : ∀ n : Nat,
    (∀ funs V st e Q, wpE D B C n funs V st e Q → ∀ r, EvalExpr D funs V st e r → Q r) ∧
    (∀ funs V st es Q, wpA D B C n funs V st es Q → ∀ r, EvalArgs D funs V st es r → Q r) ∧
    (∀ funs V st s Q, wpS D B C n funs V st s Q →
        ∀ V' st' o, ExecStmt D funs V st s V' st' o → Q V' st' o) ∧
    (∀ funs V st ss Q, wpSS D B C n funs V st ss Q →
        ∀ V' st' o, ExecStmts D funs V st ss V' st' o → Q V' st' o) ∧
    (∀ funs V st c post body Q, wpL D B C n funs V st c post body Q →
        ∀ V' st' o, ExecLoop D funs V st c post body V' st' o → Q V' st' o)
```

Also proved there: the cut rule `allRuns_cons_wp`. It executes one statement and leaves a **semantic** continuation, so a leaf can keep stepping or apply a previously proved lemma about the rest.

Bridge instantiation (`WPBridge.lean`, 72 lines):

- `Bopen c g` quantifies over every response at `staticcall` and every word at `gas()`. It refuses the other call and create ops. A local op is one `stepOp` evaluation.
- `Bopen_sound c g : BSound (Bridge.Dialect c g) (Bopen c g)` holds for **any** `c` and `g`; axioms `[propext, Quot.sound]`.
- `Bfun c g cf gf` (`WPX.lean`) is the functional transformer for the honest dialect. `Bfun_sound` and `Bfun_live` are proved.

### 2.2 The driver (typechecked)

`WPTac.lean`, 229 lines. The tactic `wp_run` does definitional symbolic execution:

- It head-normalises the goal with the **kernel** reducer (`Lean.Kernel.whnf`).
- It splits `∧` and introduces `→` and `∀`.
- It prunes a branch whose guard is concrete by kernel evaluation of a hand-built `decide`.
- It stops at `Hold P` leaves.
- At each sequence point (`Stop`, placed after every statement and loop iteration) it normalises the state. Concrete values become literals; symbolic values and states become `let`-bound locals.

Four findings from building it, each measured:

1. **`simp`-driven evaluation of a continuation-passing `wp` fails.** `simp only [wpSS, wpS, wpE, wpA]` on the 3-statement TraceReturn slice hits `maximum recursion depth`, because `simp` unfolds continuations under binders before their arguments are known.
2. **`Meta.whnf` is about 100 times slower than the kernel reducer here.** `mstore(0, shl(224, sel))` took 384 ms against 4 ms.
3. **The kernel ignores `@[irreducible]`.** The stop markers `Hold` and `Stop` must be structures.
4. **Evaluating a guard that depends on symbolic memory is expensive before it gets stuck.** The driver therefore evaluates only words whose free variables are oracle parameters.

### 2.3 Results on real code

| Slice | Statement proved | Tactic lines | `wp_run` | Kernel check | Status |
|---|---|---|---|---|---|
| traceReturn (25 tokens) | every run halts; `s ≠ 0` gives `ret abiTrue`, `s = 0` gives a revert; any `c`, any `g` | 13 | 26.8 ms | 11.5 ms | proved, axioms `[propext, Classical.choice, Quot.sound]` |
| vkLoading (225 tokens) | every run reverts, or exits normal with `success = 1` | 12 | 74.7 ms | 250 ms (fuel 60) | 3 of 4 leaves closed; the normal-exit leaf is `sorry` |
| lagrange, first 4 statements (one 6-iteration loop, symbolic memory) | the run is normal with 7 variables | 3 | 115 ms | 1.85 s (fuel 40) | proved, axioms `[propext, Quot.sound]` |
| same, fuel 400 | same | 3 | 129 ms | 33 s | proved |
| lagrange, whole slice (503 tokens) | reverts or exits normal | 3 | 21.5 s, 42 leaves | not completed | see below |

Comparison with the hand proof: `tr_all` covers both conjuncts of `BlockSound` at TraceReturn in 13 lines, against 1,053 lines in `TraceReturn.lean`. It is stated on the literal slice and scope; the link to `sliceOf poseidonPv poseidonM .traceReturn` is the `native_decide` pin of section 5.

The vkLoading residue is readable and is exactly the block's header checks, for example `loadWord (copyInto st.memory 10496 1 4576 (st.env.extCodeOf vk)) 10528 = 1`. Closing it needs the word and memory lemmas of section 3; my first `simp` attempt did not fire because the literal `1#256` did not match the lemma's `(1 : U256)`.

### 2.4 Where it stops

- **Whole lagrange slice.** `wp_run` finished (21.5 s, 42 leaves, all `Hold`). The declaration then failed with `(kernel) deep recursion detected` at the default depth. With `maxRecDepth 100000` the check ran past 300 s and I killed it. That run broke the 2-minute rule and produced no result.
- **Kernel cost is super-linear in the fuel literal.** The same 30 steps cost 1.85 s at fuel 40 and 33 s at fuel 400.
- **Sequence-point normalisation is not the cause.** With `let`-naming off, and with literal replacement off as well, the fuel-400 check took 33.9 s and 33.3 s.
- **Loops cost more per step than straight-line code at the same fuel.** About 62 ms per step on the loop against about 1.2 ms on TraceReturn. I do not know why.
- **Failure forks multiply work.** The 42 leaves come from the canonicity guards in `batch_invert` and the `staticcall` result; each failing path re-runs the rest of the slice. Without sequence-point normalisation the run hit the 400,000-heartbeat limit after 3,125 kernel steps (34.5 s) with 27 leaves reached.

This matches the project's own recorded trap (PLAN-V2 section 4.11: fuel per nesting level, never per list element).

### 2.5 The options weighed

| Option | Loops | `staticcall` | keccak | Memory read-over-write | Status |
|---|---|---|---|---|---|
| (i) verified `wp` over the AST | unrolls when bounds are concrete, which they are at this deployment; symbolic bounds need a loop hatch around `ExecLoopAll.countdown_or_halt` (`Yul/Contracts.lean`), not built | `Bopen` forks over every permitted response; `Bfun` evaluates `honestOf` | stays an uninterpreted term `keccakOf (readBytes …)`, so execution is hash-agnostic | not resolved by execution; left as `loadWord (storeWord …)` terms for a `simp` set | built and proved; certificate cost on loops unresolved |
| (ii) tactic layer over `Step` inversion lemmas | one lemma per loop shape | one lemma per call site | as (i) | as (i) | this is what `TraceReturn.lean` does by hand; `wp_sound` subsumes the lemmas |
| (iii) reflective executor on a reified symbolic state | unrolls inside the function | returns a list of paths | a term constructor | a finite map resolves reads at concrete addresses by computation | not built; my estimate is 1,500 to 3,000 lines once; needs `native_decide` or kernel `decide` per block |
| (iv) word-level reference model | n/a | n/a | n/a | n/a | not a competitor: it is the interface. With `let`-naming the leaf context of (i) already is a straight-line word program |

Recommendation:

1. Use (i) as the engine and (iv) as the interface between Yul and algebra. Each block gets a small word-level Lean function, a mechanical theorem "Yul block equals the function", and an algebra theorem that never mentions Yul.
2. Decide the certificate strategy by measurement in T3.0. Three candidates:
   - **C1, rule application.** Derive about 25 fuel-free rule lemmas from the cases of `wp_sound`; the tactic applies them with small closed side goals and names values by `∀`-introduction with equation hypotheses. Expected to be fuel-independent; not measured.
   - **C2, less fuel.** Redefine `wp` to spend fuel only at loop iterations and calls, and chunk every declaration with the cut rule. Basis: fuel 40 costs 1.85 s where fuel 400 costs 33 s.
   - **C3, option (iii).** Highest up-front cost and a larger trusted base. Fallback only.
3. Honest runs and executable exhibits go through `execOf` and the vendored interpreter.

## 3. Memory and arithmetic layers

### 3.1 What the tree has (grep at HEAD)

- `readBytes_storeWord_one`: `LoweringV2/Blocks/TraceReturn.lean:373`, and a v1 copy in `Lowering/Partials.lean`.
- `readBytes_storeWord_four`: `Yul/Bridge.lean:1252`.
- `readBytes_congr`, `readBytes_avoids_window`: `Lowering/FrameWalk.lean`.
- `loadWord_zero`: `Instances/RunShellInversion.lean`.
- `hashOfBytes_readBytes`: `Yul/Bridge.lean:451`.
- Vendored: `readBytes_copyInto` (`ObjectRun.lean:75`), `readBytes_storeWord` at address 0 (`FibExample.lean:181`).
- `qvmToFr_add`, `qvmToFr_mul`, `qvmToFr_neg`, `qvmToFr_injOn`: `Lowering/Qvm.lean:143-169`, at the `Nat` level.
- `frOfWord?`: `LoweringV2/Shared.lean`.
- Calldata: `vk_ok_calldataload` (`Blocks/VkLoading.lean:528`), `calldataload_val` (`Yul/ShellModel.lean:584`). `Lowering/Calldata.lean` has 3 `sorry` (`calldata_roundtrip`, `calldata_canonical`, `repack_spec_of_decodeRust`).

### 3.2 What is missing (zero grep hits each)

- Any lemma relating `loadWord` to `storeWord`, `copyInto` or `copyReturn`.
- Any theorem mentioning `b2w`.
- Any theorem relating the `stepOp` `mulmod`/`addmod` lambdas to `ZMod`.
- Any theorem whose name contains `wordFrom`, so there is no byte-level bridge from `calldataload` to `decodeCalldata`.
- A `touchMemory` projection `simp` set.

### 3.3 Proposed statements (typecheck in `WPX.lean`, bodies `sorry`)

```lean
theorem loadWord_storeWord (mem : Nat → UInt8) (p q : Nat) (v : U256) :
    loadWord (storeWord mem p v) q =
      if q = p then v else if q + 32 ≤ p ∨ p + 32 ≤ q then loadWord mem q
      else loadWord (storeWord mem p v) q

theorem mulmod_toFr (a b : U256) :
    Midfall.Lowering.qvmToFr
        (BitVec.ofNat 256 ((a.toNat * b.toNat) % Midfall.Generator.qvmFrModulus)).toNat =
      Midfall.Lowering.qvmToFr a.toNat * Midfall.Lowering.qvmToFr b.toNat
```

Proved in scratch: `b2w_eq_zero_iff`, `one_and_b2w`, `b2w_and_b2w`.

Design point: `stepOp` uses inline lambdas, so residues show `(fun a b n => if n = 0 then 0 else …) x y r`. The word layer should name these (`wMulmod`, `wAddmod`, …) so the algebra lemmas have a head symbol to match.

## 4. The quotient VM

Facts:

- The numerator text at the deployment has 6,572 tokens (E4.lean): 2 `switch`, 13 `case`, 11 `for`, 2 functions (`q_program_fail`, `q_pow5`), 164 `mulmod`, 145 `addmod`, 183 `mload`, 62 `mstore`, 14 `if`, 0 `staticcall`, 0 `calldataload`. Only 122 tokens are emitted as AST at HEAD.
- `Lowering/Qvm.lean` (3,545 lines), `Lowering/QvmFold.lean` and `Generator/Quotient/VmReference.lean` are entirely about the Lean reference VM against expression semantics and the bytecode builder. A grep for `ExecStmts|EvmState|Bridge\.|YulSemantics|StmtsContract` gives 0 hits in `Qvm.lean` and `VmReference.lean`, and 1 in `QvmFold.lean`.
- So **the Yul interpreter refinement is not stated anywhere.**

Sorries:

| Location | Lemma | On the per-deployment path? |
|---|---|---|
| `QvmFold.lean:376` | `quotientFold_matches_linearization` | Yes: the algebraic link to `computeLinearizationCommitment` |
| `QvmFold.lean:338` | `identityCorrespondence_of_bridge` | Yes, and it must be restated: the same file proves `bridgeCounterexample_hypotheses_hold` and `bridgeCounterexample_conclusion_fails` |
| `Qvm.lean:631` | `qvm_compile_correct_identity` | Only for route B below, or the generic theorem |
| `Qvm.lean:698`, `:713` | `qvm_compile_correct_certifier`, `qvm_compile_correct_program` | Builder correctness: generic theorem only |
| `Qvm.lean:768` | `qvm_validated_noBoundsFault` | Generic theorem only |
| `Qvm.lean:995` | `builder_segments_total` | Generic theorem only |
| `QvmFold.lean:434` | `qvm_compile_correct_stream` | Generic theorem only |

Two routes; the choice needs the AST, so it waits for G1.3:

- **Route A, direct.** Symbolically execute the emitted numerator to a word-level straight-line program, then discharge "program equals `evalExprρ` of the plan's identities" by a reflective structural check (kernel or `native_decide` in `Instances/`). The valuation layer `evalExprρ` and `memOfρ` already exists (`Qvm.lean:189-214`). Counts suggest most of the region is straight-line arithmetic.
- **Route B, generic interpreter refinement.** Prove once, generically in the bytecode, that the Yul interpreter loop refines `evalQuotientIdentity` (`VmReference.lean:902`). Then discharge the deployment's bytecode by evaluating the reference VM at a symbolic valuation, or by closing `qvm_compile_correct_identity`.

I have no evidence that either route works. The deciding experiment is T3.10.

## 5. Per-deployment or generic-in-R rows

Recommendation: **per-deployment rows on literal slices.**

Evidence:

- `Lits.lean` (generated by `GenLits.lean`) holds the helpers and four slices as constructor-form literals, 1,249 lines.
- Each is pinned by `YulSemantics.SyntaxEq.stmtsBeq_eq _ _ (by native_decide)`. The file checks in 13.5 s including imports.
- Addresses are then literals (`4096`, `10496`, `26560`, …). Trap S1 and every `vkPins`-style constant pin disappear from block proofs.
- The printed-Yul route (`yul%`) also round-trips, but leaves `mkCall "iszero" …` unreduced; and the transcript parser uses `end` as an identifier, which is a Lean keyword. Use the `repr` form.

Trade-offs:

- The theorem holds for one deployment. A new deployment re-runs every "Yul equals model" proof.
- Each pin adds a `native_decide` axiom. PLAN-V2 section 6 already allows the recorded compiler-trust axioms; whether kernel `decide` can replace them is not measured.
- The literal file must be regenerated after every WP-G1 emitter change. The pins catch drift.

How the generic theorem stays reachable:

- The engine, `Bopen`, the cut rules and the word layer are generic.
- State each block's word-level function as a function of the layout, even though the Yul link is proved per deployment. The algebra half ("model equals verifier stage") is then generic in `R` and reusable.
- The existing generic `BlockRow` statements in `Blocks.lean` stay as WP-X4 targets. No frozen file changes.

## 6. Guidance for the implementer

- Never `simp` a continuation-passing `wp` over a whole slice.
- Never use `@[irreducible]` to stop reduction; use a structure.
- Never evaluate a guard that mentions symbolic memory or calldata.
- Keep the fuel literal as small as the slice allows, and never raise `maxRecDepth` to get a large proof term through: chunk with the cut rule instead.
- Build proof terms by hand in the driver (`mkApp`), not with `mkAppOptM` on large targets; a Meta-level defeq check on a wp term timed out.
- State block boundaries with a concrete environment shape, for example `[("success", s), ("r", rv), ("vk", vk)]`. `wp_run` also accepts a symbolic tail.
- `leave` is a token once `YulSemantics.Syntax` is imported: write `| «leave» =>` in `cases`.
- Leaves come out in depth-first order with the guard-skipped path first, so the normal exit is leaf 1.
- The poisoned continuation should be discharged by a cut lemma, not by re-execution. It depends on the soundness design's exit-shape scan, which is outside this area.
