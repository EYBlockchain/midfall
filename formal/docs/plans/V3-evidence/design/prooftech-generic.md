# Proof technology for rows proved at every render (D-P71): GEN.0 skeleton and the loop rule

Written against `f8f461e` (code); HEAD moved to `cf00592` during the session, a docs-only commit
(`git diff --stat f8f461e cf00592 -- formal/Midfall formal/vendor …/lean/prooftech` is empty).
Please verify the numbers before relying on them; every one is reproducible with `out/lc.sh`.

## 1. What was built

| File | Lines | Typechecks | Sorries |
|---|---|---|---|
| `gen/VKP.lean` | 426 | yes, 14 s wall (about 11 s imports) | 1: `wpSS_exists_C` (statement only) |
| `gen/LoopRule.lean` | 522 | yes, 14 s wall | 0 |

`VKP.lean`
- the list of constants `vkBody` reads: 17 names at 20 sites (15 must be bound, `vk` and `success`
  must not be);
- `vkBodyV`, `vkBody_eq_vkBodyV` (proved, `[propext]`);
- the `fail` summary: `failT`, `Cfail`, `Cfail_sound` (proved), `Cfail_live` (proved),
  `allRuns_of_wp_fail`;
- `vk_all_param`: PROVED, axioms `[propext, Quot.sound]`, no side condition. The normal-exit leaf
  that is a `sorry` in the literal `vk_all` is closed here (`IsBit`, 3 lemmas);
- `vk_all_param_mem`: the same plus the memory fact, PROVED by `rfl` at the leaf;
- `CLive`, `CLive_of_none`, `wpSS_exists_C` (sorry): the existence-half statement.

`LoopRule.lean`
- `IterAll`, `loop_inv_aux`, `allRuns_loop`: the rule on the big-step judgment, by induction on
  the derivation; axioms `[propext]`;
- `wpIter`, `iterAll_of_wp`, `allRuns_loop_wp`, `allRuns_for_wp`, `allRuns_for_cons_wp`,
  `allRuns_for_cons_wp_count`: the engine forms; axioms `[propext]`;
- witness `sumLoop_all` (bound `n : Nat`, every `n < 2^256`, no `native_decide`), axioms
  `[propext, Classical.choice, Quot.sound]`;
- falsifiers `loopRuleNoPres_false`, `sumLoop_all_needs_bound`; axioms `[propext, Quot.sound]`;
- the table of the verifier's loops (comment, §5).

## 2. MEASURED

Machine shared with other agents' `lean` processes; times are single runs unless a range is given.

| Variant | File | Terminates < 60 s | Leaves | `wp_run` | Kernel | First stuck term |
|---|---|---|---|---|---|---|
| literal `vk_all` (baseline) | `VK.lean` | yes | 4 (1 sorry) | 106 ms | 365 ms | — |
| P1: `vkBody consts …` as stated | `out/probes/P1.lean` | yes | 1, stuck | under 50 ms (tactic total 6 ms) | 16 ms with the leaf `sorry` | `Expr.rec … (vkSite "EXPECTED_VK_CODEHASH_WORD" consts)` |
| P2: rewrite, then `wp_run` | `VKP.lean` `vk_all_param` | yes | 7 = 4 + 3 scope leaves, all closed | 86–100 ms (5 runs) | 225–243 ms | — |
| P2 + memory conjuncts | `VKP.lean` `vk_all_param_mem` | yes | 7, all closed | 425–455 ms (4 runs) | 224–256 ms | — |
| P2 without the `VK_MPTR` hypothesis (card falsifier) | `out/probes/PF.lean` | `wp_run` yes | 3 | under 50 ms | not checked | `Expr.rec … (vkSite "VK_MPTR" consts)` |
| P2 with `Cnone` (no summary) | `out/probes/PX.lean` | `wp_run` yes | 4: 1 exit + 3 stuck | 84–105 ms (3 runs) | see below | `Option.rec … (lookupFun … "fail")` |
| P2 with a symbolic environment tail `:: Vt` | `out/probes/PT.lean` | yes | 7 | 155–194 ms | 382 ms, leaves closed by an axiom | — |

- **Verdict so far: P2.** P1 cannot work: the kernel reducer does not see hypotheses, so the first
  constant site stops it. P2 meets GEN.0's thresholds (kernel ≤ 2 s, elaboration ≤ 10 s) by a wide
  margin and the block is closed, not only executed. Lines: `vk_all_param` is 14 tactic lines.
- Why `vk_all_param_mem`'s `wp_run` is 4 to 5 times slower than `vk_all_param`'s I do not know.
- **A stuck leaf does not kernel-check.** `PF.lean` and `PX.lean` hit the 60 s alarm twice each
  when their leaves were closed by `sorry` and by an axiom. `out/probes/PX2.lean` is `PX.lean`
  with `set_option debug.skipKernelTC true`: 12 s. `P1.lean` (one stuck leaf, before any sequence
  point) does check, in 16 ms. I did not isolate the cause.
- `LoopRule.lean`: `sumLoop_all` tactic total 440 ms, of which `rintro` 333–355 ms and each of the
  three `wp_run` under 50 ms; kernel 14 ms.
- The alarm recipe in the brief and in GEN.0's Guidance (`perl -e 'alarm shift; exec @ARGV' N
  lake env lean …`) kills `lake` and leaves `lean` running: five orphans after five timeouts.
  `out/lc.sh` forks, puts the child in its own process group and kills the group.

## 3. READ

- `Inline.Consts = List (String × Nat)` (`Lowering/InlineConstants.lean:256`); `vkSite`
  (`Blocks/VkLoading.lean:94`) emits `Expr.lit (.number v)`, `v : Nat`. The card's `U256` is wrong.
- `CSound` (`WP.lean:197`) quantifies over every `funs` and speaks about the BODY run after the
  arguments are evaluated. `vk_fail_reverts` (`VkLoading.lean:449`) is about the call STATEMENT; the
  body fact is `tr_fail_body` (`Blocks/TraceReturn.lean:652`), and `Cfail_sound` uses that.
- `vkPins` and `vkProgressPins` (`LoweringV2/Statements.lean:146-166`) supply 4 of the 15 lookups:
  `VK_MPTR`, `EXPECTED_VK_PAYLOAD_LENGTH`, `EXPECTED_VK_LENGTH`, `EXPECTED_VK_CODEHASH_WORD`.
  `consts_vk_none` (`VkLoading.lean:170`) and `consts_succ_none` (`TraceReturn.lean:123`) supply
  the two `none` facts for every `R`.
- No builtin this block uses can halt or is partial on a well-formed argument list: `extcodecopy`,
  `mload`, `calldataload`, `calldatasize`, `add`, `eq`, `and`, `iszero`, `extcodesize`,
  `extcodehash` (`vendor/…/Dialect/EVMExec.lean:714-856`). So execution needs no bound.
- `ExecLoopAll.countdown_or_halt` (`Yul/Contracts.lean:298`) inducts on a count and needs
  `zero : Inv 0 → guard = 0`. `wpL` (`WP.lean:167`) unrolls by fuel.

## 4. Side conditions

`vk_all_param` and `vk_all_param_mem` need NONE. The memory residue is, exactly,
`st'.memory = copyInto st.memory (BitVec.ofNat 256 mVk).toNat 1 (BitVec.ofNat 256 payLen).toNat
(st.env.extCodeOf vk)`, with `st'.env = st.env` and `st'.halted = st.halted`.

INFERRED from that residue: what a row needs to turn it into `Inv .vk`'s clauses, none of which is
a hypothesis of `vk_all_param` and none of which I added:

1. `mVk < 2^256` and `payLen < 2^256`, to drop the two `ofNat … toNat`.
2. `vkLen < 2^256` and `(st.env.extCodeOf vk).length < 2^256`, to read the first guard as a length
   equality; and `vkLen = payLen + 1`, so that the copy does not read past the code.
3. The six header slots lie inside `[mVk, mVk + payLen - 32]` and are below `2^256`, so the six
   `mload`s read the payload.
4. `n, k, w, o, l, b, q < 2^256`, so that a passed check is an equality of naturals.
5. `cPL, cNI < 2^256` and `cI + 32 * n < 2^256`, for the three calldata checks.
6. Memory outside the window is unchanged with no condition; `activeWords` does change.

## 5. The `wpSS_exists` conflict (GEN.1 step 4)

- Logically no summary is needed: with `Cnone` each `fail` site is a stuck `lookupFun` under a
  hypothesis `guard ≠ 0`, and the progress pins refute each guard.
- In practice it does not go through as written. `wp_run` cannot prune those branches (the guards
  are symbolic, and `decideWordEq` evaluates concrete words only), so they surface as stuck
  leaves, and a declaration with such a leaf did not kernel-check (section 2).
- So the existence half needs the summary too. Typechecked: `CLive` (the dual of `CSound`),
  `wpSS_exists_C` (sorry; `wpSS_exists` is its `CLive_of_none` instance), `Cfail_live` (proved).
  With `Cfail` in place the three sites are `Hold` leaves closed by `absurd` on the guard.
- The alternative is a `wp_run` option that closes a `cv ≠ 0 → …` branch from a supplied
  refutation before descending into it. Not built.
- INFERRED: `BLive (Bopen c g)` fails for an arbitrary `c` (the `staticcall` arm is a `∀` over
  responses, true when there are none), so the existence half runs at `Bfun`, not `Bopen`.
- Every later block calls a helper on its success path, where no guard can be refuted, so live
  summaries are needed there in any case.

## 6. The loop rule

- The rule needs no variant and no bound: `AllRuns` ranges over finite derivations, so the proof
  is by induction on the derivation. A decreasing measure is needed only for the existence half;
  that rule is not written here (`ExecLoop.countdown`, `vendor/…/Contract.lean:176`, is the
  normal-arm starting point).
- `allRuns_for_cons_wp_count` has the invariant indexed by `Nat`, existentially at each head.
- Applying it: `refine allRuns_for_cons_wp … (n := 20) Inv ?_ ?_`; `wp_run` on `init`; then
  `rintro Vi sti ⟨…, rfl, rfl⟩` and `wp_run` on one iteration. Leaves: the exit (a `Hold
  (AllRuns … rest Q)`, continued with `allRuns_of_wp`), and the invariant at the next head.
- The invariant must pin the environment's SPINE (`V = [("i", _), ("acc", _)]`), otherwise
  `wp_run` cannot read a variable.

## 7. Traps

1. Never close a raw `wp` goal with `sorry` or `exact`: the elaborator's `whnf` ran out of
   heartbeats on `refine allRuns_of_wp_fail 60 ?_; sorry`. Run `wp_run` first.
2. `trace_state` on a stuck leaf took 46 s. Print the head and the short arguments instead
   (`stuck_head` in `out/probes/P1.lean`).
3. `nomatch e, x` parses as two discriminants; parenthesise `(nomatch e)` inside `⟨…⟩`.
4. Building a `Step` derivation by hand: give `(D := Bridge.Dialect c g)` on every constructor
   used with a named argument, and state each builtin fact as `show stepOp op _ _ = some _; rfl`.
5. `by decide` on a `VEnv` equation fails with "free variables" (`c`, `g` hide in the type):
   restate it at `List (String × U256)` first.
6. A `Nat` bound hypothesis is consumed by `rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h`;
   `simp [Nat.mod_eq_of_lt h]` does not fire because `2 ^ 256` has been normalised to a numeral.
7. `wpLets false` was set for every run, as in `VK.lean`; the default was not tried.
8. With a symbolic environment tail the normal-exit leaf keeps an unreduced `restore`; closing it
   was not attempted.

## 8. For whoever continues

- GEN.1 step 1 cannot be done from `vkPins`, `vkProgressPins` and `vk_slice` alone: eleven lookup
  hypotheses of `vk_all_param` remain (`ERR_VK_MISMATCH`, the six header slots, `PROOF_LEN_CPTR`,
  `NUM_INSTANCE_CPTR`, `INSTANCE_CPTR`, `ERR_BAD_CALLDATA_SHAPE`). They need a constants-coherence
  clause (card OBJ.4), which GEN.1's `after` list does not name.
- Another session has uncommitted `soundness/GeneratorRows.lean` with loop children
  (`lag_sq_loop`, …) and an edited `check.sh`; I did not read them.
- `check.sh`: append `VKP LoopRule` to the `prooftech` line, after `WPX` (`VKP` imports it).
