# P-BYTES - the byte mathematics that actually blocks the four `decodeAcc_*` holes.

Status: READY. P-MC-ACC proved 8 of 12 Accumulator holes and **re-measured the blocker**: the
four `decodeAcc_*` round trips are NOT blocked on the `-s` elaboration (that note predates
the file ever compiling). They are blocked on **missing byte-level mathematics that exists
nowhere in the tree**.

## Where to work: NOT `Lowering/Accumulator.lean`

Build the lemmas in **`Exec/Accumulator.lean` or `Assumptions/Codec.lean`**, where the byte
primitives live. The four round trips then become short. P-MC-ACC's own recommendation.

## The missing lemmas (named by the package that found the gap)

| lemma | what it must say |
|---|---|
| `natToBytesBE` 16-48-16-48 frame lemma | a reconstructed `(hi, lo)` pair equals `codec.toEip` **byte for byte** — the core obstacle |
| `loadAccPoint_flag0` / `loadAccPoint_flag1` | the flag-bit cases of the accumulator point loader |
| `decodeAccCoord_inj` | coordinate decoding is injective on valid frames |
| `encodeAccCoordWords_packingOk` | the packing path produces what the layout claims |
| `biFromLimbs_biToLimbs` | the big-int limb round trip |

**Re-derive these yourself from the four open goals** rather than trusting this list —
P-MC-ACC extracted it while running out of room, and this project has measured **twenty-two**
cases where a recorded premise or blocker did not hold.

## Then close the four

`decodeAcc_injective` (:141), `decodeAcc_encode` (:249), `decodeAcc_encode_noNeg` (:275),
`decodeAcc_encode_pointPair` (:339). **Read each against sketch section F first** —
`decodeAcc_encode_pointPair` already carries an `hfb : fb.size = 0` strengthening the sketch
lacks (R-26 third defect, recorded), and `decodeAcc_encode`'s `List.Sorted` → `namesAscending`
substitution is in the dead-identifier table. **Do not drop sketched hypotheses you find
unused** — P-MC-ACC kept `hn` in `eval_addMsm` for exactly this reason and annotated it.

## Second deliverable: assess the Mathlib built-surface problem

P-MC-ACC found that **Mathlib's `Additive`/`Multiplicative` transport lemmas are not in this
project's built surface** — the lakefile builds only Mathlib modules the tree already imports.
`#check` reports unknown for `Additive.ofMul_mul`, `toMul_add`, `ofMul_zpow`, `nsmul_succ`,
`Fintype.card_univ`, `Subgroup.coe_inj`, `ZSubgroup.mem_zpowers_iff`. **Seven `gsmul` lemmas
had to be proved by hand**, and the mathematics took ~20 min against ~70 min of transport.

**Assess, do not unilaterally change:**
1. Would adding the relevant Mathlib modules to the lakefile build be net-positive?
2. **Measure the cost first** — cold `lake build` is currently 16.86 GiB tree / 4.28 GiB
   largest with 10 workers, and D-P31 exists because this host has OOM'd twice. Report the
   added build-time and peak-RSS delta before recommending it.
3. If the answer is no, **propose a small in-tree transport module** (e.g.
   `Midfall/Common/GSMul.lean`) collecting the hand-proved lemmas so the next algebra-heavy
   package does not repeat the work. **This is probably the right answer regardless** — the
   seven lemmas already exist in `Accumulator.lean` and belong somewhere reusable.

## Constraints

* **Never weaken a statement to make it provable.** Restore from the sketch if the
  implementation drifted; report if a restored form is unprovable.
* **D-P23 both halves as theorems.** P-MC-ACC could not land them for four claims and said so
  rather than leaving drafts as comments — same standard here. Falsification-deletion gap
  measured **twenty-one** times.
* **`Instances/` confinement (D-P17)**: a `VerifierEnv` exhibit cannot live in a
  theorem-bearing file. If a witness needs one, the statement must be re-cut portable.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`; three-way agreement; budget a full gate run.
* **Elaborator walls, newest first**: positional `_` synthesis in a deep `refine` times out at
  200k heartbeats where `apply` with separate premises is instant; a section variable is
  auto-included only when the STATEMENT mentions it, so an exhibit not naming `P` cannot use
  `P.g₁` and the error reads as an unknown identifier; `decide` reduces exponentiation at
  255-bit `r` but not inversion; pre-prove cardinalities as `have`s rather than `rw [ZMod.card]`.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Full build peaked 7.27 GiB tree / 2.17 GiB largest; TIGHT on the tree total is normal.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5214 jobs**, 124 modules; `checks.sh` green: **44 tracked sorries**, 1316 KATs
across 93 files, 235 fragments, 30 pins, Statements hash OK.

Read first: `Midfall/Lowering/Accumulator.lean` (the four open holes and the seven hand-proved
transport lemmas sitting in section 8), `Midfall/Exec/Accumulator.lean`,
`Midfall/Assumptions/Codec.lean`, `Midfall/Assumptions/Eip2537.lean` (the modexp machinery and
`modPow_eq`/`modPow_inv`), sketch section F from line 904, `docs/plans/P-SE-statements.md`,
`docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 44**.
- The byte lemmas landed where they are reusable, not inline at their first use.
- **Required finding**: (a) how many of the four `decodeAcc_*` closed, and whether the
  byte-mathematics diagnosis was itself correct; (b) the measured cost of widening the
  Mathlib built surface, with a recommendation.