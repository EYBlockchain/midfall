# REVIEW-V3 — independent review of the formalisation and of PLAN-V2 (2026-11-17)

**What this is.** The consolidated findings of an external review of `formal/` on branch
`formal/baseline`. It is the evidence base for `docs/plans/PLAN-V3.md`. It is **not** a decision
record: nothing here changes the frozen surface, the scope or the queue. Every repair that touches a
frozen file is listed in PLAN-V3 §2 as PROPOSED and needs a human sign-off (EXECUTION-V2 W2).

**Reviewed commits.** The review started at `6481731` and five commits landed while it ran (R.1,
then called "F.1", and the D-P49/D-P50 sign-offs). Every Lean check was re-run at **`f2fe99b`**.
Nine more commits landed while this document and PLAN-V3 were written, up to `5329c3f` (the F.2
deployment table, the R.2 emission inventory, and the sign-off of D-P45–D-P59). They change only
`docs/`, so every Lean fact below also holds there, and R.2's measurements agree with RV-12.
Two further commits (`4e18c65`: F.1) then proved `slices_seq_sound` and `slices_seq_progress`,
which this review had found true and derivable (§3), taking the headline cone from 11 to 9 and
shifting `Blocks.lean` line numbers after line 286 by about +209.
**Two parts of this document describe the state before those sign-offs**: the "recorded by the
project?" column of §1 and the table of pending decisions under RV-39. PLAN-V3 §2.1 is the
up-to-date account of how each signed decision relates to these findings. Line numbers are those of `f2fe99b` for the files the lead
checked; a few citations under `Midfall/Instances/` and `docs/` taken from reviewer reports are
pinned to `6481731` and say so in the full dump.

**Method.** Ten reviewers, one per dimension (headline statement, program and `Valid`, Yul
semantics, block contracts, verifier fidelity, generator fidelity, axioms, deployment instance,
plan, tooling). Each report was then attacked by an independent skeptic who had to re-derive every
medium-or-worse finding from the current source. The lead then re-checked the most serious findings
against the source and in Lean. 115 reviewer findings and 37 skeptic additions were produced; they
are consolidated below into 46 findings (RV-01 … RV-46).

**Evidence classes.** Each finding names how it was established.

| class | meaning |
|---|---|
| **L** | Machine-checked. The fact is a `#guard`, a proved theorem or a pinned `#print axioms` in `docs/plans/V3-evidence/ReviewProbes.lean`, which elaborates without error at `f2fe99b` and fails when a recorded fact is altered (negative control run). |
| **X** | Executed by the lead: a build, a gate script or a command, with the output recorded. |
| **S** | Source-checked by the lead: both sides (Lean and Rust or template text) read at `f2fe99b`. |
| **R** | Read-confirmed: found by a reviewer and reproduced from the source by an independent skeptic. Not machine-checked. |
| **R1** | Reported by one reviewer and not re-verified (low or informational items only). |

**Severity.** *Critical*: the headline would be false, vacuous or unsound even if every sorry were
closed as planned. *High*: a planned obligation is false or unprovable as stated, a trusted
assumption is materially unrealistic, or a major part of the claim has no plan item. *Medium*: a
real defect with bounded impact. *Low*: minor.

**Full record.** `docs/plans/V3-evidence/findings-full.md` holds every raw finding with its
evidence, counterexample, the skeptic's verdict and corrected claim, the proposed Lean checks, the
lists of what each reviewer found correct, and what was not covered. The last column of §1 maps each
RV id to the raw ids there.

---

## 0. Verdict

The project's own account of its state is accurate as far as it goes: the headline
`lowering_equivalence_poseidon` is **stated, not proved** (it depends on `sorryAx` through 11
sorried declarations), and `poseidonRender.Valid` is refuted at the deployment.

The review adds four things the project had not recorded.

1. **The reference side is not Rust-faithful.** On the fixture's own verifying key the Lean verifier
   rejects every proof for two independent reasons (RV-03, RV-04), and no Rust-generated proof has
   ever been run through it (RV-14). An equivalence to this verifier is not yet an equivalence to
   the Rust verifier.
2. **Several frozen statements are false or unsatisfiable as written** (RV-06 … RV-09, RV-11,
   RV-13, RV-18, RV-19). They need one signed-off repair pass; no amount of proof work closes them.
3. **Several sorried obligations are false as stated**, not merely open (RV-02, RV-10, RV-21 …
   RV-24, RV-31). One of them, `rejects_of_not_accepts`, silently carries the whole rejection half
   of soundness for every render.
4. **The plan has no architecture for the hard half of soundness and no demonstrated proof method**
   (RV-25, RV-37), and its definition of done does not imply its stated objective (RV-36).

What holds up is listed in §3: the shape of the headline, the composition theorem, the Yul/EVM
model for the opcodes used, most of the two ports by reading, and the proved TraceReturn rows.

---

## 1. Summary

| id | sev | class | finding | recorded by the project? | raw ids |
|---|---|---|---|---|---|
| RV-01 | — | L | The headline depends on `sorryAx`; cone of 11 | yes | — |
| RV-02 | high | L | A cone member is provably false; `False` follows from the registered sorries | partly | J-4, D-11 |
| RV-03 | critical | L+S | Multi-open groups commitments by value, Rust by allocation: Lean rejects every proof for the fixture key | partly (R-7, open) | A-1, E-1 |
| RV-04 | high | L | Rotation equality is structural: the imported key panics in the permutation argument | no | E-6 |
| RV-05 | critical | L+S | At the deployment `LeanAccepts` is identically false; the Lean-side key data are placeholders | partly | A-2, E-2, G-1, H-1, D+1, F+1, G+1 |
| RV-06 | high | L | Frozen `calldataOf` repacks twice and never returns `.ok` | no | A-3 |
| RV-07 | high | L+S | Calldata of 2²⁵⁶ bytes or more falsifies conjunct 1 | no | D-1 |
| RV-08 | high | L+S | Frozen `Valid.circuitMeta` forces `numPointSets = 0`; clauses 1 and 2 cannot both hold for a faithful plan | partly | B-1, F-1 |
| RV-09 | high | S | `Valid` ties the payload to the Lean key through the digest word only | partly | A-5, B-2, D-6, E-4, G-4, G-5, H-3, H-7, I-3, F-6, E+1 |
| RV-10 | high | L+S | `rejects_of_not_accepts` is false as stated; conjunct 3 has no true obligation | partly | A-6, C-4, D-2, I-1, A+1, C+1, D+2, E+2 |
| RV-11 | high | R | No totality: soundness is vacuous wherever the modelled program is stuck | partly | C-1, I-6 |
| RV-12 | high | L | The program is not the generator's output yet: 8 functions in the AST, 15 in the text | yes (WP-G1) | F-2, D-12 |
| RV-13 | high | L+R | `Render.scope` omits functions defined inside the quotient region | no | B-3, D-4 |
| RV-14 | high | R | No Rust-generated proof has been accepted by the Lean verifier | partly | E-3 |
| RV-15 | high | S+R | The pairing axioms leave `g₁`, `g₂` unspecified; base pins are unprovable; the axioms are eliminable | partly | G-2, H-2, E-7, I-4 |
| RV-16 | high | R | Gap B worked out: the modelled SRS has trapdoor 1; option (a) needs a theorem the tree lacks | partly | H-4, G-3 |
| RV-17 | medium | S | "The deployment" is a k = 6 test fixture; the on-chain artifact is out of scope | partly | H-6, F-9 |
| RV-18 | high | R | `permutationCommitmentsMatch` compares 8 column commitments with 3 chunks | yes at `f2fe99b`, no card | E-5, B+2, H+2 |
| RV-19 | high | R | No hypothesis gives the codec law `verifyMsgs` needs | no | A-4, D-10 |
| RV-20 | medium | R | `SoundSide` is selectable by the prover; "negligible" describes acceptance, not membership | partly | A-7 |
| RV-21 | medium | R | `prog_slices_decomp`, `runBody_iff_slices` are stated for every render and are false under name shadowing; the forward direction needs a determinism lemma | no | B-5, D-13, C-3, D-9 |
| RV-22 | medium | R | `vk_progress`, `vk_sound_clean` are false as stated | partly | D-8, B+1, F+3 |
| RV-23 | medium | R | `ec_pairing_contract` is false as stated in three ways | no | D-7, I-12 |
| RV-24 | high | R | `Inv` is too weak across quotient → PCS; `BlockSound .pcs` is false for a faithful slice | partly | D-5, F+2, G+2 |
| RV-25 | high | R | All soundness for pre-snapshot rejections sits in one monolithic sorry | partly | D-3, I-2 |
| RV-26 | medium | R | The constant table is read back by string parsing; `prefix_run_clean` is not derivable from `Valid` | partly | B-6, D-9, I-9 |
| RV-27 | medium | R | `CodegenAgrees` is token equality: builtin-versus-call and unresolved calls are invisible | partly | B-4, F-10, C+2 |
| RV-28 | low | R1 | `Valid` admits renders the generator refuses; WP-G1 cannot land inside the frozen `Program.lean` | partly | B-7, B-8, B+3 |
| RV-29 | low | R1 | Two Solidity-side trust items are unlisted; `EntryFrame.zeroAbove` is stronger than the guard | no | B-9, A-9 |
| RV-30 | medium | R | Precompile model boundary: missing precompile, address aliasing, forwarded gas | no | C-2, A-10, C-6, A-8, C-5, G-6, G-7 |
| RV-31 | low | R1 | `Evaluator.rel_worldLocal` is provably false and still a registered sorry | partly | C-7 |
| RV-32 | low | R1 | Minor verifier-port divergences outside `WellFormed` | no | E-8, E-9, E-10 |
| RV-33 | medium | R | Generator-port fidelity rests on one fixture, with spliced and typed-in parts | partly | F-4, F-5, F-7, F-8, H-10 |
| RV-34 | low | R1 | The conformance bundle is a different, unreproducible run with stale metadata | partly (R.5) | H-11 |
| RV-35 | high | R | The non-vacuity gate cannot be discharged as modelled and leaves the hash existential | partly | I-5, H-5, H+1, H-8 |
| RV-36 | medium | R | DONE does not imply the objective | partly | I-6, I-7, J-1 |
| RV-37 | high | R | The proof method is not demonstrated at scale; the automation package was skipped | partly | I-8 |
| RV-38 | medium | R | Work-breakdown gaps: cone sorries without cards | partly | I-10 |
| RV-39 | medium | R | Pending decisions, reviewed item by item | — | I-16, I-11 |
| RV-40 | medium | X | The gate suite is red at `f2fe99b` | no | J-8, G-10, J+1 |
| RV-41 | medium | S | CI does not run on this branch | no | J-7 |
| RV-42 | medium | R | Sorry and axiom detection can be evaded; the cone tool is weaker than `#print axioms` | no | J-2, J-3, J-5, J-10, G-9 |
| RV-43 | medium | R | "Frozen" pins the text of four files, not the meaning of the statements | partly | J-6, F-3 |
| RV-44 | low | R | Evidence cited as machine-checked is not in the tree; STATUS is an append log | partly | J-13, I-13, B-10, D-14 |
| RV-45 | low | R1 | Smaller gate defects | no | J-9, J-11, J-12, J-14, G-8 |
| RV-46 | info | R1 | Two pending decisions are unnecessary | no | H-9, I-14, I+3 |

---

## 2. Findings

### A. The reference side: the Lean verifier

#### RV-03 — Multi-open groups commitments by value; Rust groups by allocation *(critical, L+S)*

- **Where.** `Midfall/Halo2/Exec/Kzg/MultiOpen.lean:42` (`kzgCommitBeq`), used at `:70` and `:259`;
  `Midfall/Halo2/Exec/Kzg/Utils.lean:99-150` (`constructIntermediateSets`, whose docstring states
  the divergence); Rust `proofs/src/poly/query.rs:117-125` (`std::ptr::eq`) and
  `proofs/src/poly/kzg/utils.rs:50-66`; `proofs/src/plonk/verifier.rs:630-643`.
- **What.** Rust's `PartialEq` on `CommitmentReference::OnePiece` is pointer equality, so two
  distinct commitments with equal values stay two entries. The port compares values. When a second
  query carries an equal value at a point already recorded, the port returns `Error.opening` (the
  `DuplicatedQuery` path); Rust continues.
- **Witness.** The fixture key (`fixtures/conformance/poseidon/vk.json`) has the identity as fixed
  commitment for columns 8, 10, 11, 12, 14, 16. Columns 8, 10, 11, 12, 16 are not simple selectors
  and each is queried at rotation 0, so five equal one-piece commitments are opened at `x`. Rust
  builds them from `&vk.fixed_commitments[column.index()]`, five allocations.
  `ReviewProbes.lean` §3: five equal values at one point give `Error.opening`; five distinct values
  give five entries.
- **Consequence.** With real key data the Lean verifier rejects **every** proof for this key, while
  Rust and the contract accept. The soundness conjunct is then false and completeness vacuous, even
  with every sorry closed.
- **Recorded?** As R-7 ("must be settled, not assumed"), which asks for a corpus with a repeated
  commitment. Not recorded: that the fixture key itself has repeated commitments. R-7 appears in no
  V2 plan, queue or status document.
- **Repair.** Group by allocation identity: key each one-piece commitment by its label (column kind
  and index) or by an id assigned when the queries are collected. Add a KAT on the fixture's query
  shape.

#### RV-04 — Rotation equality is structural *(high, L)*

- **Where.** `Midfall/Halo2/Exec/Circuit.lean:130-132` (`inductive Rotation … deriving BEq`),
  `:1300-1324` (`getAnyQueryIndex`); `Midfall/Halo2/Exec/Permutation.lean:319`; Rust
  `proofs/src/poly/mod.rs:509-515` (`Rotation::cur()` is `Rotation(0)`).
- **What.** The importer builds every query rotation as `Rotation.value r`. `Permutation` looks up
  `(column, Rotation.cur)`, and `Rotation.cur == Rotation.value 0` is `false`.
- **Witness.** `ReviewProbes.lean` §3: on `PoseidonFixture.poseidonCs`, the lookup with
  `Rotation.cur` fails for all eight permutation columns (panic sites `circuit.rs:2084`, `:2074`,
  `:2094`); with `Rotation.value 0` it succeeds for all eight.
- **Consequence.** For every proof that reaches the permutation identity the Lean verifier returns a
  panic fault where Rust proceeds. This happens before the multi-open, so it pre-empts RV-03.
- **Repair.** Make `BEq Rotation` compare the integer, or collapse the type to a structure over
  `Int`. Add a KAT that runs `Permutation.expressions` on the imported key.

#### RV-14 — No Rust-generated proof has been accepted by the Lean verifier *(high, R)*

- **Where.** `Conformance.lean`, `Midfall/Conformance/Replay.lean:18-23`, `Bundle.lean`;
  `docs/conformance-schema.md`.
- **What.** The conformance replay folds over the exporter's event list and performs one transcript
  read, absorb or squeeze per event, taking the read width from the trace. It never runs
  `parseTrace`, the algebra, `collectQueries`, `multiPrepare` or `DualMSM.check`. It reads three
  fields of `vk.json`. The only `verifyNative = .ok` runs in the tree are `Fr 17` exponent-model
  fixtures with no queried non-simple fixed column.
- **Consequence.** RV-03 and RV-04 survived because the port's schedule and algebra were never
  executed on a Rust artifact. PLAN-V2 WP-I1's "validate the VK term with the conformance replay"
  validates nothing about commitments, queries, the permutation or the domain.
- **Repair.** A gate that runs the Lean verifier pipeline on a Rust proof and compares its final
  multi-scalar-multiplication terms with the Rust trace (PLAN-V3 milestone M1).

#### RV-32 — Minor verifier-port divergences *(low, R1)*

`i32Abs` models `i32::MIN.abs()` as a panic, which is the debug profile; the release profile wraps
(excluded by `SupportedV2.noRotInst`). The `Features.solidity` comments misstate the
fewer-point-sets configuration: the Lean flag models the compile-time feature and the run-time
switch together. On keys outside `WellFormed` Lean is stricter than Rust or reports a different
fault site in four places. No code change is needed for the last item; record them as accepted
divergences.

### B. The deployment instance

#### RV-05 — At the deployment `LeanAccepts` is identically false *(critical, L+S)*

- **Where.** `Midfall/Instances/G1Agreement.lean:2002-2006` (`g1CodecZ`, `ofCompressed? := fun _ =>
  none`); `Midfall/Halo2/Exec/Native.lean:164-171, 269-292` (`msgWire`, `prepareMsgs`,
  `verifyMsgs`); `Midfall/Halo2/Exec/Transcript.lean:60-70, 143-152`;
  `Midfall/Instances/PoseidonEnv.lean:191-242`.
- **What.** `verifyMsgs` re-serialises each message with `toCompressed` and runs the byte-level
  `prepare`, which reads every G1 point through `ofCompressed?`. At the deployment codec that is the
  constant `none`. Every proof carries a G1 message, so `verifyMsgs poseidonE …` is never `.ok`.
- **Witness.** `ReviewProbes.lean` §4: `poseidonRender.E.g1.ofCompressed? b = none` by `rfl`, and
  `read_g1CodecZ_err` (every G1 read at this codec is an error), on the three standard axioms.
- **Also placeholders.** The Lean key's 19 fixed commitments are the identity
  (`PoseidonEnv.lean:191-219`), `delta := 2` (`:230`; the real value is `7^(2^32) mod r`), and
  `poseidonSG2 := bls12_381Pairing.g₂` (`:236`, "Gap B").
- **Consequence.** The headline at `poseidonRender` reduces to "no run of the contract ever returns
  true". Completeness, `prefix_run_clean`, `BlockContractsAt` and `poseidon_quotient_block` are
  vacuously true; `poseidon_rejects` is false for any program that accepts a proof; the D-P45 gate
  (which adds `LeanAccepts`) is refutable. The gap is also in the frozen surface: nothing in it
  requires the compressed half of the codec to decode (RV-19).
- **Recorded?** D.2's status line says "exposes the ofCompressed blocker" and frames it as blocking
  `end_to_end`. That it makes the headline itself vacuous or false is not recorded. The recorded
  reason, "a real decoder is a discrete log", is wrong for G1: `G1PointCount.lean` proves every
  r-torsion point is a multiple of the generator.
- **Repair.** A real compressed codec, real key data, real `delta` (M1); then the curve assumption
  (RV-15, RV-16).

#### RV-15 — The pairing axioms leave the generators unspecified *(high, S+R)*

- **Where.** `Midfall/Assumptions/CurvePairing.lean:69-103`.
- **What.** The five axioms assert an `AdmissiblePairing G₁z G2fold blsGT` and nothing else; the
  docstring says so ("nothing here says … that its generators are the published ones"). The Lean
  verifier uses the class generators as KZG bases, and the contract loads its bases from the payload
  bytes. A pin such as `vkG1Words … = E.g1.toEip P.g₁` is therefore equivalent to
  `bls12_381Pairing.g₁ = g1zGen`, which the axioms do not imply.
- **Second half.** The axioms are also unnecessary: `G2fold` is a discrete-log carrier and
  `Additive G₁z` is a one-dimensional `ZMod r` space, so an admissible pairing with named generators
  can be constructed without axioms, and `holds_staged` is generic in the target group.
- **Consequence.** Under the DONE axiom list the headline is unprovable at the deployment: every
  base-point pin (D-P46 and its extensions) is underivable.
- **Repair.** Either make the three points the verifier pairs with *data* read from the payload, so
  no fact about generators is needed, or construct the pairing with named generators and delete the
  axioms. Decide together with RV-16.

#### RV-16 — Gap B worked out *(high, R)*

- **Where.** `Midfall/Instances/PoseidonEnv.lean:229-242`; `docs/DECISIONS-PENDING.md` §8.
- **What.** With `sG2Prepared = g₂` and `nG2Prepared = g₂⁻¹`, `DualMSM.check` is
  `e(left − right, g₂) = 0`, that is `left = right`. The proof's last message `π` is read after the
  last squeeze, so a prover can solve for it. Once the codec is repaired the modelled verifier
  accepts forgeries and rejects honest proofs.
- **Option (a) of the pending decision** (name `s·G₂` from its bytes by `Classical.choose`) needs
  `∃ X : G2fold, encG2 X = <bytes>`: that the deployed point lies in the subgroup generated by the
  model's generator. This cannot be obtained by evaluation, the tree has no theorem that the
  r-torsion of the twist is cyclic, and the G1 counting argument does not transfer. An elementary
  route exists but is real, uncarded mathematics.
- **Repair.** Decide the curve assumption explicitly (PLAN-V3 §2): data-driven bases with one named
  curve fact, or a known-trapdoor test SRS for the fixture.

#### RV-17 — "The deployment" is a test fixture *(medium, S)*

`poseidonRender` models the `PoseidonExample` test circuit at k = 6, deployed only to an in-process
EVM inside a cargo test. The only on-chain artifact in the repository,
`proofs/solidity-verifier/deployments/sepolia/moonlight-wrap`, is a different circuit (19 instances,
k = 20, accumulator mode) from superseded templates, excluded by `SupportedV2.noAcc`. The theorem
claims nothing about an on-chain contract, but "deployed render" and `DeployedProfile.lean` read
otherwise. Say "fixture" throughout, and state that accumulator mode is a precondition for any
claim about the Moonlight deployment.

#### RV-33 — Generator-port fidelity rests on one fixture *(medium, R)*

The only comparison of Lean output with Rust output is the poseidon fixture in one profile. In that
gate the VK payload is parsed back from the Rust-rendered `Halo2VerifyingKey.sol`; the quotient
regions and the whole PCS region are sliced from the Rust-rendered `Halo2Verifier.sol` (about 56 of
176 kB); the quotient program model, proof layout and layout sizes are typed in. Two typed-in
values contradict what Rust derives (`transcriptWords` 128 against 200; the PCS memory sizes). The
plan and the frozen docstring call `compact_quotient_computation_blocks` unported; it has been
ported since `3b8aaea`. No CI job runs the Rust crate's tests or regenerates the tracked dumps; the
committed `Halo2Verifier.sol` already differs from a fresh render in `BUILD_ID`.

#### RV-34 — The conformance bundle is a different run *(low, R1)*

`formal/fixtures/conformance/poseidon` is a separate export from `proofs/solidity-verifier/fixtures/
poseidon`; its `proof.bin` differs and its `trace.json` still carries pre-regeneration metadata. The
prover's blinding is random, so neither is reproducible (QUEUE R.5 records this).

### C. Frozen statements that are false or unsatisfiable as written

Each of these needs a human sign-off and a re-hash of `Frozen.sha256`. PLAN-V3 proposes one pass.

#### RV-06 — `calldataOf` repacks twice *(high, L)*

- **Where.** `Midfall/LoweringV2/Statements.lean:335-340`; `Midfall/Lowering/Calldata.lean:186-197,
  241-250, 257-266`.
- **What.** `calldataOf` calls `repackProof` and passes the result to `Lowering.encodeCalldata`,
  which takes the *compressed* proof and repacks again. Under the codec width law the repacked
  length differs from the compressed length, so the second repack fails with `lengthMismatch`.
- **Witness.** `ReviewProbes.lean` §5: on the in-tree toy data the frozen composition is not `.ok`;
  `repackThenEncode`, already in the tree, is.
- **Consequence.** `calldataOf … = .ok cd` is unsatisfiable, so `EndToEnd` states that `verifyNative`
  never accepts. `end_to_end` is unprovable for any render with an accepted proof. The v1 statement
  at `Lowering/Obligations.lean:361-366` has the same text.
- **Repair.** `calldataOf := repackThenEncode …`.

#### RV-07 — Calldata of 2²⁵⁶ bytes or more *(high, L+S)*

- **Where.** `vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:792` (`calldatasize` is
  `BitVec.ofNat 256 calldata.length`); `Midfall/Lowering/Calldata.lean:341` (size compared in
  `Nat`); `Statements.lean:240-247` (`EntryFrame` has no size bound).
- **Counterexample.** Take an accepted calldata and append 2²⁵⁶ zero bytes. Every modelled run is
  unchanged and returns ABI true; `decodeCalldata` fails its size guard, so `LeanAccepts` is false
  and `SoundSide` holds vacuously. Conjunct 1 is violated.
- **Consequence.** Not realisable on a chain, but the frozen statement is false as written, as are
  `Render.Rejects` and `vk_sound_clean`.
- **Repair.** Add `cd.size < 2^256` to the trusted `EntryFrame`.

#### RV-08 — `Valid.circuitMeta` forces `numPointSets = 0` *(high, L+S)*

- **Where.** `Statements.lean:186-190`; `Midfall/Generator/Encoding.lean:473-474`; Rust
  `proofs/solidity-verifier/src/lowering/vk.rs:504-519` and `plan.rs:238-244`.
- **What.** Clause 1 demands `plan.meta_` equal the raw `ConstraintSystemMeta.new`, whose
  `numPointSets` is 0. Rust post-processes the meta (`set_num_dummy_evals`, `set_num_point_sets`)
  and builds the layout from the post-processed count. Clause 2 builds the layout from
  `plan.meta_.numPointSets`.
- **Witness.** `ReviewProbes.lean` §5: the layout derived under the frozen pair has proof length
  4224; the deployed contract's is 4320.
- **Consequence.** No faithful plan satisfies clauses 1 and 2 together. `poseidon_valid` is
  unprovable for the generated contract whatever the fixture data, and PLAN-V2 WP-G4's "restate
  circuitMeta as a lemma of the constructor" cannot succeed.
- **Recorded?** R.1 and F.2 record the 96-byte gap as a clause-2 data gap that "needs the
  plan-sizing port". The defect in clause 1 is not recorded: a faithful port of `LoweringPlan::new`
  would produce a meta with `numPointSets = 3` and fail clause 1 instead.
- **Repair.** State the clause through the generator's actual derivation
  (`metaDataForStableStaticLayout`).

#### RV-09 — `Valid` ties the payload to the Lean key through the digest word only *(high, S)*

- **Where.** `Midfall/Lowering/Inv.lean:533-590` (`EnvAgrees`: `modulus`, `truncWidth`, `domainN`,
  `baryWeight`, `omegaInvMul`, `omegaOrder`, `negLagranges`, `nG2`, `sG2`, `vkDigestWord`);
  `Statements.lean:203-205`.
- **What.** No clause relates the payload's commitment words to `R.vk.fixedCommitments` and
  `R.vk.permutation.commitments`, its omega word to `R.vk.domain.omega`, its G1 and G2 base words to
  anything, or `R.E.delta` to the `DELTA` literal the generator emits. v1 had `VkSlotsAgree`; V2
  dropped it. The digest word itself is imported and unchecked (R-1).
- **Witness.** The deployment satisfies `Valid.slots` (proved at `f2fe99b`) with 19 identity
  commitments and `delta := 2`.
- **Consequence.** `blockContracts_of_valid` is false as stated: the PCS block reads commitments
  from the payload while the Lean side uses `R.vk`'s. Three consecutive cards each found a missing
  pin in this area (FP.0, T.1, S.4); they are instances of this one gap.
- **Repair.** One `PayloadAgrees` structure in `Valid` (commitments, domain words, bases, `delta`),
  and one constants-coherence clause (RV-26), instead of pin-by-pin growth.

#### RV-11 — No totality *(high, R)*

- **Where.** `Statements.lean:302-311`; `vendor/yul-semantics/YulSemantics/BigStep.lean:56-58,
  171-173, 185-187, 244-246`.
- **What.** Conjuncts 1 and 3 quantify over runs. The only existence claim is conjunct 2, under
  `LeanAccepts`. In the big-step semantics an unbound variable, an arity error or a call to an
  undefined function has no derivation. If the modelled program is stuck on some rejected calldata
  while the real EVM proceeds, soundness says nothing there.
- **Aggravation.** The token-level tie between AST and text (RV-27) cannot rule stuckness out, and
  `mainClosed` does not scan the ABI guard block.
- **Repair.** A fourth conjunct: for every entry frame a permissive run exists. `permissive` always
  admits the failing response, so the statement is true for a well-formed program.

#### RV-13 — `Render.scope` omits functions defined inside the quotient region *(high, L+R)*

- **Where.** `Statements.lean:107-110` (`scope := [hoist … R.helpers]`); `Blocks.lean:220-225`
  (`prog_slices_decomp`, second conjunct); template
  `proofs/solidity-verifier/templates/partials/quotient_numerator/QuotientHelpers.yul:6, :28`.
- **Witness.** `ReviewProbes.lean` §6: in `mainAssemblyTokens poseidonM`, `q_program_fail` and
  `q_pow5` occur after `let success`, inside the slice region.
- **Consequence.** As soon as the emitter produces the quotient region, `hoist (R.prog) = hoist
  R.helpers` is false, `runBody_iff_slices` fails for runs that call those functions, and
  `BlockProgress R .quotientLin` has no run. Latent today only because the region is not emitted.
- **Interaction with the queue.** R.2's cards G1.2 and G1.3 (READY at `6bde89f`) emit exactly these
  definitions inside `emitPartial .quotientLin`. The scope must be repaired no later than G1.2.
- **Repair.** Define the block scope as the hoist of the whole closed program.

#### RV-18 — `permutationCommitmentsMatch` *(high, R)*

`VerifyingKey.WellFormed.permutationCommitmentsMatch` equates the key's sigma-commitment count (one
per permutation column in Rust) with the per-chunk count, which is the number of proof-side product
commitments. For the fixture key it is 8 against 3. The clause is reachable from the frozen
`SupportedV2.wf`, so `Valid` is unsatisfiable for this key. R.1 found this at `f2fe99b`; no card
repairs it. Repair: `vk.permutation.commitments.size = vk.cs.permutation.columns.size`.

#### RV-19 — The codec laws are too weak *(high, R)*

`verifyMsgs` and `snapshotOf` re-read each point through `ofCompressed? (toCompressed P)`.
`G1CodecLaws` has only the decoder-first round trip, and it is a hypothesis of conjunct 2 only. A
codec that satisfies every law in the bundle can still make Lean read a different point from the
one the contract absorbs; `Inv` at the transcript checkpoint then pins memory to the wrong bytes.
Repair: add the encoder-first law and make the laws available to the soundness side, or drive the
Lean transcript from messages directly so the compressed codec leaves the headline.

#### RV-20 — `SoundSide` is selectable by the prover *(medium, R)*

`SoundSide` is a predicate on prover-supplied calldata: the lookup inputs are computed from
evaluation words the prover writes. A prover can make it false at will. On that set the theorem
gives only conjunct 3, so "the contract accepts implies the Lean verifier accepts" has no content
there. This is a gap in the formal chain, not a known attack: the contract checks the same identity
without inverting, and acceptance still requires the opening proof. The English headline must say
so. To close it formally, prove equivalence against a total reference that uses the inversion-free
identity.

#### RV-29 — Unlisted trust on the Solidity side *(low, R1)*

Both assembly blocks are `memory-safe`, which lets solc keep spilled variables in `[0x80, fmp)`; the
model matches the bytecode only if the program never touches `[0x40, TRANSCRIPT_MPTR)` except to
read `0x40`. That footprint is neither proved nor listed. Completeness also depends on solc's ABI
decoder not reverting on calldata `decodeCalldata` accepts. `EntryFrame.zeroAbove` asks for zero
memory from `0x80`; the guard the contract executes supports only "zero from `TRANSCRIPT_MPTR`".

#### RV-30 — The precompile model boundary *(medium, R)*

`permissive` requires every success to be the honest answer. A call to an address with no code
succeeds with empty returndata on a real chain, so executions on a chain without EIP-2537 are
outside the model, and the generated `returndatasize` checks are dead code in it; two docstrings say
the opposite. The honest fold selects a relation by the 160-bit key but answers on the unmasked
target, so an aliased precompile call fails in the model where the EVM would execute it. The honest
relation ignores forwarded gas, so the gas constants the generator emits are unverified for
liveness. None of these breaks soundness on a chain with the precompiles; all belong in the
trusted-base table and the English headline.

### D. Sorried obligations that are false as stated

#### RV-02 — A cone member is provably false *(high, L)*

`poseidon_valid : poseidonRender.Valid` is a registered sorry in the headline's cone, and
`poseidonRender_notValid` proves its negation. `ReviewProbes.lean` §1 derives `False` from the two.
Any goal can be closed ex falso in a module that sees both; neither the register nor `#cone_sorries`
would notice. A cone count taken while this holds measures nothing. Repair: never keep a sorry whose
negation is proved; carry `Valid` as an explicit hypothesis of a lemma until it is provable.

#### RV-10 — `rejects_of_not_accepts` *(high, L+S)*

- **Where.** `Midfall/LoweringV2/Blocks.lean:553-572` (at `4e18c65`; `:344-363` at `f2fe99b`);
  `Midfall/Lowering/Inv.lean:698-706`.
- **What.** The lemma concludes that every run reverts when Lean does not accept, with neither
  `SoundSide` nor `R.Valid` as hypothesis. Its docstring calls `SoundSide` "a completeness side
  condition" and "spurious" here.
- **Witness.** `ReviewProbes.lean` §2: the lemma alone yields `R.Rejects product` for **every**
  render, and soundness without `SoundSide` for every render.
- **Why it is false.** (i) On the logup set Lean panics (`logup.rs:460`,
  `product * f.invert().unwrap()`), while the contract computes the helper identity with prefix and
  suffix products and never inverts; `Inv.lean:698-706` says "on that set the contract accepts an
  honest proof and Lean rejects". (ii) With no `R.Valid`, nothing ties the Lean-side key to the
  program.
- **Consequence.** The decision floated in STATUS, deleting `SoundSide` from `Rejects` to drop the
  cone by one, would make `Rejects` false as well. Conjunct 3 has no true planned obligation on
  calldata outside `SoundSide`.
- **Repair.** Prove conjunct 3 from a snapshot-free obligation: every run either returns ABI true
  with the world unchanged or is a non-committing halt. It follows from the shape of the program
  (the only committing exit is the `return` in TraceReturn) and `NoWriters`.

#### RV-21 — `prog_slices_decomp` and `runBody_iff_slices` *(medium, R)*

Both are stated for every render with no hypothesis. The inliner threads a shadow list along the top
level, so in `R.prog` every slice is inlined under the shadow of `r`, `success`, `vk` and the helper
parameters, while `R.slice q` is inlined with an empty shadow. They agree only if no top-level
binder is a constant name, and no `Valid` clause says so. Separately, `runBody_iff_slices` fixes one
prefix endpoint and claims every run factors through it; that needs determinism of the prefix under
the permissive relation and an arbitrary gas oracle, where neither vendored determinism theorem
applies. Repair: a `noShadow` clause, `hR : R.Valid` on both lemmas, and either a determinism lemma
for call-free code or a total form of the prefix lemma.

#### RV-22 — `vk_progress` and `vk_sound_clean` *(medium, R)*

Both drop the decode hypothesis that `vk_blockRow` has in scope. `vk_progress` claims a clean exit
for wrong-shape calldata, whose length clause in `Clean .vk` is unsatisfiable. Progress also needs
table pins for the six header slots and three calldata constants, and payload-header content pins;
none is among D-P50's six.

#### RV-23 — `ec_pairing_contract` *(medium, R)*

False in three ways, at inputs its only consumer never uses. The honest half has no revert arm and
no check hypothesis although the production helper reverts on a false pairing. The precondition
leaves `success` unconstrained. The first conjunct quantifies over an arbitrary call relation while
pinning the result to `product`. The file header describes the trace-render tail, not the
production one.

#### RV-24 — `Inv` is too weak across quotient → PCS *(high, R)*

`snapshotOf` sets `lin := none` on every path, so the `Inv .quotient` clauses for the quotient
evaluation and the selector accumulators are `true`. `Clean R .quotient` therefore leaves unpinned
everything a faithful PCS slice reads besides the challenge slots and a few commitments. Perturb an
unpinned word: `Clean` still holds, the block exits normally with `success = 1` and pairing inputs
different from the snapshot's. So `BlockSound R .pcs` is false for a faithful PCS program, and the
quotient row cannot tell a program with the quotient numerator from one without it.

#### RV-31 — `Evaluator.rel_worldLocal` *(low, R1)*

Its own docstring says "NOT TRUE AS STATED", it is still `theorem … := by sorry`, and `SORRY.md`
lists it as an ordinary obligation. It is outside the headline cone today but PLAN-V2 X2 names it.
Delete it or replace it with its proved negation.

### E. Proof architecture

#### RV-25 — Soundness for pre-snapshot rejections sits in one monolithic sorry *(high, R)*

In `lowering_equivalence_of_blocks`, conjunct 1 splits on `LeanAccepts`. In the accepting branch the
conclusion is the hypothesis itself; in the rejecting branch it is `Render.Rejects`. The block
contracts are stated relative to one final snapshot. `BlockSound .finalPairing` does force
`DualMSM.check` on a clean exit, so the contracts cover the case "a snapshot exists and the pairing
fails". They cannot cover a decode failure, a non-canonical instance, or any Lean fault before a
snapshot exists. Staged rejection contracts and the fault table they need exist only as a card title
(C.3) and one line of WP-M0. No lemma connects `BlockSound` to `Rejects`.

#### RV-26 — The constant table is read back by string parsing *(medium, R)*

`constTableOf` splits the rendered `Constants` text into lines and parses each one. The KAT that
`Program.lean:55-57` says "must check" literal right-hand sides does not exist, and the "WP-G2" it
names has no plan or queue entry. Generic facts of the form `R.consts.lookup X = some (f R.pv)`
therefore go through string functions on a symbolic model; that is the common cause of the pins
(D-P46, D-P48, D-P50) and of `prefix_run_clean` not being derivable from the 13 clauses. Repair: a
data-level table from which the text is printed, and one decidable coherence clause.

#### RV-27 — `CodegenAgrees` is token equality *(medium, R)*

The printer does not distinguish `Expr.builtin op` from `Expr.call (opName op)`, `mainClosed`
ignores call names and treats a name bound anywhere as bound everywhere, and the writer scan treats
a user function named after a writer opcode as clean. So `Valid` leaves the emitter's builtin/call
spelling, call resolution, arity and lexical scoping trusted. `R.prog` is not a free field, so this
is an emitter-fidelity gap, not a way to smuggle a different program into a valid render. Repair:
one decidable well-formedness clause on the program (every call resolves with the right arity; no
function is named like a builtin).

#### RV-28 — `Valid` admits renders the generator refuses; WP-G1 and the frozen file *(low, R1)*

Rust's `generate_verifier_from_plan` aborts unless `validate_layout()` passes; `Valid.model` does not
ask for it. `SupportedV2` says "embedded quotient VM" but also admits Direct lowering. The emitter's
only input is a `PlanView`, which carries neither constraint-system expressions nor `qblocks`, so
emitting the quotient numerator needs a change to the frozen `mainAsmRaw`; PLAN-V2 says "extend
`mainAsmRaw` accordingly" without noting that the file is frozen.

### F. The plan

#### RV-12 — The program is not the generator's output yet *(high, L; recorded as WP-G1)*

`ReviewProbes.lean` §6 at `f2fe99b`: slice lengths `[1, 44, 3, 1, 225, 2, 3]`; 8 function
definitions in the AST against 15 in the text; `codegenAgrees poseidonPv poseidonM = false`. The
project's own inventory (QUEUE R.2, `8c5f237`) measures the same gap token for token: 6761 AST
tokens against 14054, in four regions (accumulator helpers 823, quotient helpers 68, quotient
numerator 6384, PCS block braces 18), with cards G1.1–G1.4. The accumulator helper functions render
unconditionally and are never emitted, so `Valid.codegen` fails for **every** render in scope, not
only the fixture. Every lemma that takes `hR : R.Valid` is
vacuously true today, and the "false as stated" verdicts of §D become effective the moment the
emitter is completed. Block rows proved now are rows about a placeholder program.

#### RV-35 — The non-vacuity gate *(high, R)*

The D-P45 text (add `LeanAccepts` and `G1CodecLaws`) removes the no-runs vacuity. Discharging it at
the fixture needs `DualMSM.check = true` for an honest proof, which reduces to `s • left = right`
for the trapdoor of the real SRS; the tree cannot prove that without a pairing implementation, the
trapdoor, or a trusted SRS fact. As modelled today (RV-05, RV-16) the gate is false. The hash is
existential and constrained only at the key's runtime bytes, so after the codec repair a constant
hash and a forged transcript would satisfy the gate. Also: no theorem states
`HypothesesInhabited poseidonRender _`, and `poseidonProduct` exists only in a docstring, so the
cone can reach 0 with non-vacuity never attempted.

#### RV-36 — DONE does not imply the objective *(medium, R)*

PLAN-V2 §6 asks for a green `verify.sh`, a cone of 0 and an axiom list. Only the first is executed:
`verify.sh` never reads a cone count and nothing runs `#print axioms` on a V2 theorem (RV-42). DONE
does not require the theorem's program text to equal the Rust artifact, and the existing byte-exact
gate splices PCS and quotient text from that artifact (RV-33). The "revm differential (M4)" that the
trusted-base row cites as validation of `EntryFrame` has no script, harness or card. There is no
totality requirement (RV-11).

#### RV-37 — The proof method is not demonstrated at scale *(high, R)*

TraceReturn (23 tokens) is the only closed block. VkLoading (223 tokens) and FinalPairing (22
tokens) each still carry three sorries. PLAN-V2 places the automation package "BEFORE M1" and says
hand proofs "are infeasible"; T.2 declined the tactic and the accept line (re-prove TraceReturn in
under 100 lines) was never met. No method has been demonstrated for loops, `staticcall`, the MSM or
the quotient VM, and an `Inv` chain already exceeds the default heartbeat budget. The reviewer's
"lines per token" extrapolation is not supportable (a sample of one); the supported statement is
"no demonstrated method for about 13,000 remaining tokens".

#### RV-38 — Work-breakdown gaps *(medium, R)*

`prefix_run_clean`, `runBody_iff_slices`, `noWriters_prog`, `Run_worldEq_of_noWriters`,
`prog_slices_decomp`, `inline_append`, `hoist_prog_addr_indep` and `snapshotOf_prepareMsgs` have no
card. Fourteen register rows name "Q0.x/Q1.x cards" and no Q1.x card exists. The deployment's
non-vacuity theorem is not stated.

#### RV-39 — Pending decisions, item by item *(medium, R)*

*As reviewed at `f2fe99b`. All of these were signed at `5329c3f` as D-P45–D-P59; see PLAN-V3 §2.1.*

| item | assessment |
|---|---|
| §1 keep W2 (no delegated decisions) | Sound. |
| §2 reject `hR : R.Valid` in the headline | Correct: with `¬ Valid` proved the headline would hold by contradiction. |
| §3 D-P45 | Necessary, not sufficient, and not dischargeable as modelled (RV-35). Pin the hash to `keccak256`. |
| §4 D-P46 base-slot pins | All three conjuncts are underivable from the axioms (RV-15); a commitment clause is missing (RV-09). Replace by `PayloadAgrees`. |
| §5 D-P47 fixture re-export first | Reasonable; R.1 has since run. |
| §6 D-P48 `RETURN_MPTR` pin | Probably derivable from the existing `closed` clause (RV-46); subsumed by the coherence clause (RV-26). |
| §7 D-P49 | Technically correct; ratified at `1206fb7`. |
| §8 Gap B option (a) | Understates the cost (RV-16). Decide the curve assumption as a whole. |
| §9 `Valid.model` | No decision needed (RV-46). |
| §10 WP-T before block proofs | Agree with (a); RV-37. |
| STATUS: delete `SoundSide` from `Rejects` | Unsound (RV-10). |

Governance at `6481731`: D-P49 and D-P50 were applied in code before sign-off; `1206fb7` ratified
both after the fact, which is the remedy.

### G. Gates, CI and process

#### RV-40 — The gate suite is red at `f2fe99b` *(medium, X)*

`lake build` is green (5240 jobs). `bash scripts/checks.sh` exits 1 at the sorry register:
`Midfall/Instances/PoseidonValid.lean` 227 is now 252. Because of `set -e` the later gates do not
run. Run on its own, `python3 scripts/kat_gate.py` fails: 1397 annotated checks against a pinned
1393. With the pin adjusted in a scratch copy, two gates still fail, both annotated
`-- expect TRUE` where the value prints `true` (`DeployedProfile.lean:857`,
`PoseidonCoherence.lean:502`). All three come from `2041977`, whose message says "build green".
PLAN-V2 §4 rule 7 already says a green build does not mean the KATs passed.

#### RV-41 — CI does not run on this branch *(medium, S)*

`.github/workflows/formal.yml` triggers on pull requests and on pushes to `main`. `formal/` is not
on `main`, so pushes to `formal/baseline` never run it. Reading the action's source, the
`lean-action` step would also most likely stop before the build, because its package directory
defaults to the repository root.

#### RV-42 — Sorry and axiom detection *(medium, R)*

The register and the `native_decide` confinement gate are regular-expression scans of source text.
They cannot see `admit`, `stop`, a direct `sorryAx`, a macro that expands to `sorry`, an `axiom`
declaration or `decide +native`. No script enumerates axioms. The register is keyed on `file:line`
only, and 57 of 60 rows carry the word `sorry` as their declaration text. `#cone_sorries` reports
only `sorryAx` and does not traverse inductive constructors. `check_frozen_axioms.py` prints that
the proved frozen statement is proved even if it regains `sorryAx`. No gate asserts the headline's
axiom set.

#### RV-43 — "Frozen" pins text, not meaning *(medium, R)*

The hashes cover four files. The definitions that fix the meaning of `LoweringEquivalence` and
`Render.Valid` are not pinned: the run relation, the call relations, the vendored semantics,
`decodeCalldata`, `verifyMsgs`, `snapshotOf`, the emitters, `EnvAgrees`, `Eip2537.Holds`. Nor are
`poseidonRender` or the statement of the root theorem. Completing the emitter must edit such a file,
with the freeze green.

#### RV-44 — Evidence that is not in the tree *(low, R)*

STATUS describes the R-72 evidence as machine-checked (`sides_of_none`, `gate_weak`,
`headline_of_no_runs` and others); no file declares those names. STATUS is about 340 lines under a header
that says "overwritten by every ticket (≤ 1 page)" and contains mutually contradictory numbers.
Several docstrings on and around the frozen surface misdescribe it.

#### RV-45 — Smaller gate defects *(low, R1)*

`kat_gate.py` tracks only `/--` as a comment opener, so a KAT inside a plain block comment still
counts. Two perturbation harnesses hard-code another machine's paths; one mutates tracked files in
place; none is run by a gate. In `checks.sh` a crash of the `native_decide` scanner is masked by
`|| true` and its verdict is tested after an unrelated section. Each `native_decide` adds a fresh
axiom identified by name only. PLAN-V2 says keccak is `@[extern]`; it is a pure Lean definition, so
there is no separate native implementation to diverge, and its own KATs are never evaluated.

#### RV-46 — Two pending decisions are unnecessary *(info, R1)*

`Valid.model` should be provable by generalising the scrutinee (prove the statement for a variable
`x` with `∀ e, x = .error e → False`, then instantiate), with no v1 edit and no frozen change.
D-P48's `RETURN_MPTR` pin looks derivable from the frozen `closed` clause. Neither was compiled.

---

## 3. What was checked and found correct

Positive assurance, with the same evidence classes. The full lists are in `findings-full.md`.

**Statements.**
- The three-conjunct shape of `LoweringEquivalence` is right. STOP and falling off the end are
  neither `isReturn` nor `isRevertOrHalt`, so conjunct 3 excludes them (R).
- No hypothesis quantifies over programs or mentions the program (R).
- The hash abstraction is consistent: `extcodehash` reads the frame's hash, pinned to `keccak256` at
  the key's runtime bytes only (R).
- `DeploymentV2`, `EntryFrame` and `Eip2537.Holds` are jointly satisfiable; the nominal solc frame
  is an instance of `EntryFrame`; `entryFrame_inhabited` is proved on the three standard axioms (L).
- `verifyNative_iff_msgs` and `LegacyVacuity.not_LoweringCorrect` are proved on the three standard
  axioms (L).

**Composition and contracts.**
- `lowering_equivalence_of_blocks` follows from its named lemmas; each branch and the eleven proved
  transport facts were read and are correct (R).
- `slices_seq_sound` and `slices_seq_progress` are true and derivable after the D-P49 gate; the
  checkpoint chain lines up; the contract combinators are sound, including a halting first block (R).
- `inline_append`, `hoist_prog_addr_indep`, `noWriters_prog`, `fp_pairing_algebra`,
  `keccakOf_invariant`, `RunCommitted_keccakOf` and `Run_worldEq_of_noWriters` are true as stated (R).
- `tr_blockSound` and `tr_blockProgress` are proved on the three standard axioms (L).

**Semantics.**
- The builtin model is faithful for every opcode in the production templates; the `staticcall` step
  writes only `min(outSize, returndata length)` bytes and replaces the returndata buffer (R).
- `permissive` is total (the failing response always qualifies), so no `staticcall` is stuck (R).
- `dialect_deterministic` is proved without sorry; `callsOf product` is functional (R).

**The two ports, by reading.**
- Transcript, `parse_trace` order, the algebraic identities, linearization and `multi_prepare`
  match Rust term for term, apart from RV-03 and RV-04 (R).
- `ProofCalldataLayout.fromProtocol`, `TranscriptBufferLayout.fromProofLayout`,
  `VerifierMemoryLayout.new`, `ConstraintSystemMeta.new`, `ProtocolPlan.fromConstraintSystem`,
  `generateBaseVk`, `metaDataForVk`, `metaDataForStableStaticLayout` and
  `validateGeneratorInvariants` are faithful (R).
- `asmOf`'s order matches the template; merging the two assembly blocks into one Yul block is
  harmless here; the tokenizer is adequate on this corpus; the inliner handles shadowing (R).

**Trusted base.**
- There are exactly five axioms, all in `Assumptions/CurvePairing.lean`, and they are jointly
  consistent. G1 is a real curve group; the moduli are the BLS12-381 values with kernel-checked
  primality (R).
- `Eip2537.Holds` is satisfiable, and the byte model in `Yul/Externals.lean` assumes no more than
  the real precompiles (R).
- `native_decide` is confined to `Instances/` (123 uses at `f2fe99b`). The vendored semantics has no axiom and no
  sorry. Only one registered sorry is a sorried *definition* (`Spec.accepts`) (R).

**State of the tree.**
- At `6481731`: build green; the 60 sorries match the register; the frozen hashes match; the cone
  report matches STATUS (X).
- At `f2fe99b`: build green; cones unchanged; frozen hashes match; gates red (RV-40) (X).

---

## 4. Limits of this review

- **Reading, not proving.** Class R and R1 findings were not machine-checked. Several carry a
  proposed Lean check in `findings-full.md`; PLAN-V3 turns the important ones into cards.
- **A moving tree.** Reviewers read `Midfall/Instances/` and `docs/` while five commits landed. The
  lead re-checked the findings in §2 against `f2fe99b`; some reviewer line numbers in the full dump
  are those of `6481731`.
- **Not executed.** No run of the modelled program on fixture calldata, no run of the Rust test
  suite, no comparison with an EVM implementation.
- **Not covered in depth.** The 50,000 lines of `Midfall/Generator/` were spot-checked, not read in
  full. The quotient VM proofs (`Lowering/Qvm*.lean`) and the accumulator files were read at header
  level. The security statements S1–S7 are placeholders and were not reviewed as mathematics.
- **Severity is a judgment.** "Critical" follows the letter of the scale: RV-07 is critical by that
  letter in one reviewer's report and has no practical exploit; it is listed as high here.

Please check the findings against the source before acting on them.
