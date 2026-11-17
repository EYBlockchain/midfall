# PLAN-V3 — ticket cards

Ready-to-brief cards for `PLAN-V3.md`, in the `QUEUE.md` card format (EXECUTION-V2 §3). The area
cards were written by the six design passes behind PLAN-V3, each from measurements and typechecked
Lean under `docs/plans/V3-evidence/lean/`; the plan-level cards at the end were written with the
plan. **The decisions they name, D-P60–D-P69, were signed on 2026-11-17 (`design.md`). A card still
waits for the conditions its decision records, and the orchestrator re-checks each card's NEEDS
at the current commit before briefing (EXECUTION-V2 §2.3).**

- **Order, milestones and exit gates:** PLAN-V3 §5. This file is grouped by area, not by order.
- **Ids.** `REF.n` reference side, `OBJ.n` object, `ST.n` statements, `SIM.n` soundness
  architecture (renamed from the design pass's `S.n`, which collides with live QUEUE cards),
  `T3.n` proof technology, `DG.n` gates and DONE, `PL.n` / `ROW.x` plan-level.
- **Decisions.** Numbers follow PLAN-V3 §2.2 (D-P60 … D-P69). The area header names the decisions
  its cards wait for. D-P45–D-P59 are signed and unchanged.
- **Live queue.** Several cards coincide with live `QUEUE.md` cards (R.3–R.9, R.4b, T.2b, G1.x,
  Q0.5); PLAN-V3 §10 has the mapping. Where they coincide the live card runs and the V3 card is
  its evidence and acceptance.
- **Model routing (W10).** Each card says `strongest` or `Sonnet`. A Sonnet card is one whose
  deliverable is a port of a named evidence file, a KAT, or a gate; a `strongest` card states or
  proves something new.
- **How a subagent uses a card.** (1) Open the evidence file the card names and run
  `bash docs/plans/V3-evidence/check.sh <area>`; if it fails at the tip, stop and report: the
  premise is false. (2) Port the named declarations verbatim into the target file; compile. (3)
  Only then adapt names and imports. Do not restate a statement, do not "improve" a definition,
  do not add a hypothesis: a statement that seems to need one is a PREMISE GAP (stop, report the
  exact goal). (4) Run the card's Accept commands and paste their output in the report.
- **Measured at** `f2fe99b`–`5329c3f`; no Lean source differs between those commits. At `4e18c65`
  F.1 changed `Midfall/LoweringV2/Blocks.lean` only: the two sequencing lemmas are proved, and
  line numbers after line 286 moved by about +209 (`rejects_of_not_accepts` :356 → :565, the
  transport lemmas :370-471 → :579-680, `lowering_equivalence_of_blocks` :493 → :702,
  `entryFrame_inhabited` :624 → :833). Cards quote the earlier numbers; find declarations by name.
- **Box sizes** are the design passes' estimates, not measurements.


---

## M1 and M4 — the reference side  (waits for: D-P61, D-P62, D-P63; 16 cards, 25 box-hours)

### REF.D — Reference-side decisions  **[DONE — signed 2026-11-17]**

> **Do not run.** D-P61, D-P62 and D-P63 were signed by the human on 2026-11-17 (after `53bf8c1`) and are recorded in `design.md` with their conditions. What remains of this card is those conditions, which the cards that name each decision apply.

DECISION · DECISION · box 0.5 h · orchestrator + human · after PL.0 or earlier

- **Goal.** The human signs or strikes D-P61, D-P62 and D-P63 of PLAN-V3 §2.2, and `design.md` quotes the sign-off
  (who, when, where) under those numbers.
- **Needs.** PLAN-V3 §2.1 (how the signed D-P45–D-P59 relate) and §2.2 (the row text, its
  recommendation and its "if struck" consequence); the evidence named in PLAN-V3 §3 for that row,
  re-run at the tip with `bash docs/plans/V3-evidence/check.sh`.
- **Does NOT need.** Any Lean change. The orchestrator does not decide (W2, D-P53).
- **Do.**
  1. Draft the row in `docs/DECISIONS-PENDING.md` (new items go at the end, unsigned), quoting
     PLAN-V3 §2.2 verbatim and linking the evidence output.
  2. Mark every card that names the row BLOCKED until it is signed.
  3. On sign-off, record it in `design.md`; on a strike, apply the "if struck" line of §2.2 and
     re-plan the cards that named the row.
- **Deliverable.** The `design.md` entry or entries, with sign-off lines.
- **Accept.** `design.md` contains each numbered entry with a W2 sign-off line; no `.lean` file
  changed; `git diff --stat` shows `formal/docs/` only.
- **Stop if.** The evidence for the row no longer typechecks at the tip: re-measure before asking
  for a signature.
- **Guidance.** D-P62 amends the signed D-P55 (steps 2–3): say so in the entry, and that the trusted base shrinks. D-P63 changes the fixture; R.5 (D-P58) must have reported first.

### REF.1 — Multi-open grouping by allocation slot

ALG · PORT · box 2.5 h · strongest · after REF.D

- **Goal.** Make constructIntermediateSets group one-piece commitments by Rust allocation identity, so the real key's six identity commitments at x no longer give Error.opening.
- **Needs.** Exec/Query.lean:53-108; Exec/Kzg/MultiOpen.lean:42-48, 62-80, 257-259; Exec/Kzg/Utils.lean:123-195, 262-320; producers Exec/Verifier.lean:757-802, Exec/Permutation.lean:265-306, Exec/Logup.lean:196-211, Exec/Trash.lean:135-138; pattern sites Logup.lean:391, Permutation.lean:555,605, Linearization.lean:145, Trash.lean:271, Verifier.lean:1237, Lowering/Snapshot.lean:101; KAT call sites Verifier.lean:1220,1259,1280,1296, Snapshot.lean:497, Spec/Degrees.lean:531,573, Instances/ChallengeStream.lean:139-143,272-276. Reference text: scratch D1_Grouping.lean. Rust: proofs/src/poly/query.rs:117-133, poly/kzg/utils.rs:54-58.
- **Does NOT need.** Any change to constructIntermediateSets or computeDummyQueries bodies; the curve model; the Generator/Kzg.lean port (it already groups by planned pointer); the frozen LoweringV2 files.
- **Do.**
  1. Add CommitSlot to Exec/Query.lean and change CommitmentReference.onePiece, .beq, .asTerms and VerifierQuery.new exactly as in D1_Grouping.lean.
  2. Replace kzgCommitBeq's one-piece arm by slot equality.
  3. Thread the slots through the four producers (proof index via zipIdx; lookup and trashcan index; helper index j) as listed in the memo §1.2.
  4. Fix the pattern matches and the KAT call sites; give the two ChallengeStream query sets the same .anon slot where they reuse one commitment.
  5. Move the six D1 KATs into Exec/Kzg/Utils.lean with '-- expect true'.
- **Deliverable.** inductive Midfall.Halo2.CommitSlot; CommitmentReference.onePiece (slot : CommitSlot) (com : C); VerifierQuery.new point label slot commitment eval; kzgCommitBeq with slot equality; KATs fixtureShape_groups_ok, fixtureShape_old_rejects_ok, duplicate_still_rejects_ok, duplicate_slot_distinct_values_rejects_ok, oneSlotTwoPoints_ok.
- **Accept.** lake build green; the six KATs evaluate to true; falsifier: fixtureShape_old_rejects_ok keeps the value relation and must stay true (Error.opening); every pre-existing '-- expect' token in Verifier.lean, MultiOpen.lean, Utils.lean, ChallengeStream.lean keeps its value; verify.sh --quick green.
- **Stop if.** A theorem (not a KAT) fails to compile because it unfolds the one-piece arm; report the goal state. Or a ChallengeStream pinned value moves after giving shared commitments a shared slot.
- **Guidance.** The label is not a key: 13 NoLabel queries cover 7 allocations on the fixture and label-keyed grouping returns Error.opening. Keep the Linear arm by value. This is one atomic change (about 40 edit sites, mostly mechanical); do not split it, the build is red in between. The slot order was validated at run time on the real vector (49 for 49, each agreeing with its label) by slotsFor in scratch RunLib.lean; use it as the reference.

### REF.2 — Semantic equality on Rotation

ALG · PORT · box 1 h · Sonnet · after REF.D

- **Goal.** Make BEq Rotation compare the integer, as Rust's derived PartialEq on Rotation(i32) does, so an imported key no longer panics in the permutation identity.
- **Needs.** Exec/Circuit.lean:111-132 (inductive and its hazard note), :1892, :2064-2067, :2083; Exec/Domain.lean:85-94 (Rotation.int); the 12 direct users listed in scratch D2.out. Rust: proofs/src/poly/mod.rs:509.
- **Does NOT need.** Any change to PoseidonFixture's importer (it may keep Rotation.value); DecidableEq or LawfulBEq on Rotation; the curve model.
- **Do.**
  1. Move Rotation.int from Exec/Domain.lean:90-94 to Exec/Circuit.lean directly after the inductive; delete 'deriving BEq' and add 'instance : BEq Rotation := ⟨fun a b => a.int == b.int⟩'.
  2. Flip the two KAT clauses: Circuit.lean:1892 expects true; :2083 expects index 0.
  3. Rewrite the hazard prose at Circuit.lean:120-129 and :2064-2067, and PoseidonFixture.lean:144-147, 184-186.
  4. Add a KAT in Instances (rotationRepair_ok from D2_Rotation.lean, with the tree's getAnyQueryIndex) expecting true.
- **Deliverable.** Rotation.int in Exec/Circuit.lean; instance : BEq Rotation by integer; KAT Midfall.Instances.PoseidonEnvKats.poseidonPermutationQueries_ok.
- **Accept.** lake build green; on poseidonCs, getAnyQueryIndex col Rotation.cur returns ok 0, 0, 1, 2, 3, 4, 0, 1 for the eight permutation columns; falsifier: with the structural instance the same eight calls panic at circuit.rs:2084, 2074 x5, 2094 x2 (D2.out).
- **Stop if.** Any proof depends on structural equality of Rotation (for example a 'decide' or 'rfl' on a pair containing Rotation.value 0 vs cur); report it with the goal.
- **Guidance.** Later 'deriving BEq' on structures with a Rotation field pick the instance up automatically because it precedes them. A canonicalising importer was rejected: it would need a Valid clause and every hand-built constraint system would stay exposed.

### REF.3 — WellFormed: one sigma commitment per permutation column

ALG · STATEMENT · box 0.5 h · Sonnet · after REF.D

- **Goal.** Repair VerifyingKey.WellFormed.permutationCommitmentsMatch, which compares 8 column commitments with 3 chunks at the real key.
- **Needs.** Exec/VerifyingKey.lean:99-102, 114-116; Instances/PoseidonValid.lean:38-43, 413; Instances/PoseidonEnv.lean gate 13 (:488-501); Spec/Degrees.lean:99-103 (the divCeil count stays there for the proof's product commitments). Rust: proofs/src/plonk/permutation.rs:123.
- **Does NOT need.** The frozen files' text (SupportedV2.wf only names WellFormed); the curve model.
- **Do.**
  1. Change the clause to 'vk.permutation.commitments.size = vk.cs.permutation.columns.size' and correct its docstring bullet.
  2. Replace the refutation at PoseidonValid.lean:413 by the positive discharge at the real key, and flip gate 13's negated conjunct.
- **Deliverable.** VerifyingKey.WellFormed.permutationCommitmentsMatch : vk.permutation.commitments.size = vk.cs.permutation.columns.size.
- **Accept.** lake build green; witness: 8 = 8 at poseidonVkExec by decide; falsifier kept as a KAT: divCeil 8 3 = 3 ≠ 8.
- **Stop if.** A theorem other than PoseidonValid.lean:413 consumes the divCeil form.
- **Guidance.** The only consumer today is the refutation, so this is cheap. It changes the meaning of a clause reached from the frozen SupportedV2, hence the decision in REF.D.

### REF.4 — A real, computable G1 codec on G₁z

ALG · PORT · box 2 h · Sonnet · after REF.D

- **Goal.** Replace the placeholder compressed codec by a real one whose four fields are computable, with the decoder-first laws proved.
- **Needs.** Instances/G1PointCount.lean:238 (torsion_eq_zpowers_gen), :437, :493; Instances/G1Agreement.lean:261 (emb), :1562, :1586, :1832, :1888, :1963-2009 (g1zPair, g1zToEip, g1CodecZ, g1zGen), :2080; Instances/HoldsStaging.lean (g1CodecZ_ofEip_toEip, holds_staged); Instances/Bls12_381.lean:76, :120 (G1Affine.ofCompressed?, toCompressed); Instances/CurveSurface.lean:540 (g1CodecZ_laws). Reference text: scratch RefModel.lean sections 1-2 and D4_CodecKats.lean.
- **Does NOT need.** A discrete log; a point count beyond the in-tree theorem; any Exec change; the encoder-first compressed law (REF.9, REF.10).
- **Do.**
  1. Create Instances/G1Compressed.lean with g1zOfPair?, g1zAffine, g1zToCompressed, g1zOfCompressedRaw?, g1zOfCompressed?, g1zOfEipC?, g1CodecC from RefModel.lean.
  2. Move the proved lemmas: g1zPair_of_g1zOfPair?, g1zOfPair?_g1zPair, g1CodecC_ofEip, holds_transfer, g1CodecC_compressedRoundtrip, g1CodecC_laws.
  3. State g1CodecC_compressedEncoderFirst with sorry and register it.
  4. Add the D4 KAT reading the points from vk.json, params.json and trace.json via include_str.
- **Deliverable.** def g1CodecC : G1Codec G₁z; theorem g1CodecC_ofEip : g1CodecC.ofEip? = g1CodecZ.ofEip?; theorem g1CodecC_compressedRoundtrip : g1CodecC.compressedRoundtrip; theorem holds_transfer; theorem g1CodecC_compressedEncoderFirst (sorry); KAT g1CodecC_fixturePoints_ok.
- **Accept.** lake build green; #print axioms of each proved theorem = [propext, Classical.choice, Quot.sound]; KAT true on 50 points with the six rejections; falsifier: the same KAT at g1CodecZ is false (its ofCompressed? is the constant none).
- **Stop if.** g1CodecC fails to compile as a computable def in the tree (it compiled in scratch).
- **Guidance.** The re-encode test in g1zOfCompressed? is what makes the decoder-first law a five-line proof; it is a no-op on canonical strings (measured on 50 points). Do not redefine g1CodecZ in place: prove function equality of the EIP halves and transfer Holds, so the existing theorems stay untouched.

### REF.5 — The deployment pairing by construction; retire the five D-P36a axioms

ALG · PORT · box 1.5 h · Sonnet · after REF.D

- **Goal.** Replace axioms blsGT, blsGT_group, blsGT_primeOrder, blsGT_module, bls12_381Pairing by a constructed AdmissiblePairing G₁z G2fold G₁z with named generators.
- **Needs.** Assumptions/CurvePairing.lean:69-103; Instances/G1Agreement.lean:1814-1846 (G₁z, primeOrderZ, moduleZ); Instances/G2Codec.lean:245-256; Instances/ExponentModel.lean (expModule, expPrimeOrderWith); Instances/HoldsStaging.lean (holds_staged is generic in Gₜ); Instances/HoldsFinal.lean; the 8 files naming the axioms (measurement list). Reference text: scratch RefModel.lean section 3.
- **Does NOT need.** Fp12, a Miller loop, or any real pairing; any Exec change; cyclicity of the G2 torsion.
- **Do.**
  1. Create Instances/PairingByConstruction.lean with g1zGen_ne_one, eC, the instance (g₁ := g1zGen, g₂ := g2foldExp 1, Gₜ := G₁z) and the rfl lemmas for the generators.
  2. Turn Assumptions/CurvePairing.lean's five constants into definitions pointing at the construction (abbrev blsGT := G₁z, instance bls12_381Pairing := the constructed one), or delete the file and re-point the six importers.
  3. Re-run #print axioms on holds_exhibited and on lowering_equivalence_poseidon's non-sorry dependencies.
- **Deliverable.** instance Midfall.Instances.pairingC : AdmissiblePairing G₁z G2fold G₁z; theorems pairingC_g1 : pairingC.g₁ = g1zGen and pairingC_g2 : pairingC.g₂ = g2foldExp 1; holds_exhibited with axioms = the standard three.
- **Accept.** lake build green; #print axioms holds_exhibited = [propext, Classical.choice, Quot.sound]; grep -rn '^axiom' Midfall/Assumptions/CurvePairing.lean returns nothing.
- **Stop if.** A downstream proof relied on the opacity of bls12_381Pairing (a statement that becomes false, not merely a proof that needs rewriting).
- **Guidance.** Keeping the old names as definitions is the smallest diff: 24 references in HoldsFinal.lean and 13 in ObligationsGates.lean keep compiling. The two gate scripts change in REF.5g, in the same commit.

### REF.5g — Gates follow the axiom removal

INFRA · KAT · box 0.5 h · Sonnet · after REF.5

- **Goal.** Make the axiom gates assert the new, smaller trusted base.
- **Needs.** scripts/check_frozen_axioms.py:105-131, 289-336; scripts/check_hypothesis_bundles.py:124-131; Instances/ObligationsGates.lean record assumption_dP36a; PLAN section 6 axiom list.
- **Does NOT need.** Any new gate; any Lean proof.
- **Do.**
  1. Set the D-P36a allow-list to empty so holds_exhibited must depend on exactly the standard three.
  2. Replace the assumption_dP36a registry record by a record naming the construction, and update its tokens.
- **Deliverable.** check_frozen_axioms.py requiring holds_exhibited = standard three; updated registry record.
- **Accept.** python3 scripts/check_frozen_axioms.py prints ok; reintroducing 'axiom foo : True' in the exhibit's cone reddens it.
- **Stop if.** The gate cannot distinguish 'no curve axiom' from 'no axiom report' (the parsing bug noted at check_frozen_axioms.py:147).
- **Guidance.** Orchestrator ticket: subagents are not allowed to edit gates. Do it in the same commit as REF.5.

### REF.6 — Real key data at the deployment

ALG · PORT · box 2 h · Sonnet · after REF.4, REF.5

- **Goal.** Give poseidonRender the real commitments, the real delta, the computable codec and params as a function of the SRS trapdoor.
- **Needs.** Instances/PoseidonEnv.lean:189-242 (the five terms), :210 (poseidonVkCodecRoute), header :9-52; Instances/PoseidonV2.lean:152-163 (poseidonRender); Instances/PoseidonValid.lean and PoseidonPins.lean (one reference each to blsGT); Exec/Kzg/Params.lean (ofParams). Reference text: scratch D5_KeyData.lean part 2 and D6_Render.lean.
- **Does NOT need.** The trapdoor's value; the Valid repairs of the generator side; any Exec change.
- **Do.**
  1. Define poseidonFixedCommitments and poseidonPermutationCommitments by decoding vk.json through g1CodecC; gate that all 27 decode.
  2. Set poseidonE := ⟨g1CodecC, poseidonFc, (7 : Fr blsR) ^ (2 ^ 32), false⟩ and add the KAT that it equals 0x08634d0a...89d7.
  3. Define poseidonParamsAt s := ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd s), SrsEncodes s, and poseidonRender as a function of s over G₁z.
  4. Delete poseidonVkCodecRoute and rewrite the PoseidonEnv header (the 'not computable' claim is refuted).
- **Deliverable.** def poseidonRenderAt (s : ZMod blsR) : Render blsR G₁z G2fold G₁z; def SrsEncodes (s : ZMod blsR) : Prop; theorem lowering_equivalence_poseidon_at (s) (hSrs : SrsEncodes s) (product) : LoweringEquivalence (poseidonRenderAt s) product (stated, cone root).
- **Accept.** lake build green; KAT: 27 commitments decode and their EIP encodings equal the payload's fixedComms and permutationComms; falsifier: the same comparison at Array.replicate 19 1 is false; ConeReport root re-pointed.
- **Stop if.** poseidonRenderAt is forced noncomputable by a field other than model's native_decide axiom; or the cone report cannot take a root with a hypothesis.
- **Guidance.** The modelled Rust entry calls params.verifier_params() (test.rs:378), which is ofParams, not read. Keep vk.transcriptRepr imported. For a known-trapdoor bundle, instantiate s and discharge SrsEncodes by native_decide (158 ms in the VM).

### REF.7 — KeyAgrees: the key pins EnvAgrees lacks

ALG · STATEMENT · box 1.5 h · Sonnet · after REF.6

- **Goal.** State, with witness and falsifier, the clauses tying the payload's commitments, omega words, G1/G2 bases and DELTA literal to the Lean key.
- **Needs.** Lowering/Inv.lean:423-446 (vkHeaderBytes, vkG1Words, vkG2Words, slots), :533-579 (EnvAgrees); Generator/Models.lean:94-98, 385-393; Generator/Quotient/FoldCompute.lean:158 (u256String); Exec/Accumulator.lean:461 (frWord). Reference text: scratch D5_KeyData.lean parts 1 and 3.
- **Does NOT need.** Editing the frozen Statements.lean (the Valid integration is the statement area's ticket); the trapdoor.
- **Do.**
  1. Add g1WordsBytes, headerWord? and structure KeyAgrees to Lowering/Inv.lean (refinable) exactly as in D5_KeyData.lean.
  2. Prove poseidon_keyAgrees at the deployment: seven clauses by native_decide in Instances, negSG2 from the hypothesis SrsEncodes s.
  3. Add the two falsifier KATs (19 identities; delta := 2).
- **Deliverable.** structure Midfall.Lowering.KeyAgrees (E) (vk) (PV) (params) (encG2) (frDelta) : Prop with fields fixedWords, permWords, omegaWord, omegaInvWord, g1Base, g2Base, negSG2, delta; theorem poseidon_keyAgrees (s) (h : SrsEncodes s) : KeyAgrees ...
- **Accept.** lake build green; the seven decidable clauses evaluate to true at the deployment (D5.out); falsifiers false; #print axioms poseidon_keyAgrees = standard three plus its native_decide axioms.
- **Stop if.** A clause is not decidable by evaluation at the deployment (other than negSG2).
- **Guidance.** This closes E+1, G-4, H-3 and A-5 on the data side. The omega^3 counterexample of H-3 is excluded by omegaWord. If the statement area prefers the single clause 'generateVk ... = .ok R.plan.vk', that needs a known trapdoor and the g_lagrange export; KeyAgrees is decidable today.

### REF.8 — The reference gate: Lean prepare reproduces Rust's final MSM

ALG · KAT · box 2 h · Sonnet · after REF.1, REF.2, REF.6

- **Goal.** A build-time KAT that runs the tree's verifier (no shims) on proof.bin and agrees with trace.json on challenges, reads, MSM terms and pairing inputs.
- **Needs.** Exec/Native.lean:213-217 (prepare); Exec/Verifier.lean (parseTrace, readAlgebra, linearize); Exec/Kzg/MultiOpen.lean (phaseA, phaseB, phaseC); Exec/Kzg/Msm.lean (split, eval); Conformance/Bundle.lean (parseTrace, Term, Ev); the fixture directory. Reference text: scratch RunLib.lean with the shims removed.
- **Does NOT need.** A pairing; the trapdoor; the conformance executable; the Yul side.
- **Do.**
  1. Create Instances/NativeReplay.lean: load trace.json and instances.json with include_str, take the proof bytes from the read events' wire_hex (or proof_hex once schema 2 lands).
  2. Run the staged path and compare the 10 squeezes by name, the read log, the 1+45 MSM terms and both evals.
  3. Run the unstaged Midfall.Halo2.prepare and require ok with pos = 2640.
  4. Add the falsifier KATs: delta := 2 gives a mismatch at the -G term; proof byte 1008 flipped gives a mismatch.
- **Deliverable.** def Midfall.Instances.NativeReplay.nativeReplay_ok : Bool with '#eval ... -- expect true'; falsifiers nativeReplay_delta2_differs_ok and nativeReplay_mutated_differs_ok.
- **Accept.** lake build Midfall.Instances.NativeReplay green in under 60 s of evaluation; the KAT prints true; kat_gate.py green with the new total; intended outcome: 'dual_msm.right (45 terms)' equal term by term at the commit that contains REF.1 and REF.2.
- **Stop if.** With tree functions only, any compared value differs from trace.json: that is a new fidelity finding; report the first differing item and do not adjust the comparison.
- **Guidance.** Scratch run C took 8.6 s of VM time including the MSM evaluation. Until REF.1 and REF.2 land, the tree's prepare returns PANIC circuit.rs:2084 or Error.opening at this data (RunG.out); do not weaken the gate to pass earlier. Qualify parseTrace (two definitions). Use [i]? on Array G₁z (no Inhabited).

### REF.9 — fpSqrt recovers y from x and the sign bit

ALG · PROOF · box 2.5 h · strongest · after REF.4

- **Goal.** Prove that for a curve point (x, y) with y^2 = x^3 + 4, rootFor x (y == rootFor x true) = y.
- **Needs.** Instances/Bls12_381.lean:39 (fpSqrt), :58 (rootFor); Assumptions/BasePrime.lean (Nat.Prime pBase); mathlib ZMod.euler_criterion or ZMod.pow_card_sub_one_eq_one; pBase % 4 = 3 (Assumptions/Pairing.lean pBaseKats_ok).
- **Does NOT need.** The byte level; G₁z; the torsion theorem.
- **Do.**
  1. Prove fpSqrt_sq : IsSquare a → fpSqrt a * fpSqrt a = a from a^((p+1)/2) = a * a^((p-1)/2).
  2. Prove rootFor_mem : y^2 = x^3 + 4 → rootFor x b = y ∨ rootFor x b = -y, and that rootFor x true ≠ rootFor x false unless the root is 0.
  3. Conclude rootFor_recovers.
- **Deliverable.** theorem Midfall.Instances.rootFor_recovers (x y : Fp) (h : y * y = x * x * x + 4) : rootFor x (y == rootFor x true) = y.
- **Accept.** lake build green; #print axioms = standard three; KAT: the statement evaluated at the 49 non-identity fixture points is true.
- **Stop if.** Less than one third done at 1 h, or the Euler-criterion lemma is not available in this mathlib revision under either name (report the #check output).
- **Guidance.** The y = 0 case needs care: both roots coincide and the lemma still holds. Avoid whnf on the 381-bit exponent; work with the propositional pow lemmas, as G1Agreement.lean does for nsmul.

### REF.10 — The encoder-first compressed law

ALG · PROOF · box 2.5 h · strongest · after REF.9

- **Goal.** Close g1CodecC_compressedEncoderFirst and the width lemma, so every G1CodecLaws field plus the encoder-first law holds at the deployment codec.
- **Needs.** REF.9's rootFor_recovers; g1zOfPair?_g1zPair (REF.4); Instances/Bls12_381.lean:76-131; Common/Bytes.lean (natToBytesBE, bytesToNatBE round trips).
- **Does NOT need.** Any change to the codec definitions; the pairing.
- **Do.**
  1. Prove the byte lemma: for x < pBase, masking byte 0 of natToBytesBE x 48 with 0x1f is the identity and the three flag bits read back.
  2. Prove G1Affine.ofCompressed?_toCompressed for on-curve, canonical, non-identity points, and for the identity.
  3. Assemble g1CodecC_compressedEncoderFirst and (g1zToCompressed Q).size = 48.
- **Deliverable.** theorem g1CodecC_compressedEncoderFirst : ∀ Q : G₁z, g1CodecC.ofCompressed? (g1CodecC.toCompressed Q) = some Q (no sorry); theorem g1zToCompressed_size.
- **Accept.** lake build green; #print axioms = standard three; the sorry registered in REF.4 disappears from SORRY.md.
- **Stop if.** The bit-level proof exceeds the box: fall back to the documented alternative (sign bit defined as decide (y.val > (-y).val), decoder as the inverse of the encoder) and report the trade-off instead of forcing it.
- **Guidance.** x = 0 is rejected by the decoder, but (0, ±2) are not r-torsion, so no carrier element has x = 0 except the identity, which takes the infinity branch. The law is already measured true on 50 fixture points (D4.out).

### REF.11 — Exporter schema 2: test SRS with trapdoor, calldata, mutations, manifest

INFRA · PORT · box 2.5 h · Sonnet · after REF.D

- **Goal.** Make the reference gate and the acceptance gate reproducible from one Rust test run.
- **Needs.** proofs/solidity-verifier/tests/conformance_export.rs (export_poseidon_conformance_bundle, :319-470); tests/m0_poseidon_regen.rs (the EVM leg); proofs/src/poly/kzg/params.rs:98-135 (unsafe_setup draws s first); formal/docs/conformance-schema.md; formal/fixtures/conformance/README.md.
- **Does NOT need.** Any change under proofs/src (no seeded prover); the Lean side.
- **Do.**
  1. Add MIDFALL_CONFORMANCE_SRS=unsafe:<seed>: build params with ParamsKZG::unsafe_setup(K, ChaCha8Rng::seed_from_u64(seed)), recompute s from the same seeded RNG and assert g2 * s == params.s_g2().
  2. Extend params.json (srs_kind, srs_seed, trapdoor_s_be_hex, the 256-byte EIP forms of g2, s_g2, -s_g2, SRS sha256) and trace.json (proof_hex).
  3. Write calldata.bin and evm.json from the same run, and mutations.json (one single-bit mutation per read, plus truncation and a trailing byte, each with the Rust verdict and error class).
  4. Write manifest.sha256 over the bundle; update conformance-schema.md and the stale README.
- **Deliverable.** A second bundle directory formal/fixtures/conformance/poseidon-testsrs/ with vk.json, cs.json, params.json, instances.json, proof.bin, trace.json, calldata.bin, evm.json, mutations.json, manifest.sha256; schema 2 documented.
- **Accept.** cargo test -p halo2_solidity_verifier --features rust-verifier-trace --test conformance_export exits 0 in both SRS modes; trace.json has verdict accept and pairing_check true; sha256sum -c manifest.sha256 passes; the Filecoin bundle's existing fields are byte-identical except for the added keys.
- **Stop if.** The trapdoor cannot be recomputed from the seed without touching proofs/src (the assert g2 * s == s_g2 fails).
- **Guidance.** proof.bin differs between runs because blind_quotient_limbs uses OsRng (prover.rs:126); do not try to fix that here. A bundle is one run, pinned by its manifest. With a new SRS the VK payload and the Halo2VerifyingKey.sol dump change, so this is a second deployment instance (or a replacement, per REF.D decision 3).

### REF.12 — Acceptance gate at the known trapdoor

ALG · KAT · box 1.5 h · Sonnet · after REF.8, REF.11

- **Goal.** Show the Lean verifier accepts a Rust-generated proof outright and rejects each mutation with the Rust error class.
- **Needs.** Exec/Native.lean:221-232 (verifyNative); REF.6's poseidonParamsAt and SrsEncodes; the poseidon-testsrs bundle; scratch D6_Render.lean (check_iff_g1).
- **Does NOT need.** A pairing implementation; the Yul side; the Filecoin bundle.
- **Do.**
  1. Instantiate the deployment terms on the test-SRS bundle with s read from params.json.
  2. Prove srsEncodes_fixture : SrsEncodes s by native_decide and the KAT verifyNative ... = .ok ().
  3. Replay mutations.json: each mutated proof must give the recorded verdict class.
- **Deliverable.** theorem srsEncodes_testSrs; KAT verifyNative_accepts_rust_proof_ok; KAT verifyNative_mutations_ok.
- **Accept.** lake build green; both KATs true; falsifier: at trapdoor s + 1 verifyNative returns Error.opening. Intended outcome: acceptance occurs at DualMSM.check with the exported trapdoor.
- **Stop if.** verifyNative rejects the honest proof at the exported trapdoor: report left.eval, right.eval and s; this would be a new divergence in the final check or in the exporter.
- **Guidance.** DualMSM.check at the constructed pairing is s • left = right in G₁z (check_iff_g1, proved in scratch); it took about 3 s in the VM at a wrong trapdoor. This KAT is also the LeanAccepts witness the D-P45 non-vacuity gate needs.

### REF.13 — Probe: snapshotOf against Rust's intermediate values

ALG · PROBE · box 1 h · Sonnet · after REF.8

- **Goal.** Measure whether Lowering/Snapshot.lean's snapshotOf returns ok at the real model and whether its fields equal the 137 solidity_trace entries.
- **Needs.** Lowering/Snapshot.lean (snapshotOf, steps); trace.json solidity_trace (names l_last, l_blind, l_0, quotient_identity_eval, linearization_expected_eval, f_eval, v, final_com, pcs_q_com, pcs_point_set, pairing_lhs, pairing_rhs).
- **Does NOT need.** Any block proof; any change to Snapshot or Inv.
- **Do.**
  1. Evaluate snapshotOf at the REF.6 terms on the fixture messages.
  2. Compare each snapshot field that has a named trace entry; list the fields with no trace counterpart and the entries with no snapshot field.
- **Deliverable.** A report table: field, snapshot value, trace value, agree or differ; the command that produced it.
- **Accept.** The report has the measured values and commands; no code merged.
- **Stop if.** snapshotOf is not ok: report the fault and stop (the block contracts are stated against it).
- **Guidance.** The MSM agreement already implies v, f_eval and final_com agree inside multiPrepare; this probe is about the snapshot's own bookkeeping, which the block contracts read.

### REF.14 — Probe: the calldata leg at the real codec

ALG · PROBE · box 1 h · Sonnet · after REF.6, REF.11

- **Goal.** Measure whether Lean's repackThenEncode on proof.bin equals the Rust/EVM calldata.bin, and whether decodeCalldata followed by msgWire gives back proof.bin.
- **Needs.** Lowering/Calldata.lean:257 (repackThenEncode), decodeCalldata; LoweringV2/Statements.lean:263-267 (LeanAccepts), :335-340 (the frozen calldataOf, which repacks twice); calldata.bin from REF.11; the plan's proofLayout.
- **Does NOT need.** Any proof; the Yul side.
- **Do.**
  1. Evaluate repackThenEncode at g1CodecC and the deployment layout on proof.bin; compare with calldata.bin byte for byte.
  2. Evaluate decodeCalldata on calldata.bin; re-serialise the messages with msgWire and compare with proof.bin.
- **Deliverable.** A report with both comparisons (equal, or the first differing offset) and the commands.
- **Accept.** The report has the measured values; no code merged.
- **Stop if.** The deployment proofLayout is still the unrepaired one (proofLen 4224 against the deployed 4320): report that and stop, the layout repair belongs to the program/Valid area.
- **Guidance.** This was not run in this design pass. It becomes meaningful only after the Valid.layout repair and the calldata export.


---

## M2 — the object  (waits for: D-P65, D-P67; 18 cards, 31.5 box-hours)

### OBJ.0 — Object decisions: the scope, and `ValidV3`  **[DONE — signed 2026-11-17]**

> **Do not run.** D-P65 and D-P67 were signed by the human on 2026-11-17 (after `53bf8c1`) and are recorded in `design.md` with their conditions. What remains of this card is those conditions, which the cards that name each decision apply.

DECISION · DECISION · box 0.5 h · orchestrator + human · after PL.0 or earlier

- **Goal.** The human signs or strikes D-P65 and D-P67 of PLAN-V3 §2.2, and `design.md` quotes the sign-off
  (who, when, where) under those numbers.
- **Needs.** PLAN-V3 §2.1 (how the signed D-P45–D-P59 relate) and §2.2 (the row text, its
  recommendation and its "if struck" consequence); the evidence named in PLAN-V3 §3 for that row,
  re-run at the tip with `bash docs/plans/V3-evidence/check.sh`.
- **Does NOT need.** Any Lean change. The orchestrator does not decide (W2, D-P53).
- **Do.**
  1. Draft the row in `docs/DECISIONS-PENDING.md` (new items go at the end, unsigned), quoting
     PLAN-V3 §2.2 verbatim and linking the evidence output.
  2. Mark every card that names the row BLOCKED until it is signed.
  3. On sign-off, record it in `design.md`; on a strike, apply the "if struck" line of §2.2 and
     re-plan the cards that named the row.
- **Deliverable.** The `design.md` entry or entries, with sign-off lines.
- **Accept.** `design.md` contains each numbered entry with a W2 sign-off line; no `.lean` file
  changed; `git diff --stat` shows `formal/docs/` only.
- **Stop if.** The evidence for the row no longer typechecks at the tip: re-measure before asking
  for a signature.
- **Guidance.** D-P65 is urgent: it must be signed before the G1.1–G1.3 batch (D-P52) merges G1.2. D-P67 waits for OBJ.7.

### OBJ.1 — Land the Yul token parser with its round-trip KATs

INFRA · KAT · box 1.5 h · Sonnet · after —

- **Goal.** A total parser from the yulTokens stream to the vendored AST, usable in statements and by native_decide.
- **Needs.** Scratch Parse1.lean (namespace Midfall.Lowering.YulParse, 120 lines); Midfall/Generator/YulGolden.lean yulTokens; vendored EVM.mkCall, SyntaxEq.stmtsBeq; poseidonM, poseidonPv from Instances/PoseidonValid.lean:90-91.
- **Does NOT need.** Any emitter change; any frozen file; Yul semantics.
- **Do.**
  1. Create formal/Midfall/Lowering/YulParse.lean from the scratch namespace (parseExpr, parseArgs, parseStmts, parseBlock, parseCases, parseStmt, parseTokens, parseLines)
  2. Create Instances KAT file with: whole main block round trip, guard round trip, stmtsBeq of each existing emitter against the parse of its region
  3. Add a negative KAT: a token stream with an unbalanced brace returns none
- **Deliverable.** def YulParse.parseTokens : List String → Option (Block EVM.Op); def YulParse.parseLines : List String → Option (Block EVM.Op); KATs parse_main_roundTrip_ok, parse_guard_roundTrip_ok, emitters_areTheParse_ok.
- **Accept.** `#eval` prints "parsed stmts=74 roundTrip=true tokens=14054" and "parsed stmts=1 roundTrip=true tokens=52"; seven emitter rows print stmtsBeq=true and pcs prints stmts=1/225 stmtsBeq=false (expected until OBJ.2); kat_gate total rises by the number of new lines; verify.sh --quick green.
- **Stop if.** The round trip fails at the merge commit (the text changed): report the first failing token index instead of patching the grammar.
- **Guidance.** Fuel is structural (toks.length + 1) so the functions are total and kernel-acceptable. `![..]` is matrix notation here: write `!([..].contains t)`. Tokens `:=` and `->` arrive split as `:` `=` and `-` `>`. String literals are not supported and none occur after the six-token header drop.

### OBJ.2 — Complete the program: accumulator helpers, quotient region, pcs scopes

GEN · EMIT · box 2.5 h · strongest · after OBJ.0, OBJ.1

- **Goal.** mainAsmRaw produces all 14054 tokens / 74 statements, so codegen is true at the fixture.
- **Needs.** Program.lean:98-99, :114-116, :120-121, :125-126, :132-134, :190-194 (frozen, re-hash by the orchestrator); GenAstDispatch.lean:131-135 and :188-196; renderAccumulatorHelpers, renderQuotientHelpers, renderQuotientNumeratorBlock (VerifierPartials.lean); scratch Parse1.lean namespace V3.
- **Does NOT need.** Structured emitters for the three regions (OBJ.13 to OBJ.15); WP-G3/G4; block contracts.
- **Do.**
  1. GenAst.emitAccumulatorHelpers, emitQuotientHelpers, emitQuotientNumerator (c : PartialCtx) as parseLines of the corresponding render, [] on none
  2. emitPcsFromPlan returns [Stmt.block (blocks.map Stmt.block)]; repair the five pcs gates in GenAstDispatch.lean (:251, :276, :376, :397, :431) in the same commit
  3. GenAst.emitPartialM / emitSlicesM; mainAsmRaw pv m, helpersOf, sliceOf as in the memo; bridge lemmas emitPartialM pv c q = emitPartial pv q for the five unchanged partials
  4. Restate emitSlices_eq for emitSlicesM
  5. Replace deciding_codegen (PoseidonValid.lean:276) by the positive; update the header table
- **Deliverable.** The three emitters, emitPartialM, the edited Program.lean, theorem deciding_codegen : codegenAgrees poseidonPv poseidonM = true, theorem deciding_codegenStruct.
- **Accept.** `codegenAgrees poseidonPv poseidonM` prints true; `codegenStruct (mainAsmRaw poseidonPv poseidonM) poseidonM` prints true; `(mainAsmRaw poseidonPv poseidonM).length` = 74; slice lengths [1, 44, 3, 4, 1, 2, 3]; FALSIFIERS, one per region, each must print false: 0x20 to 0x21 in the AccumulatorHelpers text, shl(224, 0x3cc81b89) to ...8a in QuotientHelpers, 0x20 to 0x21 in the numerator text, one pcs block boundary moved; mainClosed still true; noWritersFuel 20000 true; closureNamedExceptions and gate 59 still green.
- **Stop if.** A region's parse returns none; the non-brace pcs equality (3571) no longer holds; more than 2.5 h.
- **Guidance.** A mutation whose first hit is in a comment does not redden (measured): mutate a code token. Do not append the accumulator helpers to emitHelpers (gate 51 pins its eight names). The parse stand-ins make the region an opaque function of text: fine for per-deployment proofs, not for generic-in-R proofs.

### OBJ.3 — Scope is the hoist of the whole program

> **SUPERSEDED by ST.3.** This card's scope (`[hoist (R.prog 0 0)]`) was compiled against the block files and breaks `fail_lookup := rfl`; PLAN-V3 takes `[hoist helpers ++ hoist slices]` (D-P65). Do not run this card.

SEM · STATEMENT · box 1.5 h · Sonnet · after OBJ.2

- **Goal.** Blocks run in a function scope that contains q_program_fail and q_pow5, and the decomposition lemmas are true again.
- **Needs.** Statements.lean:109-110 (frozen); Blocks.lean:206-225 and :276-285 (prog_slices_decomp, runBody_iff_slices); hoist_prog_addr_indep (sorried).
- **Does NOT need.** Any block proof; the quotient contract.
- **Do.**
  1. Render.scope := [hoist D (R.prog 0 0)]
  2. Restate prog_slices_decomp conjunct 2 as hoist D (R.prog a b) = hoist D (R.prog 0 0) and conjunct 1 with the new helper block
  3. Add a KAT at the fixture: the hoisted names are the 15 of the text, in order
  4. Re-check that the closed TraceReturn contracts still compile
- **Deliverable.** Edited Render.scope; restated prog_slices_decomp; KAT scope_names_ok.
- **Accept.** KAT prints the 15 names; `#cone_sorries tr_blockProgress` still 0; FALSIFIER: with the old scope ([hoist D R.helpers]) the KAT `lookupFun` of "q_pow5" returns none - keep it as a negative example.
- **Stop if.** The TraceReturn proofs break for a reason other than the scope name (report the first failing lemma).
- **Guidance.** hoist is a filterMap over top-level statements, so funDefs inside nested scopes are not hoisted; the quotient functions are top-level in the main block (text indices 3813 and 3836). Wrapper locals do not affect hoist, which is why 0 0 is harmless.

### OBJ.4 — One constants-coherence clause and its generic lookup lemmas

GEN · STATEMENT · box 2 h · Sonnet · after OBJ.2

- **Goal.** Replace the pin-by-pin facts by constsCoherent and derive every table lookup the blocks need for every valid render.
- **Needs.** Scratch Consts2.lean; Statements.lean:136-168 and :212-217 (pins, to be deleted under the PLAN-V3 §2.2 decision (D-P65/D-P67)); Blocks/VkLoading.lean section 5, Blocks/TraceReturn.lean:217-218 (consumers).
- **Does NOT need.** The generator port; G2 or G1 base pins (key coherence, other area).
- **Do.**
  1. Create formal/Midfall/LoweringV2/Consts.lean with cAddr, expectedConsts, constLinesLiteral, progConstNames, constsCoherent, consts_lookup_of_coherent
  2. Prove the lookup lemmas for VK_MPTR, EXPECTED_VK_PAYLOAD_LENGTH, EXPECTED_VK_LENGTH, EXPECTED_VK_CODEHASH_WORD, RETURN_MPTR, TRANSCRIPT_MPTR, NUM_INSTANCE_CPTR, FR_MODULUS with the six-line script of ObjectV3Full
  3. Rewire vk_blockRow and the TraceReturn row to the lemmas
- **Deliverable.** def expectedConsts (pv : PlanView) (m : Model) : List (String × Nat); def constsCoherent (pv : PlanView) (m : Model) : Bool; eight lookup theorems.
- **Accept.** `constsCoherent poseidonPv poseidonM` prints true with (90, 90); FALSIFIERS print false: transcriptMptr + 32 in the plan view, proofEnd + 32, model verifierReturnMptr := 0x80; `#print axioms` of each lookup lemma = the standard three; SORRY.md unchanged or smaller.
- **Stop if.** A constant line of the render is not a literal (constLinesLiteral false): that is a finding about the port's printer.
- **Guidance.** The 14 literal entries are template literals; do not derive them. A number that only the model carries (smoke gas, accumulator MSM gas) is rendered and expected from the same field, so it cannot be falsified here; say so in the docstring. `.Nodup` is a Prop: wrap in decide when printing.

### OBJ.5 — Object fingerprint KAT

INFRA · KAT · box 0.75 h · Sonnet · after OBJ.2

- **Goal.** Any edit that changes the program the headline is about reddens a gate, since Frozen.sha256 does not pin the emitters.
- **Needs.** asmOf poseidonPv poseidonM 0 0; keccak256 (extern); checks.sh.
- **Does NOT need.** A hash of the import closure.
- **Do.**
  1. KAT: token count of EVM.print (asmOf ...) and keccak256 of the printed string, pinned as literals
  2. Record the two values in design.md under the PLAN-V3 §2.2 decision (D-P65/D-P67)
- **Deliverable.** theorem object_fingerprint : (tokens.length, keccak) = (literal, literal) by native_decide.
- **Accept.** KAT green; FALSIFIER: changing one literal in GenAst.emitQuotientLinAt reddens it while Frozen.sha256 stays green.
- **Stop if.** Printing the inlined program exceeds 60 s.
- **Guidance.** Pin the inlined program, not mainAsmRaw: the constant table is part of the object.

### OBJ.6 — Port the quotient glue of LoweringPlan::new

GEN · PORT · box 2.5 h · strongest · after —

- **Goal.** The six missing quotient.rs functions exist in the tree with KATs against Rust-produced data.
- **Needs.** proofs/solidity-verifier/src/lowering/quotient.rs:165-181, :189-238, :259-311, :314-323, :1402-1465, :425-527, :2101-2147; quotient_numerator/vm/mod.rs:442-470 (validate_execution_manifest); scratch ObjectV3Full.lean namespace Midfall.Generator.PlanNew; cs.json via PoseidonFixture.poseidonCs; the payload words of poseidonVkGen.
- **Does NOT need.** generate_base_vk; the constructor; any frozen file.
- **Do.**
  1. Create formal/Midfall/Generator/PlanNew.lean with frFieldCtx, quotientProgramPlan (including validate_execution_manifest), buildQuotientProgramItemsWithLimbOps, nativeCallbackScratchWords, quotientStackWordsForBuild, quotientOpcodeUsage, quotientMemUsage, quotientTemplateProgram, compactQuotientProgramFor
  2. KATs at the fixture against the payload and against quotientDeployedProgram
  3. Correct the stale docstrings that call compact_quotient_computation_blocks unported (LoweringPlan.lean:49-51, :75-77)
- **Deliverable.** The nine definitions; KATs quotientBuild_matchesPayload_ok, quotientProgram_matchesTypedIn_ok, quotientPlan_shape_ok.
- **Accept.** KATs print: len=88 consts=1 maxStack=2 constsEqPayload=true programEqPayload=true; all twelve program fields equal; plan shape inline=4 items=9 native=3 perm=7 lookup=3 tail=1 maxPower=21; FALSIFIER: defaultHybridQuotientInlineIdentities := 3 in a local copy changes the program bytes (programEqPayload=false).
- **Stop if.** validate_execution_manifest needs types not in VmTypes.lean (name them); more than 2.5 h (then split manifest validation into its own card).
- **Guidance.** `data` and `show` cannot be binder names here. The identity expression is identity.expr (quotient.rs:972). native_gate_indices indexes into the gates AFTER the inline prefix. powNat may be b ^ e. Port rules R1-R11 apply: cite the Rust line on every def.

### OBJ.7 — LoweringPlan.newFromVk, compactBlocksOf, generateAll

GEN · PORT · box 2 h · strongest · after OBJ.6

- **Goal.** The generator runs end to end in Lean from a constraint system, a configuration and a payload.
- **Needs.** plan.rs:235-329 and :381-394; artifacts.rs:337-339; Vk.lean:1049 metaDataForStableStaticLayout, :992 memoryLayoutFor; LoweringPlan.lean:534 validateGeneratorInvariants; VmCertify.lean:651; scratch ObjectV3Full.lean (newFromVk, vkCarriesBuild, compactBlocksOf, GenOut, generateAll).
- **Does NOT need.** generate_base_vk; Render; any frozen file.
- **Do.**
  1. Refactor metaDataForStableStaticLayout, metaDataForVk, memoryLayoutFor, staticWorkingMemorySizeForMeta to take (meta_, numInstances) instead of VerifierBuildInputs, keeping wrappers
  2. Add newFromVk, compactBlocksOf to PlanNew.lean; GenOut and generateAll to a new LoweringV2/Generated.lean
  3. KATs at the fixture: plan fields, invariants, certification, text
- **Deliverable.** def PlanNew.newFromVk; def PlanNew.compactBlocksOf; structure GenOut; def generateAll : Features → Fr p → VerifyingKey (Fr p) G₁ → GeneratorConfig → Halo2VerifyingKey → ArtifactBuildInputs → RenderFlags → Except Fault GenOut.
- **Accept.** KAT prints: ok, text differs from the Rust artifact in 1 line (BUILD_ID), len 175908/175908, proofLen=4320, vkMptr=10496; invariants OK; certify OK; FALSIFIERS: delta := 2 gives 3 differing lines; one flipped quotient_program word gives PANIC vk.rs:457; payload without reservation fields gives PANIC quotient.rs:204.
- **Stop if.** The refactor of the Vk.lean signatures breaks more than the four VkKats that call them.
- **Guidance.** The payload parsed by vkModelFromArtifact lacks the four reservation fields; fill them with VkPayloadLayout.forVk (31, 1, 32, 3 at the fixture). Compare plans by render or field, never whole (no BEq). The typed-in quotientStackWords 24 is wrong; the derived value is 25.

### OBJ.8 — State ValidV3 on the frozen surface and rebuild the fixture render from the generator

GEN · STATEMENT · box 2.5 h · strongest · after OBJ.0, OBJ.3, OBJ.4, OBJ.7

- **Goal.** Render.Valid is the seven-clause ValidV3 and poseidonRender's plan, qblocks and model are projections of generateAll.
- **Needs.** Statements.lean:136-217 (frozen); Blocks.lean uses of hR.vkPins, hR.transcriptMptr, hR.circuitMeta; Instances/PoseidonV2.lean:101-114 (poseidonModelVal); PoseidonEnv.lean:230 (delta := 2); scratch definitions Render.GeneratedBy, PayloadAgrees, programOk, ValidV3, Except.getOk.
- **Does NOT need.** Proofs of env, payload, supported (other areas own the key and the WellFormed repair).
- **Do.**
  1. Add Except.getOk / eq_ok_getOk to a Common file
  2. Set poseidonE.delta to the field constant with a KAT against 0x08634d0a...89d7
  3. poseidonGen := generateAll ...; poseidonRender.plan/qblocks/model := projections of poseidonGen.getOk
  4. Replace Render.Valid by the seven clauses; delete vkPins and vkProgressPins; adapt Blocks.lean consumers through the OBJ.4 lemmas
  5. Re-run the clause table in PoseidonValid.lean
- **Deliverable.** structure Render.ValidV3 (named Render.Valid on the surface); def Render.generated; def Render.GeneratedBy; structure PayloadAgrees; the rebuilt poseidonRender; a seven-row table.
- **Accept.** lake build green; Frozen.sha256 re-hashed once; table: generated PROVED, inputs PROVED, program PROVED, noWriters PROVED, env as before, payload scalar half PROVED by computation with the point half OPEN, supported REFUTED only through wf.permutationCommitmentsMatch; poseidonRender_notValid, if it still holds, runs through supported only; FALSIFIER: with delta := 2 restored, the generated clause is refuted (text differs in 3 lines).
- **Stop if.** A Blocks.lean lemma needs a fact that neither ValidV3 nor an OBJ.4 lemma gives: record it as one row, do not add a pin.
- **Guidance.** GeneratedBy is proved by construction: R.generated = .ok (gen.getOk h) with h : gen.isOk = true by native_decide, then the three equalities are rfl. poseidonRender is noncomputable; go through `show` at the computable faces as PoseidonValid.lean does. The frozen docstrings at :66-70, :179-185, :203-205 must be corrected in the same re-hash.

### OBJ.9 — Prove the decidable half of ValidV3 at the fixture

GEN · PROOF · box 2 h · Sonnet · after OBJ.8

- **Goal.** The four generator and program clauses are theorems at poseidonRender without sorryAx.
- **Needs.** OBJ.8's table; programOk; noWritersFuel; Instances/PoseidonValid.lean.
- **Does NOT need.** env, payload point half, supported.
- **Do.**
  1. poseidonValid_generated via Except.eq_ok_getOk
  2. poseidonValid_inputs (existing proof)
  3. poseidonValid_program by native_decide on programOk poseidonPv poseidonM
  4. poseidonValid_noWriters at fuel 20000
  5. Scalar half of PayloadAgrees (eight facts) by native_decide
- **Deliverable.** Five theorems in Instances/PoseidonValid.lean.
- **Accept.** `#print axioms` of each lists no sorryAx; each native_decide adds exactly one `._native.native_decide.ax_1_1` axiom, listed in the report; cone_sorries of poseidon_valid reported before and after.
- **Stop if.** native_decide on programOk exceeds 60 s: split the Bool into its five conjuncts.
- **Guidance.** The interpreted evaluation of programOkWith took about 10 s in scratch. Do not rfl or decide over the program.

### OBJ.10 — Split generateVk into base and reservation loop; data-level base payload

GEN · PORT · box 2.5 h · Sonnet · after OBJ.6

- **Goal.** The quotient sections and the four reservation fields of the payload are computed by the ported loop from a base payload, and the base payload is a function of exported key data.
- **Needs.** Vk.lean:1093-1207 generateVk; Vk.lean:758-878 generateBaseVk (header builder and commitment vectors); Instances/Bls12_381.lean G1Affine.ofCompressed? and toEip; vk.json, params.json.
- **Does NOT need.** The SRS asserts of generate_base_vk (vk.rs:151, :180, :189): they need the prover SRS and a pairing; they stay Rust-side and are recorded as trusted key generation.
- **Do.**
  1. generateVkFromBase feat env base := the body of generateVk after its first line; generateVk := generateBaseVk >>= generateVkFromBase
  2. Instantiate VkBuildEnv with VerifierMemoryLayout.new and OBJ.6's three functions
  3. baseVkOfKeyData: header scalars from the domain, G1 words from decompressed points, G2 words from exported EIP words
  4. KAT: generateVkFromBase on the 31-word base reproduces the 35 constants and (some 31, 1, some 32, 3)
- **Deliverable.** def generateVkFromBase; def baseVkOfKeyData; KAT vkFromBase_matchesPayload_ok.
- **Accept.** KAT true; renderHalo2VerifyingKey of the result equals the tracked file for every line not carrying a G2 word, and for all lines once OBJ.11 exports the G2 words; FALSIFIER: one commitment byte changed in vk.json reddens it.
- **Stop if.** The reservation loop does not settle within 8 iterations at the fixture (vk.rs:396): report the two reservation sequences.
- **Guidance.** Not measured: that the loop converges from the bare header to the artifact (only the fixed point was checked: constants and program equal the payload). That is this card's first experiment. The identity commitments (payload indices 8, 10, 11, 12, 14, 16) decode and encode to 128 zero bytes.

### OBJ.11 — Export the remaining generator inputs from Rust and re-export the dump

INFRA · PORT · box 2 h · Sonnet · after —

- **Goal.** Every input of the Lean generator is a tracked file exported by a Rust test, and the tracked dump is the output of the same run.
- **Needs.** proofs/solidity-verifier/tests/conformance_export.rs and tests/poseidon_fixture.rs; artifacts.rs:117-141 (BUILD_ID preimage); build.rs (SOLIDITY_VERIFIER_FEATURES); QUEUE R.5.
- **Does NOT need.** Any Lean proof; a new proof.bin.
- **Do.**
  1. Export build.json: srs_fingerprint hex, features string, provenance tag
  2. Add g2_eip_hex, neg_s_g2_eip_hex (16 words) and g1_eip_hex to params.json
  3. Regenerate target/poseidon-fixture-dump/*.sol in the same test and commit both
  4. Add a CI step that re-renders and runs git diff --exit-code on the dump
- **Deliverable.** formal/fixtures/conformance/poseidon/build.json; extended params.json; regenerated dump; CI step.
- **Accept.** The Rust test passes twice in a row with an empty git diff on the .sol files; Lean buildIdOf on the exported inputs equals the BUILD_ID line of the regenerated dump (KAT).
- **Stop if.** The .sol render is not deterministic across two runs (name the differing line).
- **Guidance.** Needs a human decision under R.5 because it rewrites tracked fixtures and runs cargo; this designer ran no cargo. The committed dump's BUILD_ID does not reproduce from a fresh render (recorded in QUEUE R.5).

### OBJ.12 — The artifact gate: both files byte for byte, nothing from the artifact

GEN · KAT · box 2 h · Sonnet · after OBJ.7, OBJ.10, OBJ.11

- **Goal.** The Lean generator, run on the exported inputs, prints the Rust-generated Halo2Verifier.sol and Halo2VerifyingKey.sol exactly.
- **Needs.** generateAll; generateVkFromBase; baseVkOfKeyData; the four fixture json files; include_str of the two dump files.
- **Does NOT need.** Render; any proof.
- **Do.**
  1. artifact_gate_poseidon as in the memo, by native_decide in Instances/
  2. Delete or demote to negative examples: quotientDeployedCtx, poseidonBlocks, quotientDeployedProgram, poseidonLayoutConfig, poseidonVkMptr, poseidonProofLayout, poseidonDerivedParts, vkModelFromArtifact as an input
  3. Add the gate to the definition of done
- **Deliverable.** theorem artifact_gate_poseidon; a grep gate that no definition reachable from poseidonRender reads the two dump strings.
- **Accept.** Gate true with 175908 bytes / 3024 lines and the VK file's 26018 bytes / 271 lines; `#cone_in` or a grep shows poseidonVerifierDump and poseidonVkDump are used only by the gate; FALSIFIER: one byte changed in cs.json reddens it.
- **Stop if.** A difference other than BUILD_ID appears after OBJ.11: it is a port or export finding, report the first differing line.
- **Guidance.** Until OBJ.11 lands the interim gate is: all lines of Halo2Verifier.sol but line 275, with the payload as input. Keep the two gates distinct in STATUS so the interim one is not reported as the final one.

### OBJ.13 — Structured emitter for AccumulatorHelpers

GEN · EMIT · box 2 h · Sonnet · after OBJ.2

- **Goal.** Replace the parse stand-in by an AST emitter built with the constructor helpers, when a proof needs the structure (accumulator mode, X1).
- **Needs.** templates/partials/verifier/AccumulatorHelpers.yul; GenAst.lean:185-225 constructor helpers; the parse of the region as reference.
- **Does NOT need.** validate_public_accumulator for the fixture (absent at accumulator off); any contract.
- **Do.**
  1. Five functions in template order; the sixth under pv.hasAccumulator
  2. Acceptance against the parse, per function and whole region
- **Deliverable.** def GenAst.emitAccumulatorHelpersA (c : PartialCtx) : Block Op.
- **Accept.** stmtsBeq against parseLines of the render prints true at the fixture (823 tokens) and at expectedHasAccumulator := true (1181 tokens); FALSIFIER: a one-literal change in any of the five functions prints false.
- **Stop if.** A value the region interpolates is not a PartialCtx field.
- **Guidance.** Optional before X1: no slice of the fixture calls these functions except each other (callee inventory), so no first-headline proof needs their structure.

### OBJ.14 — Structured emitter for QuotientHelpers

GEN · EMIT · box 0.75 h · Sonnet · after OBJ.2

- **Goal.** q_program_fail, q_pow5 and the two limb7 arms as AST under their flags.
- **Needs.** templates/partials/quotient_numerator/QuotientHelpers.yul; c.quotientPow5Helper, quotientLimb7Helper, quotientWideLimb7Helper, limb7YulCoeffs, wideLimb7YulCoeffs.
- **Does NOT need.** The numerator block.
- **Do.**
  1. Emit under the three flags
  2. Acceptance against the parse at the fixture and at a context with all three flags on
- **Deliverable.** def GenAst.emitQuotientHelpersA (c : PartialCtx) : Block Op.
- **Accept.** stmtsBeq true at the fixture (68 tokens: 23 + 45) and at the all-flags context; FALSIFIER: shl(224, ...) literal changed prints false; mulmod(x2, x2, q_r) to mulmod(x2, x, q_r) prints false.
- **Stop if.** The coefficient tables are strings that do not parse as literals.
- **Guidance.** The first 0x3cc81b89 in the template is in a comment.

### OBJ.15 — Structured emitter for the QVM interpreter template

GEN · EMIT · box 2.5 h · Sonnet · after OBJ.2

- **Goal.** The 953 template tokens of the numerator block as an AST function of QuotientProgram, with the six line families spliced by parseLines.
- **Needs.** templates/partials/quotient_numerator/QuotientNumeratorBlock.yul; VerifierPartials.lean:1266-1979; QuotientProgram fields; the parse of the region as reference.
- **Does NOT need.** AST twins of the block producers; the external, direct, probe and trace arms.
- **Do.**
  1. Split first: prologue and registers; opcode switch arms; native callbacks; epilogue and selector tails. One card each if the box is blown
  2. Acceptance against the parse at the fixture and at a synthetic context with every opUsage flag on
- **Deliverable.** def GenAst.emitQuotientNumeratorA (c : PartialCtx) : Block Op.
- **Accept.** stmtsBeq true at the fixture (6384 tokens for the region); stmtsBeq true at the all-arms context; FALSIFIER: one guard constant changed prints false; one family's lines dropped prints false.
- **Stop if.** More than 2.5 h on the opcode arms: stop and report which arms are done; the stand-in remains valid.
- **Guidance.** Only 10 of 31 opcode arms render at the fixture; the all-arms context is what tests the rest, and the text port renders all arms. This card is needed only by the proof of the quotient block; issue it when that proof's design asks for the interpreter's structure.

### OBJ.16 — Probe: does the port reproduce the three other in-scope fixtures

GEN · PROBE · box 1 h · Sonnet · after OBJ.7

- **Goal.** Measure port fidelity beyond one circuit before any generic claim.
- **Needs.** target/hybrid-mt-fixture-dump, rsa-signature-fixture-dump, sha-preimage-fixture-dump (tracked; all accumulator off, embedded VM, separate VK); the export test of the poseidon fixture.
- **Does NOT need.** Proofs; the accumulator or external-evaluator dumps.
- **Do.**
  1. List what must be exported per fixture (cs.json, vk.json)
  2. If exports exist or are cheap, run generateAll and count differing lines per fixture
- **Deliverable.** A table: fixture, k, instances, differing lines, first differing line.
- **Accept.** Every row cites a command output; a nonzero row is a finding with its line, not a fix.
- **Stop if.** Exports need cargo runs not yet approved: deliver the list only.
- **Guidance.** These circuits exercise limb shapes and opcode arms the poseidon fixture does not (pow5 unused in its VM program, foldMain false).

### OBJ.17 — Name the target: fixture F1

> The naming clause is signed (D-P60). This card is the docs edit that applies it.

DECISION · DECISION · box 0.5 h · orchestrator + human · after —

- **Goal.** The human signs or strikes the naming clause of D-P60 of PLAN-V3 §2.2, and `design.md` quotes the sign-off
  (who, when, where) under those numbers.
- **Needs.** PLAN-V3 §2.1 (how the signed D-P45–D-P59 relate) and §2.2 (the row text, its
  recommendation and its "if struck" consequence); the evidence named in PLAN-V3 §3 for that row,
  re-run at the tip with `bash docs/plans/V3-evidence/check.sh`.
- **Does NOT need.** Any Lean change. The orchestrator does not decide (W2, D-P53).
- **Do.**
  1. Draft the row in `docs/DECISIONS-PENDING.md` (new items go at the end, unsigned), quoting
     PLAN-V3 §2.2 verbatim and linking the evidence output.
  2. Mark every card that names the row BLOCKED until it is signed.
  3. On sign-off, record it in `design.md`; on a strike, apply the "if struck" line of §2.2 and
     re-plan the cards that named the row.
- **Deliverable.** The `design.md` entry or entries, with sign-off lines.
- **Accept.** `design.md` contains each numbered entry with a W2 sign-off line; no `.lean` file
  changed; `git diff --stat` shows `formal/docs/` only.
- **Stop if.** The evidence for the row no longer typechecks at the tip: re-measure before asking
  for a signature.
- **Guidance.** Docs only: "fixture F1" replaces "the deployment" / "deployed render" in STATUS, PLAN and new docstrings; `DeployedProfile.lean` keeps its file name until a card touches it.

---

## M3 — the statement surface  (waits for: D-P64, D-P66; 18 cards, 37 box-hours)

### ST.1 — Land the V3 staging module, its deployment file and the falsifiers (no frozen edit)

INFRA · STATEMENT · box 1.5 h · Sonnet · after —

- **Goal.** Put the V3 text, its deployment measurements and the refutations of the frozen text under version control and CI before any frozen file is touched, so sign-off is given on compiled text and the falsifiers become permanent regression facts.
- **Needs.** The three scratch files StatementsV3.lean, StatementsV3Deploy.lean, StatementsV3Falsifiers.lean (sha256 0fa92f2b.., fc09d5d9.., 95f65c9c..). Target paths: formal/Midfall/LoweringV3/Statements.lean, formal/Midfall/Instances/StatementsV3Deploy.lean, formal/Midfall/Instances/StatementsV3Falsifiers.lean. formal/Midfall.lean import list; formal/SORRY.md; the KAT total pin.
- **Does NOT need.** Any edit to LoweringV2/Statements.lean, Program.lean, Shared.lean or Frozen.sha256. Any proof. Any decision.
- **Do.**
  1. Copy the three files; change `import StatementsV3` to `import Midfall.LoweringV3.Statements`; add the three modules to Midfall.lean.
  2. Register the four sorries (prog_slices_decompV3, twoOutcomes_of_exitDiscipline, scans_prog_addr_indep, runBody_mono) in SORRY.md with the discharge experiment each docstring gives.
  3. Update the KAT pin by the number of new `#eval .. -- expect` lines and annotate each with its expected value.
  4. Run scripts/verify.sh --quick.
- **Deliverable.** Three modules in the tree: namespaces Midfall.LoweringV3, Midfall.LoweringV3.Deploy, Midfall.LoweringV3.Falsifiers, with the declarations listed in the memo.
- **Accept.** `lake build Midfall.LoweringV3.Statements Midfall.Instances.StatementsV3Deploy Midfall.Instances.StatementsV3Falsifiers` green. Printed values equal the measurements: `true`/`false` (calldata), `("today", true, false, false, 4224, 4320)`, `("faithful", false, true, true, 4320, 4320)`, `(10496, 10496, 3, 48, 0, true, false)`. `#print axioms lowering_equivalenceV3_of` and `lawsV3_satisfiable_at_G1z` show `[propext, Classical.choice, Quot.sound]`. `#print axioms rejects_of_not_accepts_contradiction` shows sorryAx. Falsifier of the ticket: changing `planFaithful` to `setNumPointSets 2` turns the second tuple's third and fourth components false.
- **Stop if.** Any of the three files fails to compile at the ticket's base commit (a Lean source changed since 2cad8cc): stop and report the first error; do not repair statements inside this ticket.
- **Guidance.** The Falsifiers file has theorems and imports Instances, so it must live under Midfall/Instances (D-P17). Do not use `simp` on anything containing `List.replicate (2 ^ 256) _`. `native_decide` appears only in the Deploy file, for `poseidon_delta_not`.

### ST.2 — Statement-surface decisions  **[DONE — signed 2026-11-17]**

> **Do not run.** D-P64 and D-P66 were signed by the human on 2026-11-17 (after `53bf8c1`) and are recorded in `design.md` with their conditions. What remains of this card is those conditions, which the cards that name each decision apply.

DECISION · DECISION · box 0.5 h · orchestrator + human · after ST.1

- **Goal.** The human signs or strikes D-P64 and D-P66 of PLAN-V3 §2.2, and `design.md` quotes the sign-off
  (who, when, where) under those numbers.
- **Needs.** PLAN-V3 §2.1 (how the signed D-P45–D-P59 relate) and §2.2 (the row text, its
  recommendation and its "if struck" consequence); the evidence named in PLAN-V3 §3 for that row,
  re-run at the tip with `bash docs/plans/V3-evidence/check.sh`.
- **Does NOT need.** Any Lean change. The orchestrator does not decide (W2, D-P53).
- **Do.**
  1. Draft the row in `docs/DECISIONS-PENDING.md` (new items go at the end, unsigned), quoting
     PLAN-V3 §2.2 verbatim and linking the evidence output.
  2. Mark every card that names the row BLOCKED until it is signed.
  3. On sign-off, record it in `design.md`; on a strike, apply the "if struck" line of §2.2 and
     re-plan the cards that named the row.
- **Deliverable.** The `design.md` entry or entries, with sign-off lines.
- **Accept.** `design.md` contains each numbered entry with a W2 sign-off line; no `.lean` file
  changed; `git diff --stat` shows `formal/docs/` only.
- **Stop if.** The evidence for the row no longer typechecks at the tip: re-measure before asking
  for a signature.
- **Guidance.** Sign only after ST.1 has landed the compiled staging module and its falsifiers, so the text signed is text that typechecks in the tree. D-P66 is conditional on D-P63.

### ST.3 — Cut-over A: the block scope and the slices move

INFRA · PORT · box 1.5 h · Sonnet · after ST.2

- **Goal.** Render.scope becomes the hoist of the helpers followed by the hoist of the seven slices; Render.slices moves from Blocks.lean into Statements.lean section 1.
- **Needs.** formal/Midfall/LoweringV2/Statements.lean:107-110 (Render.scope and its docstring); Blocks.lean:200-204 (Render.slices); the scratch text scopeV3 (:219) and slicesV3 (:209); the port/ experiment as the expected result.
- **Does NOT need.** Any proof edit in Blocks/*.lean. hoist_prog_addr_indep. WP-G1.
- **Do.**
  1. Move `Render.slices` (same text) above `Render.scope` in Statements.lean, written with `R.slice`.
  2. Replace the scope body by `[hoist D R.helpers ++ hoist D R.slices]`; replace the docstring claim that the helpers are the only funDefs.
  3. Delete the definition from Blocks.lean.
  4. Build the block layer; re-hash Frozen.sha256.
- **Deliverable.** `Render.scope` and `Render.slices` in Statements.lean; a new Frozen.sha256 line.
- **Accept.** `lake build Midfall.LoweringV2.Blocks.Compose` green with per-file sorry counts unchanged for the four measured files (Blocks 10, TraceReturn 0, VkLoading 3, FinalPairing 3). `fail_lookup` (Blocks/TraceReturn.lean:405) is not edited. scripts/checks.sh frozen-hash line green.
- **Stop if.** Any file under Blocks/ needs more than an import change: stop and report the first error.
- **Guidance.** Do NOT use `[hoist D (R.prog 0 0)]`: measured, `fail_lookup := rfl` then fails. Compose.lean was not part of the experiment; build it.

### ST.4 — Cut-over B1: codec bundles, calldataOf, EndToEnd, EntryFrame, the headline, the gate

INFRA · PORT · box 2.5 h · Sonnet · after ST.3

- **Goal.** The frozen sections 3, 5, 8, 9 of Statements.lean read as the V3 text.
- **Needs.** Scratch lines: G1CodecHeadlineLaws :70, G1CodecLawsV3 :81, withCompressed :92, calldataOfV3 :139, EntryFrameV3 :658, LoweringEquivalenceV3 :818, HypothesesInhabitedV3 :923, EndToEndV3 :946, GasTotal :747, BodyTotal :758. Statements.lean:240-247, :298-311, :317-320, :327-330, :335-340, :347-361.
- **Does NOT need.** Valid (ST.6). Any block proof. The deployment instance.
- **Do.**
  1. Add the two codec structures, `withCompressed` and its lemma in a V2-owned file (not the v1 Assumptions/Codec.lean).
  2. Replace calldataOf, EntryFrame (+cdSize), EntryFrameInhabited (+hcd), LoweringEquivalence (codec hypothesis at top, conjunct 2 without its own codec premise, conjunct 4), HypothesesInhabited, EndToEnd.
  3. Do not repair Blocks.lean here beyond what is needed to state ST.5.
  4. Re-hash.
- **Deliverable.** The six frozen definitions in their V3 text under their V2 names; GasTotal and BodyTotal.
- **Accept.** `lake build Midfall.LoweringV2.Statements` green; the staged Falsifiers still build after pointing F1 at the verbatim old composition (`frozenCalldataCore`). `#print axioms withCompressed_lawsV3` has no sorryAx.
- **Stop if.** The edit forces a change to Program.lean or Shared.lean: stop; that is another decision.
- **Guidance.** ST.4 and ST.5 land together or the tree is red in between; issue them back to back on one branch. The V3 conjunct 2 has NO local codec premise.

### ST.5 — Cut-over B2: the composition in Blocks.lean and the headline assembly

> **Changed by RECON.2.** Do not build a composition from the old `BlockContractsAt` / `BlockRow` rows (`completeV3_of_blocks`). This card lands the headline text, `TwoOutcomes`, `twoOutcomes_of_scans` and the deletions only; the composition is RECON.2's and SIM.2's.

INFRA · PORT · box 2.5 h · Sonnet · after ST.4

- **Goal.** Blocks.lean composes the V3 headline from four named obligations, with `rejects_of_not_accepts` deleted.
- **Needs.** Scratch: TwoOutcomes :550, twoOutcomes_of_exitDiscipline :565, scans_prog_addr_indep :575, twoOutcomes_of_scans :581, runBody_mono :779, RejectsV3 :853, CompleteV3 :862, TotalV3 :872, lowering_equivalenceV3_of :882 (proved text), entryFrame_inhabitedV3 :677 (proved text). Blocks.lean:116-139, :356-363, :493-608, :624-635, :688-698; Instances/PoseidonV2.lean headline assembly.
- **Does NOT need.** Any new block proof. Valid changes.
- **Do.**
  1. Delete `rejects_of_not_accepts`; add the TwoOutcomes definitions and the three sorried obligations; update SORRY.md.
  2. Replace `lowering_equivalence_of_blocks` by `lowering_equivalenceV3_of`, and keep the old conjunct-2 argument as the proof of `CompleteV3` from the block rows.
  3. Change the codec gate in `BlockContractsAt` and `BlockRow` from `G1CodecLaws` on the progress half to `G1CodecHeadlineLaws` on both halves.
  4. Adapt `entryFrame_inhabited` (+hcd) and the PoseidonV2.lean assembly to the four obligations.
  5. Restate Falsifiers F9 over a Prop copy of the deleted statement.
- **Deliverable.** `TwoOutcomes`, `RejectsV3`, `CompleteV3`, `TotalV3`, `lowering_equivalenceV3_of` and `completeV3_of_blocks` in Blocks.lean.
- **Accept.** `lake build` green. `#print axioms` of the composition theorem has no sorryAx. `#cone_sorries lowering_equivalence_poseidon` no longer lists rejects_of_not_accepts and lists twoOutcomes_of_exitDiscipline, scans_prog_addr_indep and runBody_mono. SORRY.md matches.
- **Stop if.** A proved block row uses a codec law outside the four headline laws: stop and report which; the fallback is the full bundle at the top level.
- **Guidance.** The frozen docstring calling SoundSide a completeness condition (Blocks.lean:349-352) is wrong; do not carry it. RejectsV3 keeps SoundSide and gains nothing else.

### ST.6 — Cut-over C: Render.Valid in its V3 text

> **Changed by RECON.1.** Port the single `ValidV3` that RECON.1 produced (the seven-clause structure of `ObjectV3Full.lean` with the added `programOk` conjuncts), not `StatementsV3.lean:613`. If `topBinders` or `Render.slices` must move into a frozen file, that edit belongs to the same re-hash and is named in the brief.

GEN · PORT · box 2.5 h · Sonnet · after ST.4

- **Goal.** Render.Valid has the repaired circuitMeta and supported clauses and the four added clauses (payload, exitDiscipline, noShadow, cdBound).
- **Needs.** Scratch: noShadowCore :228, WellFormedV3 :283, PlanMeta :320, payloadWord :362, g1WordsBytes :366, PayloadAgrees :373, isCommittingExit :469 to ExitDiscipline :526, SupportedV3 :592, ValidV3 :613. Statements.lean:118-134, :182-217. ProgramLemmas.lean:24 (topBinders). Exec/VerifyingKey.lean:114-116 if the in-place WellFormed repair is chosen.
- **Does NOT need.** The deployment data repairs. WP-G1. Any block proof.
- **Do.**
  1. Move `topBinders` from ProgramLemmas.lean into Program.lean.
  2. Add the exit-scan definitions and the witness/refusal lemmas; add PlanMeta, payloadWord, g1WordsBytes, PayloadAgrees, noShadowCore.
  3. Edit Valid and SupportedV2.wf per the decision.
  4. Fix every consumer of `hR.circuitMeta` / `hR.supported.wf`.
  5. Re-hash (final).
- **Deliverable.** `Render.Valid` with the V3 clause set; the exit scan; PayloadAgrees.
- **Accept.** `lake build` green; `exitDiscipline_witness` and `exitDiscipline_refuses` build by `decide`; the staged Falsifiers F2 builds against a Prop copy of the old clause 1. Falsifier of the ticket: `PayloadAgrees poseidonRender` is refuted by `poseidon_payloadAgrees_not`.
- **Stop if.** Stating `PayloadAgrees` requires importing Generator/Vk.lean into the frozen file: stop; the scratch text does not need it.
- **Guidance.** Slot numbers come from `vkHeaderTemplateSlotsDefault`, never literals. `Op` is ambiguous in files that open both namespaces; write `EVM.Op`.

### ST.7 — The V3 clause table at poseidonRender

GEN · KAT · box 2 h · Sonnet · after ST.6

- **Goal.** Instances/PoseidonValid.lean decides every V3 clause at the deployment with one named lemma per clause, and its header table is the measured one.
- **Needs.** Instances/PoseidonValid.lean; the Deploy file's deciders (planMetaB, planLayoutB, payloadScalarsB, noShadowCore, exitDisciplineFuel); the measured values.
- **Does NOT need.** Any data repair; any statement edit.
- **Do.**
  1. Add deciding lemmas for circuitMeta (PlanMeta), payload, exitDiscipline, noShadow, cdBound; re-decide supported with the repaired wf.
  2. Rewrite the header table and the stale section headers and docstrings (clauses 1, 2, 3, 8, 9 and `poseidonRender_notValid`).
  3. Keep `poseidonRender_notValid` through whichever clause is still refuted.
- **Deliverable.** Named lemmas per clause and an accurate header table.
- **Accept.** Printed verdicts: circuitMeta false and layout false at today's plan; payload refuted with scalar list `[true, true, true, true, true, true, true, false]`; exitDiscipline `(true, true, false)`; noShadow `true`; cdBound `(4484, true)`. Supported: report the verdict; expected proved, since its one refuted field is the repaired one (8 = 8).
- **Stop if.** A clause's verdict differs from the measurement: stop and report the value; do not edit the clause.
- **Guidance.** This is a measurement card. `poseidonRender` is noncomputable; go through `poseidonM`, `poseidonPv`, `poseidonPlanV2` as the file already does.

### ST.8 — TwoOutcomes: the Step-induction requirements table and the invariant statement

SEM · SKELETON · box 2 h · strongest · after ST.1

- **Goal.** A complete table of which Step constructors and which builtins can set `halted` or return a non-normal outcome, and a pinned statement of the invariant the induction carries.
- **Needs.** vendor/yul-semantics/YulSemantics/BigStep.lean (Step); Dialect/EVMExec.lean (stepOp, builtinWithExternal, HaltKind.commits); Bridge.lean:1039-1108 (the writer scan) and :1221 (Run_worldEq_of_noWriters).
- **Does NOT need.** Any render, plan or key. Any Lean-verifier fact.
- **Do.**
  1. List every builtin whose result can be `.halt` and the HaltKind it sets; confirm the committing ones are exactly stop, ret, selfdestruct.
  2. State the function-environment invariant: every declaration in scope has a body passing `exitScan true false`.
  3. State the statement-level lemma: for a block passing the scan, every derivation ends normal or halted with a non-committing kind, with break/continue/leave only where the context bits allow.
  4. Check whether the same induction skeleton serves Run_worldEq_of_noWriters.
- **Deliverable.** Sorried lemmas with pinned signatures and the table in QUEUE.md.
- **Accept.** The table covers every Op constructor and every statement-level Step constructor. The pinned lemmas typecheck and `twoOutcomes_of_exitDiscipline` is derivable from them by a proof that contains no sorry of its own.
- **Stop if.** A builtin other than stop/ret/selfdestruct can produce a committing halt: stop and report; the scan must then refuse it.
- **Guidance.** Subterm closure of a fuel-bounded scan is the awkward part: state it once, generically, for both scans.

### ST.9 — twoOutcomes_of_exitDiscipline: expressions and builtins

> **Run one pair, not both.** ST.9–ST.10 and SIM.4–SIM.5 prove the same `Step` induction (`quiet_init` / the exit discipline). SIM.3 lands exactly one exit scan; run SIM.4–SIM.5 and close ST.8–ST.10 against them.

SEM · PROOF · box 2.5 h · strongest · after ST.8

- **Goal.** The expression and argument-list half of the invariant: evaluating an expression that passes the scan leaves `halted` unset or sets it to a non-committing kind.
- **Needs.** The pinned lemmas of ST.8; stepOp.
- **Does NOT need.** Statements, loops, the tail.
- **Do.**
  1. Prove the per-builtin table by cases on Op with `simp [stepOp]`.
  2. Prove the expression lemma by induction on Step restricted to expr/args/call.
- **Deliverable.** The expression-half lemma, proved.
- **Accept.** `#print axioms` of the lemma has no sorryAx; the sorry count of the cone of `twoOutcomes_of_exitDiscipline` drops by one.
- **Stop if.** The user-call case needs a fact about the callee body that the function-environment invariant does not give: stop and restate the invariant.
- **Guidance.** Keep the call relation and gas oracle universally quantified; nothing here depends on them.

### ST.10 — twoOutcomes_of_exitDiscipline: statements and the return tail

> **Merged with SIM.5** (see ST.9).

SEM · PROOF · box 2.5 h · strongest · after ST.9

- **Goal.** Close `twoOutcomes_of_exitDiscipline`.
- **Needs.** ST.9; Step.stmts_append_inv (Yul/Contracts.lean:115); Run_worldEq_of_noWriters (registered sorry, cited); view_eq_of_worldEq_and_halt.
- **Does NOT need.** Any render.
- **Do.**
  1. Statement-level induction with the two context bits.
  2. Split the run at the tail with `Step.stmts_append_inv`; evaluate `mstore(p, 1)` then `return(p, 32)` by `simp [stepOp]` to get `halted = some (.ret, abiTrue)`.
  3. Combine with WorldEq and `committedState`.
- **Deliverable.** `twoOutcomes_of_exitDiscipline` proved.
- **Accept.** `#print axioms twoOutcomes_of_exitDiscipline` shows no sorryAx other than through `Run_worldEq_of_noWriters`. `#cone_sorries` of the headline drops by one.
- **Stop if.** Reading back 32 bytes after `storeWord` does not reduce to `abiTrue`: stop and report the term; TraceReturn.lean has the same step proved from a stronger precondition.
- **Guidance.** The statement holds from ANY start state; do not add an entry-frame hypothesis to make a step easier.

### ST.11 — prog_slices_decompV3

GEN · PROOF · box 2.5 h · strongest · after ST.3, ST.6

- **Goal.** The closed program is prefix, helpers, main locals and slices, and its hoisted scope is the block scope.
- **Needs.** `inline_append` (ProgramLemmas.lean:27, sorried - WP-A2 owns it; cite it), `emitSlices_eq` (proved), `noShadowB`.
- **Does NOT need.** Any semantic fact.
- **Do.**
  1. Rewrite `asmOf` with `inline_append` five times against `noShadowB`.
  2. Push `hoist` through `++` with `List.filterMap_append`; show the prefix and the main locals hoist to the empty scope.
- **Deliverable.** `prog_slices_decomp` in its V3 statement, proved modulo `inline_append`.
- **Accept.** `#print axioms` shows sorryAx only through `inline_append`; `hoist_prog_addr_indep` is deleted or derived.
- **Stop if.** `inline_append`'s side condition is not implied by `noShadowB` for some segment: stop and report the binder.
- **Guidance.** The statement is false without the no-shadow hypothesis. Do not try `rfl` on `R.prog`.

### ST.12 — scans_prog_addr_indep

GEN · PROOF · box 2 h · Sonnet · after ST.5

- **Goal.** NoWriters and ExitDiscipline of `R.prog 0 0` transfer to `R.prog vkAddr qAddr`.
- **Needs.** `wrapperLocals` (Program.lean:105-108); the two scans; `inlineContractConstants`.
- **Does NOT need.** Step, runs, renders' keys.
- **Do.**
  1. Show the two programs differ only in the literal of at most two `letDecl` right-hand sides.
  2. Show both scans ignore literal values.
- **Deliverable.** `scans_prog_addr_indep` proved; `noWriters_prog` (Blocks.lean:340) removed.
- **Accept.** `#print axioms scans_prog_addr_indep` has no sorryAx; the headline cone drops by one.
- **Stop if.** The inliner's output depends on the literal value: stop and report.
- **Guidance.** A relational lemma 'equal up to literals' over the Scan type serves both scans at once.

### ST.13 — runBody_mono

SEM · PROOF · box 2 h · strongest · after ST.5

- **Goal.** A run under a call relation is a run under any larger one.
- **Needs.** Step; `externalCall` (EVMExec.lean); `callsOf_le_permissive` (proved in the staged module).
- **Does NOT need.** Any render fact.
- **Do.**
  1. Induction on Step for `Bridge.Dialect c g` to `Bridge.Dialect c' g`; the builtin case splits on Op, and only the call family uses the relation.
- **Deliverable.** `runBody_mono` proved; `BodyTotal.permissive` sorry-free.
- **Accept.** `#print axioms BodyTotal.permissive` has no sorryAx.
- **Stop if.** The dialect change does not typecheck across the mutual judgement: stop and report the constructor; a generic `Step.mapDialect` lemma may be the right shape.
- **Guidance.** Value and State types are equal across the two dialects, but the dialects are different terms; expect to restate the induction motive explicitly.

### ST.14 — Deployment codec: the headline laws at poseidonE

ALG · PORT · box 2 h · Sonnet · after ST.4

- **Goal.** `G1CodecHeadlineLaws poseidonRender.E.g1` is a theorem, so LeanAccepts is no longer false for a codec reason.
- **Needs.** `withCompressed`, `withCompressed_lawsV3`, `exists_injective_comp`, `lawsV3_satisfiable_at_G1z` (proved in the staged Deploy file); Instances/PoseidonEnv.lean (poseidonE); HoldsFinal.holds_exhibited.
- **Does NOT need.** Curve arithmetic; the ZCash format; any proof bytes.
- **Do.**
  1. Define the deployment codec as `withCompressed g1CodecZ comp` for the chosen injection.
  2. Prove that `Eip2537.Holds` transfers (it reads only `toEip` and `ofEip?`).
  3. Re-run the clause table rows that mention the codec.
- **Deliverable.** `poseidonE.g1` satisfying the eight laws; a transferred Holds exhibit.
- **Accept.** `#print axioms` of the laws theorem shows `[propext, Classical.choice, Quot.sound]`; `poseidon_notInhabitedV3` no longer typechecks (delete it and record why).
- **Stop if.** An existing exhibit depends on `poseidonE.g1 = g1CodecZ` by `rfl` and cannot be restated: stop and list the exhibits.
- **Guidance.** This codec's compressed half is an abstract injection. It is enough for the headline and NOT for EndToEnd's claim about Rust proof bytes; say so in the docstring.

### ST.15 — Deployment data: delta and the post-processed plan meta

GEN · PORT · box 2 h · Sonnet · after ST.6

- **Goal.** `poseidonE.delta` is the field constant and `poseidonPlanV2.meta_` is the post-processed meta, so PlanMeta, layout and the eight scalar payload pins are proved.
- **Needs.** Instances/PoseidonEnv.lean:379-380 (delta := 2); DeployedProfile.lean:121 (poseidonMeta), :223 (poseidonPlan); `modPow` (Assumptions/Eip2537.lean).
- **Does NOT need.** Real commitments; the codec; WP-G1.
- **Do.**
  1. Set delta to the cast of `modPow 7 (2 ^ 32) blsR` and KAT it against the fixture literal.
  2. Set the plan's meta to the raw meta with `setNumPointSets` of `numPointSets` on the plan's data.
  3. Prove the PlanMeta and layout clauses and the eight scalar pins.
- **Deliverable.** Two data changes and their clause lemmas.
- **Accept.** Clause table: circuitMeta and layout proved, derived proofLen 4320; scalar list all true; the 26,018-byte VK render gate and the whole-contract render gate still green.
- **Stop if.** Changing the meta moves a rendered byte: stop and report the gate.
- **Guidance.** Measured: the faithful plan satisfies both clauses and the Rust derivation returns exactly this meta. `invariants` stays refuted; it is not this card's.

### ST.16 — BodyTotal: the requirements table

SEM · PROBE · box 2 h · Sonnet · after ST.5

- **Goal.** Know what proving totality costs: every loop of the program with its termination argument, every call with its target, every place a run could be stuck.
- **Needs.** The generator text of the main block; GenAst emitters; `honestRelations` (Externals.lean:1006).
- **Does NOT need.** Any proof.
- **Do.**
  1. Inventory the `for` loops per slice and write the variant of each.
  2. Confirm in the AST that every `staticcall` target is a literal among 0x05, 0x0b, 0x0c, 0x0f.
  3. Propose the per-slice contract shape: from a boundary carrying only the frame facts, an honest run exists and every run reverts or exits normally.
- **Deliverable.** A table in QUEUE.md and a proposed `BlockExit` contract statement that typechecks.
- **Accept.** Every loop has a stated variant or is marked unresolved; the proposed contract typechecks; the count of rows equals the count of slices.
- **Stop if.** A loop's bound is read from calldata or from unpinned memory: stop and report it; totality then needs a memory pin first.
- **Guidance.** Text-level evidence so far: 9 staticcalls, all at precompile addresses; no gas, call, create tokens. The quotient interpreter loop is the one to look at first.

### ST.17 — HypothesesInhabitedV3: feasibility probe

ALG · PROBE · box 2.5 h · strongest · after ST.14

- **Goal.** Decide whether, and by which route, `LeanAccepts poseidonRender keccak256 cd` can be proved for one concrete calldata.
- **Needs.** Halo2/Exec/Native.lean (verifyMsgs); Instances/NativeE2E.lean (the exponent-model run); Instances/Bls12_381.lean (computable affine codec, no group law); G1Agreement.lean (byte-fold agreement lemmas).
- **Does NOT need.** Any block proof.
- **Do.**
  1. List every G1 operation `verifyMsgs` performs and whether a computable twin exists for it.
  2. Sketch the transport statement from a computable carrier to `G₁z`.
  3. State what the final pairing check reduces to under a known-trapdoor SRS, and what axiom the alternative needs.
  4. Name the single (proof, calldata) pair to use.
- **Deliverable.** A written verdict with a ticket list or a stop.
- **Accept.** The report names the route, the missing lemmas with signatures that typecheck, and the trusted-base consequence of each option.
- **Stop if.** No executable path exists without re-porting the verifier over a new carrier: stop and report that as the finding.
- **Guidance.** Do not attempt the proof. No Rust proof has been accepted by a Lean run on the real curve; treat every 'it should compute' as unverified.

### ST.18 — The real compressed codec on G1z

> **Merged with REF.4, REF.9, REF.10**, which land the computable codec `g1CodecC` and its encoder-first law. Run this card only as the probe that precedes REF.9.

ALG · PROBE · box 2 h · Sonnet · after ST.14

- **Goal.** Find out whether the ZCash compressed encoding can be the deployment codec's compressed half with the eight laws proved, which is what EndToEnd's link to Rust proof bytes needs.
- **Needs.** Instances/Bls12_381.lean:76 (G1Affine.ofCompressed?), :120 (toCompressed); G1Agreement.lean (g1zPair and the curve-equation facts); `withCompressed_lawsV3`.
- **Does NOT need.** The headline; any block.
- **Do.**
  1. Define the candidate `toCompressed` on `G₁z` through `g1zPair`.
  2. State injectivity and try the two cases (same x, sign flag).
  3. KAT the encoder against the G1 points of the tracked fixture proof.
- **Deliverable.** The definition, the injectivity lemma (proved or sorried with the missing fact named) and the KAT.
- **Accept.** The KAT is green on every G1 slot of the fixture proof; the injectivity lemma typechecks.
- **Stop if.** Injectivity needs a field fact the tree does not have: stop and name it.
- **Guidance.** With injectivity, all eight laws follow from the generic lemma already proved; nothing else is needed.


---

## M3 and M6 — the soundness architecture  (waits for: D-P68; 13 cards, 25.5 box-hours)

### SIM.0 — Block architecture and proof technology  **[DONE — signed 2026-11-17]**

> **Do not run.** D-P68 were signed by the human on 2026-11-17 (after `53bf8c1`) and are recorded in `design.md` with their conditions. What remains of this card is those conditions, which the cards that name each decision apply.

DECISION · DECISION · box 0.5 h · orchestrator + human · after ST.1

- **Goal.** The human signs or strikes D-P68 of PLAN-V3 §2.2, and `design.md` quotes the sign-off
  (who, when, where) under those numbers.
- **Needs.** PLAN-V3 §2.1 (how the signed D-P45–D-P59 relate) and §2.2 (the row text, its
  recommendation and its "if struck" consequence); the evidence named in PLAN-V3 §3 for that row,
  re-run at the tip with `bash docs/plans/V3-evidence/check.sh`.
- **Does NOT need.** Any Lean change. The orchestrator does not decide (W2, D-P53).
- **Do.**
  1. Draft the row in `docs/DECISIONS-PENDING.md` (new items go at the end, unsigned), quoting
     PLAN-V3 §2.2 verbatim and linking the evidence output.
  2. Mark every card that names the row BLOCKED until it is signed.
  3. On sign-off, record it in `design.md`; on a strike, apply the "if struck" line of §2.2 and
     re-plan the cards that named the row.
- **Deliverable.** The `design.md` entry or entries, with sign-off lines.
- **Accept.** `design.md` contains each numbered entry with a W2 sign-off line; no `.lean` file
  changed; `git diff --stat` shows `formal/docs/` only.
- **Stop if.** The evidence for the row no longer typechecks at the tip: re-measure before asking
  for a signature.
- **Guidance.** D-P68 replaces D-P57's hand-proof fallback by the thresholds of PLAN-V3 §5 M5: say so in the entry.

### SIM.1 — Land the Lean staged view (section 1 of the scratch file)

ALG · PORT · box 2 h · Sonnet · after SIM.0

- **Goal.** A new refinable file Midfall/Lowering/Stage.lean holding abiHeadOk, envelopeOk, RawMsg, rawSlots, rawDecode, liftRaw, Decoded, PcsReads, pcsReads, SnapXcript, snapshotXcriptRun, LinFull, linearizeFull, padSnap, leanStage, LeanRaw, LeanFinal, with the six proved lemmas.
- **Needs.** SoundnessV3.lean lines 55-460; Midfall/Lowering/Snapshot.lean, Calldata.lean; Midfall/Halo2/Exec/Verifier.lean (linearize, collectQueries, partiallyEvaluateIdentities), Kzg/MultiOpen.lean (phaseA/B/C for the docstring citations).
- **Does NOT need.** Any Yul file; any edit to Exec (linearizeFull is a new def, linearize is untouched); the Render type can be replaced by its fields if Stage.lean must not import LoweringV2 - in that case leanStage/LeanRaw/LeanFinal go to LoweringV2/Stages.lean with SIM.2.
- **Do.**
  1. Copy the definitions and the proofs of decodeSlots_eq_raw, decodeCalldata_eq_raw, decodeCalldata_isSome_iff, linearize_eq_full, leanStage_pairing_ok/of, leanAccepts_of_final, leanFinal_of_accepts
  2. Register leanStage_prefix as a named sorry in SORRY.md
  3. Add the KATs rawDecodeAgreesKats_ok and xZeroCollapseKats_ok with `-- expect true`
  4. Add a KAT that runs pcsReads on a pairing-free fixture (Fr 17, natG1Codec) and pins the eight values
- **Deliverable.** Midfall/Lowering/Stage.lean. Signatures: `theorem decodeCalldata_eq_raw {G} (L : ProofCalldataLayout) (n : Nat) (c : G1Codec G) (cd : Bytes) : decodeCalldata (p := p) L n c cd = (rawDecode (p := p) L n cd).bind fun r => (r.1.mapM (liftRaw c)).map fun ms => (ms, r.2)`; `def leanStage (R) (H) (inst) (ms) : Checkpoint → Except Fault (Snapshot p G₁ G₂ Gₜ)`; `theorem leanAccepts_of_final : LeanFinal R H cd → LeanAccepts R H cd`; `theorem leanFinal_of_accepts : LeanAccepts R H cd → LeanFinal R H cd`.
- **Accept.** lake build green; `#cone_sorries decodeCalldata_eq_raw` prints 0; `#cone_sorries leanAccepts_of_final` prints exactly Midfall.Lowering.snapshotOf_prepareMsgs; both KATs evaluate true; falsifier: replacing `if g1WordsOk cd cur` by `if true` in rawSlots turns rawDecodeAgreesKats_ok false.
- **Stop if.** decodeCalldata changes shape between now and the port (the proof is a guard-by-guard case split and will not survive a reordering of the guards): re-derive from RawDecode.lean rather than patching.
- **Guidance.** The proof text is in RawDecode.lean and compiles in 13 s. Use `set_option linter.unusedSimpArgs false in` on the two theorems. nSets must be `R.plan.proofLayout.qEvals.itemCount` (3 at the deployment); `plan.meta_.numPointSets` is 0 there.

### SIM.2 — Land StageInv, BlockSim, BlockProgS and the proved composition

> **Changed by RECON.2.** State `BlockSim` over the scope ST.3 landed (the card's stop condition about `Render.scope` no longer applies). `Frame` carries `cdSize`. The composition concludes `rejectsV3_of_sims` and `completeV3_of_progs`, not `lowering_equivalence_of_stages`.

INFRA · SKELETON · box 2.5 h · strongest · after SIM.1

- **Goal.** A new refinable file Midfall/LoweringV2/Stages.lean with the staged contracts and every composition theorem proved, so that the headline is `lowering_equivalence_of_stages` applied to named rows.
- **Needs.** SoundnessV3.lean lines 460-830 and 1050-1350; Midfall/LoweringV2/Blocks.lean (Frame, Poisoned, Render.slices, preSlice, mainLocalsInlined, the transport lemmas, prog_slices_decomp); Midfall/Yul/Contracts.lean (Step.stmts_append_inv).
- **Does NOT need.** Any block proof; BlockSound, BlockProgress, Render.Rejects, prefix_run_clean, runBody_iff_slices, slices_seq_sound, slices_seq_progress (none is cited).
- **Do.**
  1. Port BaseInv, cdSlice, mirrorsSection, lookupMirror, MirrorAt, Mirror, Agree, StageInv, exitSim, BlockSim, hasMultiPointSet, SimPins, Render.SimContracts
  2. Port splitPost, seq_split, seq_final, seq7, Mid, FinSim, blockSim_split, blockSim_final, slices_seq_sim
  3. Port Render.preBlock, run_split, run_join, soundness_of_sims, rejects_of_sims
  4. Port exitProg, BlockProgS, Render.ProgContracts, stmts_append_run, ex_append, total_append, blockProg_step, slices_seq_prog, completeness_of_progs
  5. State prefix_sim and prefix_prog as named sorries; port lowering_equivalence_of_stages (it also needs SIM.3's two_outcomes_of_exitShape: take it as a hypothesis here if SIM.3 is not in yet)
  6. Port finSim_refutes_empty as the falsifier
- **Deliverable.** Midfall/LoweringV2/Stages.lean. `theorem slices_seq_sim (R) (H) (vkAddr) (cd) (c) (g) (h7 : ∀ q : Partial, BlockSim R q H vkAddr c g cd) : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) R.slices (fun V st => Mid R H vkAddr cd .start V st) (fun _ _ V' st' o => FinSim R H cd V' st' o)`; `theorem lowering_equivalence_of_stages (R) (product) (hR : R.Valid) (hpins : SimPins R) (hexit : R.ExitOk) (hsim : R.SimContracts product) (hprog : R.ProgContracts product) : LoweringEquivalence R product`.
- **Accept.** lake build green; `#cone_sorries slices_seq_sim`, `slices_seq_prog`, `finSim_refutes_empty` each print 0; `#cone_sorries lowering_equivalence_of_stages` prints exactly snapshotOf_prepareMsgs, noWriters_prog, prog_slices_decomp, prefix_prog, prefix_sim, quiet_init, Run_worldEq_of_noWriters; `#print axioms slices_seq_sim` shows [propext, Classical.choice, Quot.sound]; `grep -c 'Rejects\|rejects_of_not_accepts\|prefix_run_clean' Midfall/LoweringV2/Stages.lean` is 0 outside comments.
- **Stop if.** The frozen Render.scope is replaced before this lands: then state BlockSim over the new block scope and re-check that run_split still closes (its only scope fact is the second conjunct of prog_slices_decomp).
- **Guidance.** Define Render.* helpers with `_root_.Midfall.LoweringV2.Render.x` if the file's namespace is not LoweringV2. Write `Midfall.Lowering.Inv`, never bare `Inv`. Do not delete the old section 6/7 in this ticket; SIM.9 retires it once the rows are restated.

### SIM.3 — Conjunct 3 without a snapshot: exit scan, TraceReturn exit, two outcomes

INFRA · PORT · box 2 h · Sonnet · after SIM.2

- **Goal.** Replace rejects_of_not_accepts by two_outcomes_of_exitShape, proved from the leaf quiet_init, and decide Render.ExitOk at the deployment.
- **Needs.** SoundnessV3.lean lines 830-1050; Midfall/Yul/Bridge.lean (Scan, the shape of noWritersStep); Midfall/LoweringV2/Blocks/TraceReturn.lean (tr_slice, fail_lookup, failFDecl, tr_fail_reverts, tr_mstore_step, tr_mstore_o, tr_ret_o, tr_ret_step, readBytes_storeWord_one); Instances/PoseidonValid.lean (poseidonPv, poseidonM).
- **Does NOT need.** Any snapshot, LeanAccepts, SoundSide, Eip2537.Holds, or block row.
- **Do.**
  1. Put isCommitHalt, exitScan, ExitShape next to noWritersScan in Bridge.lean (INFRA) or in Stages.lean
  2. Port QuietExit, Render.slices6, slices_eq, Render.ExitOk, the leaf quiet_init
  3. Port iszero_success_inv, tr_guard_any, tr_exit_any into TraceReturn.lean or a sibling file
  4. Port entry_not_halted and two_outcomes_of_exitShape
  5. In Instances: prove poseidonRender.ExitOk by native_decide through the computable faces, fuel 100000
- **Deliverable.** `def exitScan : Nat → Bool → Bool → Scan → Bool`; `theorem tr_exit_any (R) : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice .traceReturn) (fun _ _ => True) (fun _ _ _ st' o => o = .halt ∧ (Reverted st' ∨ st'.halted = some (.ret, abiTrue)))`; `theorem two_outcomes_of_exitShape (R) (hR : R.Valid) (hx : R.ExitOk) (W) (Lyt) (H) (vkAddr) (cd) (st₀) (hentry : EntryFrame R W Lyt H cd st₀) (c) (g) (obs) (hobs : RunBody R vkAddr 0 c g st₀ obs) : obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)`.
- **Accept.** lake build green; `#cone_sorries tr_exit_any` prints 0; `#cone_sorries two_outcomes_of_exitShape` prints noWriters_prog, prog_slices_decomp, quiet_init, Run_worldEq_of_noWriters; the three `example ... := by decide` falsifiers of the scan compile (a `ret` is rejected, a top-level `leave` is rejected, a `revert` is accepted); at the deployment the scan of the program without its last statement evaluates true and the scan of the whole program evaluates false (measured today: true / false).
- **Stop if.** The emitter starts producing a second `return` (trace render) inside scope: the scan must then be restricted to production renders, which SupportedV2.production already requires.
- **Guidance.** tr_guard_any is tr_guard_reverts and tr_guard_skip with the value hypothesis removed; the only new inversion is iszero_success_inv (after `simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w] at hbi` the hypothesis is a conjunction; `subst` both sides). The scan must descend into funDef bodies, so q_program_fail and q_pow5 are covered wherever the emitter puts them.

### SIM.4 — Probe the exit-discipline meta-lemma

INFRA · PROBE · box 1.5 h · Sonnet · after SIM.3

- **Goal.** Measure the cost of quiet_init by proving it for the expression fragment, and decide whether it shares one Step induction with Run_worldEq_of_noWriters.
- **Needs.** vendor/yul-semantics/YulSemantics/BigStep.lean (Step), Dialect/EVMExec.lean (stepOp, finishCall); Midfall/Yul/Bridge.lean:1040-1230.
- **Does NOT need.** The verifier program; any render.
- **Do.**
  1. State `Step.inv_of_opInv`: a state predicate preserved by every built-in a syntactic scan admits is preserved by every Step derivation of scanned code in a scanned function environment
  2. Prove it for EvalExpr / EvalArgs over literals, variables and built-ins (no user calls, no statements)
  3. Count the constructor cases that needed a per-op fact and the lines per case
  4. Report whether the two instances (WorldEq, QuietExit) fit one parameterised lemma
- **Deliverable.** A scratch file with the expression-fragment lemma proved and a written estimate (cases, lines per case, hours) for the full induction.
- **Accept.** The fragment lemma typechecks with no sorry; the report states a number of hours for SIM.5 and whether Run_worldEq_of_noWriters is obtained for free.
- **Stop if.** The per-op fact needs unfolding all 70 local ops one by one with no uniform simp set: stop and price SIM.5 as 3 tickets rather than 1.
- **Guidance.** The claim to prove per op: an op other than ret, stop, selfdestruct never sets `halted` to a committing kind, and leaves `halted = none` when it returns values. staticcall goes through finishCall, which never records a halt of the calling frame. A function call ends `normal` or with the callee's `leave` caught, which is why the scan passes fn = true into funDef bodies.

### SIM.5 — Prove quiet_init

INFRA · PROOF · box 2.5 h · strongest · after SIM.4

- **Goal.** Close the leaf quiet_init (and Run_worldEq_of_noWriters if SIM.4 found one shared induction).
- **Needs.** SIM.4's lemma and estimate; SoundnessV3.lean:902 (statement).
- **Does NOT need.** Any block row; any Lean verifier fact.
- **Do.**
  1. Finish the Step induction over statements, loops and user calls
  2. Derive quiet_init for `R.preBlock vkAddr ++ R.slices6` in `R.scope c g`, using that every function in scope is a funDef of the scanned block and that the two wrapper addresses are literals
  3. Instantiate at WorldEq if shared
- **Deliverable.** `theorem quiet_init (R) (hx : R.ExitOk) (vkAddr) (c) (g) : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr ++ R.slices6) (fun _ st => st.halted = none) (fun _ _ _ st' o => QuietExit st' o)` with no sorry.
- **Accept.** `#cone_sorries two_outcomes_of_exitShape` no longer lists quiet_init; falsifier: the same statement with `R.slices` in place of `R.preBlock vkAddr ++ R.slices6` must NOT be provable (the scan is false on it; record the `decide`-false example).
- **Stop if.** More than one ticket is needed (SIM.4 said so): split by Step constructor family and keep each ticket under 2.5 h.
- **Guidance.** Do not go through Bridge.dialect_deterministic. The lemma is forall-runs, so permissive calls cost nothing.

### SIM.6 — The prefix rows: prefix_sim and prefix_prog

SEM · PROOF · box 2.5 h · strongest · after SIM.2

- **Goal.** From an entry frame, every run of the code before the first slice reverts or ends at StageInv .start; under honest calls and a decodable calldata a run exists.
- **Needs.** Program.lean (abiGuardBlock, wrapperLocals, mainGuardBlock, mainLocals); Blocks.lean (Render.preSlice, mainLocalsInlined); VkLoading.lean sections 2-4 (guard inversion, vk_fail_reverts, assign inversion); Statements.lean (EntryFrame, DeploymentV2); SoundnessV3.lean:772 and :1170.
- **Does NOT need.** Any snapshot or LeanAccepts for prefix_sim. A determinism lemma (the composition is existential in the prefix endpoint).
- **Do.**
  1. Put preBlock in statement-list form (the same three moves as tr_slice)
  2. Walk the ABI guard: it reverts or establishes the two head-word equalities of abiHeadOk
  3. Walk the wrapper local, the memory guard (passable by EntryFrame.fmp), the funDef no-ops, `let r`, `let success := true`
  4. Assemble StageInv .start: Frame from DeploymentV2 and the two lets, BaseInv .start from EntryFrame.zeroAbove, LeanRaw .start from the guard plus Valid.layout, Agree .start from BaseInv
  5. For prefix_prog exhibit the run, using LeanAccepts only to pass the ABI guard
- **Deliverable.** `theorem prefix_sim (R) (hR : R.Valid) (W) (Lyt) (H) (vkAddr) (cd) (st₀) (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀) (c) (g) : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr) (fun V st => V = [] ∧ st = st₀) (splitPost (fun V st => Mid R H vkAddr cd .start V st) (fun V' st' o => FinSim R H cd V' st' o))` and prefix_prog (SoundnessV3.lean:1170), both sorry-free.
- **Accept.** `#cone_sorries soundness_of_sims` no longer lists prefix_sim; falsifier: prefix_sim with `abiHeadOk` strengthened to `envelopeOk` in LeanRaw .start must fail (the prefix does not check the proof length word); record the failing goal.
- **Stop if.** The static half of abiHeadOk (proofCptr = 0x64, proofEnd = proofCptr + proofLen) is not derivable from Valid.layout without a lemma about ProofCalldataLayout.fromProtocol: stop, state that lemma as its own ALG ticket (it is true at the deployment: measured (true, true)).
- **Guidance.** This replaces prefix_run_clean and the forward half of runBody_iff_slices. Digest D-9 lists five pins the old statement needed; with no snapshot in the statement only the constant-table pins for FR_MODULUS, TRANSCRIPT_MPTR and the two ABI constants remain.

### SIM.7 — Migrate the proved rows and retire the old composition

SEM · PORT · box 1.5 h · Sonnet · after SIM.2

- **Goal.** TraceReturn and FinalPairing become BlockSim / BlockProgS rows; Blocks.lean section 7.1 loses the sorried sequencing and rejection lemmas.
- **Needs.** SoundnessV3.lean lines 1242-1350 (decoded_unique, agree_of_one, tr_blockSim, tr_blockProgS, fp_blockSim_of_blockSound); Blocks/TraceReturn.lean, Blocks/FinalPairing.lean, Blocks/Compose.lean.
- **Does NOT need.** Any new semantics.
- **Do.**
  1. Port the five lemmas
  2. In FinalPairing.lean export the poisoned half of the contract with no snapshot and no decode hypotheses (its proof does not read them)
  3. Write fp_blockProgS by the same lift as tr_blockProgS
  4. Delete slices_seq_sound, slices_seq_progress, prefix_run_clean, runBody_iff_slices, rejects_of_not_accepts, Render.Rejects, lowering_equivalence_of_blocks and update SORRY.md
  5. Point PoseidonV2.lean's headline at lowering_equivalence_of_stages
- **Deliverable.** `theorem tr_blockSim (R) (product) (H) (vkAddr) (g) (cd) : BlockSim R .traceReturn H vkAddr (permissive (callsOf product)) g cd` (no pin, no sorry); `theorem tr_blockProgS (R) (product) (hpin : trRetMptr R) (H) (vkAddr) (cd) : BlockProgS R .traceReturn H vkAddr product cd`; `fp_blockSim`, `fp_blockProgS`.
- **Accept.** `#cone_sorries tr_blockSim` and `tr_blockProgS` print 0; `grep -c 'rejects_of_not_accepts' formal/Midfall -r` is 0; scripts/checks.sh sorry register agrees with the tree.
- **Stop if.** The FinalPairing poisoned half turns out to read the snapshot: then keep it under a decode hypothesis and prove the poisoned conjunct of BlockSim .finalPairing by a direct walk (two statements).
- **Guidance.** tr_blockSim reads the closed Lean stage off the boundary: LeanRaw .pairing gives the decoding, Agree .pairing gives leanStage .pairing = .ok S, which already contains the pairing check. No hasAccumulator argument is needed there; fp_blockSim_of_blockSound needs it once (pv_hasAcc_false).

### SIM.8 — Restate the VkLoading row over StageInv

SEM · STATEMENT · box 1.5 h · Sonnet · after SIM.2

- **Goal.** vk_sim_clean, vk_poison_walk, vk_prog stated against StageInv .start and StageInv .vk, with the calldata-length clause coming from the block's own check.
- **Needs.** Blocks/VkLoading.lean sections 1-6; StageInv, LeanRaw, envelopeOk; Statements.lean (vkPins, vkProgressPins).
- **Does NOT need.** A decode hypothesis or a snapshot (digest D-8's missing hdec disappears).
- **Do.**
  1. Restate the three gaps
  2. List the pins the progress half needs beyond vkProgressPins (the six header slots and three calldata constants of digest D-8)
  3. Write the falsifier: with calldata of the wrong length the clean exit arm is unsatisfiable, so a run that exits normally refutes the row
- **Deliverable.** `theorem vk_blockSim (R) (product) (hR : R.Valid) (H) (vkAddr) (g) (cd) : BlockSim R .vkLoading H vkAddr (permissive (callsOf product)) g cd` stated (three named sorries behind it).
- **Accept.** The statements typecheck; a written list of the pins; the falsifier is a typechecked `example`.
- **Stop if.** `st.env.calldata.length == proofEnd + 32 + 32 * numInstances` cannot be obtained from `eq(calldatasize(), ..)` because calldatasize is the length modulo 2^256: stop and raise decision 5 (the EntryFrame bound).
- **Guidance.** The thirteen-step walk is unchanged. The only new content of the clean arm is LeanRaw .vk = envelopeOk, i.e. three equalities the block itself checks at VkLoading.yul:101-109.

### SIM.9 — leanStage coherence: the staged chain is a chain, with equal fields

ALG · PROOF · box 2.5 h · strongest · after SIM.1

- **Goal.** Prove leanStage_prefix strengthened to field agreement, including that snapshotOf succeeding implies snapshotXcriptRun succeeds with the same eight PCS reads.
- **Needs.** Stage.lean; Snapshot.lean (snapshotPcsStep, snapshotOf); Kzg/MultiOpen.lean (phaseA, phaseB, phaseC); TranscriptLog.lean (Pres lemmas).
- **Does NOT need.** Any Yul; the pairing.
- **Do.**
  1. Steps .transcript → .lagrange → .quotient: unfold the binds (linearize_eq_full for the last)
  2. Step .quotient → .pcs: unfold phaseA/B/C and show their transcript operations are pcsReads with nSets = a.qEvalSets.size
  3. Show a.qEvalSets.size = R.nSets from assertEmpty and the slot count of a decoded message list
- **Deliverable.** `theorem leanStage_agree (R) (hR : R.Valid) (H) (cd) (ms) (instW) (inst) (hdec : Decoded R cd ms instW inst) (S) (h : leanStage R H inst ms .pcs = .ok S) : ∃ Sq, leanStage R H inst ms .quotient = .ok Sq ∧ Sq.trace = S.trace ∧ Sq.alg = S.alg ∧ Sq.lagrange = S.lagrange ∧ Sq.a.x1 = S.a.x1 ∧ Sq.a.x2 = S.a.x2 ∧ Sq.b.fCom = S.b.fCom ∧ Sq.b.x3 = S.b.x3 ∧ Sq.c.x4 = S.c.x4 ∧ Sq.c.pi = S.c.pi` (to be typechecked when written; the existence form is SoundnessV3.lean:377).
- **Accept.** No sorry; a KAT at the exponent-model fixture: leanStage .quotient and leanStage .pcs agree on the listed fields for one accepted proof.
- **Stop if.** The byte-counting argument for a.qEvalSets.size = R.nSets needs the schedule-equals-layout lemma that xcript_total also needs: do SIM.10 first.
- **Guidance.** This is the one place the second copy of the PCS tail schedule (pcsReads) is checked against the original. It is the R-30 hazard in small; the agreement lemma is what makes it safe.

### SIM.10 — xcript_total: the transcript-only prefix always exists on decodable calldata

ALG · PROOF · box 2.5 h · strongest · after SIM.1

- **Goal.** Close the leaf xcript_total: no dynamic fault is reachable in parseTrace, readAlgebra and pcsReads once the calldata decodes.
- **Needs.** Stage.lean; Verifier.lean:94-217 and :839-934; Valid.circuitMeta, Valid.layout, SupportedV2; SimPins.compressedEnc; the scalar round trip frOfRepr? (frToRepr s).
- **Does NOT need.** linearize, phaseA/B/C algebra, the pairing, SoundSide.
- **Do.**
  1. Show the Lean read schedule (count and kind of reads) equals plan.slots for a valid render
  2. Show every read of a re-serialised decoded message succeeds
  3. Discharge the static panics (verifier.rs:118/134/348/366/370/410) from the key shape
- **Deliverable.** `theorem xcript_total (R) (hR : R.Valid) (hpins : SimPins R) (H) (cd) (ms) (instW) (inst) (hdec : Decoded R cd ms instW inst) : ∃ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x` with no sorry.
- **Accept.** No sorry; falsifier: without `hpins.compressedEnc` the statement is refuted at the deployment codec, where ofCompressed? is constant none (cite G1Agreement.lean:2006).
- **Stop if.** Valid.circuitMeta and Valid.layout cannot both hold at any faithful plan (review finding 6): this lemma is then vacuous; wait for the statements-area repair.
- **Guidance.** This is expected to exceed one ticket; split by function (parseTrace, readAlgebra, pcsReads). It is the parser row's entire Lean half.

### SIM.11 — The fault table as a gate and as a theorem statement

ALG · KAT · box 2 h · Sonnet · after SIM.1

- **Goal.** Make the fault-site table checkable: every Lean fault site string is classified, and the classification is the statement lean_fault_table.
- **Needs.** The table in this memo; the 88 site strings of Midfall/Halo2/Exec; scripts/checks.sh.
- **Does NOT need.** Any proof.
- **Do.**
  1. Write formal/docs/FAULTS.md: one row per site string with class (static / dynamic), owner block, contract check file:line
  2. Add a check to scripts/checks.sh: the set of site strings in Exec equals the set in FAULTS.md
  3. State lean_fault_table (SoundnessV3.lean:1368) in Stage.lean as a registered sorry marked FALSE AT HEAD until the reference repairs
  4. Add executable KATs for the three dynamic rows that can be driven without a pairing: logup.rs:460, kzg/mod.rs:479, DuplicatedQuery at x = 0
- **Deliverable.** FAULTS.md; the gate; `theorem lean_fault_table (R) (hR : R.Valid) (hpins : SimPins R) (H) (cd) (ms) (instW) (inst) (hdec : Decoded R cd ms instW inst) (hside : SoundSide R H cd) : (∃ S, snapshotOf R.E H R.vk inst ms none = .ok S) ∨ (∃ S2, snapshotOfAlgebra R.E H R.vk inst ms = .ok S2 ∧ S2.alg.x = 0) ∨ prepareMsgs (Gₜ := Gₜ) R.E H Features.solidity R.vk inst ms = .error (Fault.panic "proofs/src/poly/kzg/mod.rs:479")`.
- **Accept.** The gate prints 88 classified / 0 unclassified (63 distinct Fault.panic literals today); adding a new panic site to Exec without a FAULTS.md row reddens it; the three KATs evaluate true.
- **Stop if.** A site classified static turns out to depend on the proof bytes or the hash: that is a new divergence; stop and report it before anything else.
- **Guidance.** I classified by reading the main sites, not all 88. Treat every `static` as a claim to be confirmed when its row is written.

### SIM.12 — PCS row decomposition: the decode-exists lemma

SEM · STATEMENT · box 2 h · strongest · after SIM.2, SIM.1

- **Goal.** State the one obligation the PCS row has that no row had before: a normal exit with success = 1 implies the calldata decodes, and x = 0 and x3 in a point set revert.
- **Needs.** StageInv .quotient (Mirror, LeanRaw); Eip2537.Holds.g1Decodes; points_subgroup_checked_generator (Calldata.lean:1351); decodeCalldata_isSome_iff; the generator's coverage invariant (kzg/mod.rs:723-740 and its Lean port validateAbsorbedG1PrecompileCoverage); hasMultiPointSet.
- **Does NOT need.** The MSM algebra (that is the agreement half of the row).
- **Do.**
  1. State pcs_decoded: from StageInv .quotient, every run of the PCS slice that exits normally with success = 1 satisfies LeanRaw .pcs
  2. State pcs_zero_checks: on such an exit, for every decoding, the Lean x is non-zero and the Lean x3 is in no point set
  3. Derive the Agree .pcs existence half from lean_fault_table and those two
  4. Write the falsifiers
- **Deliverable.** Three typechecked statements (sorried), one proved derivation.
- **Accept.** The derivation `Agree .pcs existence from pcs_decoded, pcs_zero_checks, lean_fault_table` has no sorry of its own; falsifier for pcs_decoded: with the pi term removed from the pairing-input block the statement must fail (pi is then validated only by the pairing).
- **Stop if.** A proof commitment is found that reaches no G1MSM in the emitted PCS slice at the deployment: that is a real divergence (the contract would absorb an unvalidated point); stop and report.
- **Guidance.** pi is validated twice: by the one-pair MSM x3*pi (kzg/mod.rs:1898) and by the pairing. Under permissive calls a failed MSM sets success to 0, so only the success = 1 exit carries the validity facts.


---

## M5 — proof technology  (waits for: D-P68; 12 cards, 26 box-hours)

### T3.0 — Certificate-cost probe: choose how the kernel checks a symbolic execution

SEM · PROBE · box 2.5 h · strongest · after —

- **Goal.** Decide, by measurement, the certificate strategy for loop-bearing blocks: C1 rule application, C2 definitional execution with minimal fuel and chunking, or C3 reflective executor.
- **Needs.** Scratch files WP.lean, WPBridge.lean, WPTac.lean, LAGP.lean, Lits.lean; lagrangeLit; the vendored Step rules.
- **Does NOT need.** Any algebra, any other block, the generator, WP-G1.
- **Do.**
  1. Fuel sweep on LAGP.lean (take 4): fuel 20, 40, 80, 160; record profiler 'type checking'.
  2. Replace the 6-iteration loop by six straight-line copies of its body at the same fuel, to separate loop cost from fuel cost.
  3. C2 variant: redefine wp so fuel is spent only at loop iterations and calls (two-level definition: level n+1 is structural on syntax and uses level n for the next iteration and for call bodies); re-measure.
  4. C1 variant: prove three fuel-free AllRuns rules (assign of a builtin, cond, loop unroll) from Step inversion; drive the same slice with them; re-measure.
  5. Record the table and the chosen strategy in the ticket report.
- **Deliverable.** A table (strategy, fuel, steps, wp_run ms, kernel ms) of at least 8 rows and one chosen strategy, with the scratch files that produced it.
- **Accept.** A strategy whose kernel time on the 10-statement lagrange prefix (take 10, 16 iterations) is at most 2 s in total and varies by less than 2x between fuel 40 and fuel 160. Command: lim.sh 100 LAGP.lean with profiler on, for each row.
- **Stop if.** No strategy meets the threshold in the box: stop and open decision D-P68 (reflective executor) with the table attached. Do not raise maxRecDepth or maxHeartbeats to pass.
- **Guidance.** Measured so far: fuel 400 gives 33 s, fuel 40 gives 1.85 s for the same 30 steps; let-naming and literal replacement are not the cause (33.9 s and 33.3 s with them off). Loops cost about 62 ms per step against 1.2 ms on TraceReturn at the same fuel, cause unknown. Always run under lim.sh: one run with maxRecDepth 100000 went past 300 s.

### T3.1 — Land the wp engine and the lawful executable Bridge dialect

SEM · PORT · box 2 h · Sonnet · after —

- **Goal.** Move the proved engine into the tree unchanged in content.
- **Needs.** Scratch WP.lean (419 lines), WPBridge.lean (72), P1_Exec.lean (171); vendor/yul-semantics BigStep.lean; Midfall/Yul/Bridge.lean.
- **Does NOT need.** The driver tactic, any deployment fact, vendor edits.
- **Do.**
  1. Create Midfall/Yul/Wp.lean from WP.lean (imports YulSemantics only).
  2. Create Midfall/Yul/WpBridge.lean with execBuiltin, execOf, execOf_lawful, callsOf_graph placement decided by imports (callsOf lives in LoweringV2/Statements.lean, so honestExec goes in a LoweringV2 file), Bopen, Bopen_sound, Bfun, Bfun_sound, Bfun_live, Cnone, Cnone_sound.
  3. Add the falsifiers and the KAT below.
  4. Register nothing in SORRY.md: the files have no sorry.
- **Deliverable.** wp_sound, wpSS_sound, wpS_sound, allRuns_cons_wp, Bopen_sound, Bfun_sound, Bfun_live, execOf_lawful, honest_adequacy, with the signatures in the scratch files.
- **Accept.** #print axioms wp_sound = [propext]; Bopen_sound and execOf_lawful = [propext, Quot.sound]. Falsifier 1: an example that wpS at any fuel is False on Stmt.exprStmt of a valued builtin (add). Falsifier 2: wp 0 is False. KAT: Bopen at Bridge.nondetBlock does not prove a post that fixes the response, so the demonic quantifier is load-bearing. verify.sh --quick green.
- **Stop if.** Importing callsOf into Midfall/Yul creates a cycle: keep honestExec in LoweringV2 and report.
- **Guidance.** `leave` is a token once YulSemantics.Syntax is imported: write `| «leave» =>` in cases. Keep Stop a structure. The proof compiled first time apart from that keyword; do not restructure it.

### T3.2 — Totality: wpSS_exists

SEM · PROOF · box 2.5 h · strongest · after T3.1

- **Goal.** From one wp evaluation obtain a run as well as all-runs, so a block's StmtsTotal contract is a single execution and non-stuckness (finding C-1) is a by-product.
- **Needs.** Wp.lean; BLive and the statement wpSS_exists in scratch WPX.lean; Step constructors.
- **Does NOT need.** The driver, deployment facts, Bopen (use Bfun).
- **Do.**
  1. State the five-class conjunction mirroring wp_sound with an existential conclusion.
  2. Prove by induction on fuel, building the Step derivation in each case.
  3. Project wpSS_exists.
  4. Add the falsifier.
- **Deliverable.** theorem wpSS_exists (hB : BLive D B) (hC : ∀ funs fn args st, C funs fn args st = none) (h : wpSS D B C n funs V st ss Q) : ∃ V' st' o, ExecStmts D funs V st ss V' st' o ∧ Q V' st' o
- **Accept.** No sorry; #print axioms lists no sorryAx. Consumer: StmtsTotal for traceReturnLit under Bfun at the honest dialect, by one wp_run. Falsifier: BLive (Bopen ExternalCalls.none g) is false (a staticcall has no response).
- **Stop if.** At 1 h fewer than two of the five classes are done: commit WIP and report which constructor blocks.
- **Guidance.** Same shape and size as wp_sound (about 200 lines of cases). The call case needs the summary table to be empty, which is why hC is stated that way.

### T3.3 — Generated slice literals with pins

GEN · EMIT · box 1.5 h · Sonnet · after —

- **Goal.** Make every block proof start from a literal: sliceOf poseidonPv poseidonM q = lit_q, helpersOf .. = helpersLit, and the prefix.
- **Needs.** Scratch GenLits.lean; YulSemantics.SyntaxEq.stmtsBeq_eq; Instances/PoseidonValid.lean (poseidonPv, poseidonM).
- **Does NOT need.** Any semantics, any proof about the slices.
- **Do.**
  1. Add formal/scripts/gen_slices.lean writing Midfall/Instances/PoseidonSlices.lean (constructor-form literals via repr, width 100).
  2. Emit one pin theorem per literal: stmtsBeq_eq _ _ (by native_decide).
  3. Add a checks.sh line: regenerate to a temp file and diff.
  4. Record each native_decide axiom name.
- **Deliverable.** Midfall/Instances/PoseidonSlices.lean (generated, committed) with literals and pins for the 7 slices, the helpers and the prefix.
- **Accept.** File builds in at most 60 s; regeneration diff is empty; changing one literal number reddens the build; pins' axioms are standard plus native_decide axioms only.
- **Stop if.** A literal exceeds what the elaborator accepts in 60 s (pcs is 3607 tokens, not measured): split that slice into numbered chunks and pin the concatenation.
- **Guidance.** Use repr, not yul%: yul% leaves mkCall "name" unreduced and the transcript parser uses `end` as an identifier. Measured: helpers plus 4 slices, 1249 lines, 13.5 s. Regenerate after every WP-G1 card.

### T3.4 — TraceReturn at the deployment (calibration A)

SEM · PROOF · box 2 h · Sonnet · after T3.1, T3.3

- **Goal.** Meet PLAN-V2 WP-T's own accept line: TraceReturn re-proved in under 100 lines, and used.
- **Needs.** Scratch TR.lean (tr_all) and WPTac.lean; the T3.3 pins; BlockSound / exitOk in Blocks.lean; readBytes_storeWord_one.
- **Does NOT need.** Inv transfer, other blocks, the generic tr_blockSound.
- **Do.**
  1. Port wp_run as a tactic file under Midfall/Tools or Midfall/Yul.
  2. Port tr_all.
  3. Derive the per-deployment form of BlockSound at .traceReturn by rewriting with the pins.
  4. Report lines and profiler times.
- **Deliverable.** tr_all and tr_blockSound_dep stated on poseidonRender's slice and scope.
- **Accept.** At most 100 lines in total; kernel type checking at most 0.1 s (measured 11.5 ms); axioms standard plus pin axioms; a mutated literal (return length 31) makes the proof fail.
- **Stop if.** Transport from the literal to poseidonRender.slice needs more than the pins (poseidonRender is noncomputable): report the exact goal.
- **Guidance.** Leaf order is depth-first with the guard-skipped path first. State the boundary environment as ("success", s) :: Vr.

### T3.5 — Word and memory layer, accepted by the vkLoading residue

ALG · PROOF · box 2.5 h · strongest · after T3.1

- **Goal.** Supply the lemmas the residues need: Boolean words, touchMemory projections, read-over-write, calldata words.
- **Needs.** EVMExec.lean definitions (loadWord, storeWord, copyInto, copyReturn, wordFrom, touchMemory, b2w); the scratch VK.lean normal-exit leaf; statements loadWord_storeWord in WPX.lean.
- **Does NOT need.** ZMod, the verifier, loops.
- **Do.**
  1. Midfall/Yul/Word.lean: b2w_eq_zero_iff, one_and_b2w, b2w_and_b2w, iszero form, stated on the literal forms simp actually produces (1#256).
  2. touchMemory_memory, touchMemory_env and friends as rfl simp lemmas.
  3. loadWord_storeWord (equal and disjoint windows), loadWord_copyInto inside the window, loadWord_copyReturn.
  4. Close the VK.lean leaf with a named simp set.
- **Deliverable.** Simp set yul_word and the lemmas above; loadWord_storeWord with the statement in memo 3.3.
- **Accept.** The sorry in vk_all disappears; #print axioms vk_all has no sorryAx. Falsifier: loadWord (storeWord mem p v) (p+1) = v is refuted on a concrete memory.
- **Stop if.** The byte reassembly lemma (load of a stored word) is not closed at 1 h: deliver the disjoint case and the Boolean-word set, name the rest.
- **Guidance.** T.1 already recorded the technique: reduce to List.range maps with a per-index i < 32 fact; do not simp [storeWord] wholesale. My first simp attempt failed only because 1#256 did not match (1 : U256).

### T3.6 — vkLoading row at the deployment (calibration B)

SEM · PROOF · box 2.5 h · strongest · after T3.4, T3.5

- **Goal.** Close the first non-trivial block per deployment and measure lines per token.
- **Needs.** vk_all; Clean / Inv at .vk; Frame; the three sorried lemmas at Blocks/VkLoading.lean:728, :743, :756 as the content to reproduce.
- **Does NOT need.** Loops, staticcall, ZMod.
- **Do.**
  1. State the block's word-level post (memory window equals the payload, header words, calldata length facts, success = 1).
  2. Prove it by wp_run plus yul_word.
  3. Derive Clean at .vk from it, taking the decode hypothesis explicitly (finding I-9).
  4. Report lines per token and seconds.
- **Deliverable.** vk_block_dep and the derived row at poseidonRender.
- **Accept.** No sorry; at most 150 lines for 225 tokens; elaboration at most 5 s excluding imports; kernel at most 1 s.
- **Stop if.** Inv .vk needs a fact the block does not establish: report it as a premise gap, do not add a pin.
- **Guidance.** Execution is already measured: 74.7 ms, 4 leaves, kernel 250 ms at fuel 60.

### T3.7 — Statement-level driver with cuts, accepted by the lagrange slice

SEM · PROOF · box 2.5 h · strongest · after T3.0, T3.1

- **Goal.** Make a loop-bearing slice checkable: one declaration per statement group, failure paths cut instead of re-executed.
- **Needs.** The strategy chosen in T3.0; allRuns_cons_wp; lagrangeLit; helpersLit.
- **Does NOT need.** Algebra about the values.
- **Do.**
  1. Add the block rule, the loop-iteration rule and the call rule at the AllRuns level.
  2. Prove one cut lemma: from success = 0 after batch_invert the rest of the slice reverts.
  3. Drive the slice statement by statement, applying the cut at each failing fork.
  4. Report leaves and times.
- **Deliverable.** Tactic yul_exec and theorem lag_runs_dep: every run of the lagrange slice reverts or exits normal.
- **Accept.** No sorry; kernel type checking at most 60 s in total with default maxRecDepth and maxHeartbeats; open leaves before closing at most 6 (measured without cuts: 42).
- **Stop if.** The kernel budget is exceeded with the T3.0 strategy: stop, report the per-statement table, and reopen T3.0's decision.
- **Guidance.** Without normalisation the run needed 3125 kernel steps and timed out; with it wp_run took 21.5 s but the single proof term hit kernel deep recursion. Chunk; never raise maxRecDepth.

### T3.8 — Field-arithmetic bridge, accepted by x_n = x^(2^k)

ALG · PROOF · box 2 h · strongest · after T3.5

- **Goal.** Relate EVM mulmod/addmod at the scalar modulus to ZMod, under canonicity where needed.
- **Needs.** qvmToFr_add, qvmToFr_mul, qvmToFr_neg (Lowering/Qvm.lean:143-169); the statement mulmod_toFr in WPX.lean; the lagrange first-loop residue.
- **Does NOT need.** Yul semantics, memory.
- **Do.**
  1. Name the word operations (wMulmod, wAddmod) and prove them equal to the stepOp lambdas.
  2. Prove mulmod_toFr, addmod_toFr, and sub(r, x) as negation for x < r.
  3. Close: the first lagrange loop computes x ^ (2 ^ 6) in ZMod r.
- **Deliverable.** mulmod_toFr, addmod_toFr, neg bridge, and the x^(2^k) lemma.
- **Accept.** No sorry. Falsifier: the negation bridge fails at x = r (non-canonical) on a concrete value.
- **Stop if.** The modulus literal makes decide or norm_num exceed 60 s: state the lemmas over a variable modulus with a hypothesis.
- **Guidance.** qvmFrModulus_eq_r (Qvm.lean:133) is proved by decide.

### T3.9 — Lagrange row at the deployment (calibration C)

SEM · PROOF · box 2.5 h · strongest · after T3.7, T3.8

- **Goal.** Close the first block with loops and a demonic staticcall; this is the calibration point that prices everything after it.
- **Needs.** lag_runs_dep; batch_invert in helpersLit; Eip2537 modexp facts; Inv at .lagrange.
- **Does NOT need.** PCS, the quotient.
- **Do.**
  1. Word-level model of the slice (the ten lagrange values, l_blind, l_0, instance_eval).
  2. Yul equals model by yul_exec.
  3. Model equals the verifier's values (algebra only).
  4. Record tickets, lines per token, seconds.
- **Deliverable.** lag_block_dep and the derived row.
- **Accept.** No sorry; reported lines per token and kernel seconds; the composition consumes it.
- **Stop if.** More than two tickets: stop and re-estimate from the measured numbers before starting transcriptParser or pcs.
- **Guidance.** Either inline batch_invert (one call site in this slice) or give it a summary through the C table; decide by which is fewer lines after T3.7.

### T3.10 — Quotient numerator: classify, choose the route, state the contract

SEM · STATEMENT · box 2 h · strongest · after T3.3

- **Goal.** Replace 'the QVM interpreter refines vm/reference.rs' by a statement that exists and a route that has been measured.
- **Needs.** G1.3 merged (the numerator as AST); evalExprρ and memOfρ (Qvm.lean:189-214); evalQuotientIdentity (VmReference.lean:902).
- **Does NOT need.** The builder-correctness sorries (Qvm.lean:698, 713, 768, 995; QvmFold.lean:434).
- **Do.**
  1. Classify the 11 loops and 2 switches of the emitted numerator: straight-line compact blocks or bytecode interpreter.
  2. Run wp_run on the first 30 statements; record leaves and time.
  3. Choose route A (execute to a word program, reflective comparison with evalExprρ) or route B (generic interpreter refinement).
  4. State the block contract; restate identityCorrespondence_of_bridge, which the file itself refutes.
- **Deliverable.** A typechecked contract statement with a satisfiability witness and a falsifier, and the route decision with its measurement.
- **Accept.** The statement typechecks; the witness and falsifier are terms; the report gives tokens covered by each route.
- **Stop if.** G1.3 is not merged: do the classification on the text only and stop.
- **Guidance.** Counts at the deployment: 164 mulmod, 145 addmod, 183 mload, 62 mstore, 11 for, 2 switch, 13 case. No Yul-level statement exists in Qvm.lean, QvmFold.lean or VmReference.lean today.

### T3.11 — Executable exhibit as a KAT

INFRA · KAT · box 1.5 h · Sonnet · after T3.1

- **Goal.** Run the theorem's program before proving about it: the interpreter at the open honest dialect on real calldata.
- **Needs.** honestExec; asmOf poseidonPv poseidonM; fixture calldata through Lowering.repackThenEncode (Calldata.lean:257).
- **Does NOT need.** Any proof.
- **Do.**
  1. Build the fixture calldata as a Lean term.
  2. Run Interp.run (honestExec product) on it from an entry-like frame.
  3. Add byte-flip mutants.
  4. Wire into kat_gate.py.
- **Deliverable.** A Bool KAT in Instances/ and its expected verdicts.
- **Accept.** KAT evaluates in at most 30 s; the fixture run and each mutant's outcome are pinned as measured.
- **Stop if.** The fixture calldata cannot be produced in Lean: pin the synthetic run (measured: returns abiTrue in 9.8 s with the pairing mocked) and report the blocker.
- **Guidance.** On zero proof bytes with product := fun _ => true the program at HEAD returns true: that is a statement about the mock and the missing numerator, not about acceptance.


---

## M0 and M7 — gates and the definition of done  (waits for: D-P69; 10 cards, 15 box-hours)

### DG.0 — Make the gates green at the tip

INFRA · KAT · box 1 h · Sonnet · after —

- **Goal.** checks.sh exits 0 at the branch tip, with no new tooling.
- **Needs.** formal/SORRY.md row 18; formal/scripts/kat_gate.py (EXPECTED_KAT_TOTAL); Midfall/Instances/DeployedProfile.lean:857; Midfall/Instances/PoseidonCoherence.lean:502. Patch 0 and the kat_gate.py diff of the memo.
- **Does NOT need.** Any Lean tool, any change to checks.sh, any re-hash of a frozen file.
- **Do.**
  1. Apply Patch 0 (one SORRY.md row, two annotations) and the kat_gate.py diff.
  2. Run python3 scripts/kat_gate.py --static; if the total is not 1397 (G1.4b or G1.1-G1.3 landed first), move the pin to the printed number and name the added gates in the comment.
  3. Run bash scripts/checks.sh once, in full.
- **Deliverable.** One commit touching exactly those four files.
- **Accept.** python3 scripts/kat_gate.py --static prints 'ok (static): 1397 annotated known-answer checks in 102 files; no file was run'. bash scripts/checks.sh exits 0 and its KAT line reads 'ok: 1397 annotated known-answer checks pass across 102 files'. Falsifier: restore 'expect TRUE' on one line and the static pass fails in under 2 s naming the file.
- **Stop if.** Any gate other than the three known ones is red: report its first failing line and do not adjust it.
- **Guidance.** The full KAT pass was NOT run in this design session (102 lean processes, about 8 minutes); only the static pass and the two affected #evals were. Caught: review J-8 and J+1 (commit 2041977).

### DG.1 — Land the axiom gate

INFRA · PORT · box 2 h · strongest · after DG.0

- **Goal.** The axiom half of DONE is a build error, and a user axiom or unlisted native axiom in the headline cone is red today.
- **Needs.** $D/Done.lean (685 lines, import Lean only); $D/t1.imports, $D/t1.body, $D/donetest.tail (the self-tests); the ConeReport.lean, Midfall.lean and verify.sh diffs of the memo.
- **Does NOT need.** Report.lean, the sorry register, the closure manifest. Do not add Done.lean or ConeReport.lean to Frozen.sha256 in this ticket.
- **Do.**
  1. Copy Done.lean to formal/Midfall/Tools/Done.lean and import it from Midfall.lean before ConeReport.
  2. Create formal/scripts/DoneTest.lean: 'import Midfall.Tools.Done' plus the three Midfall imports of t1.imports, then t1.body and donetest.tail.
  3. Append the three #assert_axioms commands to ConeReport.lean.
  4. Apply the verify.sh diff (the Report.lean lines can be left for DG.2).
- **Deliverable.** Midfall/Tools/Done.lean; scripts/DoneTest.lean; ConeReport.lean with '#assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon [propext, Classical.choice, Quot.sound, sorryAx, <five D-P36a>] native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]'.
- **Accept.** lake env lean scripts/DoneTest.lean exits 0. bash scripts/verify.sh --quick prints 'assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: ok (9 named, 1 native)'. Falsifier, in a scratch copy of the ConeReport lines: delete sorryAx from the list and the output is 'error: ... 1 axiom(s) outside the allow-list / sorryAx: an unproved obligation is in the cone'.
- **Stop if.** check_orphans.py or kat_gate.py objects to a file under scripts/; or any of the 18 guarded messages differs (a toolchain difference): report the diff, do not edit the expectation.
- **Guidance.** Keep the keywords non-reserved (&" native "). The closure-hash test in DoneTest pins two hash values; they change only if the hash function or the toolchain changes. Caught: J-1, G-9, J-14.

### DG.2 — Sorry register by declaration, from the environment

INFRA · PORT · box 2.5 h · strongest · after DG.1

- **Goal.** The register is keyed by declaration name with status, cone membership and statement hash; an unrelated line shift no longer reddens the gate; a hole without a sorry token is seen.
- **Needs.** $D/report.body; $D/b/formal/scripts/{sorries.sh, gen_sorry.sh, lean_grep.py, checks.sh}; $D/SORRY.v3.md (the migrated table as it reads at HEAD); QUEUE card IDs for the 11 cone rows.
- **Does NOT need.** The closure section of checks.sh (DG.3). No change to any .lean file under Midfall/.
- **Do.**
  1. Create formal/scripts/Report.lean: 'import Midfall' then report.body.
  2. Replace sorries.sh, gen_sorry.sh, lean_grep.py; apply the sorry-register and native_decide hunks of the checks.sh diff.
  3. Migrate SORRY.md: new prose and header, then bash scripts/gen_sorry.sh.
  4. Write the owning card ID into the 'removed by' column of the 11 ROOT rows.
- **Deliverable.** scripts/Report.lean; SORRY.md with header '| declaration | module | kind | status | cone | statement | removed by |' and 60 rows at HEAD.
- **Accept.** The checks.sh sorry section prints 'ok: 60 sorried declarations, 11 in the headline cone, 1 REFUTED' and the native section 'ok: 123 uses, all under Midfall/Instances/' (numbers at HEAD). Controls, each run once and reverted: insert three comment lines above a sorry in Blocks.lean and the gate stays green; add 'theorem x : (1:Nat) = 2 := by admit' to a module without sorries and it goes red; add 'by decide +native' outside Instances and it goes red.
- **Stop if.** The text scan and the environment scan disagree on modules at the starting commit: report both lists.
- **Guidance.** gen_sorry.sh carries owners by declaration name, so a rename reads as remove plus add. checks.sh then runs Report.lean (about 20 s) once per section that needs it. Caught: J-2, J-8, J-10, J-12, I-10, G-10.

### DG.3 — Pin the closure of the frozen statements

> **Ordering.** Land after M1: D-P61's edits to `Halo2/Exec` change the closure of `LeanAccepts`, so a fingerprint taken earlier would have to be re-pinned at once.

INFRA · DECISION · box 1.5 h · strongest · after DG.2

- **Goal.** A change to any definition the frozen statements reach, inside the pinned zone, is a red gate whose diff names the definition.
- **Needs.** A signed decision on the pinned zone (see decisions). $D/b/formal/scripts/gen_closure.sh; the closure hunk of the checks.sh diff; #closure_fingerprint in Report.lean (already there after DG.2).
- **Does NOT need.** Any edit to the frozen .lean files.
- **Do.**
  1. Land gen_closure.sh with the signed PINNED pattern.
  2. bash scripts/gen_closure.sh; commit Midfall/LoweringV2/Closure.manifest and append the printed line to Frozen.sha256.
  3. Apply the closure hunk of checks.sh.
- **Deliverable.** Midfall/LoweringV2/Closure.manifest (972 DECL rows with the proposed pattern at HEAD); one new line in Frozen.sha256.
- **Accept.** checks.sh prints 'ok: 972 pinned declarations' (at HEAD). Falsifier on a throwaway branch: change the body of Midfall.Yul.Bridge.permissive to 'c' and checks.sh fails with a diff line 'DECL Midfall.Yul.Bridge Midfall.Yul.Bridge.permissive def ...'.
- **Stop if.** The manifest differs between two consecutive runs, or between macOS and the CI runner: report the differing lines; do not pin.
- **Guidance.** Do not hash pretty-printed text. Do not pin the generator, verifier or Instances zones before the statement freeze: every EMIT ticket would need a sign-off. Cross-platform stability of the hashes is not yet measured. Caught: J-6.

### DG.4 — State Done at the deployment, with its refutation

> **Changed by review.** The gate field is `GateAtV3` (= `HypothesesInhabitedV3` at a given calldata: `EntryFrameV3`, `G1CodecHeadlineLaws`, `keccak256`, `LeanAccepts`); `T7.lean`'s `GateAt` is the V2-shaped prototype. Add the fields `reference` and `vkArtifact`, drop `total` (it is conjunct 4), and re-prove `not_done_today` against `ValidV3`. See PLAN-V3 §6.

INFRA · STATEMENT · box 2 h · Sonnet · after DG.1

- **Goal.** DONE is one Lean proposition, landed and frozen, together with the theorem that says it does not hold today.
- **Needs.** A signed decision on the five fields (see decisions). $D/t7.body. Names verified at HEAD: LoweringEquivalence, Render.Valid, DeploymentV2, EntryFrame, Eip2537.Holds, SoundSide, CompleteSide, LeanAccepts, G1CodecLaws, HypothesesInhabited, RunBody, callsOf, ExternalGas.ofFun, renderHalo2Verifier, rootCtxOfVerifier, partsOf, mainAssemblyText, abiGuardText, poseidonRender, poseidonM, poseidonVerifierDump, poseidonRender_notValid.
- **Does NOT need.** A proof of any field. The fixture calldata term (Done takes it as a parameter).
- **Do.**
  1. Create Midfall/Instances/PoseidonDone.lean from t7.body (GateAt, hypothesesInhabited_of_gateAt, Total, ArtifactEq, Done, not_done_today, artifact_whole_false_today, not_done_today').
  2. Import it from Midfall.lean; add Done to the closure roots in Report.lean.
  3. If the repaired V3 statements have landed, write fields 1 to 3 against them instead.
- **Deliverable.** structure Midfall.Instances.PoseidonDone.Done (fixtureCd : Bytes) : Prop with fields headline, valid, gate, total, artifact; theorem not_done_today (cd : Bytes) : ¬ Done cd.
- **Accept.** #print axioms Midfall.Instances.PoseidonDone.not_done_today shows no sorryAx. #assert_axioms on it with native [poseidonModel_isOk, deciding_layout] prints 'ok (8 named, 2 native)'. The falsifier W2 asks for is not_done_today itself; the witness is by design absent.
- **Stop if.** A field does not typecheck against the names above, or the human has not signed the field list.
- **Guidance.** artifact_whole_false_today uses native_decide, so the file must live under Midfall/Instances. When field 2 or field 5 becomes true the corresponding refutation stops compiling: delete it in that ticket, that is the signal. Caught: I-7, J-1, H+1.

### DG.5 — The fixture calldata as a pure term

GEN · KAT · box 1.5 h · Sonnet · after DG.4

- **Goal.** Done's parameter has a value: the calldata of the tracked fixture proof, as a term the kernel can see.
- **Needs.** formal/fixtures/conformance/poseidon/proof.bin and instances.json; Lowering.repackThenEncode (Calldata.lean:257), not the frozen calldataOf, which repacks twice; the layout of the repaired render.
- **Does NOT need.** Any Yul semantics. Any proof about the calldata.
- **Do.**
  1. Define poseidonFixtureCalldata : Bytes as a hex literal generated once from the fixture.
  2. Add an IO KAT that reads proof.bin and instances.json, applies repackThenEncode, and compares with the term.
  3. Add a negative control: the term with one byte flipped is not equal.
- **Deliverable.** Midfall.Instances.PoseidonExhibit.poseidonFixtureCalldata : Bytes; fixtureCalldata_matchesFile_ok : IO Bool with '-- expect true'.
- **Accept.** The KAT prints true; the flipped-byte control prints false; kat_gate.py --static total moves by exactly the gates added and the pin is moved in the same commit.
- **Stop if.** repackThenEncode does not return ok on the fixture at the render's layout: that is a finding for the object area, report the error value.
- **Guidance.** This card may be owned by the object area; it is listed here because Done cannot be instantiated without it. The frozen calldataOf never returns ok (review item 5).

### DG.6 — No registered sorry may be refuted

INFRA · KAT · box 0.5 h · Sonnet · after DG.2

- **Goal.** A sorry whose negation is proved in the tree is a red gate, so False can no longer sit in the cone unnoticed.
- **Needs.** The ticket (statements area) that deletes poseidon_valid or turns Valid into a hypothesis. #assert_no_refuted_sorry from Done.lean.
- **Does NOT need.** Any change to the tool.
- **Do.**
  1. After poseidon_valid is gone, add '#assert_no_refuted_sorry [Midfall]' to scripts/Report.lean.
  2. Record in EXECUTION that a refutation is landed as 'theorem <name>_refuted : ¬ type_of% @<name>'.
- **Deliverable.** One line in scripts/Report.lean.
- **Accept.** The report prints 'assert_no_refuted_sorry: ok (N sorried theorems, M proved negations scanned)'. Falsifier: DoneTest case (j). At HEAD the same command errors with 'Midfall.Instances.PoseidonV2.poseidon_valid is refuted by Midfall.Instances.PoseidonValid.poseidonRender_notValid'.
- **Stop if.** The command still errors after the statements ticket: a second refuted sorry exists; report its name.
- **Guidance.** It finds only refutations someone landed. rejects_of_not_accepts is reported false by the review and stays OPEN until its refutation is a theorem. Caught: J-4.

### DG.7 — CI that runs and can pass

INFRA · PROBE · box 2 h · Sonnet · after DG.0, DG.2

- **Goal.** Every push to formal/** runs the gates on a runner that can hold the build, and one green run has been observed.
- **Needs.** The formal.yml of the memo; the runner label ubuntu-latest-16-core-x64 (ci.yaml:47, 65, 92); a human to make the check required on formal/baseline.
- **Does NOT need.** Any Rust job. Full verify.sh in CI (ram_guard.sh is macOS-only).
- **Do.**
  1. Replace .github/workflows/formal.yml and push.
  2. Read the first run: note where it fails, if it does, with the log line.
  3. Record wall time per step and the cache size from the log.
  4. Push a throwaway branch formal/ci-negctl with EXPECTED_KAT_TOTAL off by one and confirm it is red; delete the branch.
- **Deliverable.** One green workflow run on formal/baseline and one red run on the control branch, both cited by run number in the commit body.
- **Accept.** The green run's last step prints 'verify.sh: ok (--report)'. The control run fails in the gates step with 'KAT TOTAL MOVED'.
- **Stop if.** The runner label is not available to this workflow, or lean-action rejects an input name: report the log line; choosing another runner is a human decision.
- **Guidance.** Nothing here was run in this session. Unverified: lean-action's input names beyond lake-package-directory, the time on that runner, whether the closure hashes agree with macOS, and whether any KAT reads an untracked file. Caught: J-7, J-8.

### DG.8 — STATUS generated from the report

INFRA · PORT · box 1 h · Sonnet · after DG.2

- **Goal.** STATUS.md is one page that opens with tool output and carries the English statement skeleton with its trusted-base table.
- **Needs.** bash scripts/verify.sh --report; section 7 of the memo; EXECUTION section 6 (progress measure wording).
- **Does NOT need.** A new script. History: nothing from the present 344-line file survives unless it is still true.
- **Do.**
  1. Overwrite docs/STATUS.md: the report output verbatim, then at most ten lines, then the English statement with each trusted item marked PROVED-AWAY, TESTED-BY <KAT name> or UNTESTED.
  2. Replace the progress-measure bullet of EXECUTION section 6 by the four report lines; keep the cone count only as the last check of DONE.
- **Deliverable.** docs/STATUS.md of at most 80 lines.
- **Accept.** wc -l docs/STATUS.md is at most 80. The first block of STATUS.md equals the output of 'bash scripts/verify.sh --report' at that commit (diff is empty).
- **Stop if.** Something in the old STATUS cannot be confirmed by a command at the current commit: leave it out and list it in the commit body.
- **Guidance.** Caught: J+2, I-13 (stale and contradictory numbers), J-13 (probe theorems cited but not in the tree).

### DG.9 — The DONE commit

INFRA · KAT · box 1 h · Sonnet · after DG.3, DG.4, DG.5, DG.6, DG.7, DG.8

- **Goal.** DONE is asserted by the build and replayed.
- **Needs.** theorem poseidon_done : Done poseidonFixtureCalldata, proved by the other areas; the decided curve-axiom list.
- **Does NOT need.** Any new statement.
- **Do.**
  1. Point the #assert_axioms line of ConeReport at Midfall.Instances.PoseidonDone.poseidon_done and delete sorryAx from its list; list every native owner by name.
  2. Add '#replay_native Midfall.Instances.PoseidonDone.poseidon_done' to scripts/Report.lean.
  3. Add Done.lean, ConeReport.lean and PoseidonDone.lean to Frozen.sha256; widen PINNED to every zone.
  4. Fill the English statement: paste the two lists from the tool output.
- **Deliverable.** ConeReport.lean asserting poseidon_done without sorryAx; STATUS.md with the final statement.
- **Accept.** 'assert_axioms Midfall.Instances.PoseidonDone.poseidon_done: ok (k named, n native)' with no 'unused allowances' line; 'replay_native ...: ok (n native axiom(s) re-evaluated to true)'; 'cone_report ...: 0 sorried leaves ... [CLOSED]' with no ROOT IS VACUOUS line; 'exhibits: 4 PRESENT, 0 MISSING of 4'; 'block_coverage ...: 7 INTEGRATED'; CI green.
- **Stop if.** #replay_native exceeds the 60 s rule for a single axiom: split that deployment fact, do not skip the replay.
- **Guidance.** Replay cost today is 10.2 s for one axiom; at DONE it is the sum of every native owner in the cone.

---

## Plan-level cards (written with PLAN-V3; decisions as named on each card)

These complete the queue: the cut-over, the W13 repair of the present tree, the four remaining
block rows (each a SKELETON that issues its own PROOF children), the headline and the end-to-end
statement. They follow the same format. Model routing (EXECUTION-V2 W10) is on each card.

### PL.0 — Cut over to PLAN-V3

INFRA · DECISION · box 0.5 h · orchestrator, no subagent · after D-P60 is signed

- **Goal.** `QUEUE.md`, `STATUS.md` and `PLAN.md` point at PLAN-V3, with nothing proved deleted and
  no card in flight lost.
- **Needs.** `design.md` quoting the sign-off of D-P60; PLAN-V3 §10 (the mapping table from live
  cards to V3 cards).
- **Does NOT need.** Any `.lean` edit; any other decision of PLAN-V3 §2.2 (each gates its own cards).
- **Do.**
  1. Let the card in flight return and merge it under its own rules.
  2. Tag `formal/v2-cutover`.
  3. Append to `QUEUE.md` the section "V3" with one line per card of this file in the order of
     PLAN-V3 §5, each marked READY, or BLOCKED on the decision it names.
  4. Apply PLAN-V3 §10's table to the live cards: mark each CONTINUES, MERGED INTO <V3 id> or HELD.
  5. Point `PLAN.md`'s header and `STATUS.md`'s plan line at `docs/plans/PLAN-V3.md`.
- **Deliverable.** One docs commit. No Lean change.
- **Accept.** `git diff --stat` touches only `formal/docs/`; every live READY card has exactly one of
  the three marks; `bash docs/plans/V3-evidence/check.sh` exits 0 at the tip.
- **Stop if.** `check.sh` fails at the tip: an evidence file no longer typechecks, so the card that
  relies on it is re-measured before it is queued.
- **Guidance.** Do not copy the cards into `QUEUE.md`; link them. `QUEUE.md` stays one line per card.

### PL.1 — W13: take the refuted sorries out of the tree

INFRA · PORT · box 1.5 h · Sonnet · after DG.6

- **Goal.** No registered sorry has a proved negation, by statement or by instance.
  `#assert_no_refuted_sorry [Midfall]` passes.
- **Needs.** `Midfall/Instances/PoseidonV2.lean:190` (`poseidon_valid`, sorry), `:229`
  (`poseidon_block_contracts`), `:247` (`lowering_equivalence_poseidon`), `:255`;
  `Midfall/Instances/PoseidonValid.lean` (`poseidonRender_notValid`);
  `Midfall/Lowering/QvmFold.lean:327` (`identityCorrespondence_of_bridge`, sorry) and `:718`, `:749`
  (`bridgeCounterexample_hypotheses_hold`, `bridgeCounterexample_conclusion_fails`);
  `Midfall/Tools/ConeReport.lean` (the root list); `docs/plans/V3-evidence/ReviewProbes.lean` §1.
- **Does NOT need.** Any frozen file. Any change to `LoweringEquivalence`.
- **Do.**
  1. Delete `poseidon_valid` AND its consumers `lowering_equivalence_poseidon` and
     `lowering_equivalence_poseidon_is_the_root`. Do NOT restate them with
     `(hR : poseidonRender.Valid)`: that hypothesis is refuted in the tree, so the lemma would be
     provable by `absurd` — the trap D-P54 rejects. Keep `poseidon_quotient_block`,
     `poseidon_rejects` and `poseidon_block_contracts` (the last already takes `hR` as an argument
     and is used by nothing else).
  2. ConeReport: replace the deleted root by `Midfall.LoweringV2.lowering_equivalence_of_blocks`.
  3. `identityCorrespondence_of_bridge`: delete it, or restate it with the missing hypothesis the
     counterexample violates and land the restated form with a witness. Report which.
  4. Extend DG.6's detector, or add a hand-listed exception file, so the by-instance refutation is
     reported; regenerate `SORRY.md`; delete the `false_from_registered_holes` probe from
     `ReviewProbes.lean` (it no longer elaborates, which is the evidence).
- **Deliverable.** The deletions; the ConeReport root; the decision on
  `identityCorrespondence_of_bridge`, recorded in the report.
- **Accept.** `#assert_no_refuted_sorry [Midfall]` passes; the report prints `0 REFUTED`;
  `grep -rn 'theorem lowering_equivalence_poseidon' Midfall` is empty; `verify.sh --quick` green.
- **Stop if.** Another registered sorry is reported REFUTED: list it and stop; each is its own card.
- **Guidance.** W7: STATUS says "headline: not stated" until M7. D-P54 stands: no theorem takes
  `poseidonRender.Valid` as a hypothesis while its negation is proved.

### RECON.1 — One `ValidV3`: reconcile the two typechecked texts

GEN · STATEMENT · box 2.5 h · strongest · after OBJ.7, ST.1 · before ST.2, OBJ.0 (D-P67), ST.6

- **Goal.** Exactly one text of `Render.ValidV3`, `PayloadAgrees` and `programOk` in the staging
  module, typechecked, with its clause table at F1 — so that D-P67 is signed on one statement.
- **Needs.** The two existing texts and their differences (found in review of PLAN-V3):
  `docs/plans/V3-evidence/lean/object/ObjectV3Full.lean:687-704` (`PayloadAgrees`: has `digest`,
  no `delta`), `:747-755` (`programOkWith`: codegenStruct, constsCoherent, callsResolved, noShadow,
  closed, `0x80 ≤ transcriptMptr`), `:762-779` (`ValidV3`, seven clauses, `supported : SupportedV2`);
  `docs/plans/V3-evidence/lean/statements/StatementsV3.lean:373-430` (`PayloadAgrees`: has `delta`,
  no `digest`), `:613-643` (an 18-clause `ValidV3` with `vkPins`, `exitDiscipline`, `cdBound`),
  `:233` (`noShadowB`), `:526` (`ExitDiscipline`); `Generator/Artifacts.lean:130-134` (`frDelta` is
  inert at F1).
- **Does NOT need.** Any frozen edit (staging module only); any block proof.
- **Do.**
  1. Take `ObjectV3Full.lean`'s seven-clause structure as the base.
  2. Add to `programOk`: the frozen token clause (`codegenAgrees`), ONE exit scan (the one SIM.3
     lands), `cdBound` (`proofEnd + 32 + 32 * numInstances < 2 ^ 256`), and `hasMultiPointSet`.
  3. `PayloadAgrees`: the object text's fields (digest, header words, omega, omegaInv, nInv, the
     accumulator quadruple, G1 base, G2 base, −s·G2, fixed and permutation commitments). Drop the
     `delta` field: show by `#eval` that changing `R.E.delta` changes `R.generated` (so `generated`
     pins it) and that changing `inputs.frDelta` alone changes nothing at F1.
  4. `supported`: keep `SupportedV2`, whose `wf` field means D-P59's repaired `WellFormed` once R.7
     has merged; delete `SupportedV3` / `WellFormedV3` from the staging module.
  5. Re-run the clause table at F1 and land a falsifier per clause (one mutated render each).
- **Deliverable.** One `structure Render.ValidV3`, one `PayloadAgrees`, one `programOk`; the clause
  table as `#eval … -- expect` lines; `not_done_today` re-proved against it.
- **Accept.** `grep -c 'structure.*ValidV3' ` over the staging module is 1; every clause has a
  witness line and a falsifier line; `delta := 2` falsifies `generated` (not `payload`).
- **Stop if.** `generated` does not pin `E.delta` at F1 (then a `qblocks` clause is needed: report
  the exact function through which `delta` should reach the text).
- **Guidance.** The 18-clause text in `StatementsV3.lean` is the fallback if D-P67 is struck; keep
  it in the evidence directory, not in the staging module.

### RECON.2 — One composition: the four V3 obligations from the staged rows

SEM · SKELETON · box 2.5 h · strongest · after SIM.1, ST.1, RECON.1 · before SIM.0 (D-P68), SIM.2, ST.5

- **Goal.** The staged architecture concludes the V3 headline's four obligations, with the calldata
  size bound reaching every row, and no second composition in the tree.
- **Needs.** `docs/plans/V3-evidence/lean/soundness/SoundnessV3.lean`: `StageInv` (:539),
  `Render.SimContracts` (:604), `two_outcomes_of_exitShape` (:1023), `ProgContracts` and
  `completeness_of_progs` (:1065, :1197), `lowering_equivalence_of_stages` (:1226);
  `docs/plans/V3-evidence/lean/statements/StatementsV3.lean`: `TwoOutcomes` (:550),
  `twoOutcomes_of_scans` (:581), `RejectsV3`, `CompleteV3`, `TotalV3`,
  `lowering_equivalenceV3_of` (:882); `Midfall/LoweringV2/Blocks.lean:56-64` (`Frame`);
  `Midfall/Lowering/Inv.lean:748-749` (the `Nat` length clause of `Inv .vk`).
- **Does NOT need.** Any block proof; `BlockSound`, `BlockContractsAt`, `BlockRow` (the old rows
  are not composed again).
- **Do.**
  1. Land the falsifier first: with `cd' := cd ++ 2^256 zero bytes`, the vkLoading row of
     `SimContracts` as written is false (state it on a toy render or as a `¬` about the statement
     shape; W12).
  2. Add `cdSize : cd.size < 2 ^ 256` to `Frame` (a §6 refinement: a field added to `Frame`).
     Check the five block files still compile; `prefix_sim` / `prefix_prog` now take it from
     `EntryFrameV3.cdSize`.
  3. Re-gate `ProgContracts` and `completeness_of_progs` on `G1CodecHeadlineLaws` (four laws)
     instead of the seven frozen ones; list any row that needs a fifth law (then D-P64's bundle
     grows, a decision).
  4. Restate the conclusions: `rejectsV3_of_sims (hR : R.ValidV3) (hsim) : RejectsV3 R product`
     and `completeV3_of_progs (hR) (hprog) : CompleteV3 R product`. `SimPins`' fields come from
     `G1CodecHeadlineLaws` and from `programOk` (`hasMultiPointSet`), not from a separate bundle.
  5. Conjunct 3: use `twoOutcomes_of_scans` (unconditional in the state); delete the
     entry-frame-guarded `two_outcomes_of_exitShape` route, keeping `tr_exit_any` and `quiet_init`
     as its leaves.
  6. Delete `lowering_equivalence_of_stages`; the headline is `lowering_equivalenceV3_of` applied
     to the four obligations.
- **Deliverable.** `rejectsV3_of_sims`, `completeV3_of_progs` (proved from rows and named leaves);
  the `Frame.cdSize` field; the leaf list of each obligation.
- **Accept.** `#cone_sorries` of each obligation lists named leaves only, none of them the V2
  `prog_slices_decomp`; `grep -c 'lowering_equivalence_of_stages\|completeV3_of_blocks'` over
  `Midfall/` is 0; the padded-calldata falsifier is in the tree.
- **Stop if.** A row needs a hypothesis no V3 conjunct supplies (name the row and the hypothesis:
  that is a frozen-surface question for D-P64).
- **Guidance.** This card is why ST.5 must NOT build a composition from the old block rows, and why
  SIM.2's stop condition about `Render.scope` no longer applies (ST.3 lands the scope in M2, before
  SIM.2: state `BlockSim` over the new scope from the start).

### HLP.1 — Helper call summaries

SEM · PROOF · box 2.5 h · strongest · after T3.1, T3.3, T3.5

- **Goal.** One call summary with its `CSound` proof for each helper the rows call, so that a row
  executes a call site in one step.
- **Needs.** `docs/plans/V3-evidence/lean/prooftech/WP.lean` (`CT`, `CSound`, `wp_sound`),
  `WPTac.lean` (`wp_run`); the literal helpers (T3.3): `fail`, `scalar_inv`, `transcript_init`,
  `common_word`, `common_uncompressed_g1`, `squeeze_to`, `batch_invert`, `ec_pairing`, and after the
  G1 batch `q_program_fail`, `q_pow5`; the word and memory layer (T3.5). Call-site counts at F1
  (`object/Parse1.lean`): `squeeze_to` 10, `common_uncompressed_g1` 9, `q_program_fail` 13,
  `q_pow5` 6, `scalar_inv` 3 in PCS.
- **Does NOT need.** Any row; any Lean-verifier fact (summaries are word-level: "writes these
  bytes, returns this word, or reverts"); the accumulator helpers (no F1 slice calls them).
- **Do.**
  1. For each helper state its summary as a word-level pre/post over memory and the returned
     values, including the revert arm, for ANY call relation and gas oracle (`Bopen`).
  2. Prove each by `wp_run` on the literal body. `batch_invert` has the one loop: state its
     invariant, or leave it as a named leaf with the measured kernel cost (it is calibration C's
     subject).
  3. Assemble the table `C : CT` and prove `CSound`.
  4. Re-run T3.6's vkLoading proof with the table in place and record the change in kernel time.
- **Deliverable.** `helperSummaries : CT (Bridge.Dialect c g)` and
  `helperSummaries_sound : CSound (Bridge.Dialect c g) helperSummaries`, with one named lemma per
  helper.
- **Accept.** `#assert_axioms helperSummaries_sound` (standard three plus the slice pins);
  `#cone_sorries` lists at most `batch_invert`'s loop leaf; a falsifier: a summary with one wrong
  written word fails its proof (shown once, on `common_word`).
- **Stop if.** A helper needs a fact about the Lean verifier to state its summary (then the summary
  is at the wrong level: keep it word-level); `ec_pairing`'s summary needs the base-point pins
  (state it over the bytes in memory instead).
- **Guidance.** Summaries are the family rule (EXECUTION-V2 §4) applied to helpers: one shared
  shape, one row per helper. `squeeze_to` and `common_*` carry the keccak terms: keep `keccakOf
  (readBytes …)` uninterpreted.

### TOT.1 — Totality at F1: `TotalV3 poseidonRender`

SEM · PROOF · box 2.5 h · strongest · after ROW.FP, T3.2, ST.13, ST.16, SIM.6

- **Goal.** `theorem poseidon_total (product : PairingProduct) : TotalV3 poseidonRender product`:
  from every entry frame, under the honest precompiles and any total gas oracle, a run exists.
- **Needs.** `wpSS_exists` (T3.2) and `Bfun`, `Bfun_live` (`prooftech/WPX.lean`); `execOf_lawful`,
  `callsOf_graph` (`prooftech/P1_Exec.lean`); the per-slice symbolic executions of the ROW cards;
  `total_append`, `run_join` (`soundness/SoundnessV3.lean`); `runBody_mono` (ST.13); ST.16's
  requirements table; `BodyTotal`, `GasTotal`, `TotalV3` (`statements/StatementsV3.lean:758-870`).
- **Does NOT need.** `LeanAccepts`, `SoundSide`, `CompleteSide`, or any snapshot: totality is for
  every calldata. The permissive relation (the honest one is the statement; a permissive run
  exists trivially and is not the claim).
- **Do.**
  1. Gas-obliviousness: the program executes no `gas()` (decidable scan on the literal program),
     so `Step` at `ExternalGas.ofFun f` and at any total `g` agree on it. This lifts rows stated
     at `ofFun fun _ => 0` to every total oracle.
  2. Per-slice existence from every `StageInv` state AND from every `Poisoned` state, at the
     honest dialect: `wpSS_exists` with `Bfun` on the same symbolic execution the row used. The
     T3.2 falsifier shows `BLive` fails for `Bopen` with no calls: use `Bfun`, never `Bopen`, here.
  3. Prefix existence from every `EntryFrameV3` state (SIM.6's `prefix_prog` gives the accepted
     case; the rejecting exits are reverts, which are runs).
  4. Compose with `total_append` and `run_join`; conclude `BodyTotal`, then `TotalV3`.
- **Deliverable.** `poseidon_total`; the gas-obliviousness lemma `step_gas_oblivious`.
- **Accept.** `#assert_axioms poseidon_total` (standard three plus the slice pins); a falsifier: a
  toy program that calls an undefined function has no run (`¬ ∃ obs, …`, proved), so the statement
  is not trivially true.
- **Stop if.** A slice has a path on which the honest relation gives no response (a `staticcall`
  to an address outside the four precompiles): that is a stuck path in the model and a finding
  about the generated code — report it.
- **Guidance.** This is conjunct 4 of the headline and the `total` field of `Done`. It does NOT
  follow from the soundness rows: `wp_sound` with `Bopen` is an all-runs statement.

### ROW.TP — TranscriptParser row: skeleton and requirements table

SEM · SKELETON · box 2 h · strongest · after SIM.2, SIM.10, T3.6 (calibration B), OBJ.2

- **Goal.** `BlockSim` and `BlockProgS` at `.transcriptParser` for fixture F1, derived from named
  leaves, with the requirements table computed on the literal slice.
- **Needs.** The literal slice (T3.3; 44 statements, 923 tokens); `StageInv` at `.vk` and
  `.transcript` (`SoundnessV3.lean`: `LeanRaw`, `MirrorAt`, `Agree`); `rawDecode`,
  `decodeCalldata_eq_raw`; `pcsReads`, `snapshotXcriptRun`; the helpers `transcript_init`,
  `common_word`, `common_uncompressed_g1`, `squeeze_to` (literal, T3.3); template
  `proofs/solidity-verifier/templates/partials/verifier/TranscriptProofParser.yul:63-68, 319, 382,
  416-420`; fault-table rows 7, 9, 10, 11 (`design/soundness.md` §5).
- **Does NOT need.** `ofEip?` or any curve fact (point validity is NOT known at this boundary: put
  nothing about decoded points outside `Agree`); the algebra of `linearize`; any PCS code.
- **Do.**
  1. `wp_run` the slice with the four helpers as call summaries (`CSound`), not inlined. State one
     summary per helper first and prove each by `wp_run` on its body.
  2. Read the residue at the normal exit as a word program: the five copies, the range checks, the
     absorb/squeeze schedule.
  3. State the SEM leaf `tp_computes`: every run reverts, or exits normal with `success = 1`,
     `Mirror … .transcript`, `(rawDecode …).isSome`, and the challenge slots holding the stated
     keccak terms.
  4. State the ALG leaf `tp_agrees`: if `Decoded R cd ms instW inst`, then
     `leanStage R H inst ms .transcript = .ok S` and `Inv … .transcript … S` holds of that memory.
     Its core, "the Lean prefix's transcript is the layout's schedule", is ONE lemma used five times.
  5. Prove the glue `tp_blockSim` and `tp_blockProgS` from the two leaves; register the leaves.
- **Deliverable.** `tp_blockSim`, `tp_blockProgS` (proved from leaves); `tp_computes`, `tp_agrees`
  (stated, with a requirements table of one row per statement group and per helper).
- **Accept.** `#cone_sorries tp_blockSim` lists exactly the two leaves and the helper summaries not
  yet proved; a falsifier: with one literal of the slice changed, `tp_computes`'s residue differs
  (shown by `#eval` of the interpreter on the fixture calldata); children are in `QUEUE.md`.
- **Stop if.** A fact about a decoded point is needed outside `Agree`; `wp_run` exceeds 60 s on the
  slice with summaries; the `x3` truncation residue does not match `Arith.lean:284`.
- **Guidance.** This is the first hash-heavy block: keccak stays the uninterpreted `keccakOf
  (readBytes …)`; relate it to the Lean transcript with `hashOfBytes_readBytes`
  (`Yul/Bridge.lean:451`). The non-canonical-scalar and out-of-range-G1 reverts are fault-table
  rows 7 and 9: the contract's check and `rawDecode`'s guard must be the same inequality.

### ROW.Q — Quotient row: contract and route

SEM · SKELETON · box 2.5 h · strongest · after T3.10 (calibration D), OBJ.2, SIM.2

- **Goal.** `BlockSim` and `BlockProgS` at `.quotientLin` for F1 from named leaves, on the route
  T3.10 chose.
- **Needs.** T3.10's contract and classification of the 6,572 tokens; `linearizeFull`,
  `linearize_eq_full` (`SoundnessV3.lean`); `evalExprρ`, `memOfρ` (`Lowering/Qvm.lean:189-214`);
  `quotientFold_matches_linearization` (`Lowering/QvmFold.lean:376`, open);
  `Generator/Quotient/VmReference.lean:902` (`evalQuotientIdentity`); the literal slice with
  `q_program_fail`, `q_pow5`; fault-table row 17.
- **Does NOT need.** The bytecode builder's correctness (`qvm_compile_correct_*`,
  `builder_segments_total`): those are for the ∀-render theorem (X4).
- **Do.**
  1. Split the slice by T3.10's classes (straight-line generated lines, the interpreter loop, the
     linearization scope) and give each a SEM leaf.
  2. Route A: `wp_run` each straight-line class to a word program; state the reflective check
     "word program = `evalExprρ` of the identity" as a Bool evaluated in `Instances/`.
     Route B: state the interpreter-loop refinement against `evalQuotientIdentity` once.
  3. State the ALG leaf: the folded value equals the Lean `linearize` result, under `SoundSide`.
  4. Restate `identityCorrespondence_of_bridge` (`QvmFold.lean:338`): the same file proves its
     hypotheses can hold while its conclusion fails. Land the corrected statement with a witness.
  5. Prove the glue; register the leaves.
- **Deliverable.** `q_blockSim`, `q_blockProgS` from leaves; the corrected
  `identityCorrespondence_of_bridge`; the requirements table (one row per identity family).
- **Accept.** `#cone_sorries q_blockSim` lists the named leaves only; the `Inv .quotient` clauses for
  `QUOTIENT_EVAL_MPTR` and the selector accumulators are no longer `true` by default (a perturbation
  KAT changes them).
- **Stop if.** No class is dischargeable by route A's check within 60 s on one identity; the
  logup helper identity the contract computes is not the one `linearize` checks outside the
  `SoundSide` set (that would be a new divergence: report it with the two formulas).
- **Guidance.** This row is the only reader of `SoundSide`. Largest single risk of the plan
  (PLAN-V3 §9.4): expect to split into 6–10 PROOF children, one per line family.

### ROW.PCS — PCS row: decode-exists and the MSM loops

SEM · SKELETON · box 2.5 h · strongest · after ROW.Q, SIM.12, T3.9 (calibration C), M1

- **Goal.** `BlockSim` and `BlockProgS` at `.pcs` for F1 from named leaves.
- **Needs.** The literal slice (225 statements, 3,623 tokens) and the MSM helpers; `Mirror`,
  `Agree` at `.quotient`; SIM.12's `decode_exists` statement; `Holds.g1Decodes`;
  `decodeCalldata_isSome_iff`; `hasMultiPointSet` (true at F1: sets `[[0],[0,1],[0,1,-9]]`);
  `PayloadAgrees.fixedComms`, `.permutationComms`, `.omega`, `.omegaInv`; generator
  `proofs/solidity-verifier/src/lowering/kzg/mod.rs:723-740, 1503, 1592, 1826, 1898`; fault-table
  rows 8, 20, 21, 24.
- **Does NOT need.** The pairing; `DualMSM.check`.
- **Do.**
  1. State and prove the G1MSM coverage invariant: every G1 window `Mirror` names is an operand of
     some MSM call on every path that exits normally with `success = 1`.
  2. SEM leaf: the block computes the two MSM results as stated word/point functions, or poisons
     `success`, or reverts (`scalar_inv(0)`).
  3. The new obligation: normal exit with `success = 1` implies `∃ ms instW inst, Decoded R cd …`.
     Ingredients: step 1, `Holds.g1Decodes`, `decodeCalldata_isSome_iff`.
  4. ALG leaf: under a decoding, the two results are `toEip` of `left`, `right` of the Lean
     `multiPrepare` (reference-repaired, M1).
  5. The `x = 0` case: show the block reverts there using `hasMultiPointSet` (row 20), so no side
     condition is needed at F1.
- **Deliverable.** `pcs_blockSim`, `pcs_blockProgS` from leaves; `g1msm_coverage`; `decode_exists`.
- **Accept.** `#cone_sorries pcs_blockSim` lists the named leaves only; a falsifier render whose
  point sets are all singletons makes step 5's lemma fail (stated as a `¬` theorem on a toy plan).
- **Stop if.** The MSM loop's kernel check exceeds calibration C's threshold: apply D-P68's
  certificate decision first. A G1 window is found that no MSM reads: that is a soundness defect in
  the generated contract, not a proof gap — report it to the human immediately.
- **Guidance.** Point validity is established HERE and nowhere earlier. Before this exit `Agree` is
  vacuous; after it, it is the whole content.

### ROW.FP — FinalPairing row, restated

SEM · PROOF · box 2.5 h · strongest · after ROW.PCS, PL.1, REF.5, T3.5

- **Goal.** `BlockSim` and `BlockProgS` at `.finalPairing` for F1, proved.
- **Needs.** `Blocks/FinalPairing.lean` (`fp_pairing_algebra`: true as stated;
  `ec_pairing_contract`: false as stated in three ways, REVIEW-V3 RV-23);
  `fp_blockSim_of_blockSound` (`SoundnessV3.lean`, proved); `Holds.pairing2`; `PayloadAgrees.g1Base`,
  `.g2Base`, `.negSG2`; the literal `ec_pairing` helper.
- **Does NOT need.** A pairing implementation (the product is a parameter, W11).
- **Do.**
  1. Restate `ec_pairing_contract` at `c = permissive (callsOf product)`, with precondition
     `StageInv … .pcs ∨ Poisoned` (so `success ∈ {0, 1}`), and give the honest half a revert arm.
  2. Prove it by `wp_run` on the literal helper with `Bopen`: the `staticcall` forks over every
     permitted response; on success the response is the honest one.
  3. Export the poisoned half of the row without a snapshot argument.
  4. Close `fp_blockSim`, `fp_blockProgS` with `fp_blockSim_of_blockSound`.
- **Deliverable.** `fp_blockSim`, `fp_blockProgS`, the restated `ec_pairing_contract`.
- **Accept.** `#assert_axioms` on both rows: the standard three plus the slice pins; the old
  `ec_pairing_contract` text is refuted by a landed counterexample (`success = 3`), then deleted.
- **Stop if.** A base-point pin is not derivable from `PayloadAgrees` (then D-P62 or REF.7 is
  incomplete).

### PL.H — The headline

INFRA · PROOF · box 1 h · strongest · after every ROW card, TOT.1, SIM.5, SIM.6, ST.11–ST.13

- **Goal.** `theorem lowering_equivalence_poseidon (product : PairingProduct) :
  LoweringEquivalenceV3 poseidonRender product`, and `theorem poseidon_done : Done fixtureCd`.
- **Needs.** `lowering_equivalenceV3_of`; `two_outcomes_of_exitShape`, `rejects_of_sims`,
  `completeness_of_progs`; `poseidon_total` (TOT.1); `poseidon_valid` (now provable, `ValidV3`);
  `poseidon_inhabited`; `artifact_gate_poseidon`.
- **Does NOT need.** Any new proof. If one is needed, a leaf was mis-stated.
- **Do.** Apply the composition; add the `#assert_axioms` gates; delete `not_done_today`.
- **Deliverable.** The two theorems and the gates.
- **Accept.** PLAN-V3 §6, verbatim.
- **Stop if.** `#assert_axioms` reports an axiom outside the frozen list: do not extend the list;
  report the owner declaration.

### PL.E — End to end and the English statement

ALG · PROOF · box 2.5 h · strongest · after PL.H

- **Goal.** `EndToEndV3` at F1, and the English statement of PLAN-V3 §6 in `STATUS.md`.
- **Needs.** `Lowering.verifyNative_iff_msgs_codec` (proved); `entryFrame_inhabitedV3`;
  `calldata_roundtrip`, `calldata_canonical`, `repack_spec_of_decodeRust`
  (`Lowering/Calldata.lean:731, :790, :1276`, open) at the fixture layout; `G1CodecLawsV3` at
  `g1CodecC` (REF.10).
- **Does NOT need.** The three calldata lemmas for every layout: the fixture layout suffices.
- **Do.** Copy `verifyNative_iff_msgs_codec` into a V2 module (measure its cone with `#cone_in`);
  prove the three calldata lemmas at the fixture layout; derive `end_to_end_poseidon`; write the
  English statement from the report's output, itemised as §6 lists.
- **Deliverable.** `theorem end_to_end_poseidon`; the STATUS section.
- **Accept.** `#assert_axioms end_to_end_poseidon` with the frozen list; every item of §6's English
  statement is present and names the tool output it came from.
- **Stop if.** A calldata lemma is false at the fixture layout: land the counterexample (NEGATIVE).
